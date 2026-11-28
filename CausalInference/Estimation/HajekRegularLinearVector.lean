/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolutionVector
public import CausalInference.Estimation.HajekRegularLinear

/-!
# Regular asymptotically linear estimators of a vector parameter

Let `T_n` estimate `θ ∈ ℝ^p` and be asymptotically linear at `θ₀` on an i.i.d. sample with law
`P_θ₀`, coordinatewise with influence function `φ = (φ_1, …, φ_p)`, each `φ_j` square integrable
with mean zero. Write `C = E_θ₀[φ sᵀ]` for the cross moment of `φ` with the score and
`Σ = E_θ₀[φ φᵀ]` for the covariance of `φ`.

* `T` is regular at `θ₀` if and only if `C = 1`, and then its limit law is `N(0, Σ)`
  (`isHajekRegularVec_of_crossMoment_eq_one`, `crossMoment_eq_one_of_isHajekRegularVec`).
* If `C = 1`, then `Σ = I(θ₀)⁻¹ + Cov(φ - I(θ₀)⁻¹ s)` (`crossMoment_eq_inv_add`), so that
  `Σ - I(θ₀)⁻¹` is positive semidefinite and `Σ = I(θ₀)⁻¹` exactly when `φ = I(θ₀)⁻¹ s` almost
  everywhere (`crossMoment_eq_inv_iff`).
* A regular estimator with limit `N(0, V)` has `V = I(θ₀)⁻¹` if and only if it is
  asymptotically efficient (`hajek_eq_iff_isAsymptoticallyEfficientVec`); the scalar form is
  `hajek_eq_iff_isAsymptoticallyEfficient`.
* An estimator asymptotically linear with influence function `I(θ₀)⁻¹ s` is regular with limit
  `N(0, I(θ₀)⁻¹)` and efficient (`isHajekRegularVec_of_isAsymptoticallyLinear_inv`); in
  particular so is the maximum likelihood estimator, as a measurable statistic of the sample
  (`mle_isHajekRegularVec`).

The proofs reduce to the scalar theory along lines: for a direction `d` and a vector `t`, the
statistic `tᵀ (T_n - θ₀)` is asymptotically linear with influence function `tᵀ φ`, and in the line
through `θ₀` in the direction `d` the score is `dᵀ s`, so the scalar results give
`tᵀ C d = tᵀ d`.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*; A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 8; P. J. Bickel,
C. A. J. Klaassen, Y. Ritov and J. A. Wellner (1993), *Efficient and Adaptive Estimation for
Semiparametric Models*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix
open scoped Topology ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace

namespace CausalInference

/-! ### Cross moment matrices -/

section CrossMoment

variable {S : Type*} [MeasurableSpace S] {p : ℕ}

/-- The cross moment matrix `E_μ[u wᵀ]` of two vector functions, with entries
`∫ u_j w_k dμ`. -/
noncomputable def crossMoment (μ : Measure S) (u w : S → Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k ↦ ∫ x, u x j * w x k ∂μ

/-- The entry `M i j` of a matrix is `eᵢᵀ M eⱼ`. -/
theorem single_dotProduct_mulVec_single (M : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp [dotProduct, mulVec, Pi.single_apply]

/-- **Bilinear forms of a cross moment.** For square integrable `u` and `w`,
`E_μ[(aᵀ u)(bᵀ w)] = aᵀ E_μ[u wᵀ] b`. -/
theorem integral_dotProduct_mul_dotProduct {μ : Measure S} {u w : S → Fin p → ℝ}
    (hu : ∀ j, MemLp (fun x ↦ u x j) 2 μ) (hw : ∀ k, MemLp (fun x ↦ w x k) 2 μ)
    (a b : Fin p → ℝ) :
    ∫ x, (a ⬝ᵥ u x) * (b ⬝ᵥ w x) ∂μ = a ⬝ᵥ (crossMoment μ u w *ᵥ b) := by
  have hprod : ∀ j k, Integrable (fun x ↦ u x j * w x k) μ :=
    fun j k ↦ (hu j).integrable_mul (hw k)
  have e : (fun x ↦ (a ⬝ᵥ u x) * (b ⬝ᵥ w x)) =
      fun x ↦ ∑ j, ∑ k, a j * b k * (u x j * w x k) := by
    funext x
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [e, integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦
    (hprod j k).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum _ fun k _ ↦ (hprod j k).const_mul _]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_const_mul]
  simp only [crossMoment, Matrix.of_apply]
  ring

/-- A linear combination of square integrable functions is square integrable. -/
theorem memLp_dotProduct {μ : Measure S} {u : S → Fin p → ℝ}
    (hu : ∀ j, MemLp (fun x ↦ u x j) 2 μ) (a : Fin p → ℝ) :
    MemLp (fun x ↦ a ⬝ᵥ u x) 2 μ := by
  simp only [dotProduct]
  exact memLp_finsetSum _ fun j _ ↦ (hu j).const_mul (a j)

/-- The second moment matrix `E_μ[u uᵀ]` of a square integrable `u` is positive semidefinite. -/
theorem posSemidef_crossMoment {μ : Measure S} {u : S → Fin p → ℝ}
    (hu : ∀ j, MemLp (fun x ↦ u x j) 2 μ) : (crossMoment μ u u).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨IsHermitian.ext fun i j ↦ ?_, fun a ↦ ?_⟩
  · simp [crossMoment, mul_comm]
  · rw [star_trivial, ← integral_dotProduct_mul_dotProduct hu hu]
    exact integral_nonneg fun x ↦ mul_self_nonneg _

end CrossMoment

/-- A centered Gaussian law determines its covariance matrix. -/
theorem multivariateGaussian_zero_injective {p : ℕ} {V W : Matrix (Fin p) (Fin p) ℝ}
    (hV : V.PosSemidef) (hW : W.PosSemidef)
    (h : multivariateGaussian 0 V = multivariateGaussian 0 W) : V = W := by
  ext i j
  have e := congrArg (fun m ↦ covarianceBilin m (WithLp.toLp 2 (Pi.single i 1))
    (WithLp.toLp 2 (Pi.single j 1))) h
  simp only [covarianceBilin_multivariateGaussian hV, covarianceBilin_multivariateGaussian hW,
    single_dotProduct_mulVec_single] at e
  exact e

/-- Two matrices with the same bilinear forms are equal. -/
theorem ext_of_dotProduct_mulVec {p : ℕ} {M N : Matrix (Fin p) (Fin p) ℝ}
    (h : ∀ a b : Fin p → ℝ, a ⬝ᵥ (M *ᵥ b) = a ⬝ᵥ (N *ᵥ b)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rwa [single_dotProduct_mulVec_single, single_dotProduct_mulVec_single] at this

/-- `eᵢᵀ eᵢ = 1`. -/
theorem single_dotProduct_single_self {p : ℕ} (i : Fin p) :
    (Pi.single i 1 : Fin p → ℝ) ⬝ᵥ Pi.single i 1 = 1 := by
  rw [dotProduct_single, mul_one, Pi.single_eq_same]

/-- `eᵢᵀ eⱼ = 0` for `i ≠ j`. -/
theorem single_dotProduct_single_of_ne {p : ℕ} {i j : Fin p} (h : i ≠ j) :
    (Pi.single i 1 : Fin p → ℝ) ⬝ᵥ Pi.single j 1 = 0 := by
  rw [dotProduct_single, mul_one, Pi.single_eq_of_ne' h]

/-- **A matrix acting as the identity on every pair with `tᵀ d ≠ 0` is the identity.** The
pairs `(eᵢ, eᵢ)` give the diagonal and `(eᵢ, eᵢ + eⱼ)` the entries off the diagonal. -/
theorem eq_one_of_forall_dotProduct_mulVec {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (h : ∀ t d : Fin p → ℝ, t ⬝ᵥ d ≠ 0 → t ⬝ᵥ (C *ᵥ d) = t ⬝ᵥ d) : C = 1 := by
  have hd : ∀ i, C i i = 1 := fun i ↦ by
    have := h (Pi.single i 1) (Pi.single i 1) (by rw [single_dotProduct_single_self]; simp)
    rwa [single_dotProduct_mulVec_single, single_dotProduct_single_self] at this
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hd, one_apply_eq]
  · have := h (Pi.single i 1) (Pi.single i 1 + Pi.single j 1) (by
      rw [dotProduct_add, single_dotProduct_single_self, single_dotProduct_single_of_ne hij]
      norm_num)
    rw [mulVec_add, dotProduct_add, dotProduct_add, single_dotProduct_mulVec_single,
      single_dotProduct_mulVec_single, single_dotProduct_single_self,
      single_dotProduct_single_of_ne hij, hd] at this
    rw [one_apply_ne hij]
    linarith

/-- For a positive definite `M`, `aᵀ M⁻¹ b = bᵀ M⁻¹ a`. -/
theorem dotProduct_inv_mulVec_comm {p : ℕ} {M : Matrix (Fin p) (Fin p) ℝ} (hM : M.PosDef)
    (a b : Fin p → ℝ) : a ⬝ᵥ (M⁻¹ *ᵥ b) = b ⬝ᵥ (M⁻¹ *ᵥ a) := by
  have hsymm : (M⁻¹)ᵀ = M⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hM.isHermitian.inv
  rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, dotProduct_comm]

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {p : ℕ} {F : ParametricFamily (Fin p → ℝ) S}
  [SigmaFinite F.ν] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → S} {θ₀ : Fin p → ℝ}

omit [SigmaFinite F.ν] in
/-- The influence function of an asymptotically linear estimator is square integrable under
`P_θ₀` when the observations have law `P_θ₀`. -/
theorem memLp_law_of_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) {θhat : ℕ → Ω → ℝ} {a : ℝ} {φ : S → ℝ}
    (hlin : IsAsymptoticallyLinear θhat a φ O μ) : MemLp φ 2 (F.law θ₀) := by
  rw [← hlaw]
  exact (memLp_map_measure_iff hlin.measurable.aestronglyMeasurable (hO.aemeasurable 0)).2
    hlin.memLp

omit [SigmaFinite F.ν] in
/-- **Linear combinations of an asymptotically linear estimator.** If each coordinate of `T` is
asymptotically linear at `θ₀` with influence function `φ_j`, then `tᵀ T_n - tᵀ θ₀` is
asymptotically linear at `0` with influence function `tᵀ φ`. -/
theorem isAsymptoticallyLinear_dotProduct {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    {φ : S → Fin p → ℝ}
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ φ x j) O μ) (t : Fin p → ℝ) :
    IsAsymptoticallyLinear (fun n ω ↦ t ⬝ᵥ T n (fun i ↦ O i ω) - t ⬝ᵥ θ₀) 0
      (fun x ↦ t ⬝ᵥ φ x) O μ := by
  have h1 := IsAsymptoticallyLinear.sum_const_mul Finset.univ t fun j _ ↦ hlin j
  have h2 := h1.sub (IsAsymptoticallyLinear.const μ O (∑ j, t j * θ₀ j))
  rw [sub_self] at h2
  simpa only [dotProduct, sub_zero] using h2

/-- `x ↦ tᵀ T(x) - c` is measurable for measurable `T`. -/
theorem measurable_dotProduct_sub {n : ℕ} {T : (Fin n → S) → Fin p → ℝ} (hT : Measurable T)
    (t : Fin p → ℝ) (c : ℝ) : Measurable fun x ↦ t ⬝ᵥ T x - c := by
  simp only [dotProduct]
  exact (Finset.measurable_sum _ fun j _ ↦
    measurable_const.mul ((measurable_pi_apply j).comp hT)).sub_const _

/-- **Linear combinations under local alternatives along a line.** Under the hypotheses of the
vector theory and a measurable line through `θ₀` in a direction `d ≠ 0`, if each coordinate of
`T` is asymptotically linear at `θ₀` with influence function `φ_j`, then under `θ₀ + (h / √n) d`
the law of `√n (tᵀ T_n - tᵀ θ_n)` converges to `N(h (E[(tᵀ φ)(dᵀ s)] - tᵀ d), E[(tᵀ φ)²])`. This
is the scalar result `tendsto_integral_pi_law_of_isAsymptoticallyLinear` in the line, for the
statistic `tᵀ (T_n - θ₀)`, followed by the deterministic shift `h (1 - tᵀ d)`. -/
theorem tendsto_integral_pi_law_dotProduct (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef) {d : Fin p → ℝ}
    (hd : d ≠ 0) (hm : F.LineMeasurable θ₀ d) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n)) {φ : S → Fin p → ℝ}
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ φ x j) O μ) (t : Fin p → ℝ) (h : ℝ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ x, f (√(n : ℝ) * (t ⬝ᵥ T n x - t ⬝ᵥ (θ₀ + (√(n : ℝ))⁻¹ • (h • d))))
      ∂(F.pi n).law (θ₀ + (√(n : ℝ))⁻¹ • (h • d))) atTop
      (𝓝 (∫ y, f y ∂gaussianReal
        (h * (∫ x, (t ⬝ᵥ φ x) * (d ⬝ᵥ F.scoreVec θ₀ x) ∂F.law θ₀ - t ⬝ᵥ d))
        (∫ x, (t ⬝ᵥ φ x) ^ 2 ∂F.law θ₀).toNNReal)) := by
  obtain ⟨hR, hIpos, r', -, hsr, hdl⟩ := line_hypotheses hreg hs hI hd hm
  have hlaw' : μ.map (O 0) = (F.line θ₀ d).law 0 := by rw [line_law_zero]; exact hlaw
  set c := h * (1 - t ⬝ᵥ d) with hcdef
  have hcont : Continuous fun y : ℝ ↦ y + c := continuous_id.add continuous_const
  have key := tendsto_integral_pi_law_of_isAsymptoticallyLinear hO hlaw' hR hsr hdl hIpos
    (T := fun n x ↦ t ⬝ᵥ T n x - t ⬝ᵥ θ₀) (fun n ↦ measurable_dotProduct_sub (hTm n) t _)
    (isAsymptoticallyLinear_dotProduct hlin t) h (f.compContinuous ⟨_, hcont⟩)
  have he : ∫ x, (t ⬝ᵥ φ x) * (F.line θ₀ d).score 0 x ∂F.law θ₀ =
      ∫ x, (t ⬝ᵥ φ x) * (d ⬝ᵥ F.scoreVec θ₀ x) ∂F.law θ₀ :=
    integral_congr_ae ((line_score_zero_ae hreg d).mono fun x hx ↦ by simp only [hx])
  rw [line_law_zero, he] at key
  set E := ∫ x, (t ⬝ᵥ φ x) * (d ⬝ᵥ F.scoreVec θ₀ x) ∂F.law θ₀
  set σ := (∫ x, (t ⬝ᵥ φ x) ^ 2 ∂F.law θ₀).toNNReal
  have key' : Tendsto (fun n : ℕ ↦ ∫ x, f (√(n : ℝ) * ((t ⬝ᵥ T n x - t ⬝ᵥ θ₀) -
      (0 + h / √(n : ℝ))) + c) ∂(F.pi n).law (θ₀ + (0 + h / √(n : ℝ)) • d)) atTop
      (𝓝 (∫ y, f (y + c) ∂gaussianReal ((E - 1) * h) σ)) := key
  have hr : ∫ y, f (y + c) ∂gaussianReal ((E - 1) * h) σ =
      ∫ y, f y ∂gaussianReal (h * (E - t ⬝ᵥ d)) σ := by
    rw [← integral_map hcont.aemeasurable f.continuous.aestronglyMeasurable,
      gaussianReal_map_add_const]
    congr 2
    rw [hcdef]
    ring
  rw [hr] at key'
  refine key'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hθ : θ₀ + ((0 : ℝ) + h / √(n : ℝ)) • d = θ₀ + (√(n : ℝ))⁻¹ • (h • d) := by
    simp only [zero_add, smul_smul, div_eq_mul_inv, mul_comm]
  rw [hθ]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hcdef]
  refine congrArg f ?_
  field_simp
  ring

/-- **An asymptotically linear estimator with unit cross moment is regular.** Under the
hypotheses of the vector theory, with every line through `θ₀` measurable, let each coordinate
of the measurable estimator `T` be asymptotically linear at `θ₀` with influence function `φ_j`
on an i.i.d. sample with law `P_θ₀`. If `E_θ₀[φ sᵀ] = 1`, then `T` is regular at `θ₀` with limit
`N(0, E_θ₀[φ φᵀ])`. By the Cramér-Wold device it suffices that for every `t` the law of
`√n (tᵀ T_n - tᵀ θ_n)` under `θ_n = θ₀ + k / √n` tends to `N(0, E[(tᵀ φ)²])`, which is
`tendsto_integral_pi_law_dotProduct` along the line in the direction `k` (or `t` when `k = 0`),
where the mean `E[(tᵀ φ)(kᵀ s)] - tᵀ k` vanishes. -/
theorem isHajekRegularVec_of_crossMoment_eq_one (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ u, F.LineMeasurable θ₀ u) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n)) {φ : S → Fin p → ℝ}
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ φ x j) O μ)
    (hc : crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1) :
    F.IsHajekRegularVec T θ₀ (multivariateGaussian 0 (crossMoment (F.law θ₀) φ φ)) := by
  obtain ⟨ε, hε, hball, -⟩ := hreg.exists_ball_pos
  have hΘ : F.Θ ∈ 𝓝 θ₀ := Filter.mem_of_superset (ball_mem_nhds θ₀ hε) hball
  have hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀) := fun j ↦
    memLp_law_of_isAsymptoticallyLinear hO hlaw (hlin j)
  have hG := posSemidef_crossMoment hφ
  have hcross : ∀ t d : Fin p → ℝ,
      ∫ x, (t ⬝ᵥ φ x) * (d ⬝ᵥ F.scoreVec θ₀ x) ∂F.law θ₀ = t ⬝ᵥ d := fun t d ↦ by
    rw [integral_dotProduct_mul_dotProduct hφ hreg.memLp_scoreVec, hc, one_mulVec]
  have hvar : ∀ t : Fin p → ℝ, ∫ x, (t ⬝ᵥ φ x) ^ 2 ∂F.law θ₀ =
      t ⬝ᵥ (crossMoment (F.law θ₀) φ φ *ᵥ t) := fun t ↦ by
    simp_rw [sq]
    exact integral_dotProduct_mul_dotProduct hφ hφ t t
  refine ⟨hTm, fun k f ↦ ?_⟩
  let X : ∀ n : ℕ, (Fin n → S) → EuclideanSpace ℝ (Fin p) := fun n x ↦
    √(n : ℝ) • (WithLp.toLp 2 (T n x) - WithLp.toLp 2 (θ₀ + (√(n : ℝ))⁻¹ • k))
  have hX : ∀ n, Measurable (X n) := fun n ↦ by
    have h1 : Measurable fun x ↦ (WithLp.toLp 2 (T n x) : EuclideanSpace ℝ (Fin p)) :=
      (PiLp.continuous_toLp 2 _).measurable.comp (hTm n)
    exact (h1.sub_const _).const_smul (√(n : ℝ))
  let ν : ℕ → Measure (EuclideanSpace ℝ (Fin p)) := fun n ↦
    ((F.pi n).law (θ₀ + (√(n : ℝ))⁻¹ • k)).map (X n)
  have hν : ∀ᶠ n in atTop, IsProbabilityMeasure (ν n) :=
    (eventually_isProbabilityMeasure_pi_law hΘ k).mono fun n hn ↦ by infer_instance
  refine (tendsto_integral_of_forall_inner hν (fun t g ↦ ?_) f).congr fun n ↦
    integral_map (hX n).aemeasurable f.continuous.aestronglyMeasurable
  obtain ⟨t', rfl⟩ : ∃ t' : Fin p → ℝ, t = WithLp.toLp 2 t' := ⟨WithLp.ofLp t, rfl⟩
  have hci : Continuous fun y : EuclideanSpace ℝ (Fin p) ↦ ⟪y, WithLp.toLp 2 t'⟫ :=
    continuous_id.inner continuous_const
  rw [← integral_map hci.aemeasurable g.continuous.aestronglyMeasurable,
    multivariateGaussian_map_inner hG, WithLp.ofLp_toLp, ← hvar]
  have hL : ∀ n : ℕ, ∫ x, g ⟪x, WithLp.toLp 2 t'⟫ ∂ν n = ∫ x, g (√(n : ℝ) *
      (t' ⬝ᵥ T n x - t' ⬝ᵥ (θ₀ + (√(n : ℝ))⁻¹ • k))) ∂(F.pi n).law (θ₀ + (√(n : ℝ))⁻¹ • k) := by
    intro n
    rw [integral_map (f := fun y ↦ g ⟪y, WithLp.toLp 2 t'⟫) (hX n).aemeasurable
      (g.continuous.comp hci).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [X]
    rw [← WithLp.toLp_sub, ← WithLp.toLp_smul, inner_toLp_toLp, dotProduct_smul,
      dotProduct_sub, smul_eq_mul]
  refine Tendsto.congr (fun n ↦ (hL n).symm) ?_
  by_cases ht : t' = 0
  · subst ht
    have e : ∫ y, g y ∂gaussianReal 0 (∫ x, ((0 : Fin p → ℝ) ⬝ᵥ φ x) ^ 2 ∂F.law θ₀).toNNReal =
        g 0 := by simp [gaussianReal_zero_var]
    rw [e]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_isProbabilityMeasure_pi_law hΘ k] with n hn
    simp
  by_cases hk : k = 0
  · subst hk
    have h0 := tendsto_integral_pi_law_dotProduct hO hlaw hreg hs hI ht (hm t') hTm hlin t' 0 g
    simpa using h0
  · have h1 := tendsto_integral_pi_law_dotProduct hO hlaw hreg hs hI hk (hm k) hTm hlin t' 1 g
    rwa [one_smul, hcross, sub_self, mul_zero] at h1

/-- At an interior point of `Θ`, the limit law of a regular estimator is a probability
measure: the sample laws are eventually probability measures and the constant `1` is a test
function. -/
theorem IsHajekRegularVec.isProbabilityMeasure (hΘ : F.Θ ∈ 𝓝 θ₀)
    {T : ∀ n, (Fin n → S) → Fin p → ℝ} {L : Measure (EuclideanSpace ℝ (Fin p))}
    (hT : F.IsHajekRegularVec T θ₀ L) : IsProbabilityMeasure L := by
  have h1 := hT.tendsto 0 (BoundedContinuousFunction.const _ 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    smul_zero, add_zero] at h1
  refine isProbabilityMeasure_iff_real.2 (tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_))
  filter_upwards [eventually_isProbabilityMeasure_pi_law hΘ 0] with n hn
  rw [smul_zero, add_zero] at hn
  exact probReal_univ.symm

/-- **The cross moment of a regular asymptotically linear estimator along a line.** Under the
hypotheses of `tendsto_integral_pi_law_dotProduct`, if `T` is regular at `θ₀` with some limit
law, then `tᵀ E_θ₀[φ sᵀ] d = tᵀ d` whenever `tᵀ d ≠ 0`. The statistic
`(tᵀ T_n - tᵀ θ₀) / tᵀ d` is regular in the line through `θ₀` in the direction `d`
(`IsHajekRegularFunctional.isHajekRegular_line`) and asymptotically linear there with influence
function `tᵀ φ / tᵀ d`, so the scalar characterization
`exists_isHajekRegular_iff_integral_mul_score_eq_one` gives `E[(tᵀ φ)(dᵀ s)] = tᵀ d`. -/
theorem dotProduct_crossMoment_mulVec_of_isHajekRegularVec (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef) {d : Fin p → ℝ}
    (hm : F.LineMeasurable θ₀ d) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n)) {φ : S → Fin p → ℝ}
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ φ x j) O μ)
    {L : Measure (EuclideanSpace ℝ (Fin p))} (hT : F.IsHajekRegularVec T θ₀ L)
    {t : Fin p → ℝ} (htd : t ⬝ᵥ d ≠ 0) :
    t ⬝ᵥ (crossMoment (F.law θ₀) φ (F.scoreVec θ₀) *ᵥ d) = t ⬝ᵥ d := by
  obtain ⟨ε, hε, hball, -⟩ := hreg.exists_ball_pos
  have hΘ : F.Θ ∈ 𝓝 θ₀ := Filter.mem_of_superset (ball_mem_nhds θ₀ hε) hball
  have hd : d ≠ 0 := fun h0 ↦ htd (by rw [h0, dotProduct_zero])
  have hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀) := fun j ↦
    memLp_law_of_isAsymptoticallyLinear hO hlaw (hlin j)
  have := hT.isProbabilityMeasure hΘ
  obtain ⟨hR, hIpos, r', -, hsr, hdl⟩ := line_hypotheses hreg hs hI hd hm
  have hlaw' : μ.map (O 0) = (F.line θ₀ d).law 0 := by rw [line_law_zero]; exact hlaw
  have hψ : HasFDerivAt (fun θ ↦ t ⬝ᵥ θ) (gradCLM t) θ₀ := by
    simpa [← gradCLM_apply] using (gradCLM t).hasFDerivAt
  have hl := (hT.dotProduct t).isHajekRegular_line hΘ hψ (by rwa [gradCLM_apply])
  rw [gradCLM_apply] at hl
  have hl' : IsAsymptoticallyLinear
      (fun n ω ↦ (t ⬝ᵥ T n (fun i ↦ O i ω) - t ⬝ᵥ θ₀) / (t ⬝ᵥ d)) 0
      (fun x ↦ (t ⬝ᵥ d)⁻¹ * (t ⬝ᵥ φ x)) O μ := by
    have h := (isAsymptoticallyLinear_dotProduct hlin t).const_mul (t ⬝ᵥ d)⁻¹
    rw [mul_zero] at h
    simpa only [div_eq_inv_mul] using h
  have hc := (exists_isHajekRegular_iff_integral_mul_score_eq_one hO hlaw' hR hsr hdl hIpos
    (fun n ↦ (measurable_dotProduct_sub (hTm n) t _).div_const _) hl').1 ⟨_, hl⟩
  have he : ∫ x, (t ⬝ᵥ d)⁻¹ * (t ⬝ᵥ φ x) * (F.line θ₀ d).score 0 x ∂F.law θ₀ =
      (t ⬝ᵥ d)⁻¹ * ∫ x, (t ⬝ᵥ φ x) * (d ⬝ᵥ F.scoreVec θ₀ x) ∂F.law θ₀ := by
    rw [← integral_const_mul]
    exact integral_congr_ae ((line_score_zero_ae hreg d).mono fun x hx ↦ by
      simp only [hx, mul_assoc])
  rw [line_law_zero, he, integral_dotProduct_mul_dotProduct hφ hreg.memLp_scoreVec,
    inv_mul_eq_one₀ htd] at hc
  exact hc.symm

/-- **A regular asymptotically linear estimator has unit cross moment.** Under the hypotheses
of `isHajekRegularVec_of_crossMoment_eq_one`, if `T` is regular at `θ₀` with some limit law,
then `E_θ₀[φ sᵀ] = 1`. -/
theorem crossMoment_eq_one_of_isHajekRegularVec (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ u, F.LineMeasurable θ₀ u) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n)) {φ : S → Fin p → ℝ}
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ φ x j) O μ)
    {L : Measure (EuclideanSpace ℝ (Fin p))} (hT : F.IsHajekRegularVec T θ₀ L) :
    crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1 :=
  eq_one_of_forall_dotProduct_mulVec fun _ d htd ↦
    dotProduct_crossMoment_mulVec_of_isHajekRegularVec hO hlaw hreg hs hI (hm d) hTm hlin hT htd

/-- **Regularity of an asymptotically linear estimator is unit cross moment with the score.**
Under the hypotheses of `isHajekRegularVec_of_crossMoment_eq_one`, `T` is regular at `θ₀` with
some limit law if and only if `E_θ₀[φ sᵀ] = 1`. -/
theorem exists_isHajekRegularVec_iff_crossMoment_eq_one (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ u, F.LineMeasurable θ₀ u) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n)) {φ : S → Fin p → ℝ}
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ φ x j) O μ) :
    (∃ L, F.IsHajekRegularVec T θ₀ L) ↔ crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1 :=
  ⟨fun ⟨_, hT⟩ ↦ crossMoment_eq_one_of_isHajekRegularVec hO hlaw hreg hs hI hm hTm hlin hT,
    fun hc ↦ ⟨_, isHajekRegularVec_of_crossMoment_eq_one hO hlaw hreg hs hI hm hTm hlin hc⟩⟩

omit [SigmaFinite F.ν] [IsProbabilityMeasure μ] in
/-- **The convolution decomposition of the covariance.** At a regular point with positive
definite information, let `φ` be square integrable under `P_θ₀` with `E_θ₀[φ sᵀ] = 1`. Then
`E[φ φᵀ] = I(θ₀)⁻¹ + E[(φ - I⁻¹ s)(φ - I⁻¹ s)ᵀ]`: for all `a, b`, expanding
`(aᵀ φ - (I⁻¹ a)ᵀ s)(bᵀ φ - (I⁻¹ b)ᵀ s)` the cross terms are `aᵀ I⁻¹ b` each and the last term is
`(I⁻¹ a)ᵀ I (I⁻¹ b) = aᵀ I⁻¹ b`. -/
theorem crossMoment_eq_inv_add (hreg : F.IsRegularAtVec θ₀)
    (hI : (F.fisherInfoMatrix θ₀).PosDef) {φ : S → Fin p → ℝ}
    (hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀))
    (hc : crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1) :
    crossMoment (F.law θ₀) φ φ = (F.fisherInfoMatrix θ₀)⁻¹ +
      crossMoment (F.law θ₀) (fun x ↦ φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x)
        (fun x ↦ φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) := by
  have hsv := hreg.memLp_scoreVec
  have hψ : ∀ j, MemLp (fun x ↦ (φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j) 2
      (F.law θ₀) := fun j ↦
    (hφ j).sub (memLp_dotProduct hsv fun k ↦ (F.fisherInfoMatrix θ₀)⁻¹ j k)
  have hcross : ∀ a b : Fin p → ℝ,
      ∫ x, (a ⬝ᵥ φ x) * (b ⬝ᵥ F.scoreVec θ₀ x) ∂F.law θ₀ = a ⬝ᵥ b := fun a b ↦ by
    rw [integral_dotProduct_mul_dotProduct hφ hsv, hc, one_mulVec]
  have hd : ∀ (c : Fin p → ℝ) x, c ⬝ᵥ (φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) =
      c ⬝ᵥ φ x - ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ c) ⬝ᵥ F.scoreVec θ₀ x := fun c x ↦ by
    rw [dotProduct_sub, dotProduct_inv_mulVec_comm hI c, dotProduct_comm (F.scoreVec θ₀ x)]
  refine ext_of_dotProduct_mulVec fun a b ↦ ?_
  rw [add_mulVec, dotProduct_add, ← integral_dotProduct_mul_dotProduct hψ hψ]
  simp_rw [hd]
  have i1 : Integrable (fun x ↦ (a ⬝ᵥ φ x) * (b ⬝ᵥ φ x)) (F.law θ₀) :=
    (memLp_dotProduct hφ a).integrable_mul (memLp_dotProduct hφ b)
  have i2 : Integrable (fun x ↦ (a ⬝ᵥ φ x) *
      (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ b) ⬝ᵥ F.scoreVec θ₀ x)) (F.law θ₀) :=
    (memLp_dotProduct hφ a).integrable_mul (memLp_dotProduct hsv _)
  have i3 : Integrable (fun x ↦ (b ⬝ᵥ φ x) *
      (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ⬝ᵥ F.scoreVec θ₀ x)) (F.law θ₀) :=
    (memLp_dotProduct hφ b).integrable_mul (memLp_dotProduct hsv _)
  have i4 : Integrable (fun x ↦ (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ⬝ᵥ F.scoreVec θ₀ x) *
      (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ b) ⬝ᵥ F.scoreVec θ₀ x)) (F.law θ₀) :=
    (memLp_dotProduct hsv _).integrable_mul (memLp_dotProduct hsv _)
  have e : (fun x ↦ (a ⬝ᵥ φ x - ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ⬝ᵥ F.scoreVec θ₀ x) *
      (b ⬝ᵥ φ x - ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ b) ⬝ᵥ F.scoreVec θ₀ x)) = fun x ↦
      (a ⬝ᵥ φ x) * (b ⬝ᵥ φ x) -
        (a ⬝ᵥ φ x) * (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ b) ⬝ᵥ F.scoreVec θ₀ x) -
        (b ⬝ᵥ φ x) * (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ⬝ᵥ F.scoreVec θ₀ x) +
        (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ⬝ᵥ F.scoreVec θ₀ x) *
          (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ b) ⬝ᵥ F.scoreVec θ₀ x) := funext fun x ↦ by ring
  have i12 : Integrable (fun x ↦ (a ⬝ᵥ φ x) * (b ⬝ᵥ φ x) -
      (a ⬝ᵥ φ x) * (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ b) ⬝ᵥ F.scoreVec θ₀ x)) (F.law θ₀) :=
    i1.sub i2
  have i123 : Integrable (fun x ↦ (a ⬝ᵥ φ x) * (b ⬝ᵥ φ x) -
      (a ⬝ᵥ φ x) * (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ b) ⬝ᵥ F.scoreVec θ₀ x) -
      (b ⬝ᵥ φ x) * (((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ⬝ᵥ F.scoreVec θ₀ x)) (F.law θ₀) :=
    i12.sub i3
  rw [e, integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2,
    integral_dotProduct_mul_dotProduct hφ hφ, hcross, hcross,
    integral_dotProduct_scoreVec_mul hsv, mulVec_inv_mulVec hI,
    dotProduct_comm ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) b, ← dotProduct_inv_mulVec_comm hI a b]
  ring

omit [SigmaFinite F.ν] [IsProbabilityMeasure μ] in
/-- **Equality in the matrix bound.** Under the hypotheses of `crossMoment_eq_inv_add`,
`E_θ₀[φ φᵀ] - I(θ₀)⁻¹` is positive semidefinite, and `E_θ₀[φ φᵀ] = I(θ₀)⁻¹` if and only if
`φ = I(θ₀)⁻¹ s(θ₀; ·)` `P_θ₀`-almost everywhere. -/
theorem crossMoment_eq_inv_iff (hreg : F.IsRegularAtVec θ₀)
    (hI : (F.fisherInfoMatrix θ₀).PosDef) {φ : S → Fin p → ℝ}
    (hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀))
    (hc : crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1) :
    (crossMoment (F.law θ₀) φ φ - (F.fisherInfoMatrix θ₀)⁻¹).PosSemidef ∧
      (crossMoment (F.law θ₀) φ φ = (F.fisherInfoMatrix θ₀)⁻¹ ↔
        φ =ᵐ[F.law θ₀] fun x ↦ (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) := by
  have hsv := hreg.memLp_scoreVec
  have hψ : ∀ j, MemLp (fun x ↦ (φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j) 2
      (F.law θ₀) := fun j ↦
    (hφ j).sub (memLp_dotProduct hsv fun k ↦ (F.fisherInfoMatrix θ₀)⁻¹ j k)
  rw [crossMoment_eq_inv_add hreg hI hφ hc, add_sub_cancel_left, add_eq_left]
  refine ⟨posSemidef_crossMoment hψ, ⟨fun h0 ↦ ?_, fun h ↦ ?_⟩⟩
  · have hj : ∀ j, ∀ᵐ x ∂F.law θ₀,
        (φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j = 0 := by
      intro j
      have e := congrFun (congrFun h0 j) j
      simp only [crossMoment, of_apply] at e
      have := (integral_eq_zero_iff_of_nonneg (fun x ↦ mul_self_nonneg _)
        ((hψ j).integrable_mul (hψ j))).1 e
      filter_upwards [this] with x hx
      exact mul_self_eq_zero.1 hx
    filter_upwards [ae_all_iff.2 hj] with x hx
    funext j
    exact sub_eq_zero.1 (hx j)
  · ext i j
    simp only [crossMoment, of_apply]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h] with x hx
    simp [hx]

/-- **The matrix bound for regular asymptotically linear estimators.** Under the hypotheses of
`isHajekRegularVec_of_crossMoment_eq_one`, if `T` is regular at `θ₀` with limit `N(0, V)`, then
`E_θ₀[φ sᵀ] = 1`, `V = E_θ₀[φ φᵀ] = I(θ₀)⁻¹ + E[(φ - I⁻¹ s)(φ - I⁻¹ s)ᵀ]`, `V - I(θ₀)⁻¹` is
positive semidefinite, and `V = I(θ₀)⁻¹` if and only if `φ = I(θ₀)⁻¹ s` almost everywhere. -/
theorem hajek_isAsymptoticallyLinear_vec (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ u, F.LineMeasurable θ₀ u) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n)) {φ : S → Fin p → ℝ}
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ φ x j) O μ)
    {V : Matrix (Fin p) (Fin p) ℝ} (hV : V.PosSemidef)
    (hT : F.IsHajekRegularVec T θ₀ (multivariateGaussian 0 V)) :
    crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1 ∧ V = crossMoment (F.law θ₀) φ φ ∧
      V = (F.fisherInfoMatrix θ₀)⁻¹ +
        crossMoment (F.law θ₀) (fun x ↦ φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x)
          (fun x ↦ φ x - (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) ∧
      (V - (F.fisherInfoMatrix θ₀)⁻¹).PosSemidef ∧
      (V = (F.fisherInfoMatrix θ₀)⁻¹ ↔
        φ =ᵐ[F.law θ₀] fun x ↦ (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) := by
  have hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀) := fun j ↦
    memLp_law_of_isAsymptoticallyLinear hO hlaw (hlin j)
  have hc := crossMoment_eq_one_of_isHajekRegularVec hO hlaw hreg hs hI hm hTm hlin hT
  have hT' := isHajekRegularVec_of_crossMoment_eq_one hO hlaw hreg hs hI hm hTm hlin hc
  have hVG : V = crossMoment (F.law θ₀) φ φ := by
    refine multivariateGaussian_zero_injective hV (posSemidef_crossMoment hφ)
      (ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_)
    exact tendsto_nhds_unique (hT.tendsto 0 f) (hT'.tendsto 0 f)
  obtain ⟨h1, h2⟩ := crossMoment_eq_inv_iff hreg hI hφ hc
  rw [← hVG] at h1 h2
  exact ⟨hc, hVG, hVG.trans (crossMoment_eq_inv_add hreg hI hφ hc), h1, h2⟩

/-! ### Efficiency -/

/-- **A regular estimator on an i.i.d. sample.** Under `θ₀`, on every i.i.d. sample with law
`P_θ₀`, `√n (T_n(O_0, …, O_{n-1}) - θ₀)` converges in distribution to the limit law. -/
theorem IsHajekRegularVec.tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hθ₀ : θ₀ ∈ F.Θ) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    {L : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure L]
    (hT : F.IsHajekRegularVec T θ₀ L) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (WithLp.toLp 2 (T n fun i ↦ O i ω) -
      WithLp.toLp 2 θ₀ : EuclideanSpace ℝ (Fin p))) atTop id (fun _ ↦ μ) L := by
  have hR : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ O i ω) μ := fun n ↦
    AEMeasurable.of_eval fun i ↦ hO.aemeasurable i
  have hTc : ∀ n : ℕ, Measurable fun x : Fin n → S ↦ (√(n : ℝ) • (WithLp.toLp 2 (T n x) -
      WithLp.toLp 2 θ₀) : EuclideanSpace ℝ (Fin p)) := fun n ↦ by
    have h1 : Measurable fun x ↦ (WithLp.toLp 2 (T n x) : EuclideanSpace ℝ (Fin p)) :=
      (PiLp.continuous_toLp 2 _).measurable.comp (hT.measurable n)
    exact (h1.sub_const _).const_smul (√(n : ℝ))
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun n ↦ (hTc n).comp_aemeasurable (hR n)) aemeasurable_id).2 fun f ↦ ?_
  have h0 := hT.tendsto 0 f
  simp only [smul_zero, add_zero] at h0
  refine h0.congr fun n ↦ ?_
  have hmap : μ.map (fun ω (i : Fin n) ↦ O i ω) = (F.pi n).law θ₀ := by
    rw [hO.map_fin_eq_pi n, hlaw, pi_law n hθ₀]
  rw [← hmap]
  exact integral_map (hR n) (f.continuous.measurable.comp (hTc n)).aestronglyMeasurable

/-- **Equality in the Hájek bound is asymptotic efficiency, vector parameter.** At a regular
point with positive definite information, a regular estimator with limit `N(0, V)` has
`V = I(θ₀)⁻¹` if and only if it is asymptotically efficient on every i.i.d. sample with law
`P_θ₀`, by uniqueness of limits in distribution and of the covariance of a Gaussian law. -/
theorem hajek_eq_iff_isAsymptoticallyEfficientVec (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀)
    (hI : (F.fisherInfoMatrix θ₀).PosDef) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    {V : Matrix (Fin p) (Fin p) ℝ} (hV : V.PosSemidef)
    (hT : F.IsHajekRegularVec T θ₀ (multivariateGaussian 0 V)) :
    V = (F.fisherInfoMatrix θ₀)⁻¹ ↔
      F.IsAsymptoticallyEfficientVec (fun n ω ↦ T n fun i ↦ O i ω) θ₀ μ := by
  obtain ⟨ε, hε, hball, -⟩ := hreg.exists_ball_pos
  have hθ₀ : θ₀ ∈ F.Θ := hball (mem_ball_self hε)
  have hD := hT.tendstoInDistribution hO hlaw hθ₀
  refine ⟨fun h ↦ by subst h; exact ⟨hreg, hI, hD⟩, fun h ↦ ?_⟩
  refine multivariateGaussian_zero_injective hV hI.inv.posSemidef ?_
  simpa using tendstoInDistribution_unique _ hD h.2.2

omit [SigmaFinite F.ν] in
/-- **Equality in the Hájek bound is asymptotic efficiency, scalar parameter.** In a scalar
family regular at `t₀` with positive information, a regular estimator with limit `N(0, V)` has
`V = I(t₀)⁻¹` if and only if it is asymptotically efficient on every i.i.d. sample with law
`P_t₀`, by uniqueness of limits in distribution and of the variance of a Gaussian law. -/
theorem hajek_eq_iff_isAsymptoticallyEfficient {G : ParametricFamily ℝ S} [SigmaFinite G.ν]
    {t₀ : ℝ} (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = G.law t₀) (hreg : G.IsRegularAt t₀)
    (hI : 0 < G.fisherInfo t₀) {T : ∀ n, (Fin n → S) → ℝ} {V : ℝ≥0}
    (hT : G.IsHajekRegular T t₀ (gaussianReal 0 V)) :
    (V : ℝ) = (G.fisherInfo t₀)⁻¹ ↔
      G.IsAsymptoticallyEfficient (fun n ω ↦ T n fun i ↦ O i ω) t₀ μ := by
  have hD := hT.tendstoInDistribution hO hlaw (mem_of_mem_nhds hreg.mem_nhds)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hV : V = (G.fisherInfo t₀)⁻¹.toNNReal := by rw [← h, Real.toNNReal_coe]
    subst hV
    exact ⟨hreg, hI, hD⟩
  · have e := tendstoInDistribution_unique _ hD h.2.2
    simp only [Measure.map_id] at e
    rw [(gaussianReal_ext_iff.1 e).2, Real.coe_toNNReal _ (inv_nonneg.2 hI.le)]

/-- **An estimator asymptotically linear in the efficient influence function is regular and
efficient.** Under the hypotheses of the vector theory, with every line through `θ₀`
measurable, if each coordinate of the measurable estimator `T` is asymptotically linear at `θ₀`
with influence function `(I(θ₀)⁻¹ s(θ₀; ·))_j`, then `T` is regular at `θ₀` with limit
`N(0, I(θ₀)⁻¹)` and asymptotically efficient. The efficient influence function has cross
moment `I⁻¹ I = 1` with the score and covariance `I⁻¹ I I⁻¹ = I⁻¹`. -/
theorem isHajekRegularVec_of_isAsymptoticallyLinear_inv (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ u, F.LineMeasurable θ₀ u) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n))
    (hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x) j) O μ) :
    F.IsHajekRegularVec T θ₀ (multivariateGaussian 0 (F.fisherInfoMatrix θ₀)⁻¹) ∧
      F.IsAsymptoticallyEfficientVec (fun n ω ↦ T n fun i ↦ O i ω) θ₀ μ := by
  have hsv := hreg.memLp_scoreVec
  set φ : S → Fin p → ℝ := fun x ↦ (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ F.scoreVec θ₀ x with hφdef
  have hφ : ∀ j, MemLp (fun x ↦ φ x j) 2 (F.law θ₀) := fun j ↦
    memLp_dotProduct hsv fun k ↦ (F.fisherInfoMatrix θ₀)⁻¹ j k
  have hdφ : ∀ (a : Fin p → ℝ) x, a ⬝ᵥ φ x =
      ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ⬝ᵥ F.scoreVec θ₀ x := fun a x ↦ by
    rw [hφdef, dotProduct_inv_mulVec_comm hI a, dotProduct_comm]
  have hc : crossMoment (F.law θ₀) φ (F.scoreVec θ₀) = 1 := by
    refine ext_of_dotProduct_mulVec fun a b ↦ ?_
    rw [← integral_dotProduct_mul_dotProduct hφ hsv, one_mulVec]
    simp_rw [hdφ]
    rw [integral_dotProduct_scoreVec_mul hsv, dotProduct_comm, dotProduct_inv_mulVec_comm hI,
      mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hI.isUnit), one_mulVec]
  have hG : crossMoment (F.law θ₀) φ φ = (F.fisherInfoMatrix θ₀)⁻¹ := by
    refine ext_of_dotProduct_mulVec fun a b ↦ ?_
    rw [← integral_dotProduct_mul_dotProduct hφ hφ]
    simp_rw [hdφ]
    rw [integral_dotProduct_scoreVec_mul hsv, mulVec_inv_mulVec hI, dotProduct_comm,
      dotProduct_inv_mulVec_comm hI]
  have hT := isHajekRegularVec_of_crossMoment_eq_one hO hlaw hreg hs hI hm hTm hlin hc
  rw [hG] at hT
  exact ⟨hT, (hajek_eq_iff_isAsymptoticallyEfficientVec hO hlaw hreg hI
    hI.inv.posSemidef hT).1 rfl⟩

/-- **The maximum likelihood estimator is regular.** Under the hypotheses of the vector theory,
with every line through `θ₀` measurable, let the maximum likelihood estimator be a measurable
statistic `T n` of the sample that is consistent and solves the likelihood equation with
probability tending to one. Then `T` is regular at `θ₀` with limit `N(0, I(θ₀)⁻¹)`, and it is
asymptotically efficient: it is asymptotically linear with influence function `I(θ₀)⁻¹ s`
(`mle_isAsymptoticallyLinear_vec`). -/
theorem mle_isHajekRegularVec (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ u, F.LineMeasurable θ₀ u) {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    (hTm : ∀ n, Measurable (T n))
    (hθ : TendstoInMeasure μ (fun n ω ↦ T n fun i ↦ O i ω) atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ
      (fun n ↦ {ω | ∑ i ∈ range n, F.scoreVec (T n fun i ↦ O i ω) (O i ω) = 0})) :
    F.IsHajekRegularVec T θ₀ (multivariateGaussian 0 (F.fisherInfoMatrix θ₀)⁻¹) ∧
      F.IsAsymptoticallyEfficientVec (fun n ω ↦ T n fun i ↦ O i ω) θ₀ μ :=
  isHajekRegularVec_of_isAsymptoticallyLinear_inv hO hlaw hreg hs hI hm hTm
    (mle_isAsymptoticallyLinear_vec hO hlaw hreg hs hI hθ hroot)

end ParametricFamily

end CausalInference
