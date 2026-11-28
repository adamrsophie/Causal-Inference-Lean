/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CochranQ
public import CausalInference.Estimation.ChiSquared

/-!
# Meta-analysis: the null law of Cochran's `Q`

Under the Gaussian common effect model with `k = m + 1` studies, Cochran's `Q` has the
chi-square law with `m = k - 1` degrees of freedom, the pooled estimate has the law
`N(θ, 1 / ∑ wᵢ)`, and the two are independent (Cochran 1954). The statement proved here allows
a common scale: if `Yᵢ ~ N(θ, σ² vᵢ)` independently and the weights use `vᵢ`, then
`(θ̂, Q / σ²)` has the law `N(θ, σ² / ∑ wᵢ) ⊗ χ²ₘ` (`hasLaw_ivwEstimate_cochranQ`).

**Proof.** Standardize: `Zᵢ = (Yᵢ - θ) / √(σ² vᵢ)` is a standard Gaussian vector
(`pi_gaussianReal_map_standardize`). With the unit vector `uᵢ = √(wᵢ / ∑ wⱼ)`
(`ivwUnitVector`), `⟪u, Z⟫ = √(∑ wᵢ) (θ̂ - θ) / σ` and `‖Z‖² - ⟪u, Z⟫² = Q / σ²`
(`inner_ivwUnitVector_standardize`, `norm_sq_standardize_sub`). Extend `u` to an orthonormal
basis `b₀ = u, b₁, …, bₘ`; the coordinates `⟪bⱼ, Z⟫` are independent standard Gaussians
(`stdGaussian_map_inner_orthonormal`), and by Parseval `Q / σ² = ∑_{j ≥ 1} ⟪bⱼ, Z⟫²`, a
function of coordinates other than the one that determines `θ̂`.

The same orthonormal coordinates give the **chi-square law of a projected Gaussian vector**:
for a symmetric idempotent matrix `M` of rank `r` and `Z ~ N(0, I)`, `Zᵀ M Z ~ χ²ᵣ`
(`multivariateGaussian_map_quadForm_of_idempotent`).

## Main definitions

* `ivwUnitVector`, `standardize`, `studentT`.

## Main results

* `stdGaussian_map_inner_orthonormal`, `chiSquared_eq_map_pi`, `stdGaussian_map_sum_sq`,
  `pi_map_tStat`, `stdGaussian_map_tStat`, `pi_gaussianReal_map_standardize`,
  `multivariateGaussian_map_quadForm_of_idempotent`.
* `hasLaw_ivwEstimate_cochranQ`, `hasLaw_cochranQ_div`, `hasLaw_ivwEstimate`,
  `indepFun_ivwEstimate_cochranQ`, and `IsGaussianCommonEffectModel.hasLaw_cochranQ` with the
  independence and the law of `θ̂` in the model.

## References

* W. G. Cochran, *The combination of estimates from different experiments*, Biometrics 10
  (1954).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped RealInnerProductSpace NNReal

/-! ### Orthonormal coordinates of a standard Gaussian vector -/

section GaussianTools

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Orthonormal coordinates of a standard Gaussian vector**: for an orthonormal family
`(bⱼ)_{j ∈ κ}` in `ℝ^ι` and `Z ~ N(0, I)`, the coordinates `(⟪bⱼ, Z⟫)ⱼ` form a standard Gaussian
vector in `ℝ^κ`. They are `A Z` for the matrix `A` with rows `bⱼ`, and `A Aᵀ = I`. -/
theorem stdGaussian_map_inner_orthonormal {b : κ → EuclideanSpace ℝ ι} (hb : Orthonormal ℝ b) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => WithLp.toLp 2 fun j => ⟪b j, z⟫) =
      stdGaussian (EuclideanSpace ℝ κ) := by
  classical
  set A : Matrix κ ι ℝ := Matrix.of fun j i => b j i with hA
  have hAA : A * (1 : Matrix ι ι ℝ) * Aᵀ = 1 := by
    ext j l
    have h := orthonormal_iff_ite.1 hb j l
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h
    simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, hA, Matrix.of_apply,
      Matrix.one_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hfun : (fun z : EuclideanSpace ℝ ι => WithLp.toLp 2 fun j => ⟪b j, z⟫) =
      matrixCLM A := by
    ext z j
    simp [matrixCLM_apply, hA, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  rw [hfun, ← multivariateGaussian_zero_one, multivariateGaussian_map_matrixCLM PosSemidef.one 0 A,
    hAA, map_zero, multivariateGaussian_zero_one]

/-- `χ²ₘ` is the law of `X₁² + ⋯ + Xₘ²` for independent standard Gaussians `X₁, …, Xₘ`. -/
theorem chiSquared_eq_map_pi (m : ℕ) :
    chiSquared m = (Measure.pi fun _ : Fin m => gaussianReal 0 1).map fun x => ∑ j, x j ^ 2 := by
  rw [chiSquared, multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  simp [EuclideanSpace.real_norm_sq_eq]

/-- **The chi-square law of squared orthonormal coordinates**: for an orthonormal family
`b₁, …, bₘ` and `Z ~ N(0, I)`, `∑ⱼ ⟪bⱼ, Z⟫² ~ χ²ₘ`. -/
theorem stdGaussian_map_sum_sq {m : ℕ} {b : Fin m → EuclideanSpace ℝ ι} (hb : Orthonormal ℝ b) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => ∑ j, ⟪b j, z⟫ ^ 2) = chiSquared m := by
  have h : (fun z : EuclideanSpace ℝ ι => ∑ j, ⟪b j, z⟫ ^ 2) =
      (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖ ^ 2) ∘
        (fun z => WithLp.toLp 2 fun j => ⟪b j, z⟫) := by
    ext z
    simp [EuclideanSpace.real_norm_sq_eq]
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map_inner_orthonormal hb,
    chiSquared, multivariateGaussian_zero_one]

/-- **Student's `t` law with `m` degrees of freedom**: the law of `X / √(V / m)` for independent
`X ~ N(0, 1)` and `V ~ χ²ₘ`. -/
noncomputable def studentT (m : ℕ) : Measure ℝ :=
  ((gaussianReal 0 1).prod (chiSquared m)).map fun p => p.1 / √(p.2 / m)

instance (m : ℕ) : IsProbabilityMeasure (studentT m) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- **The `t` ratio of independent standard Gaussians**: for independent standard Gaussians
`X₀, …, Xₘ`, `X₀ / √((X₁² + ⋯ + Xₘ²) / m) ~ tₘ`. Proof: split the product measure as
`N(0, 1) ⊗ N(0, 1)^m`. -/
theorem pi_map_tStat (m : ℕ) :
    (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1).map
      (fun x => x 0 / √((∑ j : Fin m, x j.succ ^ 2) / m)) = studentT m := by
  have e := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0
  have hfun : (fun x : Fin (m + 1) → ℝ => x 0 / √((∑ j : Fin m, x j.succ ^ 2) / m)) =
      (fun p : ℝ × (Fin m → ℝ) => p.1 / √((∑ j, p.2 j ^ 2) / m)) ∘
        MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 := by
    ext x
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
  have hprod := Measure.map_prod_map (gaussianReal 0 1)
    (Measure.pi fun _ : Fin m => gaussianReal 0 1) measurable_id
    (show Measurable fun x : Fin m → ℝ => ∑ j, x j ^ 2 by fun_prop)
  rw [Measure.map_id] at hprod
  rw [hfun, ← Measure.map_map (by fun_prop) e.measurable, e.map_eq, studentT,
    chiSquared_eq_map_pi, hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **The `t` ratio of orthonormal coordinates**: if `u, b₁, …, bₘ` is an orthonormal family and
`Z ~ N(0, I)`, then `⟪u, Z⟫ / √(∑ⱼ ⟪bⱼ, Z⟫² / m) ~ tₘ`. -/
theorem stdGaussian_map_tStat {m : ℕ} {u : EuclideanSpace ℝ ι} {b : Fin m → EuclideanSpace ℝ ι}
    (hb : Orthonormal ℝ (Fin.cons u b : Fin (m + 1) → EuclideanSpace ℝ ι)) :
    (stdGaussian (EuclideanSpace ℝ ι)).map
      (fun z => ⟪u, z⟫ / √((∑ j, ⟪b j, z⟫ ^ 2) / m)) = studentT m := by
  have h : (fun z : EuclideanSpace ℝ ι => ⟪u, z⟫ / √((∑ j, ⟪b j, z⟫ ^ 2) / m)) =
      ((fun x : Fin (m + 1) → ℝ => x 0 / √((∑ j : Fin m, x j.succ ^ 2) / m)) ∘
        WithLp.ofLp) ∘ (fun z => WithLp.toLp 2 fun j =>
          ⟪(Fin.cons u b : Fin (m + 1) → EuclideanSpace ℝ ι) j, z⟫) := by
    ext z
    simp
  have hpi : (stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))).map WithLp.ofLp =
      Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1 := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map_inner_orthonormal hb,
    ← Measure.map_map (by fun_prop) (by fun_prop), hpi, pi_map_tStat]

/-- The standardization `x ↦ ((xᵢ - μᵢ) / √sᵢ)ᵢ`. -/
noncomputable def standardize (μ s : ι → ℝ) (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => (x i - μ i) / √(s i)

omit [Fintype ι] in
@[fun_prop]
theorem measurable_standardize (μ s : ι → ℝ) : Measurable (standardize μ s) := by
  unfold standardize
  fun_prop

/-- **Standardization**: if the coordinates are independent `N(μᵢ, sᵢ)` with `sᵢ > 0`, then
`((xᵢ - μᵢ) / √sᵢ)ᵢ` is a standard Gaussian vector. -/
theorem pi_gaussianReal_map_standardize {μ s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    (Measure.pi fun i => gaussianReal (μ i) (s i).toNNReal).map (standardize μ s) =
      stdGaussian (EuclideanSpace ℝ ι) := by
  have h1 : standardize μ s = WithLp.toLp 2 ∘ fun x i => (x i - μ i) / √(s i) := rfl
  have h2 : ∀ i, (gaussianReal (μ i) (s i).toNNReal).map (fun t => (t - μ i) / √(s i)) =
      gaussianReal 0 1 := by
    intro i
    have : (fun t => (t - μ i) / √(s i)) = (· / √(s i)) ∘ (· - μ i) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_div_const, sub_self, zero_div]
    congr 1
    ext
    simp [Real.sq_sqrt (hs i).le, (hs i).le, (hs i).ne']
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.pi_map_pi (f := fun i t => (t - μ i) / √(s i)) (fun i => by fun_prop)]
  simp only [h2]
  exact map_pi_eq_stdGaussian

/-- **The chi-square law of a projected Gaussian vector.** If `M` is symmetric and idempotent,
`Mᵀ = M = M²`, of rank `r`, and `Z ~ N(0, I)`, then `Zᵀ M Z ~ χ²ᵣ`. With an orthonormal basis
`b₁, …, bᵣ` of the range of `M`, `Zᵀ M Z = ‖M Z‖² = ∑ⱼ ⟪bⱼ, Z⟫²`, and the coordinates are
independent standard Gaussians. -/
theorem multivariateGaussian_map_quadForm_of_idempotent [DecidableEq ι] {r : ℕ}
    {M : Matrix ι ι ℝ} (hsymm : Mᵀ = M) (hidem : M * M = M) (hrank : M.rank = r) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map (quadForm M) = chiSquared r := by
  set L := Matrix.toEuclideanLin M with hL
  set V : Submodule ℝ (EuclideanSpace ℝ ι) := LinearMap.range L
  have hfin : Module.finrank ℝ V = r := by
    rw [← hrank, Matrix.rank_eq_finrank_range_toLin M (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis]
    rfl
  set B := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
  set b : Fin r → EuclideanSpace ℝ ι := fun j => (B j : EuclideanSpace ℝ ι)
  have hb : Orthonormal ℝ b := B.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hLapp : ∀ x, L x = WithLp.toLp 2 (M *ᵥ WithLp.ofLp x) := fun x => rfl
  have hLL : ∀ x, L (L x) = L x := by
    intro x
    rw [hLapp, hLapp, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hidem]
  have hsym : ∀ x y, ⟪L x, y⟫ = ⟪x, L y⟫ := by
    intro x y
    simp only [hLapp, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
  have hfix : ∀ j, L (b j) = b j := by
    intro j
    obtain ⟨w, hw⟩ := (B j).2
    rw [show b j = L w from hw.symm, hLL]
  have hpt : ∀ z : EuclideanSpace ℝ ι, quadForm M z = ‖WithLp.toLp 2 fun j => ⟪b j, z⟫‖ ^ 2 := by
    intro z
    have hmem : L z ∈ V := LinearMap.mem_range_self L z
    have hj : ∀ j, ⟪b j, z⟫ = ⟪B j, (⟨L z, hmem⟩ : V)⟫ := by
      intro j
      rw [Submodule.coe_inner]
      change ⟪b j, z⟫ = ⟪b j, L z⟫
      rw [← hsym, hfix]
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hj]
    rw [B.sum_sq_inner_right, ← Submodule.norm_coe, ← real_inner_self_eq_norm_sq]
    change _ = ⟪L z, L z⟫
    rw [hsym, hLL, hLapp, EuclideanSpace.inner_eq_star_dotProduct, quadForm]
    simp only [star_trivial]
    exact dotProduct_comm _ _
  have hfun : quadForm M = (fun x : EuclideanSpace ℝ (Fin r) => ‖x‖ ^ 2) ∘
      fun z : EuclideanSpace ℝ ι => WithLp.toLp 2 fun j => ⟪b j, z⟫ := funext hpt
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), multivariateGaussian_zero_one,
    stdGaussian_map_inner_orthonormal hb, chiSquared, multivariateGaussian_zero_one]

end GaussianTools

/-! ### Whitening the inverse variance weighted model -/

section Whitening

variable {ι : Type*} [Fintype ι] {v : ι → ℝ}

/-- The unit vector `uᵢ = √(wᵢ / ∑ⱼ wⱼ)` along which the pooled estimate is read off. -/
noncomputable def ivwUnitVector (v : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => √(ivWeight v i / ∑ j, ivWeight v j)

/-- `u` is a unit vector (positive variances, at least one study). -/
theorem norm_ivwUnitVector [Nonempty ι] (hv : ∀ i, 0 < v i) : ‖ivwUnitVector v‖ = 1 := by
  have hW := sum_ivWeight_pos hv
  rw [ivwUnitVector, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (div_pos (ivWeight_pos hv _) hW).le]
  rw [sum_ivWeight_div hv, Real.sqrt_one]

/-- **The pooled estimate as a coordinate**: with `Zᵢ = (yᵢ - θ) / √(σ² vᵢ)`,
`⟪u, Z⟫ = √(∑ wᵢ) (θ̂ - θ) / √σ²`. -/
theorem inner_ivwUnitVector_standardize [Nonempty ι] (hv : ∀ i, 0 < v i) {σ2 : ℝ}
    (hσ : 0 < σ2) (θ : ℝ) (y : ι → ℝ) :
    ⟪ivwUnitVector v, standardize (fun _ => θ) (fun i => σ2 * v i) y⟫ =
      √(∑ i, ivWeight v i) * (ivwEstimate v y - θ) / √σ2 := by
  have hW := sum_ivWeight_pos hv
  have hsW : 0 < √(∑ i, ivWeight v i) := Real.sqrt_pos.2 hW
  have hsσ : 0 < √σ2 := Real.sqrt_pos.2 hσ
  have hterm : ∀ i, (y i - θ) / √(σ2 * v i) * √(ivWeight v i / ∑ j, ivWeight v j) =
      ivWeight v i * (y i - θ) / (√(∑ j, ivWeight v j) * √σ2) := by
    intro i
    have hsi : 0 < √(v i) := Real.sqrt_pos.2 (hv i)
    rw [Real.sqrt_div (ivWeight_pos hv i).le, Real.sqrt_mul hσ.le, ivWeight, one_div,
      Real.sqrt_inv]
    have h : v i = √(v i) ^ 2 := (Real.sq_sqrt (hv i).le).symm
    set a := √(v i)
    rw [h]
    field_simp
  simp only [ivwUnitVector, standardize, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [hterm, ← Finset.sum_div, sum_ivWeight_mul_sub hv]
  rw [div_eq_div_iff (by positivity) hsσ.ne']
  have h2 := Real.mul_self_sqrt hW.le
  linear_combination (-(ivwEstimate v y - θ) * √σ2) * h2

/-- **`Q` as a squared length**: with `Zᵢ = (yᵢ - θ) / √(σ² vᵢ)`,
`‖Z‖² - ⟪u, Z⟫² = Q / σ²`. -/
theorem norm_sq_standardize_sub [Nonempty ι] (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2)
    (θ : ℝ) (y : ι → ℝ) :
    ‖standardize (fun _ => θ) (fun i => σ2 * v i) y‖ ^ 2 -
        ⟪ivwUnitVector v, standardize (fun _ => θ) (fun i => σ2 * v i) y⟫ ^ 2 =
      cochranQ v y / σ2 := by
  have hW := sum_ivWeight_pos hv
  have hsq : ∀ i, ((y i - θ) / √(σ2 * v i)) ^ 2 = ivWeight v i * (y i - θ) ^ 2 / σ2 := by
    intro i
    have := hv i
    rw [div_pow, Real.sq_sqrt (mul_pos hσ (hv i)).le, ivWeight]
    field_simp
  rw [inner_ivwUnitVector_standardize hv hσ, standardize, EuclideanSpace.real_norm_sq_eq]
  simp only [hsq, ← Finset.sum_div]
  rw [cochranQ_eq_sub hv y θ, div_pow, mul_pow, Real.sq_sqrt hW.le, Real.sq_sqrt hσ.le]
  ring

/-- An orthonormal basis of `ℝ^ι`, `k = m + 1`, whose first vector is `u`. -/
theorem exists_orthonormalBasis_ivwUnitVector {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (hv : ∀ i, 0 < v i) :
    ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ ι), b 0 = ivwUnitVector v := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hu := norm_ivwUnitVector hv
  have hon : Orthonormal ℝ (({0} : Set (Fin (m + 1))).domRestrict
      fun _ => ivwUnitVector v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have : i = j := Subsingleton.elim i j
    subst this
    change ⟪ivwUnitVector v, ivwUnitVector v⟫ = if i = i then 1 else 0
    simp only [↓reduceIte, real_inner_self_eq_norm_sq, hu, one_pow]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by simp [hcard]) (v := fun _ => ivwUnitVector v) (s := {0})
  exact ⟨b, hb 0 rfl⟩

end Whitening

/-! ### The joint law of the pooled estimate and `Q` -/

section Law

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ι → Ω → ℝ}
  {v : ι → ℝ} {θ : ℝ}

/-- **The joint law of `θ̂` and `Q` on the sample space.** Under `⊗ᵢ N(θ, σ² vᵢ)` with `vᵢ > 0`,
`σ² > 0` and `k = m + 1` studies, `(θ̂, Q / σ²)` has the law `N(θ, σ² / ∑ wᵢ) ⊗ χ²ₘ`. -/
theorem hasLaw_pi_ivwEstimate_cochranQ {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) :
    HasLaw (fun y : ι → ℝ => (ivwEstimate v y, cochranQ v y / σ2))
      ((gaussianReal θ (σ2 / ∑ i, ivWeight v i).toNNReal).prod (chiSquared m))
      (Measure.pi fun i => gaussianReal θ (σ2 * v i).toNNReal) := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  set W := ∑ i, ivWeight v i with hWdef
  have hW : 0 < W := sum_ivWeight_pos hv
  set μ := Measure.pi fun i => gaussianReal θ (σ2 * v i).toNNReal
  set S := standardize (fun _ : ι => θ) (fun i => σ2 * v i)
  have hS : μ.map S = stdGaussian (EuclideanSpace ℝ ι) :=
    pi_gaussianReal_map_standardize fun i => mul_pos hσ (hv i)
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_ivwUnitVector hcard hv
  -- the orthonormal coordinates are independent standard Gaussians
  set T : (ι → ℝ) → (Fin (m + 1) → ℝ) := fun y j => ⟪b j, S y⟫ with hTdef
  have hT : HasLaw T (Measure.pi fun _ => gaussianReal 0 1) μ := by
    have hTe : T = WithLp.ofLp ∘ (fun z => WithLp.toLp 2 fun j => ⟪b j, z⟫) ∘ S := rfl
    refine ⟨by rw [hTe]; fun_prop, ?_⟩
    rw [hTe, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), hS,
      stdGaussian_map_inner_orthonormal b.orthonormal, ← map_pi_eq_stdGaussian,
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  -- the statistics as functions of the coordinates
  set c := √(σ2 / W)
  set G : (Fin (m + 1) → ℝ) → ℝ × ℝ := fun x => (c * x 0 + θ, ∑ j : Fin m, x j.succ ^ 2)
  have hkey : (fun y : ι → ℝ => (ivwEstimate v y, cochranQ v y / σ2)) = G ∘ T := by
    funext y
    have hpar : ∑ j, T y j ^ 2 = ‖S y‖ ^ 2 := b.sum_sq_inner_right (S y)
    rw [Fin.sum_univ_succ] at hpar
    have hQ := norm_sq_standardize_sub hv hσ θ y
    simp only [Function.comp_apply, G, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hTdef]
      simp only
      rw [hb0, inner_ivwUnitVector_standardize hv hσ, ← hWdef,
        show c = √σ2 / √W from Real.sqrt_div hσ.le W]
      have hsW : 0 < √W := Real.sqrt_pos.2 hW
      have hsσ : 0 < √σ2 := Real.sqrt_pos.2 hσ
      field_simp
      ring
    · rw [← hQ, ← hpar]
      rw [hTdef]
      simp only [hb0]
      ring
  -- the law of `G` under independent standard Gaussians
  have hG : HasLaw G ((gaussianReal θ (σ2 / W).toNNReal).prod (chiSquared m))
      (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) := by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0
    have hGe : G = Prod.map (fun t => c * t + θ) (fun x : Fin m → ℝ => ∑ j, x j ^ 2) ∘ e := by
      funext x
      simp [G, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
    have h1 : (gaussianReal 0 1).map (fun t => c * t + θ) = gaussianReal θ (σ2 / W).toNNReal := by
      have : (fun t : ℝ => c * t + θ) = (· + θ) ∘ (c * ·) := rfl
      rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
        gaussianReal_map_add_const, mul_zero, zero_add]
      congr 1
      ext
      simp [c, Real.sq_sqrt (div_pos hσ hW).le, (div_pos hσ hW).le]
    refine ⟨by rw [hGe]; fun_prop, ?_⟩
    rw [hGe, ← Measure.map_map (by fun_prop) e.measurable, he.map_eq,
      ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h1, chiSquared_eq_map_pi]
  rw [hkey]
  exact hG.comp hT

/-- **The joint law of `θ̂` and `Q`** (Cochran 1954). Let the estimates `Yᵢ` be independent with
`Yᵢ ~ N(θ, σ² vᵢ)`, `vᵢ > 0`, `σ² > 0`, from `k = m + 1` studies, and let the weights be
`wᵢ = 1 / vᵢ`. Then `(θ̂, Q / σ²)` has the law `N(θ, σ² / ∑ wᵢ) ⊗ χ²ₘ`. -/
theorem hasLaw_ivwEstimate_cochranQ {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * v i).toNNReal) P) :
    HasLaw (fun ω => (ivwEstimate v (fun i => Y i ω), cochranQ v (fun i => Y i ω) / σ2))
      ((gaussianReal θ (σ2 / ∑ i, ivWeight v i).toNNReal).prod (chiSquared m)) P :=
  (hasLaw_pi_ivwEstimate_cochranQ hcard hv hσ).comp (hind.hasLaw_pi hY)

/-- **`Q / σ² ~ χ²_{k-1}`** under the hypotheses of `hasLaw_ivwEstimate_cochranQ`. -/
theorem hasLaw_cochranQ_div {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * v i).toNNReal) P) :
    HasLaw (fun ω => cochranQ v (fun i => Y i ω) / σ2) (chiSquared m) P :=
  (measurePreserving_snd).comp_hasLaw (hasLaw_ivwEstimate_cochranQ hcard hv hσ hind hY)

/-- **`θ̂ ~ N(θ, σ² / ∑ wᵢ)`** under the hypotheses of `hasLaw_ivwEstimate_cochranQ`. -/
theorem hasLaw_ivwEstimate {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * v i).toNNReal) P) :
    HasLaw (fun ω => ivwEstimate v (fun i => Y i ω))
      (gaussianReal θ (σ2 / ∑ i, ivWeight v i).toNNReal) P :=
  (measurePreserving_fst).comp_hasLaw (hasLaw_ivwEstimate_cochranQ hcard hv hσ hind hY)

/-- **`θ̂` and `Q` are independent** under the hypotheses of `hasLaw_ivwEstimate_cochranQ`. -/
theorem indepFun_ivwEstimate_cochranQ {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (hv : ∀ i, 0 < v i) {σ2 : ℝ} (hσ : 0 < σ2) (hind : iIndepFun Y P)
    (hY : ∀ i, HasLaw (Y i) (gaussianReal θ (σ2 * v i).toNNReal) P) :
    IndepFun (fun ω => ivwEstimate v (fun i => Y i ω)) (fun ω => cochranQ v (fun i => Y i ω))
      P := by
  have := hind.isProbabilityMeasure
  have h := (indepFun_iff_hasLaw_prodMk_prod (hasLaw_ivwEstimate hcard hv hσ hind hY)
    (hasLaw_cochranQ_div hcard hv hσ hind hY)).2 (hasLaw_ivwEstimate_cochranQ hcard hv hσ hind hY)
  have h' := h.comp (φ := id) (ψ := fun q => q * σ2) measurable_id (by fun_prop)
  convert h' using 1 <;> funext ω <;> simp [div_mul_cancel₀ _ hσ.ne']

/-- **The null law of Cochran's `Q` in the Gaussian common effect model** (Cochran 1954): with
`k = m + 1` studies, `Q ~ χ²ₘ`, `θ̂ ~ N(θ, 1 / ∑ wᵢ)`, and `θ̂` and `Q` are independent. -/
theorem IsGaussianCommonEffectModel.hasLaw_cochranQ {m : ℕ} (hcard : Fintype.card ι = m + 1)
    (h : IsGaussianCommonEffectModel P Y θ v) :
    HasLaw (fun ω => cochranQ v (fun i => Y i ω)) (chiSquared m) P ∧
      HasLaw (fun ω => ivwEstimate v (fun i => Y i ω))
        (gaussianReal θ (1 / ∑ i, ivWeight v i).toNNReal) P ∧
      IndepFun (fun ω => ivwEstimate v (fun i => Y i ω))
        (fun ω => cochranQ v (fun i => Y i ω)) P := by
  have hY : ∀ i, HasLaw (Y i) (gaussianReal θ (1 * v i).toNNReal) P := fun i => by
    simpa using h.hasLaw i
  refine ⟨?_, hasLaw_ivwEstimate hcard h.pos one_pos h.indep hY,
    indepFun_ivwEstimate_cochranQ hcard h.pos one_pos h.indep hY⟩
  simpa using hasLaw_cochranQ_div hcard h.pos one_pos h.indep hY

end Law

end MetaAnalysis

end CausalInference
