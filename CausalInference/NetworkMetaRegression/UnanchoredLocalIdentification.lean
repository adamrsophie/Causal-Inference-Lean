/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredIdentification

/-!
# Local identification of the comparator arm from subgroup means

Without shared prognostic effects the comparator arm `b` has its own parameters
`w = (β₂,b, γ_b) ∈ ℝ^p × ℝ`. If study `j_B` reports the aggregate means of `b` in `Z` subgroups
with covariate laws `F_1, …, F_Z`, the data on `w` are the **subgroup means**

`Θ(w)_z = ∫ g⁻¹((μ_{j_B} + γ_b) + xᵀ(β₁ + β₂,b)) F_z(dx)`

(`subgroupMeans`, built from `coefMean` of `SharedModifiersManifold.lean`). Their derivative is
the matrix with rows `∫ g⁻¹'(η(x)) (xᵀ, 1) F_z(dx)` (`subgroupMeansDeriv`,
`subgroupMeansDeriv_apply`).

* **Local identification** (`subgroupMeans_locally_identified`): if this derivative is injective
  at `w₀` (rank `p + 1`), the subgroup means determine `w` on a neighborhood of `w₀`.
* **Binary modifiers** (`cornerCells_injective`, `crossedCells_injective`): with two covariates
  and the three cells `(0,0), (1,0), (0,1)` (or the four crossed cells) as subgroups, the
  subgroup means determine `w` globally for every strictly increasing inverse link.

* **Fewer subgroups than parameters** (`subgroupMeans_not_locally_identified`): if `Z < p + 1`
  and the derivative at `w₀` is onto `ℝ^Z`, every neighborhood of `w₀` contains a second
  parameter with the same subgroup means.

## Main definitions

* `subgroupMeans`, `subgroupMeansDeriv`, `twoPointSubgroups`, `cornerCell`, `crossedCell`.

## Main results

* `hasStrictFDerivAt_subgroupMeans`, `continuous_subgroupMeansDeriv`,
  `subgroupMeansDeriv_apply`.
* `exists_mem_nhds_injOn_of_hasStrictFDerivAt`: a strict derivative with trivial kernel gives
  local injectivity.
* `subgroupMeans_locally_identified`, `withArm_subgroupMeans_locally_identified`,
  `cornerCells_injective`, `crossedCells_injective`.
* `exists_ne_eq_of_hasStrictFDerivAt_surjective`: a surjective strict derivative with nontrivial
  kernel gives a nontrivial level set near the point.
* `subgroupMeans_not_locally_identified`, `not_pointIdentified_withArm_subgroupMeans`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology

variable {p Z : ℕ}

/-! ### The subgroup means and their derivative -/

/-- The **subgroup means** `w ↦ (∫ g⁻¹((α + w₂) + xᵀ(β₁ + w₁)) F_z(dx))_z` of an arm with
parameters `w = (β₂, γ)`, baseline `α` and prognostic effects `β₁`. -/
noncomputable def subgroupMeans (F : Fin Z → Measure (Fin p → ℝ)) (ginv : ℝ → ℝ) (α : ℝ)
    (β₁ : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) : Fin Z → ℝ :=
  fun z => coefMean (F z) ginv α β₁ w

/-- The derivative of the subgroup means: the derivative `coefMeanDeriv` in each subgroup. -/
noncomputable def subgroupMeansDeriv (F : Fin Z → Measure (Fin p → ℝ)) (ginv' : ℝ → ℝ) (α : ℝ)
    (β₁ : Fin p → ℝ) (w : (Fin p → ℝ) × ℝ) : (Fin p → ℝ) × ℝ →L[ℝ] (Fin Z → ℝ) :=
  ContinuousLinearMap.pi fun z => coefMeanDeriv (F z) ginv' α β₁ w

/-- The subgroup means of arm `b` of `M.withArm b w` in study `j_B` are `subgroupMeans` at `w`. -/
theorem MultilevelModel.subgroupMeans_withArm {J K : Type*} [DecidableEq K] (ginv : ℝ → ℝ)
    (M : MultilevelModel J K p) (b : K) (jB : J) (F : Fin Z → Measure (Fin p → ℝ))
    (w : (Fin p → ℝ) × ℝ) :
    (fun z => (M.withArm b w).armMean ginv ((M.withArm b w).μ jB) (F z) b) =
      subgroupMeans F ginv (M.μ jB) M.β₁ w :=
  funext fun z => MultilevelModel.armMean_withArm ginv M b w (M.μ jB) (F z)

section Smooth

variable {F : Fin Z → Measure (Fin p → ℝ)} [∀ z, IsFiniteMeasure (F z)] {ginv ginv' : ℝ → ℝ}
  {C : ℝ} (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv')
  (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ z i, Integrable (fun x : Fin p → ℝ => x i) (F z))
  {α : ℝ} {β₁ : Fin p → ℝ}
include hd' hbd hF

/-- **The derivative is the weighted moment matrix**: the `z`-th coordinate of the derivative in
the direction `v = (v₁, v₂)` is `∫ g⁻¹'(η_w(x)) (xᵀv₁ + v₂) F_z(dx)`. -/
theorem subgroupMeansDeriv_apply (w v : (Fin p → ℝ) × ℝ) (z : Fin Z) :
    subgroupMeansDeriv F ginv' α β₁ w v z =
      ∫ x, ginv' (coefPred α β₁ x w) * (x ⬝ᵥ v.1 + v.2) ∂F z := by
  rw [subgroupMeansDeriv, ContinuousLinearMap.pi_apply, coefMeanDeriv_apply hd' hbd (hF z)]

include hd in
/-- **The subgroup means are strictly differentiable** with derivative `subgroupMeansDeriv`,
for an inverse link with continuous derivative bounded by `C` and subgroup laws with
integrable coordinates. -/
theorem hasStrictFDerivAt_subgroupMeans (w₀ : (Fin p → ℝ) × ℝ) :
    HasStrictFDerivAt (subgroupMeans F ginv α β₁) (subgroupMeansDeriv F ginv' α β₁ w₀) w₀ :=
  hasStrictFDerivAt_pi.2 fun z => hasStrictFDerivAt_coefMean hd hd' hbd (hF z) w₀

/-- The derivative of the subgroup means is continuous in the parameters. -/
theorem continuous_subgroupMeansDeriv : Continuous (subgroupMeansDeriv F ginv' α β₁) := by
  have h : ∀ z, Continuous (coefMeanDeriv (F z) ginv' α β₁) := fun z =>
    continuous_coefMeanDeriv hd' hbd (hF z)
  have e : subgroupMeansDeriv F ginv' α β₁ =
      fun w => ContinuousLinearMap.piEquivL ℝ ((Fin p → ℝ) × ℝ) (F := fun _ : Fin Z => ℝ)
        fun z => coefMeanDeriv (F z) ginv' α β₁ w :=
    rfl
  rw [e]
  exact (ContinuousLinearMap.piEquivL ℝ ((Fin p → ℝ) × ℝ)
    (F := fun _ : Fin Z => ℝ)).continuous.comp (continuous_pi h)

end Smooth

/-! ### Local injectivity -/

/-- **A strict derivative with trivial kernel gives local injectivity.** If `f` has the strict
derivative `f'` at `a` and `f'` is injective, `f` is injective on a neighborhood of `a`. The
derivative is antilipschitz with some constant `K`; on a neighborhood where `f` is approximated by
`f'` within `1 / (2K)`, equal values force `‖x - y‖ ≤ ‖x - y‖ / 2`. -/
theorem exists_mem_nhds_injOn_of_hasStrictFDerivAt {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} {f' : E →L[ℝ] G} {a : E} (hf : HasStrictFDerivAt f f' a)
    (hinj : Function.Injective f') : ∃ s ∈ 𝓝 a, Set.InjOn f s := by
  have hker : LinearMap.ker (f' : E →ₗ[ℝ] G) = ⊥ := LinearMap.ker_eq_bot.2 hinj
  obtain ⟨K, hK0, hK⟩ := LinearMap.exists_antilipschitzWith _ hker
  set c : NNReal := (2 * K)⁻¹ with hcdef
  have hc0 : 0 < c := by positivity
  obtain ⟨s, hs, happrox⟩ := hf.approximates_deriv_on_nhds (c := c) (Or.inr hc0)
  refine ⟨s, hs, fun x hx y hy hxy => ?_⟩
  have h1 := happrox x hx y hy
  rw [hxy, sub_self, zero_sub, norm_neg] at h1
  have h2 := hK.le_mul_norm (map_zero _) (x - y)
  have h3 : ‖x - y‖ ≤ (K : ℝ) * (c * ‖x - y‖) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 K.coe_nonneg)
  have hKc : (K : ℝ) * c = 1 / 2 := by
    rw [hcdef, NNReal.coe_inv, NNReal.coe_mul]
    have : (K : ℝ) ≠ 0 := by exact_mod_cast hK0.ne'
    field_simp
    norm_num
  have h4 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h4)

section Local

variable {F : Fin Z → Measure (Fin p → ℝ)} [∀ z, IsFiniteMeasure (F z)] {ginv ginv' : ℝ → ℝ}
  {C : ℝ} (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv')
  (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ z i, Integrable (fun x : Fin p → ℝ => x i) (F z))
include hd hd' hbd hF

/-- **Local identification from subgroup means.** For an inverse link with continuous derivative
bounded by `C` and subgroup laws with integrable coordinates, if the derivative of the subgroup
means at `w₀` is injective (the weighted moment matrix has rank `p + 1`), the subgroup means are
injective on a neighborhood of `w₀`. -/
theorem subgroupMeans_locally_identified {α : ℝ} {β₁ : Fin p → ℝ} {w₀ : (Fin p → ℝ) × ℝ}
    (hrank : Function.Injective (subgroupMeansDeriv F ginv' α β₁ w₀)) :
    ∃ U ∈ 𝓝 w₀, Set.InjOn (subgroupMeans F ginv α β₁) U :=
  exists_mem_nhds_injOn_of_hasStrictFDerivAt (hasStrictFDerivAt_subgroupMeans hd hd' hbd hF w₀)
    hrank

/-- **Local identification of the comparator arm.** In the multilevel model, under the
hypotheses of `subgroupMeans_locally_identified` at `w₀ = (β₂,b, γ_b)` of `M` (baseline
`μ_{j_B}`), the models `M.withArm b w` with `w` near `w₀` are determined by their subgroup means
of `b` in study `j_B`. -/
theorem withArm_subgroupMeans_locally_identified {J K : Type*} [DecidableEq K]
    (M : MultilevelModel J K p) (b : K) (jB : J)
    (hrank : Function.Injective (subgroupMeansDeriv F ginv' (M.μ jB) M.β₁ (M.β₂ b, M.γ b))) :
    ∃ U ∈ 𝓝 (M.β₂ b, M.γ b), Set.InjOn
      (fun w => fun z => (M.withArm b w).armMean ginv ((M.withArm b w).μ jB) (F z) b) U := by
  obtain ⟨U, hU, hinj⟩ := subgroupMeans_locally_identified hd hd' hbd hF hrank
  refine ⟨U, hU, fun w hw w' hw' h => hinj hw hw' ?_⟩
  simpa only [MultilevelModel.subgroupMeans_withArm] using h

end Local

/-- The two subgroup laws `δ_0` and `δ_1` on one covariate. -/
noncomputable def twoPointSubgroups : Fin 2 → Measure (Fin 1 → ℝ) :=
  ![Measure.dirac fun _ => 0, Measure.dirac fun _ => 1]

instance (z : Fin 2) : IsProbabilityMeasure (twoPointSubgroups z) := by
  fin_cases z <;>
    simp only [twoPointSubgroups, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> infer_instance

/-- The coordinates of the two point subgroups are integrable. -/
theorem integrable_twoPointSubgroups (z : Fin 2) (i : Fin 1) :
    Integrable (fun x : Fin 1 → ℝ => x i) (twoPointSubgroups z) := by
  fin_cases z <;> exact integrable_dirac (by simp)

/-- For the identity link (derivative `1`) and the subgroups `δ_0`, `δ_1`, the derivative of the
subgroup means is `v ↦ (v₂, v₁ + v₂)` at every point, an injective map. -/
theorem injective_subgroupMeansDeriv_twoPoint (α : ℝ) (β₁ : Fin 1 → ℝ) (w₀ : (Fin 1 → ℝ) × ℝ) :
    Function.Injective (subgroupMeansDeriv twoPointSubgroups (fun _ => 1) α β₁ w₀) := by
  intro v v' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [subgroupMeansDeriv_apply (C := 1) continuous_const (fun _ => by simp)
      integrable_twoPointSubgroups,
    subgroupMeansDeriv_apply (C := 1) continuous_const (fun _ => by simp)
      integrable_twoPointSubgroups] at h0 h1
  simp only [twoPointSubgroups, Fin.isValue, Matrix.cons_val_zero, dotProduct,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul, integral_dirac,
    zero_mul, zero_add, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
  have h2 : v.1 = v'.1 := funext fun i => by fin_cases i; simp; linarith
  exact Prod.ext h2 h0

/-- **Instance of local identification**: one covariate, the identity link (derivative `1`), the
subgroups `δ_0` and `δ_1`, baseline `0` and `β₁ = 0`. The derivative is
`v ↦ (v₂, v₁ + v₂)`, injective, so the subgroup means are injective near every `w₀`. -/
theorem subgroupMeans_locally_identified_instance (w₀ : (Fin 1 → ℝ) × ℝ) :
    ∃ U ∈ 𝓝 w₀, Set.InjOn (subgroupMeans twoPointSubgroups id 0 0) U :=
  subgroupMeans_locally_identified (C := 1) (fun t => hasDerivAt_id t) continuous_const
    (fun _ => by simp) integrable_twoPointSubgroups (injective_subgroupMeansDeriv_twoPoint 0 0 w₀)

/-- **Instance of local identification of the comparator arm**: the model `⟨0, 0, 0, 0⟩` with
two studies and two treatments indexed by `Bool`, one covariate, the identity link, comparator
`b = false` in study `true` and the subgroups `δ_0`, `δ_1`. -/
theorem withArm_subgroupMeans_locally_identified_instance :
    ∃ U ∈ 𝓝 (((⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).β₂ false),
        (⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).γ false), Set.InjOn
      (fun w => fun z => ((⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).withArm false w).armMean id
        (((⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).withArm false w).μ true)
        (twoPointSubgroups z) false) U :=
  withArm_subgroupMeans_locally_identified (C := 1) (fun t => hasDerivAt_id t) continuous_const
    (fun _ => by simp) integrable_twoPointSubgroups _ false true
    (injective_subgroupMeansDeriv_twoPoint _ _ _)

/-! ### Two crossed binary effect modifiers -/

/-- The three cells `(0,0), (1,0), (0,1)` of two binary covariates. -/
def cornerCell : Fin 3 → Fin 2 → ℝ := ![![0, 0], ![1, 0], ![0, 1]]

/-- The four cells `(0,0), (1,0), (0,1), (1,1)` of two binary covariates. -/
def crossedCell : Fin 4 → Fin 2 → ℝ := ![![0, 0], ![1, 0], ![0, 1], ![1, 1]]

/-- **Three cells of two binary effect modifiers identify the comparator arm.** With two
covariates and the point masses at the cells `(0,0)`, `(1,0)`, `(0,1)` as subgroup laws, the
subgroup means are injective in `w = (β₂, γ)` for every strictly increasing inverse link, every
baseline and every `β₁`: the three cells give `α + γ`, `α + γ + (β₁ + β₂)_1` and
`α + γ + (β₁ + β₂)_2`. -/
theorem cornerCells_injective {ginv : ℝ → ℝ} (hmono : StrictMono ginv) (α : ℝ)
    (β₁ : Fin 2 → ℝ) :
    Function.Injective
      (subgroupMeans (fun z => Measure.dirac (cornerCell z)) ginv α β₁) := by
  intro w w' h
  have hz : ∀ z : Fin 3, coefPred α β₁ (cornerCell z) w = coefPred α β₁ (cornerCell z) w' :=
    fun z => hmono.injective (by
      have := congrFun h z
      simpa [subgroupMeans, coefMean, integral_dirac] using this)
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  simp only [coefPred, dotProduct, cornerCell, Fin.isValue, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Pi.add_apply, Fin.sum_univ_succ, zero_mul,
    Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_succ, Finset.sum_const_zero, add_zero,
    add_right_inj, Matrix.cons_val_one, one_mul, Matrix.cons_val, Finset.sum_singleton,
    Fin.succ_zero_eq_one, zero_add] at h0 h1 h2
  have e1 : w.1 = w'.1 := funext fun i => by fin_cases i <;> simp <;> linarith
  exact Prod.ext e1 h0

/-- **The four crossed cells identify the comparator arm**, since they contain the three cells
of `cornerCells_injective`. -/
theorem crossedCells_injective {ginv : ℝ → ℝ} (hmono : StrictMono ginv) (α : ℝ)
    (β₁ : Fin 2 → ℝ) :
    Function.Injective
      (subgroupMeans (fun z => Measure.dirac (crossedCell z)) ginv α β₁) := by
  intro w w' h
  have hc : ∀ z : Fin 3, crossedCell (Fin.castSucc z) = cornerCell z := fun z => by
    fin_cases z <;> rfl
  refine cornerCells_injective hmono α β₁ (funext fun z => ?_)
  have := congrFun h (Fin.castSucc z)
  simpa only [subgroupMeans, hc] using this

/-- **Instance of the crossed cell theorem** with the logit link `Real.sigmoid`, baseline `0` and
`β₁ = 0`. -/
theorem crossedCells_injective_instance :
    Function.Injective (subgroupMeans (fun z => Measure.dirac (crossedCell z)) Real.sigmoid 0 0) :=
  crossedCells_injective Real.sigmoid_strictMono 0 0

/-- **Instance of the three cell theorem** with the logit link `Real.sigmoid`, baseline `0` and
`β₁ = 0`. -/
theorem cornerCells_injective_instance :
    Function.Injective (subgroupMeans (fun z => Measure.dirac (cornerCell z)) Real.sigmoid 0 0) :=
  cornerCells_injective Real.sigmoid_strictMono 0 0

/-! ### Fewer subgroups than parameters -/

/-- **A surjective strict derivative with nontrivial kernel gives a nontrivial level set near
every point.** If `f` has the strict derivative `f'` at `a`, `f'` is onto a finite dimensional
space and `f' v = 0` for some `v ≠ 0`, every neighborhood of `a` contains a point `x ≠ a` with
`f x = f a`. The points are `φ⁻¹(f a, t v)` for the local homeomorphism `φ = (f, π_ker)` of the
implicit function theorem and small `t ≠ 0`. -/
theorem exists_ne_eq_of_hasStrictFDerivAt_surjective {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {f : E → G} {f' : E →L[ℝ] G} {a : E} (hf : HasStrictFDerivAt f f' a)
    (hsurj : f'.range = ⊤) {v : E} (hv : v ≠ 0) (hv0 : f' v = 0) :
    ∀ U ∈ 𝓝 a, ∃ x ∈ U, x ≠ a ∧ f x = f a := by
  intro U hU
  set φ := hf.implicitToOpenPartialHomeomorph f f' hsurj
  let k : f'.ker := ⟨v, by simpa using hv0⟩
  have hk : Tendsto (fun t : ℝ => t • k) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • k) (𝓝 0) (𝓝 ((0 : ℝ) • k)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpair : Tendsto (fun t : ℝ => (f a, t • k)) (𝓝[≠] 0) (𝓝 (f a, 0)) :=
    tendsto_const_nhds.prodMk_nhds hk
  have htgt := hf.mem_implicitToOpenPartialHomeomorph_target hsurj
  have hsymm0 : φ.symm (f a, 0) = a := by
    rw [← hf.implicitToOpenPartialHomeomorph_self hsurj]
    exact φ.left_inv (hf.mem_implicitToOpenPartialHomeomorph_source hsurj)
  have h1 : Tendsto (fun t : ℝ => φ.symm (f a, t • k)) (𝓝[≠] 0) (𝓝 a) := by
    have := (φ.continuousAt_symm htgt).tendsto.comp hpair
    rwa [hsymm0] at this
  have h3 := hpair.eventually (φ.open_target.mem_nhds htgt)
  have h0 : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨t, ht, htU, httarget⟩ := (h0.and ((h1.eventually hU).and h3)).exists
  have hφ : φ (φ.symm (f a, t • k)) = (f a, t • k) := φ.right_inv httarget
  refine ⟨_, htU, fun he => ?_, ?_⟩
  · rw [he, hf.implicitToOpenPartialHomeomorph_self hsurj] at hφ
    have hz : t • k = 0 := (Prod.mk.inj hφ).2.symm
    have : t • v = 0 := congrArg Subtype.val hz
    exact hv ((smul_eq_zero.mp this).resolve_left ht)
  · have := congrArg Prod.fst hφ
    rwa [hf.implicitToOpenPartialHomeomorph_fst hsurj] at this

section NotLocal

variable {F : Fin Z → Measure (Fin p → ℝ)} [∀ z, IsFiniteMeasure (F z)] {ginv ginv' : ℝ → ℝ}
  {C : ℝ} (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv')
  (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ z i, Integrable (fun x : Fin p → ℝ => x i) (F z))
include hd hd' hbd hF

/-- **Fewer subgroups than parameters: no local identification.** For an inverse link with
continuous derivative bounded by `C` and subgroup laws with integrable coordinates, if there
are `Z < p + 1` subgroups and the derivative of the subgroup means at `w₀` is onto `ℝ^Z` (full row
rank), every neighborhood of `w₀` contains a `w ≠ w₀` with the same subgroup means. -/
theorem subgroupMeans_not_locally_identified {α : ℝ} {β₁ : Fin p → ℝ} {w₀ : (Fin p → ℝ) × ℝ}
    (hZ : Z < p + 1) (hsurj : (subgroupMeansDeriv F ginv' α β₁ w₀).range = ⊤) :
    ∀ U ∈ 𝓝 w₀, ∃ w ∈ U, w ≠ w₀ ∧
      subgroupMeans F ginv α β₁ w = subgroupMeans F ginv α β₁ w₀ := by
  have hker : LinearMap.ker (subgroupMeansDeriv F ginv' α β₁ w₀ :
      (Fin p → ℝ) × ℝ →ₗ[ℝ] (Fin Z → ℝ)) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hZ)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hker
  exact exists_ne_eq_of_hasStrictFDerivAt_surjective
    (hasStrictFDerivAt_subgroupMeans hd hd' hbd hF w₀) hsurj hv0 hv

/-- **The comparator arm is not identified from fewer subgroups than parameters.** Under the
hypotheses of `subgroupMeans_not_locally_identified` at `w₀ = (β₂,b, γ_b)` of `M` (baseline
`μ_{j_B}`), the parameters `(β₂,b, γ_b)` are not point identified from the subgroup means of `b`
in study `j_B` among the models `M.withArm b w` with `w` in any neighborhood of `w₀`. -/
theorem not_pointIdentified_withArm_subgroupMeans {J K : Type*} [DecidableEq K]
    (M : MultilevelModel J K p) (b : K) (jB : J) (hZ : Z < p + 1)
    (hsurj : (subgroupMeansDeriv F ginv' (M.μ jB) M.β₁ (M.β₂ b, M.γ b)).range = ⊤)
    {U : Set ((Fin p → ℝ) × ℝ)} (hU : U ∈ 𝓝 (M.β₂ b, M.γ b)) :
    ¬PointIdentified (M.withArm b '' U)
      (fun N => fun z => N.armMean ginv (N.μ jB) (F z) b) (fun N => (N.β₂ b, N.γ b)) := by
  intro h
  obtain ⟨w, hw, hne, heq⟩ := subgroupMeans_not_locally_identified hd hd' hbd hF hZ hsurj U hU
  have hw₀ : M.withArm b (M.β₂ b, M.γ b) = M := by
    ext <;> simp [MultilevelModel.withArm]
  have := h _ ⟨w, hw, rfl⟩ _ ⟨_, mem_of_mem_nhds hU, rfl⟩ (by
    simp only [MultilevelModel.subgroupMeans_withArm]
    rw [hw₀] at *
    simpa [← MultilevelModel.subgroupMeans_withArm, hw₀] using heq)
  apply hne
  simpa [MultilevelModel.withArm] using this

end NotLocal

/-- **Instance of the non identification from fewer subgroups**: one covariate, the identity
link, the single subgroup `δ_0`, baseline `0` and `β₁ = 0`. The derivative `v ↦ v₂` is onto
`ℝ`, and `1 < 2`, so every neighborhood of every `w₀` holds a second parameter with the same
subgroup mean. -/
theorem subgroupMeans_not_locally_identified_instance (w₀ : (Fin 1 → ℝ) × ℝ) :
    ∀ U ∈ 𝓝 w₀, ∃ w ∈ U, w ≠ w₀ ∧
      subgroupMeans (fun _ : Fin 1 => Measure.dirac (fun _ => (0 : ℝ))) id 0 0 w =
        subgroupMeans (fun _ : Fin 1 => Measure.dirac (fun _ => (0 : ℝ))) id 0 0 w₀ := by
  have hd : ∀ t : ℝ, HasDerivAt id ((fun _ => (1 : ℝ)) t) t := fun t => hasDerivAt_id t
  have hF : ∀ (z : Fin 1) (i : Fin 1), Integrable (fun x : Fin 1 → ℝ => x i)
      (Measure.dirac (fun _ => (0 : ℝ))) := fun _ _ => integrable_dirac (by simp)
  refine subgroupMeans_not_locally_identified (C := 1) hd continuous_const (fun _ => by simp) hF
    (by norm_num) ?_
  refine LinearMap.range_eq_top.2 fun y => ⟨(0, y 0), funext fun z => ?_⟩
  rw [ContinuousLinearMap.coe_coe,
    subgroupMeansDeriv_apply (C := 1) continuous_const (fun _ => by simp) hF]
  simp [Subsingleton.elim z 0]

/-- **Instance of the non identification of the comparator arm**: the model `⟨0, 0, 0, 0⟩` with
two studies and two treatments indexed by `Bool`, one covariate, the identity link, comparator
`b = false` in study `true`, the single subgroup `δ_0` and the neighborhood `Set.univ`. -/
theorem not_pointIdentified_withArm_subgroupMeans_instance :
    ¬PointIdentified (((⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).withArm false) '' Set.univ)
      (fun N => fun _ : Fin 1 => N.armMean id (N.μ true) (Measure.dirac fun _ => 0) false)
      (fun N => (N.β₂ false, N.γ false)) := by
  have hF : ∀ (z : Fin 1) (i : Fin 1), Integrable (fun x : Fin 1 → ℝ => x i)
      (Measure.dirac (fun _ => (0 : ℝ))) := fun _ _ => integrable_dirac (by simp)
  refine not_pointIdentified_withArm_subgroupMeans (F := fun _ => Measure.dirac fun _ => 0)
    (C := 1) (fun t => hasDerivAt_id t) continuous_const (fun _ => by simp) hF _ false true
    (by norm_num) ?_ Filter.univ_mem
  refine LinearMap.range_eq_top.2 fun y => ⟨(0, y 0), funext fun z => ?_⟩
  rw [ContinuousLinearMap.coe_coe,
    subgroupMeansDeriv_apply (C := 1) continuous_const (fun _ => by simp) hF]
  simp [Subsingleton.elim z 0]

end NetworkMetaRegression

end CausalInference
