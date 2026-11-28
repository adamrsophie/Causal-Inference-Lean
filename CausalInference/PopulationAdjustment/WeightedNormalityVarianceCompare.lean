/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityVariance

/-!
# The sandwich variance against the naive variance

The **naive variance** of the weighted arm mean treats the tilt `w₀` as known:
`σ_naive² = E[(1{A = a} w₀ (Y - m₀) / q)²] = E[U²] / q²`. The sandwich variance
`σ² = E[IF²]` subtracts from `U` the projection term `ℓ = cᵀ M⁻¹ w₀ (φ(X) - t)`, which accounts
for the estimation of the tilt. In general (`weightedNaiveVariance_sub_weightedArmVariance`)

  `σ_naive² - σ² = (2 E[U ℓ] - E[ℓ²]) / q²`,

which has no sign in general: `nonaffine_weightedNaiveVariance_lt_weightedArmVariance` gives a
randomized model with a regression that is not affine where the sandwich variance is larger.
Under randomization of the arm (`X ⫫ A`) and an arm regression
`E[Y | X, A = a] = a₀ + γᵀ φ(X)` affine in the features, the coupling vector is
`c = π M γ` with `π = P(A = a)`, the projection term is `ℓ = π w₀ γᵀ(φ(X) - t)`, and

  `σ_naive² - σ² = (π / q)² E[w₀² (γᵀ(φ(X) - t))²] ≥ 0`

(`weightedNaiveVariance_sub_weightedArmVariance_of_affine`), a nonnegative quadratic form in `γ`
with the matrix `(π / q)² E[w₀² (φ(X) - t)(φ(X) - t)ᵀ]`. The two variances agree exactly when the
projection coefficient vanishes, `γ = 0`, equivalently `c = 0`
(`weightedNaiveVariance_eq_weightedArmVariance_iff`).

## Main definitions

* `weightedArmResidual`, `weightedArmProjection`: the terms `U` and `ℓ` of the influence
  function `IF = (U - ℓ) / q`.
* `weightedNaiveVariance`: `E[(U / q)²]`.

## Main results

* `weightedNaiveVariance_sub_weightedArmVariance`: the general difference.
* `integral_armIndObs_mul_fst`, `integral_armIndObs_mul_fst_mul_outcome`: randomization and
  the arm regression inside the integrals.
* `weightedCoupling_eq_and_sub_of_affine`: `c = π M γ` and the difference as a quadratic form.
* `weightedNaiveVariance_sub_weightedArmVariance_of_affine`,
  `weightedArmVariance_le_weightedNaiveVariance`,
  `weightedNaiveVariance_eq_weightedArmVariance_iff`.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
* Stefanski, Boos, *The calculus of M-estimation* (2002).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)}

/-- The **weighted residual** `U = 1{A = a} w₀ (Y - m₀)` of arm `a`. -/
noncomputable def weightedArmResidual (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (z : 𝒳 × Bool × ℝ) : ℝ :=
  armIndObs a z * tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 *
    (z.2.2 - tiltArmMean ν φ t a (tiltMinimizer ν φ t))

/-- The **projection term** `ℓ = cᵀ M⁻¹ w₀ (φ(X) - t)` of arm `a`. -/
noncomputable def weightedArmProjection (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (z : 𝒳 × Bool × ℝ) : ℝ :=
  weightedCoupling ν φ t a ⬝ᵥ ((tiltedSecondMoment ν φ t (tiltMinimizer ν φ t))⁻¹ *ᵥ
    fun j => tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 * (φ z.1 j - t j))

/-- The **naive variance** `E[(U / q)²]` of the weighted arm mean, which treats the tilt as
known. -/
noncomputable def weightedNaiveVariance (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) : ℝ :=
  ∫ z, (weightedArmResidual ν φ t a z / weightedArmMass ν φ t a) ^ 2 ∂ν

/-- The influence function is `(U - ℓ) / q`. -/
theorem weightedArmInfluence_eq_residual_sub_projection (ν : Measure (𝒳 × Bool × ℝ))
    (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool) (z : 𝒳 × Bool × ℝ) :
    weightedArmInfluence ν φ t a z =
      (weightedArmResidual ν φ t a z - weightedArmProjection ν φ t a z) /
        weightedArmMass ν φ t a := rfl

/-- The projection term is a fixed linear combination of the balance coordinates
`w₀ (φ_k(X) - t_k)` of the estimating function. -/
theorem weightedArmProjection_eq_sum (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (z : 𝒳 × Bool × ℝ) :
    weightedArmProjection ν φ t a z = ∑ k, (weightedCoupling ν φ t a ᵥ*
      (tiltedSecondMoment ν φ t (tiltMinimizer ν φ t))⁻¹) k *
        weightedEstFun φ t a z (weightedStackedParam ν φ t a) (Sum.inl k) := by
  rw [weightedArmProjection, dotProduct_mulVec, dotProduct]
  rfl

/-- The residual, its products with the projection term, and the squared projection term are
integrable for a square integrable outcome. -/
theorem integrable_weightedArmResidual_mul [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) (a : Bool) :
    Integrable (fun z => weightedArmResidual ν φ t a z ^ 2) ν ∧
      Integrable (fun z => weightedArmResidual ν φ t a z * weightedArmProjection ν φ t a z) ν ∧
      Integrable (fun z => weightedArmProjection ν φ t a z ^ 2) ν := by
  set θ₀ := weightedStackedParam ν φ t a
  set b := weightedCoupling ν φ t a ᵥ* (tiltedSecondMoment ν φ t (tiltMinimizer ν φ t))⁻¹
  have hres : ∀ z, weightedArmResidual ν φ t a z = weightedEstFun φ t a z θ₀ (Sum.inr ()) :=
    fun z => rfl
  refine ⟨?_, ?_, ?_⟩
  · have h := integrable_weightedEstFun_mul hφ hB hy a a θ₀ θ₀ (Sum.inr ()) (Sum.inr ())
    refine h.congr (ae_of_all _ fun z => ?_)
    simp only [hres, sq]
  · have h := integrable_finsetSum Finset.univ fun k _ =>
      (integrable_weightedEstFun_mul hφ hB hy a a θ₀ θ₀ (Sum.inr ()) (Sum.inl k)).const_mul (b k)
    refine h.congr (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [hres, weightedArmProjection_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · have h := integrable_finsetSum Finset.univ fun k _ => integrable_finsetSum Finset.univ
      fun l _ => (integrable_weightedEstFun_mul hφ hB hy a a θ₀ θ₀ (Sum.inl k)
        (Sum.inl l)).const_mul (b k * b l)
    refine h.congr (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [sq, weightedArmProjection_eq_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The naive variance against the sandwich variance, in general**:
`σ_naive² - σ² = (2 E[U ℓ] - E[ℓ²]) / q²`, for a square integrable outcome and bounded
features. -/
theorem weightedNaiveVariance_sub_weightedArmVariance [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) (a : Bool) :
    weightedNaiveVariance ν φ t a - weightedArmVariance ν φ t a =
      (2 * ∫ z, weightedArmResidual ν φ t a z * weightedArmProjection ν φ t a z ∂ν -
        ∫ z, weightedArmProjection ν φ t a z ^ 2 ∂ν) / weightedArmMass ν φ t a ^ 2 := by
  obtain ⟨hUU, hUL, hLL⟩ := integrable_weightedArmResidual_mul hφ hB hy a
  set q := weightedArmMass ν φ t a
  have h1 : Integrable (fun z => (weightedArmResidual ν φ t a z / q) ^ 2) ν :=
    (hUU.div_const (q ^ 2)).congr (ae_of_all _ fun z => by simp only [div_pow])
  have h2 : Integrable (fun z => weightedArmInfluence ν φ t a z ^ 2) ν := by
    refine (((hUU.sub (hUL.const_mul 2)).add hLL).div_const (q ^ 2)).congr
      (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, weightedArmInfluence_eq_residual_sub_projection]
    ring
  rw [weightedNaiveVariance, weightedArmVariance, ← integral_sub h1 h2]
  have he : (fun z => (weightedArmResidual ν φ t a z / q) ^ 2 -
      weightedArmInfluence ν φ t a z ^ 2) = fun z =>
        (2 * (weightedArmResidual ν φ t a z * weightedArmProjection ν φ t a z) -
          weightedArmProjection ν φ t a z ^ 2) / q ^ 2 := by
    funext z
    rw [weightedArmInfluence_eq_residual_sub_projection]
    ring
  rw [he, integral_div, integral_sub (hUL.const_mul 2) hLL, integral_const_mul]

/-! ### Randomization and an affine arm regression -/

/-- **Randomization**: if the arm is independent of the covariates, `E[1{A = a} f(X)] =
P(A = a) E[f(X)]` for a measurable `f`. -/
theorem integral_armIndObs_mul_fst [IsProbabilityMeasure ν]
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) ν) (a : Bool) {f : 𝒳 → ℝ}
    (hf : Measurable f) :
    ∫ z, armIndObs a z * f z.1 ∂ν = ν.real {z | z.2.1 = a} * ∫ z, f z.1 ∂ν := by
  have hg : Measurable fun s : Bool => if s = a then (1 : ℝ) else 0 := measurable_of_countable _
  have h := (hind.comp hf hg).symm.integral_fun_mul_eq_mul_integral
    (hg.comp measurable_snd.fst).aestronglyMeasurable (hf.comp measurable_fst).aestronglyMeasurable
  have h1 : ∫ z, armIndObs a z ∂ν = ν.real {z | z.2.1 = a} := by
    have he : (fun z : 𝒳 × Bool × ℝ => armIndObs a z) = Set.indicator {z | z.2.1 = a} 1 := by
      funext z
      simp [armIndObs, Set.indicator]
    rw [he, integral_indicator_one (measurableSet_eq_fun measurable_snd.fst measurable_const)]
  rw [← h1]
  exact h

/-- **The regression in the arm**: if `E[Y | X, A] = μ_A(X)`, then
`E[1{A = a} h(X) Y] = E[1{A = a} h(X) μ_a(X)]` for a bounded measurable `h`. -/
theorem integral_armIndObs_mul_fst_mul_outcome [IsFiniteMeasure ν] {mu : Bool → 𝒳 → ℝ}
    (hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν)
    (hreg : ν[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] fun z => mu z.2.1 z.1)
    (a : Bool) {h : 𝒳 → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ∫ z, armIndObs a z * h z.1 * z.2.2 ∂ν = ∫ z, armIndObs a z * h z.1 * mu a z.1 ∂ν := by
  have hpair : Measurable fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have hm : MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance ≤
      (inferInstance : MeasurableSpace (𝒳 × Bool × ℝ)) := hpair.comap_le
  have hF : Measurable fun q : 𝒳 × Bool => (if q.2 = a then (1 : ℝ) else 0) * h q.1 :=
    (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
      measurable_const).mul (hh.comp measurable_fst)
  have hfm : StronglyMeasurable[MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
      inferInstance] fun z : 𝒳 × Bool × ℝ => armIndObs a z * h z.1 :=
    (hF.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have hbd : ∀ᵐ z ∂ν, ‖armIndObs a z * h z.1‖ ≤ C := ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    rcases armIndObs_eq_zero_or_one a z with h0 | h0
    · rw [h0, abs_zero, zero_mul]; exact (abs_nonneg _).trans (hC z.1)
    · rw [h0, abs_one, one_mul]; exact hC z.1
  have hce := condExp_stronglyMeasurable_mul_of_bound hm hfm hy C hbd
  calc ∫ z, armIndObs a z * h z.1 * z.2.2 ∂ν
      = ∫ z, (ν[(fun z : 𝒳 × Bool × ℝ => armIndObs a z * h z.1) * (fun z => z.2.2) |
          MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]) z ∂ν :=
        (integral_condExp hm).symm
    _ = ∫ z, armIndObs a z * h z.1 * (ν[fun z => z.2.2 |
          MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]) z ∂ν :=
        integral_congr_ae hce
    _ = ∫ z, armIndObs a z * h z.1 * mu z.2.1 z.1 ∂ν :=
        integral_congr_ae (hreg.mono fun z hz => by
          simp only
          rw [hz])
    _ = ∫ z, armIndObs a z * h z.1 * mu a z.1 ∂ν := by
        congr 1
        funext z
        unfold armIndObs
        split_ifs with h0
        · rw [h0]
        · simp

/-- **The coupling vector and the comparison under randomization and an affine arm
regression.** If the arm is independent of the covariates, `E[Y | X, A] = μ_A(X)` with
`μ_a(x) = a₀ + γᵀφ(x)` affine in the features, the outcome is square integrable and the features
are bounded and satisfy the margin condition, then the coupling vector is `c = π M γ` with
`π = P(A = a)`, and `σ_naive² - σ² = (π / q)² E[w₀² (γᵀ(φ(X) - t))²]`. -/
theorem weightedCoupling_eq_and_sub_of_affine [IsProbabilityMeasure ν]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) ν) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    {mu : Bool → 𝒳 → ℝ}
    (hreg : ν[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] fun z => mu z.2.1 z.1)
    {a0 : ℝ} {γ : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + γ ⬝ᵥ φ x) :
    weightedCoupling ν φ t a =
        ν.real {z | z.2.1 = a} • (tiltedSecondMoment ν φ t (tiltMinimizer ν φ t) *ᵥ γ) ∧
      weightedNaiveVariance ν φ t a - weightedArmVariance ν φ t a =
        (ν.real {z | z.2.1 = a} / weightedArmMass ν φ t a) ^ 2 *
          ∫ z, tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 ^ 2 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2 ∂ν := by
  have hy1 := hy.integrable one_le_two
  set β₀ := tiltMinimizer ν φ t with hβ₀
  set π := ν.real {z | z.2.1 = a} with hπ
  set m₀ := tiltArmMean ν φ t a β₀ with hm₀
  set M := tiltedSecondMoment ν φ t β₀ with hM
  set w : 𝒳 → ℝ := fun x => tiltWeight φ t 0 β₀ x with hw
  set sγ : 𝒳 → ℝ := fun x => γ ⬝ᵥ (φ x - t) with hsγ
  set Cw := Real.exp (p * (‖β₀‖ * B))
  have hwm : Measurable w := measurable_tiltWeight φ t 0 β₀ hφ
  have hwb : ∀ x, |w x| ≤ Cw := fun x => by
    rw [abs_of_pos (tiltWeight_pos _ _ _ _ _)]
    exact (tiltWeight_mem_Icc (hB x) le_rfl).2
  have hΔm : ∀ k, Measurable fun x => φ x k - t k := fun k =>
    ((measurable_pi_apply k).comp hφ).sub_const _
  have hΔb : ∀ k x, |φ x k - t k| ≤ B := fun k x => by
    have h := norm_le_pi_norm (φ x - t) k
    rw [Real.norm_eq_abs, Pi.sub_apply] at h
    exact h.trans (hB x)
  have hsm : Measurable sγ :=
    (continuous_const.dotProduct continuous_id).measurable.comp (hφ.sub_const t)
  have hsb : ∀ x, |sγ x| ≤ p * (‖γ‖ * B) := fun x =>
    (abs_dotProduct_le_mul_norm γ (φ x - t)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)) (Nat.cast_nonneg p))
  have habs : ∀ {f g : 𝒳 → ℝ} {C D : ℝ}, (∀ x, |f x| ≤ C) → (∀ x, |g x| ≤ D) →
      ∀ x, |f x * g x| ≤ C * D := fun hf hg x => by
    rw [abs_mul]
    exact mul_le_mul (hf x) (hg x) (abs_nonneg _) ((abs_nonneg _).trans (hf x))
  have hint : ∀ {f : 𝒳 → ℝ} {C : ℝ}, Measurable f → (∀ x, |f x| ≤ C) →
      Integrable (fun z : 𝒳 × Bool × ℝ => f z.1) ν := fun hf hC =>
    integrable_of_abs_le (hf.comp measurable_fst) fun z => hC z.1
  have hint2 : ∀ {f g : 𝒳 → ℝ} {C D : ℝ}, Measurable f → Measurable g → (∀ x, |f x| ≤ C) →
      (∀ x, |g x| ≤ D) → Integrable (fun z : 𝒳 × Bool × ℝ => f z.1 * g z.1) ν :=
    fun hf hg hC hD => hint (hf.mul hg) (habs hC hD)
  have hmuaff : ∀ x, mu a x = (a0 + γ ⬝ᵥ t) + sγ x := fun x => by
    simp only [hsγ, haff, dotProduct_sub]
    ring
  have hmum : Measurable (mu a) := by
    rw [show mu a = fun x => (a0 + γ ⬝ᵥ t) + sγ x from funext hmuaff]
    exact measurable_const.add hsm
  have hmub : ∀ x, |mu a x| ≤ |a0 + γ ⬝ᵥ t| + p * (‖γ‖ * B) := fun x => by
    rw [hmuaff]
    exact (abs_add_le _ _).trans (add_le_add_right (hsb x) _)
  -- the balance of the tilt kills `E[w₀ sγ]`
  have hws : ∫ z, w z.1 * sγ z.1 ∂ν = 0 := by
    have he : (fun z : 𝒳 × Bool × ℝ => w z.1 * sγ z.1) =
        fun z => ∑ k, γ k * (tiltWeight φ t 0 β₀ z.1 * (φ z.1 k - t k)) := by
      funext z
      simp only [hw, hsγ, dotProduct, Pi.sub_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [he, integral_finsetSum]
    · exact Finset.sum_eq_zero fun k _ => by
        rw [integral_const_mul, integral_tiltWeight_tiltMinimizer_mul_sub hφ hB hδ hmargin k,
          mul_zero]
    · intro k _
      exact (hint (hwm.mul (hΔm k)) (habs hwb (hΔb k))).const_mul _
  -- the arm mean is the affine regression at the target moments
  have hqpos := integral_armIndObs_mul_tiltWeight_pos (ν := ν) hφ hB β₀ hq
  have hmass : ∫ z, armIndObs a z * tiltWeight φ t 0 β₀ z.1 ∂ν = π * ∫ z, w z.1 ∂ν :=
    integral_armIndObs_mul_fst hind a hwm
  have hm0 : m₀ = a0 + γ ⬝ᵥ t := by
    have h1 : ∫ z, armIndObs a z * tiltWeight φ t 0 β₀ z.1 * z.2.2 ∂ν =
        π * ((a0 + γ ⬝ᵥ t) * ∫ z, w z.1 ∂ν) := by
      rw [integral_armIndObs_mul_fst_mul_outcome hy1 hreg a hwm hwb]
      have h2 := integral_armIndObs_mul_fst hind a (hwm.mul hmum)
      simp only [Pi.mul_apply] at h2
      rw [show (fun z : 𝒳 × Bool × ℝ => armIndObs a z * tiltWeight φ t 0 β₀ z.1 * mu a z.1) =
        fun z => armIndObs a z * (w z.1 * mu a z.1) from funext fun z => by ring, h2]
      congr 1
      have he : (fun z : 𝒳 × Bool × ℝ => w z.1 * mu a z.1) =
          fun z => (a0 + γ ⬝ᵥ t) * w z.1 + w z.1 * sγ z.1 := funext fun z => by
        rw [hmuaff]; ring
      have i1 : Integrable (fun z : 𝒳 × Bool × ℝ => (a0 + γ ⬝ᵥ t) * w z.1) ν :=
        (hint hwm hwb).const_mul _
      rw [he, integral_add i1 (hint2 hwm hsm hwb hsb), integral_const_mul, hws, add_zero]
    have hI : (∫ z, w z.1 ∂ν) ≠ 0 := by
      intro h0
      have h3 := hqpos
      rw [hmass, h0, mul_zero] at h3
      exact lt_irrefl _ h3
    rw [hm₀, tiltArmMean, h1, hmass, mul_div_mul_left _ _ hq.ne', mul_div_assoc, div_self hI,
      mul_one]
  have hmus : ∀ x, mu a x - m₀ = sγ x := fun x => by rw [hmuaff, hm0]; ring
  -- the key identity `E[1{A = a} h(X) (Y - m₀)] = π E[h(X) sγ(X)]`
  have key : ∀ {h : 𝒳 → ℝ} {C : ℝ}, Measurable h → (∀ x, |h x| ≤ C) →
      ∫ z, armIndObs a z * h z.1 * (z.2.2 - m₀) ∂ν = π * ∫ z, h z.1 * sγ z.1 ∂ν := by
    intro h C hh hC
    have hI2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * h z.1) ν :=
      integrable_of_abs_le (C := C) ((measurable_armIndObs a).mul (hh.comp measurable_fst))
        fun z => by
        rw [abs_mul]
        rcases armIndObs_eq_zero_or_one a z with h0 | h0
        · rw [h0, abs_zero, zero_mul]; exact (abs_nonneg _).trans (hC z.1)
        · rw [h0, abs_one, one_mul]; exact hC z.1
    have hI1 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * h z.1 * z.2.2) ν :=
      hy1.bdd_mul (c := C) hI2.aestronglyMeasurable (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        rcases armIndObs_eq_zero_or_one a z with h0 | h0
        · rw [h0, abs_zero, zero_mul]; exact (abs_nonneg _).trans (hC z.1)
        · rw [h0, abs_one, one_mul]; exact hC z.1)
    have e1 : ∫ z, armIndObs a z * h z.1 * (z.2.2 - m₀) ∂ν =
        ∫ z, armIndObs a z * h z.1 * z.2.2 ∂ν - m₀ * ∫ z, armIndObs a z * h z.1 ∂ν := by
      rw [← integral_const_mul, ← integral_sub hI1 (hI2.const_mul m₀)]
      congr 1; funext z; ring
    have e2 : ∫ z, armIndObs a z * h z.1 * mu a z.1 ∂ν = π * ∫ z, h z.1 * mu a z.1 ∂ν := by
      have h2 := integral_armIndObs_mul_fst hind a (hh.mul hmum)
      simp only [Pi.mul_apply] at h2
      rw [← h2]
      congr 1; funext z; ring
    have e3 := integral_armIndObs_mul_fst hind a hh
    have e4 : ∫ z, h z.1 * sγ z.1 ∂ν = ∫ z, h z.1 * mu a z.1 ∂ν - m₀ * ∫ z, h z.1 ∂ν := by
      have i4 : Integrable (fun z : 𝒳 × Bool × ℝ => m₀ * h z.1) ν := (hint hh hC).const_mul m₀
      rw [← integral_const_mul, ← integral_sub (hint2 hh hmum hC hmub) i4]
      congr 1; funext z; rw [← hmus]; ring
    rw [e1, integral_armIndObs_mul_fst_mul_outcome hy1 hreg a hh hC, e2, e3, e4]
    ring
  -- the coupling vector is `π M γ`
  have hMt : Mᵀ = M := by
    ext j k
    simp only [hM, tiltedSecondMoment, Matrix.transpose_apply, Matrix.of_apply]
    congr 1; funext z; ring
  have hMu : IsUnit M.det :=
    isUnit_iff_ne_zero.2 (det_tiltedSecondMoment_ne_zero hφ hB hδ hmargin β₀)
  have hc : weightedCoupling ν φ t a = π • (M *ᵥ γ) := by
    funext k
    have h1 := key (h := fun x => w x * (φ x k - t k)) (hwm.mul (hΔm k)) (habs hwb (hΔb k))
    beta_reduce at h1
    have h2 : (M *ᵥ γ) k = ∫ z, w z.1 * (φ z.1 k - t k) * sγ z.1 ∂ν := by
      have he : (fun z : 𝒳 × Bool × ℝ => w z.1 * (φ z.1 k - t k) * sγ z.1) = fun z =>
          ∑ j, (tiltWeight φ t 0 β₀ z.1 * (φ z.1 k - t k) * (φ z.1 j - t j)) * γ j := by
        funext z
        simp only [hw, hsγ, dotProduct, Pi.sub_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [he, integral_finsetSum]
      · simp only [Matrix.mulVec, dotProduct, hM, tiltedSecondMoment, Matrix.of_apply]
        exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
      · intro j _
        exact (hint ((hwm.mul (hΔm k)).mul (hΔm j)) (habs (habs hwb (hΔb k)) (hΔb j))).mul_const _
    rw [Pi.smul_apply, smul_eq_mul, h2, ← h1, weightedCoupling]
    congr 1; funext z; ring
  -- the projection term is `π w₀ sγ`
  have hproj : ∀ z, weightedArmProjection ν φ t a z = π * (w z.1 * sγ z.1) := fun z => by
    rw [weightedArmProjection, hc, smul_dotProduct, dotProduct_mulVec, ← vecMul_transpose, hMt,
      vecMul_vecMul, Matrix.mul_nonsing_inv _ hMu, vecMul_one, smul_eq_mul]
    congr 1
    simp only [hw, hsγ, dotProduct, Pi.sub_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- conclusion
  have hK1 : ∫ z, weightedArmResidual ν φ t a z * weightedArmProjection ν φ t a z ∂ν =
      π * (π * ∫ z, w z.1 ^ 2 * sγ z.1 ^ 2 ∂ν) := by
    have h1 := key (h := fun x => w x ^ 2 * sγ x) ((hwm.pow_const 2).mul hsm)
      (habs (fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hwb x) 2) hsb)
    beta_reduce at h1
    have e : (fun z => weightedArmResidual ν φ t a z * weightedArmProjection ν φ t a z) =
        fun z => π * (armIndObs a z * (w z.1 ^ 2 * sγ z.1) * (z.2.2 - m₀)) :=
      funext fun z => by rw [hproj, weightedArmResidual]; ring
    have e2 : ∫ z, w z.1 ^ 2 * sγ z.1 * sγ z.1 ∂ν = ∫ z, w z.1 ^ 2 * sγ z.1 ^ 2 ∂ν := by
      congr 1; funext z; ring
    rw [e, integral_const_mul, h1, e2]
  have hK2 : ∫ z, weightedArmProjection ν φ t a z ^ 2 ∂ν =
      π ^ 2 * ∫ z, w z.1 ^ 2 * sγ z.1 ^ 2 ∂ν := by
    rw [← integral_const_mul]
    congr 1; funext z; rw [hproj]; ring
  refine ⟨hc, ?_⟩
  rw [weightedNaiveVariance_sub_weightedArmVariance hφ hB hy a, hK1, hK2]
  have hq0 : weightedArmMass ν φ t a ≠ 0 := hqpos.ne'
  field_simp
  ring

/-- **The difference of the naive and the sandwich variance is a nonnegative quadratic form**
under randomization and an affine arm regression:
`σ_naive² - σ² = (π / q)² E[w₀² (γᵀ(φ(X) - t))²]`. -/
theorem weightedNaiveVariance_sub_weightedArmVariance_of_affine [IsProbabilityMeasure ν]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) ν) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    {mu : Bool → 𝒳 → ℝ}
    (hreg : ν[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] fun z => mu z.2.1 z.1)
    {a0 : ℝ} {γ : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + γ ⬝ᵥ φ x) :
    weightedNaiveVariance ν φ t a - weightedArmVariance ν φ t a =
      (ν.real {z | z.2.1 = a} / weightedArmMass ν φ t a) ^ 2 *
        ∫ z, tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 ^ 2 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2 ∂ν :=
  (weightedCoupling_eq_and_sub_of_affine hφ hB hδ hmargin hind hq hy hreg haff).2

/-- **The sandwich variance is at most the naive variance** under randomization and an affine
arm regression. -/
theorem weightedArmVariance_le_weightedNaiveVariance [IsProbabilityMeasure ν]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) ν) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    {mu : Bool → 𝒳 → ℝ}
    (hreg : ν[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] fun z => mu z.2.1 z.1)
    {a0 : ℝ} {γ : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + γ ⬝ᵥ φ x) :
    weightedArmVariance ν φ t a ≤ weightedNaiveVariance ν φ t a := by
  have h := weightedNaiveVariance_sub_weightedArmVariance_of_affine hφ hB hδ hmargin hind hq hy
    hreg haff
  have h0 : 0 ≤ (ν.real {z | z.2.1 = a} / weightedArmMass ν φ t a) ^ 2 *
      ∫ z, tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 ^ 2 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2 ∂ν :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith

/-- **Equality exactly when the projection coefficient vanishes.** Under randomization and an
affine arm regression `μ_a = a₀ + γᵀφ`, the sandwich and the naive variance agree if and only if
`γ = 0`, and the coupling vector `c` vanishes if and only if `γ = 0`. -/
theorem weightedNaiveVariance_eq_weightedArmVariance_iff [IsProbabilityMeasure ν]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) ν) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    {mu : Bool → 𝒳 → ℝ}
    (hreg : ν[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] fun z => mu z.2.1 z.1)
    {a0 : ℝ} {γ : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + γ ⬝ᵥ φ x) :
    (weightedNaiveVariance ν φ t a = weightedArmVariance ν φ t a ↔ γ = 0) ∧
      (weightedCoupling ν φ t a = 0 ↔ γ = 0) := by
  obtain ⟨hc, hdiff⟩ := weightedCoupling_eq_and_sub_of_affine hφ hB hδ hmargin hind hq hy hreg
    haff
  set β₀ := tiltMinimizer ν φ t
  set M := tiltedSecondMoment ν φ t β₀
  have hMu : IsUnit M.det :=
    isUnit_iff_ne_zero.2 (det_tiltedSecondMoment_ne_zero hφ hB hδ hmargin β₀)
  have hqpos := integral_armIndObs_mul_tiltWeight_pos (ν := ν) hφ hB β₀ hq
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← sub_eq_zero, hdiff] at h
    have hK : ∫ z, tiltWeight φ t 0 β₀ z.1 ^ 2 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2 ∂ν = 0 := by
      rcases mul_eq_zero.1 h with h1 | h1
      · exact absurd h1 (pow_ne_zero 2 (div_ne_zero hq.ne' hqpos.ne'))
      · exact h1
    by_contra hγ
    have hpos := dotProduct_tiltedSecondMoment_mulVec_pos (ν := ν) hφ hB hδ hmargin β₀ hγ
    rw [dotProduct_tiltedSecondMoment_mulVec hφ hB] at hpos
    set ε := Real.exp (-(p * (‖β₀‖ * B)))
    have hε : 0 < ε := Real.exp_pos _
    have hsm : Measurable fun z : 𝒳 × Bool × ℝ => γ ⬝ᵥ (φ z.1 - t) :=
      (continuous_const.dotProduct continuous_id).measurable.comp
        ((hφ.comp measurable_fst).sub_const t)
    have hwm := measurable_tiltWeight_fst hφ t β₀
    have hsb : ∀ z : 𝒳 × Bool × ℝ, |γ ⬝ᵥ (φ z.1 - t)| ≤ p * (‖γ‖ * B) := fun z =>
      (abs_dotProduct_le_mul_norm γ (φ z.1 - t)).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hB z.1) (norm_nonneg _)) (Nat.cast_nonneg p))
    have hwb : ∀ z : 𝒳 × Bool × ℝ, ε ≤ tiltWeight φ t 0 β₀ z.1 ∧
        tiltWeight φ t 0 β₀ z.1 ≤ Real.exp (p * (‖β₀‖ * B)) := fun z =>
      tiltWeight_mem_Icc (hB z.1) le_rfl
    have hI1 : Integrable (fun z : 𝒳 × Bool × ℝ =>
        tiltWeight φ t 0 β₀ z.1 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2) ν :=
      integrable_tiltWeight_mul_of_abs_le hφ hB β₀ (hsm.pow_const 2) (C := (p * (‖γ‖ * B)) ^ 2)
        fun z => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hsb z) 2
    have hI2 : Integrable (fun z : 𝒳 × Bool × ℝ =>
        ε⁻¹ * (tiltWeight φ t 0 β₀ z.1 ^ 2 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2)) ν := by
      have hm2 : Measurable fun z : 𝒳 × Bool × ℝ =>
          tiltWeight φ t 0 β₀ z.1 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2 := hwm.mul (hsm.pow_const 2)
      have hb2 : ∀ z : 𝒳 × Bool × ℝ, |tiltWeight φ t 0 β₀ z.1 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2| ≤
          Real.exp (p * (‖β₀‖ * B)) * (p * (‖γ‖ * B)) ^ 2 := fun z => by
        rw [abs_mul, abs_pow, abs_of_pos (tiltWeight_pos _ _ _ _ _)]
        exact mul_le_mul (hwb z).2 (pow_le_pow_left₀ (abs_nonneg _) (hsb z) 2) (by positivity)
          (Real.exp_pos _).le
      refine ((integrable_tiltWeight_mul_of_abs_le hφ hB β₀ hm2 hb2).const_mul ε⁻¹).congr
        (ae_of_all _ fun z => ?_)
      ring
    have hle : ∫ z, tiltWeight φ t 0 β₀ z.1 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2 ∂ν ≤
        ∫ z, ε⁻¹ * (tiltWeight φ t 0 β₀ z.1 ^ 2 * (γ ⬝ᵥ (φ z.1 - t)) ^ 2) ∂ν := by
      refine integral_mono hI1 hI2 fun z => ?_
      have hw0 := tiltWeight_pos φ t 0 β₀ z.1
      rw [← mul_assoc, sq (tiltWeight φ t 0 β₀ z.1), ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [le_mul_iff_one_le_left hw0, inv_mul_eq_div, one_le_div hε]
      exact (hwb z).1
    rw [integral_const_mul, hK, mul_zero] at hle
    linarith
  · rw [← sub_eq_zero, hdiff, h]
    simp
  · rw [hc] at h
    have h1 : M *ᵥ γ = 0 := by
      have := congrArg (fun v => (ν.real {z | z.2.1 = a})⁻¹ • v) h
      simpa [smul_smul, inv_mul_cancel₀ hq.ne'] using this
    have h2 := congrArg (fun v => M⁻¹ *ᵥ v) h1
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu] using h2
  · rw [hc, h]
    simp

end PopulationAdjustment

end CausalInference
