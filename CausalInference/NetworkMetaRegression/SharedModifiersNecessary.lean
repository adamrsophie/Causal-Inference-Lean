/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.IdentifiabilityTwoStudy
public import CausalInference.NetworkMetaRegression.Estimands

/-!
# Without shared effect modifiers the target effect is not identified

In the two study network of `IdentifiabilityTwoStudy.lean` (individual data on `a` and `c`,
arm summaries of `b` and `c`), drop the shared effect modifier assumption, so that the
interactions `β₂,b` of `b` are free. The aggregate study reports one mean for arm `b`, one
equation for the `p + 1` unknowns `(γ_b, β₂,b)`.

**What "necessary" means here.** The results below are non identification results in this data
configuration: there are parameter values that reproduce every observed quantity (the surfaces
of `a` and `c` in the individual data study, the aggregate means of `b` and `c` in the aggregate
study) and give different target effects of `b` against `a`. They do not say that the
assumption is needed in every network: individual data on `b`, or several aggregate studies of
`b` with different covariate laws, can identify `β₂,b`. The effect in the population of the
aggregate study itself stays identified without the assumption
(`MultilevelModel.twoStudy_comparator_identified`).

## Main definitions

* `binaryLaw q`: the law of a binary covariate on `{0, 1}` with `P(X = 1) = q`.

## Main results

* `binary_family`: one binary effect modifier with `P(X = 1) = q ∈ (0, 1)` in the aggregate
  study, a continuous strictly increasing inverse link, any value `θ` of it as the observed mean
  of `b`, and any two interactions `d ≠ d'` for `b`. There are effects `γ, γ'` with the observed
  mean `θ` for both, every other surface unchanged, conditional effects of `b` against `a` that
  differ in every target whose covariate mean is not one exceptional value, and marginal
  effects that differ in every binary target with the aggregate study's baseline and
  prevalence `q* ≠ q`.
* `identity_family_example`: the concrete pair on the identity link with `q = 1/2`:
  `(γ_b, β₂,b) = (0, 0)` and `(-1, 2)` give the same data and, in the target concentrated at
  `x = 1`, effects of `b` against `a` that differ by `1`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis
  MultilevelModel

/-! ### A binary covariate -/

/-- The law of a binary covariate on `{0, 1} ⊆ ℝ¹` with `P(X = 1) = q`. -/
noncomputable def binaryLaw (q : ℝ) : Measure (Fin 1 → ℝ) :=
  ENNReal.ofReal (1 - q) • Measure.dirac (fun _ => 0) +
    ENNReal.ofReal q • Measure.dirac (fun _ => 1)

theorem isProbabilityMeasure_binaryLaw {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (binaryLaw q) := by
  constructor
  simp only [binaryLaw, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [hq.2]) hq.1]
  simp

/-- Every function is integrable under `binaryLaw q`. -/
theorem integrable_binaryLaw (q : ℝ) (f : (Fin 1 → ℝ) → ℝ) : Integrable f (binaryLaw q) :=
  ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

theorem integral_binaryLaw {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (f : (Fin 1 → ℝ) → ℝ) :
    ∫ x, f x ∂binaryLaw q = (1 - q) * f (fun _ => 0) + q * f (fun _ => 1) := by
  rw [binaryLaw, integral_add_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal (by linarith [hq.2]),
    ENNReal.toReal_ofReal hq.1, smul_eq_mul, smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-! ### The family -/

variable {μ₀ μ₁ β γa δa : ℝ}

/-- The aggregate mean of `b` in the triangle model under the binary law. -/
theorem armMean_triangleModel_b {ginv : ℝ → ℝ} {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (μ₀ μ₁ β γa γb δa δb α : ℝ) :
    (triangleModel μ₀ μ₁ β γa γb δa δb).armMean ginv α (binaryLaw r) 1 =
      (1 - r) * ginv (α + γb) + r * ginv (α + γb + (β + δb)) := by
  rw [armMean, integral_binaryLaw hr]
  simp only [surface, eta_eq_affine, triangleModel, dotProduct, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply]
  ring_nf

/-- Only the surfaces of `b` depend on `(γ_b, δ_b)`. -/
theorem surface_triangleModel_ne_b (ginv : ℝ → ℝ) (μ₀ μ₁ β γa γb γb' δa δb δb' α : ℝ) {t : Fin 3}
    (ht : t ≠ 1) :
    (triangleModel μ₀ μ₁ β γa γb δa δb).surface ginv α t =
      (triangleModel μ₀ μ₁ β γa γb' δa δb').surface ginv α t := by
  funext x
  fin_cases t
  · rfl
  · exact absurd rfl ht
  · rfl

/-- **Two interaction values, the same data, different target effects.** -/
theorem binary_family {g ginv : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y) (hmono : StrictMono ginv)
    (hcont : Continuous ginv) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) (μ₀ μ₁ β γa δa : ℝ)
    {θ : ℝ} (hθ : θ ∈ Set.range ginv) {d d' : ℝ} (hd : d ≠ d') :
    ∃ γ γ' : ℝ,
      (triangleModel μ₀ μ₁ β γa γ δa d).armMean ginv μ₁ (binaryLaw q) 1 = θ ∧
      (triangleModel μ₀ μ₁ β γa γ' δa d').armMean ginv μ₁ (binaryLaw q) 1 = θ ∧
      (γ, d) ≠ (γ', d') ∧
      (∀ α t, t ≠ 1 → (triangleModel μ₀ μ₁ β γa γ δa d).surface ginv α t =
        (triangleModel μ₀ μ₁ β γa γ' δa d').surface ginv α t) ∧
      (∃ x₀ : ℝ, ∀ (α : ℝ) (F : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure F],
        Integrable (fun x => x 0) F → covMean F 0 ≠ x₀ →
        linkConditional g F ((triangleModel μ₀ μ₁ β γa γ δa d).surface ginv α 0)
            ((triangleModel μ₀ μ₁ β γa γ δa d).surface ginv α 1) ≠
          linkConditional g F ((triangleModel μ₀ μ₁ β γa γ' δa d').surface ginv α 0)
            ((triangleModel μ₀ μ₁ β γa γ' δa d').surface ginv α 1)) ∧
      ∀ q' ∈ Set.Icc (0 : ℝ) 1, q' ≠ q →
        linkMarginal g (binaryLaw q') ((triangleModel μ₀ μ₁ β γa γ δa d).surface ginv μ₁ 0)
            ((triangleModel μ₀ μ₁ β γa γ δa d).surface ginv μ₁ 1) ≠
          linkMarginal g (binaryLaw q') ((triangleModel μ₀ μ₁ β γa γ' δa d').surface ginv μ₁ 0)
            ((triangleModel μ₀ μ₁ β γa γ' δa d').surface ginv μ₁ 1) := by
  have hqI : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
  have hdot : ∀ v : Fin 1 → ℝ, Measurable fun x : Fin 1 → ℝ => x ⬝ᵥ v := fun v =>
    (by unfold dotProduct; fun_prop : Continuous fun x : Fin 1 → ℝ => x ⬝ᵥ v).measurable
  have hrange : ∀ γ dd r, r ∈ Set.Icc (0 : ℝ) 1 →
      (triangleModel μ₀ μ₁ β γa γ δa dd).armMean ginv μ₁ (binaryLaw r) 1 ∈ Set.range ginv := by
    intro γ dd r hr
    have := isProbabilityMeasure_binaryLaw hr
    rw [armMean_eq_shiftMean, ← range_shiftMean hmono hcont (hdot _)
      (fun _ => integrable_binaryLaw r _)]
    exact ⟨_, rfl⟩
  have hsolve : ∀ dd, ∃ γ,
      (triangleModel μ₀ μ₁ β γa γ δa dd).armMean ginv μ₁ (binaryLaw q) 1 = θ := by
    intro dd
    have := isProbabilityMeasure_binaryLaw hqI
    obtain ⟨c, hc, -⟩ := existsUnique_shiftMean_eq (F := binaryLaw q) hmono hcont
      (hdot (fun _ => β + dd)) (fun _ => integrable_binaryLaw q _) hθ
    refine ⟨c - μ₁, ?_⟩
    rw [armMean_eq_shiftMean]
    convert hc using 2
    · funext x
      congr 1
    · simp [triangleModel]
  obtain ⟨γ, hγ⟩ := hsolve d
  obtain ⟨γ', hγ'⟩ := hsolve d'
  set p0 := ginv (μ₁ + γ)
  set p1 := ginv (μ₁ + γ + (β + d))
  set p0' := ginv (μ₁ + γ')
  set p1' := ginv (μ₁ + γ' + (β + d'))
  have hm : (1 - q) * p0 + q * p1 = (1 - q) * p0' + q * p1' := by
    rw [← armMean_triangleModel_b hqI, ← armMean_triangleModel_b hqI, hγ, hγ']
  have hp1 : p1 ≠ p1' := by
    intro e
    have h0 : p0 = p0' := by
      have : (1 - q) * (p0 - p0') = 0 := by rw [e] at hm; linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by linarith [hq.2])
      · linarith
    have hγγ : γ = γ' := by have := hmono.injective h0; linarith
    have := hmono.injective e
    exact hd (by rw [hγγ] at this; linarith)
  refine ⟨γ, γ', hγ, hγ', fun h => hd (Prod.ext_iff.1 h).2,
    fun α t ht => surface_triangleModel_ne_b ginv _ _ _ _ _ _ _ _ _ _ ht, ?_, ?_⟩
  · refine ⟨(γ - γ') / (d' - d), fun α F _ hF hx => ?_⟩
    have hF' : ∀ i : Fin 1, Integrable (fun x : Fin 1 → ℝ => x i) F := fun i => by
      rw [Subsingleton.elim i 0]; exact hF
    rw [linkConditional_surface hg _ α hF', linkConditional_surface hg _ α hF']
    simp only [triangleModel, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    intro e
    apply hx
    have hdd : d' - d ≠ 0 := sub_ne_zero.2 (Ne.symm hd)
    field_simp
    linarith
  · intro q' hq' hqq
    have hA : (triangleModel μ₀ μ₁ β γa γ δa d).armMean ginv μ₁ (binaryLaw q') 0 =
        (triangleModel μ₀ μ₁ β γa γ' δa d').armMean ginv μ₁ (binaryLaw q') 0 := by
      simp only [armMean, surface_triangleModel_ne_b ginv μ₀ μ₁ β γa γ γ' δa d d' μ₁
        (t := 0) (by decide)]
    have hne : (triangleModel μ₀ μ₁ β γa γ δa d).armMean ginv μ₁ (binaryLaw q') 1 ≠
        (triangleModel μ₀ μ₁ β γa γ' δa d').armMean ginv μ₁ (binaryLaw q') 1 := by
      rw [armMean_triangleModel_b hq', armMean_triangleModel_b hq']
      intro e
      have h1 : (q' - q) * ((p1 - p1') - (p0 - p0')) = 0 := by linear_combination e - hm
      rcases mul_eq_zero.1 h1 with h | h
      · exact hqq (by linarith)
      · have h2 : p0 - p0' = 0 := by linear_combination hm - q * h
        exact hp1 (by linarith)
    change g (armMean ginv _ μ₁ (binaryLaw q') 1) - g (armMean ginv _ μ₁ (binaryLaw q') 0) ≠
      g (armMean ginv _ μ₁ (binaryLaw q') 1) - g (armMean ginv _ μ₁ (binaryLaw q') 0)
    rw [hA]
    intro e
    apply hne
    obtain ⟨z, hz⟩ := hrange γ d q' hq'
    obtain ⟨z', hz'⟩ := hrange γ' d' q' hq'
    rw [← hz, ← hz', hg, hg] at e
    rw [← hz, ← hz', show z = z' by linarith]

/-- **The concrete pair on the identity link.** With `q = 1/2`, intercepts `0`, no prognostic
effect, `γ_a = 0` and `δ_a = 0`, the parameters `(γ_b, δ_b) = (0, 0)` (shared effect modifiers)
and `(-1, 2)` (not shared) give the same aggregate means of `b` and `c` (`0` and `0`) and the
same surfaces of `a` and `c`, while in the target concentrated at `x = 1` the effects of `b`
against `a` are `0` and `1`, both marginal and conditional. -/
theorem identity_family_example :
    let M := triangleModel 0 0 0 0 0 0 0
    let M' := triangleModel 0 0 0 0 (-1) 0 2
    M.SharedEffectModifiers {0, 1} ∧ ¬ M'.SharedEffectModifiers {0, 1} ∧
      M.armMean id 0 (binaryLaw (1 / 2)) 1 = 0 ∧ M'.armMean id 0 (binaryLaw (1 / 2)) 1 = 0 ∧
      M.armMean id 0 (binaryLaw (1 / 2)) 2 = M'.armMean id 0 (binaryLaw (1 / 2)) 2 ∧
      (∀ α, M.surface id α 0 = M'.surface id α 0 ∧ M.surface id α 2 = M'.surface id α 2) ∧
      linkMarginal id (Measure.dirac fun _ => 1) (M.surface id 0 0) (M.surface id 0 1) = 0 ∧
      linkMarginal id (Measure.dirac fun _ => 1) (M'.surface id 0 0) (M'.surface id 0 1) = 1 ∧
      linkConditional id (Measure.dirac fun _ => 1) (M.surface id 0 0) (M.surface id 0 1) = 0 ∧
      linkConditional id (Measure.dirac fun _ => 1) (M'.surface id 0 0) (M'.surface id 0 1) =
        1 := by
  dsimp only
  have hI : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨(triangleModel_shared_iff _ _ _ _ _ _ _).2 rfl,
    fun h => absurd ((triangleModel_shared_iff _ _ _ _ _ _ _).1 h) (by norm_num), ?_, ?_, ?_,
    fun α => ⟨surface_triangleModel_ne_b _ _ _ _ _ _ _ _ _ _ _
      (by decide), surface_triangleModel_ne_b _ _ _ _ _ _ _ _ _ _ _ (by decide)⟩, ?_, ?_, ?_, ?_⟩
  · rw [armMean_triangleModel_b hI]; norm_num
  · rw [armMean_triangleModel_b hI]; norm_num
  · simp only [armMean, surface_triangleModel_ne_b id 0 0 0 0 0 (-1) 0 0 2 0 (t := 2)
      (by decide)]
  all_goals
    simp [linkMarginal, linkConditional, linkContrast, surface, eta, metaRegressionPredictor,
      triangleModel, dotProduct]
  all_goals norm_num

end NetworkMetaRegression

end CausalInference
