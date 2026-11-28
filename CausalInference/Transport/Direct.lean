/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Formula
public import CausalInference.Measures.LinkScale
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Transport: direct transportability, standardization to an intermediate population and scale
alignment

An effect measure on the scale `g` compares the means `a(x)`, `b(x)` of two arms at covariate
value `x`; its marginal value in a population with covariate law `P` is
`linkMarginal g P a b = g(∫ b dP) - g(∫ a dP)`.

* **Direct transportability.** Under structural invariance (common conditional mean functions)
  the marginal effect of a population depends on it only through its covariate law, so equal
  covariate laws give equal marginal effects (`linkMarginal_eq_of_map_eq`).
* **Standardization to an intermediate population.** A source regression standardized to the
  covariate law of an intermediate population is, by the transport g-formula, the marginal
  effect in that population, and subtracting it from an effect reported there against a third
  arm leaves the effect of the third arm against the source arm in that population
  (`sub_linkMarginal_regression_eq`).
* **Scale alignment.** Let the arms have link scale predictors `η_B(x)`, `η_C(x)` for a link `g`
  with inverse `g⁻¹` on the mean space `D`, sharing their effect modifiers:
  `η_B(x) - η_C(x) = γ`. An effect reported on the scale `h` is **aligned** with the model when
  `h ∘ g⁻¹` is the identity on `g(D)`, that is `h = g` on `D` (`isAlignedScale_iff_eqOn`).
  Aligned, the reported conditional effect is `γ` at every covariate value
  (`linkContrast_eq_of_isAlignedScale`), so the average conditional effect is `γ` in every
  population (`linkConditional_eq_of_aligned`), and on a collapsible scale so is the marginal
  effect (`linkMarginal_eq_of_aligned`). Misaligned, the conditional effect can vary with the
  covariate and the average conditional effect then depends on the covariate law: a log link
  model with common effect `log 2` gives risk differences `1` and `2` in two strata
  (`linkConditional_misaligned_example`).

## Main results

* `linkMarginal_eq_of_map_eq`, `sub_linkMarginal_regression_eq`.
* `isAlignedScale_iff_eqOn`, `linkContrast_eq_of_isAlignedScale`, `linkConditional_eq_of_aligned`,
  `linkMarginal_eq_of_aligned`, `linkConditional_misaligned_example`.

## References

* E. Bareinboim and J. Pearl, *Causal inference and the data-fusion problem*, Proceedings of the
  National Academy of Sciences 113 (2016).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace Transport

open MeasureTheory ProbabilityTheory MissingData PointTreatment EffectMeasure Filter Topology

/-! ### Direct transportability -/

section Direct

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsFiniteMeasure μ₁]
  [IsFiniteMeasure μ₂] {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳} {Y₁ : Bool → Ω₁ → ℝ} {Y₂ : Bool → Ω₂ → ℝ}
  {m : Bool → 𝒳 → ℝ}

omit [IsFiniteMeasure μ₂] in
/-- The mean of a potential outcome is the mean of its conditional mean function under the
covariate law. -/
theorem integral_eq_integral_map_of_condExp (hX₁ : Measurable X₁) {Y : Ω₁ → ℝ}
    (hY : Integrable Y μ₁) {f : 𝒳 → ℝ} (hf : Measurable f)
    (H : (fun ω => f (X₁ ω)) =ᵐ[μ₁] μ₁[Y | MeasurableSpace.comap X₁ inferInstance]) :
    ∫ ω, Y ω ∂μ₁ = ∫ x, f x ∂(μ₁.map X₁) :=
  ((integral_target_eq_integral_common (μ₂ := μ₁) hX₁ hY hf H).2)

/-- **Equal covariate laws give direct transportability.** If `m_t` is a common regression of
`Y(t)` for both arms, the potential outcomes are integrable and the covariate laws of the two
populations are equal, then the marginal effects on any scale `g` are equal:
`g(E₁[Y₁(1)]) - g(E₁[Y₁(0)]) = g(E₂[Y₂(1)]) - g(E₂[Y₂(0)])`, both being
`linkMarginal g P_X (m 0) (m 1)`. -/
theorem linkMarginal_eq_of_map_eq (g : ℝ → ℝ) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hY₁ : ∀ t, Integrable (Y₁ t) μ₁) (hY₂ : ∀ t, Integrable (Y₂ t) μ₂)
    (hcom : ∀ t, IsCommonRegression μ₁ X₁ (Y₁ t) μ₂ X₂ (Y₂ t) (m t))
    (hlaw : μ₁.map X₁ = μ₂.map X₂) :
    g (∫ ω, Y₁ true ω ∂μ₁) - g (∫ ω, Y₁ false ω ∂μ₁) =
      linkMarginal g (μ₁.map X₁) (m false) (m true) ∧
    g (∫ ω, Y₂ true ω ∂μ₂) - g (∫ ω, Y₂ false ω ∂μ₂) =
      linkMarginal g (μ₁.map X₁) (m false) (m true) := by
  have h1 : ∀ t, ∫ ω, Y₁ t ω ∂μ₁ = ∫ x, m t x ∂(μ₁.map X₁) := fun t =>
    integral_eq_integral_map_of_condExp hX₁ (hY₁ t) (hcom t).1 (hcom t).2.1
  have h2 : ∀ t, ∫ ω, Y₂ t ω ∂μ₂ = ∫ x, m t x ∂(μ₁.map X₁) := fun t => by
    rw [hlaw]
    exact (integral_target_eq_integral_common hX₂ (hY₂ t) (hcom t).1 (hcom t).2.2).2
  exact ⟨by rw [h1, h1]; rfl, by rw [h2, h2]; rfl⟩

end Direct

variable {X : Type} [MeasurableSpace X]

/-! ### Standardization to an intermediate population -/

section TwoStep

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsFiniteMeasure μ₁]
  [IsFiniteMeasure μ₂] {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳} {A : Ω₁ → Bool} {Y₁ : Bool → Ω₁ → ℝ}
  {Y₂ : Bool → Ω₂ → ℝ} {e : 𝒳 → ℝ}

/-- **Standardization to an intermediate population.** A study in the source compares arms
`false` and `true`; an intermediate population `(μ₂, X₂, Y₂)` reports
`d̂ = g(m_C) - g(E₂[Y₂(false)])` for a third arm. Under the assumptions of the transport
g-formula for both arms (indicator form of ignorability in the source, positivity, structural
invariance, overlap), the source regression standardized to the intermediate covariate law is
the intermediate effect,
`linkMarginal g P*_X (m 0) (m 1) = g(E₂[Y₂(1)]) - g(E₂[Y₂(0)])`, and the anchored difference
`d̂ - linkMarginal g P*_X (m 0) (m 1)` is the effect `g(m_C) - g(E₂[Y₂(1)])` in the intermediate
population. -/
theorem sub_linkMarginal_regression_eq (g : ℝ → ℝ) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hA : Measurable A) (hY : ∀ b, Measurable (Y₁ b)) (hYi : ∀ b, Integrable (Y₁ b) μ₁)
    (hY₂ : ∀ b, Integrable (Y₂ b) μ₂) (hign : IndicatorIgnorable μ₁ A X₁ Y₁)
    (hps : IsPropensityScore μ₁ A X₁ e) (hpos : ∀ b, ∀ᵐ ω ∂μ₁, 0 < armProb e b (X₁ ω))
    {m : Bool → 𝒳 → ℝ} (hreg : IsOutcomeRegression μ₁ A X₁ (obsOutcome A Y₁) m)
    {gc : Bool → 𝒳 → ℝ} (hcom : ∀ b, IsCommonRegression μ₁ X₁ (Y₁ b) μ₂ X₂ (Y₂ b) (gc b))
    (hov : μ₂.map X₂ ≪ μ₁.map X₁) {mC dHat : ℝ} (hd : dHat = g mC - g (∫ ω, Y₂ false ω ∂μ₂)) :
    linkMarginal g (μ₂.map X₂) (m false) (m true) =
        g (∫ ω, Y₂ true ω ∂μ₂) - g (∫ ω, Y₂ false ω ∂μ₂) ∧
      dHat - linkMarginal g (μ₂.map X₂) (m false) (m true) = g mC - g (∫ ω, Y₂ true ω ∂μ₂) := by
  have h : ∀ b, ∫ ω, Y₂ b ω ∂μ₂ = ∫ x, m b x ∂(μ₂.map X₂) := fun b =>
    integral_target_eq_integral_regression b hX₁ hX₂ hA hY hYi (hY₂ b) hign hps (hpos b) hreg
      (hcom b) hov
  have hB : linkMarginal g (μ₂.map X₂) (m false) (m true) =
      g (∫ ω, Y₂ true ω ∂μ₂) - g (∫ ω, Y₂ false ω ∂μ₂) := by
    rw [linkMarginal, h, h]
  refine ⟨hB, ?_⟩
  rw [hB, hd]
  ring

end TwoStep

/-! ### Scale alignment -/

section Alignment

/-- An effect reported on the scale `h` is **aligned** with a model on the link `g` with inverse
`ginv` on the mean space `D` when `h ∘ ginv` is the identity on the range `g(D)` of the
predictor. -/
def IsAlignedScale (D : Set ℝ) (g ginv h : ℝ → ℝ) : Prop :=
  ∀ η ∈ g '' D, h (ginv η) = η

/-- **Alignment is `h = g` on the mean space**, when `ginv` inverts `g` on `D`. -/
theorem isAlignedScale_iff_eqOn {D : Set ℝ} {g ginv : ℝ → ℝ} (hinv : ∀ p ∈ D, ginv (g p) = p)
    (h : ℝ → ℝ) : IsAlignedScale D g ginv h ↔ Set.EqOn h g D := by
  constructor
  · intro hal p hp
    have := hal (g p) ⟨p, hp, rfl⟩
    rwa [hinv p hp] at this
  · rintro heq _ ⟨p, hp, rfl⟩
    rw [hinv p hp, heq hp]

omit [MeasurableSpace X] in
/-- **The aligned case.** If `h` is aligned with the model and the two predictors share their
effect modifiers, `η_B(x) - η_C(x) = γ`, then at every `x` whose predictors lie in `g(D)` the
reported conditional effect of the means `ginv ∘ η_B` against `ginv ∘ η_C` is `γ`. -/
theorem linkContrast_eq_of_isAlignedScale {D : Set ℝ} {g ginv h : ℝ → ℝ}
    (hal : IsAlignedScale D g ginv h) {ηB ηC : X → ℝ} {γ : ℝ} {x : X}
    (hγ : ηB x - ηC x = γ) (hB : ηB x ∈ g '' D) (hC : ηC x ∈ g '' D) :
    linkContrast h (fun y => ginv (ηC y)) (fun y => ginv (ηB y)) x = γ := by
  rw [linkContrast, hal _ hB, hal _ hC, hγ]

/-- **Conditional transport under alignment.** If `h` is aligned with the model, the predictors
share their effect modifiers and lie almost surely in `g(D)` under a covariate law `P`, then the
average conditional effect on the scale `h` is `γ` in `P`, whatever `P`. No collapsibility is
needed. -/
theorem linkConditional_eq_of_aligned {D : Set ℝ} {g ginv h : ℝ → ℝ}
    (hal : IsAlignedScale D g ginv h) {ηB ηC : X → ℝ} {γ : ℝ} (hγ : ∀ x, ηB x - ηC x = γ)
    (P : Measure X) [IsProbabilityMeasure P] (hP : ∀ᵐ x ∂P, ηB x ∈ g '' D ∧ ηC x ∈ g '' D) :
    linkConditional h P (fun y => ginv (ηC y)) (fun y => ginv (ηB y)) = γ := by
  rw [linkConditional, integral_congr_ae (g := fun _ => γ)
    (hP.mono fun x hx => linkContrast_eq_of_isAlignedScale hal (hγ x) hx.1 hx.2)]
  simp

/-- **Collapsible transport under alignment.** If the model scale `g` is collapsible on `D`,
`ginv` maps `g(D)` into `D`, the predictors share their effect modifiers, and in a covariate law
`P` the predictors lie almost surely in `g(D)` with integrable means, then the marginal effect on
the model scale is `γ`. In particular the direct transport gap between two such populations is
zero. -/
theorem linkMarginal_eq_of_aligned {D : Set ℝ} {g ginv : ℝ → ℝ} (hcol : LinkCollapsible D g)
    (hinv : ∀ p ∈ D, ginv (g p) = p) {ηB ηC : X → ℝ} {γ : ℝ} (hγ : ∀ x, ηB x - ηC x = γ)
    (P : Measure X) [IsProbabilityMeasure P] (hP : ∀ᵐ x ∂P, ηB x ∈ g '' D ∧ ηC x ∈ g '' D)
    (hiB : Integrable (fun y => ginv (ηB y)) P) (hiC : Integrable (fun y => ginv (ηC y)) P) :
    linkMarginal g P (fun y => ginv (ηC y)) (fun y => ginv (ηB y)) = γ := by
  have hal : IsAlignedScale D g ginv g := (isAlignedScale_iff_eqOn hinv g).2 fun _ _ => rfl
  have hmem : ∀ η ∈ g '' D, ginv η ∈ D := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hinv p hp]; exact hp
  exact hcol X P _ _ hiC hiB (hP.mono fun x hx => ⟨hmem _ hx.2, hmem _ hx.1⟩) γ
    (hP.mono fun x hx => linkContrast_eq_of_isAlignedScale hal (hγ x) hx.1 hx.2)

/-- **The misaligned case.** Take the log link on the positive means, `g = log`, `g⁻¹ = exp`,
and report risk differences, `h = id`, which is not aligned with the model. With predictors
`η_C(x) = log 2 · 1{x}` and `η_B = η_C + log 2`, sharing their effect modifiers, the means are
`1, 2` in the arm `C` and `2, 4` in the arm `B`, so the conditional risk difference is `1` at
`x = false` and `2` at `x = true`. The average conditional effect is therefore `1` in the
population concentrated at `false` and `2` in the one concentrated at `true`. -/
theorem linkConditional_misaligned_example :
    ¬ IsAlignedScale (Set.Ioi 0) Real.log Real.exp id ∧
    (∀ x : Bool, ((if x then Real.log 2 else 0) + Real.log 2) - (if x then Real.log 2 else 0) =
      Real.log 2) ∧
    linkConditional id (Measure.dirac false) (fun x => Real.exp (if x then Real.log 2 else 0))
      (fun x => Real.exp ((if x then Real.log 2 else 0) + Real.log 2)) = 1 ∧
    linkConditional id (Measure.dirac true) (fun x => Real.exp (if x then Real.log 2 else 0))
      (fun x => Real.exp ((if x then Real.log 2 else 0) + Real.log 2)) = 2 := by
  have hinv : ∀ p ∈ Set.Ioi (0 : ℝ), Real.exp (Real.log p) = p := fun p hp => Real.exp_log hp
  refine ⟨fun hal => ?_, fun x => by ring, ?_, ?_⟩
  · have h1 := (isAlignedScale_iff_eqOn hinv id).1 hal (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    simp at h1
  · simp [linkConditional, linkContrast, Real.exp_add, Real.exp_log]
    norm_num
  · simp [linkConditional, linkContrast, Real.exp_add, Real.exp_log]
    norm_num

end Alignment

end Transport

end CausalInference
