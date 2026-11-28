/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyLogistic

/-!
# The record law of a trial with a binary outcome and a logistic regression

The logistic outcome model of a trial (`Trial.LogisticOutcomeModel`) asks that the law of the
records `((X, A), Y)` be the logistic family at `ξ₀`. This file derives that law from two
statements about the outcome that are checked directly in a model: the observed outcome is almost
surely `0` or `1`, and its regression on the covariates and the arm is `σ(z(X, A) ⬝ ξ₀)`. A binary
variable is determined in law by its conditional mean, so the two statements give the law of the
records (`map_eq_logisticFamily_law`), and with a measurable design of full rank they give the
logistic outcome model (`Trial.LogisticOutcomeModel.of_isOutcomeRegression`).

The regression of a model is often computed on a product space, where the outcome is a function of
the conditioning variables and of an independent noise: the conditional expectation given a
function of the first factor of a product of probability laws is the integral over the second
factor (`condExp_prod_comp_fst`).

## Main results

* `condExp_prod_comp_fst`: the conditional expectation given a function of the first factor of a
  product measure.
* `map_eq_logisticFamily_law`: a binary outcome with a logistic regression has the record law of
  the logistic family.
* `Trial.LogisticOutcomeModel.of_isOutcomeRegression`: the logistic outcome model of a trial from
  a binary observed outcome and its regression.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### Conditional expectation on a product with an independent noise -/

section Noise

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {ρ : Measure α} {τ : Measure β} [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ]

/-- **Conditional expectation given the first factor of a product.** Under the product `ρ ⊗ τ`
of probability laws, let `F` be integrable and let the average of `F (a, ·)` over the second
factor be `φ (W a)` for a measurable `W` and a measurable `φ`. Then `φ (W ω.1)` is a version of
the conditional expectation of `F` given `W ω.1`. -/
theorem condExp_prod_comp_fst {W : α → γ} (hW : Measurable W) {F : α × β → ℝ}
    (hF : Integrable F (ρ.prod τ)) {φ : γ → ℝ} (hφ : Measurable φ)
    (hφF : ∀ a, ∫ u, F (a, u) ∂τ = φ (W a)) :
    (ρ.prod τ)[F | MeasurableSpace.comap (fun ω : α × β => W ω.1) inferInstance] =ᵐ[ρ.prod τ]
      fun ω => φ (W ω.1) := by
  have hV : Measurable fun ω : α × β => W ω.1 := hW.comp measurable_fst
  have hφi : Integrable (fun ω : α × β => φ (W ω.1)) (ρ.prod τ) := by
    have h1 : Integrable (fun a => ∫ u, F (a, u) ∂τ) ρ := hF.integral_prod_left
    simp only [hφF] at h1
    exact h1.comp_fst τ
  refine (ae_eq_condExp_of_forall_setIntegral_eq hV.comap_le hF
    (fun s _ _ => hφi.integrableOn) (fun s hs _ => ?_)
    ((hφ.comp (comap_measurable _)).stronglyMeasurable.aestronglyMeasurable)).symm
  obtain ⟨B, hB, rfl⟩ := hs
  have hpre : (fun ω : α × β => W ω.1) ⁻¹' B = (W ⁻¹' B) ×ˢ (Set.univ : Set β) := by
    ext ω; simp
  rw [hpre, setIntegral_prod _ (hpre ▸ hφi.integrableOn), setIntegral_prod _ hF.integrableOn]
  refine setIntegral_congr_fun (hW hB) fun a _ => ?_
  simp only [Measure.restrict_univ, integral_const, probReal_univ, one_smul, hφF]

end Noise

/-! ### The record law of a binary outcome with a logistic regression -/

section Law

variable {Ω C κ : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [Fintype κ]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {Cv : Ω → C} {Yo : Ω → ℝ}

/-- A variable that is almost surely `0` or `1` is integrable. -/
theorem integrable_of_ae_zero_or_one (hYo : Measurable Yo)
    (hbin : ∀ᵐ ω ∂μ, Yo ω = 0 ∨ Yo ω = 1) : Integrable Yo μ :=
  (integrable_const (1 : ℝ)).mono' hYo.aestronglyMeasurable
    (hbin.mono fun ω h => by rcases h with h | h <;> simp [h])

/-- **A binary outcome with a logistic regression has the record law of the logistic family.** If
the outcome `Y` is almost surely `0` or `1` and its regression on the regressors `C` is
`E[Y | C] = σ(z(C) ⬝ ξ₀)`, then the law of the records `(C, Y)` is the logistic family at `ξ₀`
with the regressor law `R = law(C)`. Both laws give the rectangle `B × S` the mass
`∫_B (1[0 ∈ S] (1 - σ) + 1[1 ∈ S] σ) dR`. -/
theorem map_eq_logisticFamily_law (hCv : Measurable Cv) (hYo : Measurable Yo) {R : Measure C}
    [IsProbabilityMeasure R] (hR : μ.map Cv = R) {z : C → κ → ℝ}
    (hz : ∀ j, Measurable fun c => z c j) {ξ₀ : κ → ℝ} (hbin : ∀ᵐ ω ∂μ, Yo ω = 0 ∨ Yo ω = 1)
    (hreg : μ[Yo | MeasurableSpace.comap Cv inferInstance] =ᵐ[μ]
      fun ω => Real.sigmoid (z (Cv ω) ⬝ᵥ ξ₀)) :
    μ.map (fun ω => (Cv ω, Yo ω)) = (glmFamily logisticKernel R z hz).law ξ₀ := by
  set F := glmFamily logisticKernel R z hz
  have : IsProbabilityMeasure (F.law ξ₀) :=
    ParametricFamily.isProbabilityMeasure_law (F := F) (Set.mem_univ ξ₀)
  have hD : Measurable fun ω => (Cv ω, Yo ω) := hCv.prodMk hYo
  have hYi : Integrable Yo μ := integrable_of_ae_zero_or_one hYo hbin
  set σ₀ : C → ℝ := fun c => Real.sigmoid (z c ⬝ᵥ ξ₀)
  have hσm : Measurable σ₀ :=
    continuous_sigmoid.measurable.comp (measurable_dotProduct_design hz ξ₀)
  refine Measure.ext_prod fun {B S} hB hS => ?_
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  change (μ.map _).real (B ×ˢ S) = (F.law ξ₀).real (B ×ˢ S)
  set s0 : ℝ := S.indicator 1 0
  set s1 : ℝ := S.indicator 1 1
  -- the mass of a rectangle under the law of the records
  have hL : (μ.map fun ω => (Cv ω, Yo ω)).real (B ×ˢ S) =
      ∫ c in B, s0 + (s1 - s0) * σ₀ c ∂R := by
    rw [map_measureReal_apply hD (hB.prod hS)]
    have hpre : (fun ω => (Cv ω, Yo ω)) ⁻¹' (B ×ˢ S) = Cv ⁻¹' B ∩ Yo ⁻¹' S := rfl
    have h1 : μ.real (Cv ⁻¹' B ∩ Yo ⁻¹' S) =
        ∫ ω in Cv ⁻¹' B, (Yo ⁻¹' S).indicator 1 ω ∂μ := by
      rw [setIntegral_indicator (hYo hS)]
      simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
    have h2 : ∫ ω in Cv ⁻¹' B, (Yo ⁻¹' S).indicator 1 ω ∂μ =
        ∫ ω in Cv ⁻¹' B, s0 + (s1 - s0) * Yo ω ∂μ := by
      refine setIntegral_congr_ae (hCv hB) (hbin.mono fun ω h _ => ?_)
      have e : (Yo ⁻¹' S).indicator (1 : Ω → ℝ) ω = S.indicator 1 (Yo ω) := rfl
      rcases h with h | h <;> rw [e, h] <;> simp only [s0, s1] <;> ring
    have hYσ : ∫ ω in Cv ⁻¹' B, Yo ω ∂μ = ∫ ω in Cv ⁻¹' B, σ₀ (Cv ω) ∂μ := by
      rw [← setIntegral_condExp hCv.comap_le hYi ⟨B, hB, rfl⟩]
      exact setIntegral_congr_ae (hCv hB) (hreg.mono fun ω h _ => h)
    have hσi : Integrable (fun ω => σ₀ (Cv ω)) μ :=
      (integrable_const (1 : ℝ)).mono' (hσm.comp hCv).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.sigmoid_pos _)]
          exact Real.sigmoid_le_one _)
    have h3 : ∫ ω in Cv ⁻¹' B, s0 + (s1 - s0) * Yo ω ∂μ =
        ∫ ω in Cv ⁻¹' B, s0 + (s1 - s0) * σ₀ (Cv ω) ∂μ := by
      rw [integral_add (integrable_const _) (hYi.const_mul _).integrableOn,
        integral_add (integrable_const _) (hσi.const_mul _).integrableOn, integral_const_mul,
        integral_const_mul, hYσ]
    rw [hpre, h1, h2, h3, ← hR, setIntegral_map (f := fun c => s0 + (s1 - s0) * σ₀ c) hB
      ((measurable_const.add
      (measurable_const.mul hσm)).aestronglyMeasurable) hCv.aemeasurable]
  -- the mass of a rectangle under the logistic family
  have hRt : (F.law ξ₀).real (B ×ˢ S) = ∫ c in B, s0 + (s1 - s0) * σ₀ c ∂R := by
    have hdm : Measurable fun q : C × ℝ => F.density ξ₀ q := F.measurable_density ξ₀
    have hind : Measurable ((B ×ˢ S).indicator (1 : C × ℝ → ℝ)) :=
      measurable_const.indicator (hB.prod hS)
    have hint : Integrable (fun q => F.density ξ₀ q * (B ×ˢ S).indicator 1 q)
        (R.prod logisticKernel.lam) := by
      refine (F.integrable_density ξ₀ (Set.mem_univ _)).mono' (hdm.mul hind).aestronglyMeasurable
        (ae_of_all _ fun q => ?_)
      have h0 : 0 ≤ F.density ξ₀ q := F.density_nonneg ξ₀ (Set.mem_univ _) q
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      refine mul_le_of_le_one_right h0 ?_
      by_cases hq : q ∈ B ×ˢ S <;> simp [hq]
    rw [← integral_indicator_one (hB.prod hS), ParametricFamily.integral_law (Set.mem_univ ξ₀)]
    change ∫ q, F.density ξ₀ q * (B ×ˢ S).indicator 1 q ∂(R.prod logisticKernel.lam) = _
    rw [integral_prod _ hint, ← integral_indicator hB]
    refine integral_congr_ae (ae_of_all _ fun c => ?_)
    simp only [logisticKernel]
    rw [integral_add_measure (integrable_dirac eNorm_lt_top) (integrable_dirac eNorm_lt_top),
      integral_dirac, integral_dirac]
    change logisticDens (z c ⬝ᵥ ξ₀) 0 * (B ×ˢ S).indicator 1 (c, 0) +
      logisticDens (z c ⬝ᵥ ξ₀) 1 * (B ×ˢ S).indicator 1 (c, 1) = _
    by_cases hc : c ∈ B
    · have hp : ∀ y, (B ×ˢ S).indicator (1 : C × ℝ → ℝ) (c, y) = S.indicator 1 y := fun y => by
        by_cases hy : y ∈ S <;> simp [hc, hy]
      rw [hp, hp, Set.indicator_of_mem hc]
      simp only [logisticDens, s0, s1, σ₀]
      norm_num
      ring
    · simp [hc]
  rw [hL, hRt]

end Law

/-! ### The logistic outcome model of a trial -/

section Trial

variable {Ω₁ 𝒳 κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] [Fintype κ]
  {T : Trial Ω₁ 𝒳 Bool} {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

/-- **The logistic outcome model of a trial from its outcome and regression.** In a randomized
trial, if the observed outcome is almost surely `0` or `1` and its regression on the covariates
and the arm is `σ(z(X, A) ⬝ ξ₀)` (`PointTreatment.IsOutcomeRegression`), and the design is
measurable, integrable and of full rank, then the trial satisfies the logistic outcome model
`Trial.LogisticOutcomeModel z ξ₀`: its records have the law of the logistic family at `ξ₀`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.of_isOutcomeRegression
    [IsProbabilityMeasure T.μ] (hT : T.IsRandomizedTwoArm) (hz : ∀ j, Measurable fun c => z c j)
    (hzi : ∀ j, Integrable (fun ω => z (T.X ω, T.A ω) j) T.μ)
    (hfull : ∀ v : κ → ℝ, (∀ᵐ ω ∂T.μ, z (T.X ω, T.A ω) ⬝ᵥ v = 0) → v = 0)
    (hbin : ∀ᵐ ω ∂T.μ, T.obsOutcome ω = 0 ∨ T.obsOutcome ω = 1)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => Real.sigmoid (z (x, a) ⬝ᵥ ξ₀)) :
    T.LogisticOutcomeModel z ξ₀ where
  measurable_z := hz
  integrable_z := hzi
  full_rank := hfull
  law_eq := map_eq_logisticFamily_law (hT.measurable_X.prodMk hT.measurable_A)
      (measurable_obsOutcome hT.measurable_A hT.measurable_Y) rfl hz hbin hreg.2

end Trial

end PopulationAdjustment

end CausalInference
