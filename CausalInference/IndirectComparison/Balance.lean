/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Constancy
public import CausalInference.Measures.LinkScaleExamples
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Balance, and target estimands under absolute and relative constancy

**Balance.** A covariate is *balanced* between two populations when it has the same law in both
(`CovBalanced`). An unadjusted component `W` is *balanced given* the adjustment set `X` when one
Markov kernel is the conditional law of `W` given `X` in both populations (`CondBalanced`).
Balance of `X` and of `W` given `X` is balance of `(X, W)` (`CondBalanced.covBalanced`).

**Target estimands.** Let `P` be a source population and `Q` a target, with overlap
`Q_X ≪ P_X` and density ratio `w`.

* Under absolute constancy of both arms (a common conditional mean `m_t` in both populations),
  the target marginal effect is computed from the source conditional means and either the target
  covariate law or the source reweighted by `w`, and so is the target average conditional effect
  (`target_estimands_of_commonRegression`).
* Relative constancy identifies the target average conditional effect
  (`linkConditional_eq_of_relativeConstancy`) but not the target marginal effect: two
  populations with the same conditional log risk ratio in every stratum have marginal log risk
  ratios `log (4/3)` and `log (6/5)` (`relativeConstancy_not_marginal_example`).
* On a collapsible scale with a constant conditional effect the target marginal effect and the
  target average conditional effect coincide (`marginalEffect_eq_linkConditional_of_collapsible`).

## Main definitions

* `CovBalanced`, `CondBalanced`.

## Main results

* `CondBalanced.covBalanced`, `condBalanced_prod_example`.
* `target_estimands_of_commonRegression`, `relativeConstancy_not_marginal_example`,
  `constancy_transport_example`,
  `marginalEffect_eq_linkConditional_of_collapsible`, `log_collapsible_example`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure Transport

/-! ### Balance -/

section Balance

variable {Ω₁ Ω₂ 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲]

/-- The covariate is **balanced** between two populations: it has the same law in both. -/
def CovBalanced (μ₁ : Measure Ω₁) (X₁ : Ω₁ → 𝒳) (μ₂ : Measure Ω₂) (X₂ : Ω₂ → 𝒳) : Prop :=
  μ₁.map X₁ = μ₂.map X₂

/-- The component `W` is **balanced given** `X`: one Markov kernel `κ` is the conditional law of
`W` given `X` in both populations, that is, each joint law of `(X, W)` is the law of `X`
composed with `κ`. -/
def CondBalanced (μ₁ : Measure Ω₁) (X₁ : Ω₁ → 𝒳) (W₁ : Ω₁ → 𝒲) (μ₂ : Measure Ω₂) (X₂ : Ω₂ → 𝒳)
    (W₂ : Ω₂ → 𝒲) : Prop :=
  ∃ κ : Kernel 𝒳 𝒲, IsMarkovKernel κ ∧ μ₁.map (fun ω => (X₁ ω, W₁ ω)) = μ₁.map X₁ ⊗ₘ κ ∧
    μ₂.map (fun ω => (X₂ ω, W₂ ω)) = μ₂.map X₂ ⊗ₘ κ

/-- **Balance of `X` and of `W` given `X` is balance of `(X, W)`.** -/
theorem CondBalanced.covBalanced {μ₁ : Measure Ω₁} {X₁ : Ω₁ → 𝒳} {W₁ : Ω₁ → 𝒲}
    {μ₂ : Measure Ω₂} {X₂ : Ω₂ → 𝒳} {W₂ : Ω₂ → 𝒲} (hX : CovBalanced μ₁ X₁ μ₂ X₂)
    (hW : CondBalanced μ₁ X₁ W₁ μ₂ X₂ W₂) :
    CovBalanced μ₁ (fun ω => (X₁ ω, W₁ ω)) μ₂ (fun ω => (X₂ ω, W₂ ω)) := by
  obtain ⟨κ, -, h₁, h₂⟩ := hW
  rw [CovBalanced, h₁, h₂, show μ₁.map X₁ = μ₂.map X₂ from hX]

end Balance

/-- **An instance of conditional balance.** With two independent fair coins `(x, w)` in each of two
populations, `w` is balanced given `x` with the constant kernel `halfLaw`, `x` is balanced, and
so is `(x, w)`. -/
theorem condBalanced_prod_example :
    CondBalanced (halfLaw.prod halfLaw) Prod.fst Prod.snd (halfLaw.prod halfLaw) Prod.fst
        Prod.snd ∧
      CovBalanced (halfLaw.prod halfLaw) Prod.fst (halfLaw.prod halfLaw) Prod.fst ∧
      CovBalanced (halfLaw.prod halfLaw) (fun ω : Bool × Bool => (ω.1, ω.2))
        (halfLaw.prod halfLaw) (fun ω : Bool × Bool => (ω.1, ω.2)) := by
  have e : (halfLaw.prod halfLaw).map (fun ω : Bool × Bool => (ω.1, ω.2)) =
      (halfLaw.prod halfLaw).map Prod.fst ⊗ₘ Kernel.const Bool halfLaw := by
    rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.compProd_const]
    exact Measure.map_id
  have hC : CondBalanced (halfLaw.prod halfLaw) Prod.fst Prod.snd (halfLaw.prod halfLaw)
      Prod.fst Prod.snd := ⟨Kernel.const Bool halfLaw, inferInstance, e, e⟩
  exact ⟨hC, rfl, hC.covBalanced rfl⟩

/-! ### Target estimands -/

section Target

variable {Ω₁ Ω₂ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]
  {P : Population Ω₁ 𝒳 ι} {Q : Population Ω₂ 𝒳 ι} {a b : ι}

/-- **Target estimands under absolute constancy.** If `m_a` and `m_b` are common conditional mean
functions of `Y(a)` and `Y(b)` in the source `P` and the target `Q`, the potential outcomes of
the target are integrable, and `Q_X ≪ P_X` with density ratio `w`, then the target marginal effect
is `h(∫ m_b dQ_X) - h(∫ m_a dQ_X) = h(E_P[w m_b]) - h(E_P[w m_a])`, and for a measurable scale
`h` the target average conditional effect is `E_P[w(X) τ_ab(X)]`. -/
theorem target_estimands_of_commonRegression [IsFiniteMeasure P.μ] [IsFiniteMeasure Q.μ]
    {h : ℝ → ℝ}
    (hh : Measurable h) (hX₁ : Measurable P.X) (hX₂ : Measurable Q.X) {ma mb : 𝒳 → ℝ}
    (ha : IsCommonRegression P.μ P.X (P.Y a) Q.μ Q.X (Q.Y a) ma)
    (hb : IsCommonRegression P.μ P.X (P.Y b) Q.μ Q.X (Q.Y b) mb)
    (hYa : Integrable (Q.Y a) Q.μ) (hYb : Integrable (Q.Y b) Q.μ)
    (hov : Q.covLaw ≪ P.covLaw) :
    Q.marginalEffect h a b = linkMarginal h Q.covLaw ma mb ∧
      Q.marginalEffect h a b =
        h (∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * mb (P.X ω) ∂P.μ) -
          h (∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * ma (P.X ω) ∂P.μ) ∧
      linkConditional h Q.covLaw ma mb =
        ∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * linkContrast h ma mb (P.X ω) ∂P.μ := by
  rw [Population.isCommonRegression_iff] at ha hb
  have e := Q.marginalEffect_eq_linkMarginal h hX₂ hYa hYb ha.2 hb.2
  refine ⟨e, ?_, integral_densityRatio_mul hX₁ hov ((hh.comp hb.1.1).sub (hh.comp ha.1.1))⟩
  rw [e, linkMarginal, Population.covLaw, integral_densityRatio_mul hX₁ hov ha.1.1,
    integral_densityRatio_mul hX₁ hov hb.1.1]

end Target

/-- A population on `Bool` with covariate `id`, law `ν`, and potential outcomes `m t`, which are
their own conditional means. -/
noncomputable def stratumPopulation (ν : Measure Bool) (m : Fin 2 → Bool → ℝ) :
    Population Bool Bool (Fin 2) :=
  ⟨ν, id, m⟩

instance (ν : Measure Bool) [IsFiniteMeasure ν] (m : Fin 2 → Bool → ℝ) :
    IsFiniteMeasure (stratumPopulation ν m).μ :=
  ‹_›

theorem stratumPopulation_isCondMean (ν : Measure Bool) [IsFiniteMeasure ν] (m : Fin 2 → Bool → ℝ)
    (t : Fin 2) : (stratumPopulation ν m).IsCondMean t (m t) :=
  Population.isCondMean_of_eq_comp measurable_id (measurable_of_finite _) rfl Integrable.of_finite

/-- **Relative constancy does not identify the marginal effect.** Under two equally likely strata
on the log scale, the source risks `(1/4, 1/2)` under `a` and `(1/2, 1/2)` under `b`, and the
target risks `(1/8, 1/2)` and `(1/4, 1/2)`, have the conditional log risk ratio `(log 2, 0)` in
both populations: relative constancy holds and the average conditional effects agree. The
marginal log risk ratios are `log (4/3)` in the source and `log (6/5)` in the target. -/
theorem relativeConstancy_not_marginal_example :
    let P := stratumPopulation halfLaw fun t x => if t = 0 then (if x then 1 / 4 else 1 / 2)
      else 1 / 2
    let Q := stratumPopulation halfLaw fun t x => if t = 0 then (if x then 1 / 8 else 1 / 2)
      else (if x then 1 / 4 else 1 / 2)
    RelativeConstancy Real.log P Q 0 1 ∧
      linkConditional Real.log P.covLaw (P.Y 0) (P.Y 1) =
        linkConditional Real.log Q.covLaw (Q.Y 0) (Q.Y 1) ∧
      P.marginalEffect Real.log 0 1 = Real.log (4 / 3) ∧
      Q.marginalEffect Real.log 0 1 = Real.log (6 / 5) ∧
      P.marginalEffect Real.log 0 1 ≠ Q.marginalEffect Real.log 0 1 := by
  intro P Q
  have hcov : ∀ R : Population Bool Bool (Fin 2), R.μ = halfLaw → R.X = id → R.covLaw = halfLaw :=
    fun R h1 h2 => by rw [Population.covLaw, h1, h2, Measure.map_id]
  have hP : P.covLaw = halfLaw := hcov P rfl rfl
  have hQ : Q.covLaw = halfLaw := hcov Q rfl rfl
  have key : Real.log (1 / 2) - Real.log (1 / 4) = Real.log (1 / 4) - Real.log (1 / 8) := by
    rw [← Real.log_div (by norm_num) (by norm_num), ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hcon : ∀ x, linkContrast Real.log (P.Y 0) (P.Y 1) x =
      linkContrast Real.log (Q.Y 0) (Q.Y 1) x := by
    intro x
    cases x
    · simp [linkContrast, P, Q, stratumPopulation]
    · simpa [linkContrast, P, Q, stratumPopulation] using key
  have hrel : RelativeConstancy Real.log P Q 0 1 :=
    ⟨linkContrast Real.log (P.Y 0) (P.Y 1), _, _, _, _, stratumPopulation_isCondMean _ _ 0,
      stratumPopulation_isCondMean _ _ 1, stratumPopulation_isCondMean _ _ 0,
      stratumPopulation_isCondMean _ _ 1, Filter.Eventually.of_forall fun _ => rfl,
      Filter.Eventually.of_forall fun x => (hcon x).symm⟩
  have e1 : P.marginalEffect Real.log 0 1 = Real.log (4 / 3) := by
    simp only [Population.marginalEffect, Population.armMean, P, stratumPopulation,
      integral_halfLaw]
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have e2 : Q.marginalEffect Real.log 0 1 = Real.log (6 / 5) := by
    simp only [Population.marginalEffect, Population.armMean, Q, stratumPopulation,
      integral_halfLaw]
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hrel, ?_, e1, e2, ?_⟩
  · rw [hP, hQ]; exact integral_congr_ae (Filter.Eventually.of_forall hcon)
  · rw [e1, e2]
    exact (Real.log_lt_log (by norm_num) (by norm_num : (6 : ℝ) / 5 < 4 / 3)).ne'

/-- **An instance of transport under constancy.** For the populations of
`relativeConstancy_not_marginal_example` (equal covariate laws, so overlap holds), relative
constancy carries the source conditional log risk ratio to the target: the target average
conditional effect is the source conditional effect averaged over the target covariate law. For
a population compared with itself, its own conditional means are common regressions, absolute
constancy gives relative constancy, and the marginal effect is `linkMarginal` of the reweighted
source. -/
theorem constancy_transport_example :
    let P := stratumPopulation halfLaw fun t x => if t = 0 then (if x then 1 / 4 else 1 / 2)
      else 1 / 2
    let Q := stratumPopulation halfLaw fun t x => if t = 0 then (if x then 1 / 8 else 1 / 2)
      else (if x then 1 / 4 else 1 / 2)
    (∀ᵐ x ∂Q.covLaw, linkContrast Real.log (P.Y 0) (P.Y 1) x =
        linkContrast Real.log (Q.Y 0) (Q.Y 1) x) ∧
      linkConditional Real.log Q.covLaw (Q.Y 0) (Q.Y 1) =
        ∫ x, linkContrast Real.log (P.Y 0) (P.Y 1) x ∂Q.covLaw ∧
      RelativeConstancy Real.log P P 0 1 ∧
      P.marginalEffect Real.log 0 1 = linkMarginal Real.log P.covLaw (P.Y 0) (P.Y 1) := by
  intro P Q
  have hrel := (relativeConstancy_not_marginal_example).1
  have hcov : ∀ R : Population Bool Bool (Fin 2), R.μ = halfLaw → R.X = id → R.covLaw = halfLaw :=
    fun R h1 h2 => by rw [Population.covLaw, h1, h2, Measure.map_id]
  have hov : Q.covLaw ≪ P.covLaw := by
    rw [hcov P rfl rfl, hcov Q rfl rfl]
  have hc : ∀ (R : Population Bool Bool (Fin 2)) (t : Fin 2), R = P ∨ R = Q →
      R.IsCondMean t (R.Y t) := by
    rintro R t (rfl | rfl) <;> exact stratumPopulation_isCondMean _ _ t
  have hcr : ∀ t, IsCommonRegression P.μ P.X (P.Y t) P.μ P.X (P.Y t) (P.Y t) := fun t =>
    (Population.isCommonRegression_iff t _).2 ⟨hc P t (Or.inl rfl), hc P t (Or.inl rfl)⟩
  refine ⟨hrel.ae_eq measurable_id measurable_id hov (hc P 0 (Or.inl rfl)) (hc P 1 (Or.inl rfl))
      (hc Q 0 (Or.inr rfl)) (hc Q 1 (Or.inr rfl)),
    (linkConditional_eq_of_relativeConstancy Real.measurable_log hrel measurable_id
      measurable_id hov (hc P 0 (Or.inl rfl)) (hc P 1 (Or.inl rfl)) (hc Q 0 (Or.inr rfl))
      (hc Q 1 (Or.inr rfl))).1,
    relativeConstancy_of_structurallyInvariant ⟨_, hcr 0⟩ ⟨_, hcr 1⟩,
    (target_estimands_of_commonRegression Real.measurable_log measurable_id measurable_id
      (hcr 0) (hcr 1) Integrable.of_finite Integrable.of_finite
      Measure.AbsolutelyContinuous.rfl).1⟩

/-- **Marginal and conditional target estimands coincide on a collapsible scale.** If the scale
`g` is collapsible on `D`, the conditional means `m_a`, `m_b` of integrable potential outcomes
take values in `D` and have a constant conditional effect `c` under the covariate law of a
probability population `Q`, then the marginal effect of `Q` and its average conditional effect
are both `c`. -/
theorem marginalEffect_eq_linkConditional_of_collapsible {Ω ι : Type*} {𝒳 : Type}
    [MeasurableSpace Ω] [MeasurableSpace 𝒳] {Q : Population Ω 𝒳 ι} [IsProbabilityMeasure Q.μ]
    {D : Set ℝ} {g : ℝ → ℝ} (hcol : LinkCollapsible D g) (hX : Measurable Q.X) {a b : ι}
    {ma mb : 𝒳 → ℝ} (ha : Q.IsCondMean a ma) (hb : Q.IsCondMean b mb)
    (hYa : Integrable (Q.Y a) Q.μ) (hYb : Integrable (Q.Y b) Q.μ)
    (hD : ∀ᵐ x ∂Q.covLaw, ma x ∈ D ∧ mb x ∈ D) {c : ℝ}
    (hc : ∀ᵐ x ∂Q.covLaw, linkContrast g ma mb x = c) :
    Q.marginalEffect g a b = c ∧ linkConditional g Q.covLaw ma mb = c := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX
  refine ⟨?_, ?_⟩
  · rw [Q.marginalEffect_eq_linkMarginal g hX hYa hYb ha hb]
    exact hcol 𝒳 Q.covLaw ma mb (ha.integrable hX) (hb.integrable hX) hD c hc
  · simp [linkConditional, integral_congr_ae hc]

/-- **An instance on the log scale.** Under two equally likely strata, risks `(1/4, 1/2)` under
`a` and `(1/2, 1)` under `b` have the conditional log risk ratio `log 2` in both strata, and the
marginal log risk ratio and the average conditional effect are both `log 2`. -/
theorem log_collapsible_example :
    let Q := stratumPopulation halfLaw fun t x => if t = 0 then (if x then 1 / 4 else 1 / 2)
      else (if x then 1 / 2 else 1)
    Q.marginalEffect Real.log 0 1 = Real.log 2 ∧
      linkConditional Real.log Q.covLaw (Q.Y 0) (Q.Y 1) = Real.log 2 := by
  intro Q
  have hX : Measurable Q.X := measurable_id
  have hD : ∀ᵐ x ∂Q.covLaw, Q.Y 0 x ∈ Set.Ioi 0 ∧ Q.Y 1 x ∈ Set.Ioi 0 :=
    Filter.Eventually.of_forall fun x => by
      cases x <;> norm_num [Q, stratumPopulation]
  have hc : ∀ᵐ x ∂Q.covLaw, linkContrast Real.log (Q.Y 0) (Q.Y 1) x = Real.log 2 :=
    Filter.Eventually.of_forall fun x => by
      cases x <;>
        · simp only [linkContrast, Q, stratumPopulation]
          rw [← Real.log_div (by norm_num) (by norm_num)]
          norm_num
  have : IsProbabilityMeasure Q.μ := by simp only [Q, stratumPopulation]; infer_instance
  exact marginalEffect_eq_linkConditional_of_collapsible linkCollapsible_log hX
    (stratumPopulation_isCondMean _ _ 0) (stratumPopulation_isCondMean _ _ 1) Integrable.of_finite
    Integrable.of_finite hD hc

end IndirectComparison

end CausalInference
