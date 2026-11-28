/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Direct
public import CausalInference.Transport.Identification

/-!
# Indirect comparison: populations, trials, relative effects and estimands

The objects shared by indirect comparisons through a common comparator and by population
adjustment.

**Treatments.** Treatments form an arbitrary type `ι`. An indirect comparison names three of
them: two active treatments `a`, `b` and a common comparator `c`. A general index type, rather
than an inductive type with three constructors, is what a network of trials needs: the pairwise
and network results index the same objects by any finite set of treatments, and the smallest
anchored network is the case of three named elements. No result here needs the three treatments
to be distinct unless it says so.

**Populations.** A population (`Population Ω 𝒳 ι`) is a probability space with covariates `X`
and potential outcomes `Y t`, one for each treatment, as one side of a `Transport.TransportModel`
(`Transport.TransportModel.sourceTrial`, `Transport.TransportModel.targetPopulation`). It enters
most results only through its covariate law `covLaw` and versions of the conditional means
`E[Y(t) | X]` (`IsCondMean`). A trial (`Trial`) adds the assigned treatment.

**Orientation of contrasts.** Throughout, the effect of `b` relative to `a` on the scale `g` is
`g(mean of b) - g(mean of a)`: the conditional effect is `linkContrast g (m a) (m b)`, the
marginal effect `linkMarginal g ν (m a) (m b)`, the average conditional effect
`linkConditional g ν (m a) (m b)` (`Measures/LinkScale.lean`). Writing `d_ab` for it, the link
positions `η_t = g(mean of t)` give `d_ab = η_b - η_a`, so `d_ab = -d_ba`, `d_aa = 0`, and
contrasts add along paths: `d_ab = d_ac - d_bc` (`linkMarginal_eq_sub`). The indirect comparison
of `a` and `b` through `c` is therefore `d_ac - d_bc`.

**Two trials.** In the anchored setting (`AnchoredSetting`) one trial compares `a` with `c` and
reports individual data (the law `Trial.ipdLaw` of covariates, assigned treatment and outcome),
another compares `b` with `c` and reports aggregate data (`Trial.aggregate`: arm means of the
outcome and means of covariate features), and the estimand is a contrast of `a` and `b` in a
target population. In the unanchored setting (`UnanchoredSetting`) there is no common
comparator.

## Main definitions

* `Population`, `Population.covLaw`, `Population.armMean`, `Population.IsCondMean`,
  `Population.marginalEffect`.
* `Trial`, `Trial.obsOutcome`, `Trial.ipdLaw`, `Trial.ipdEmpirical`, `Trial.armSummary`,
  `Trial.aggregate`,
  `AggregateData`.
* `AnchoredSetting`, `UnanchoredSetting`.
* `linkPosition`; `anchoredEstimand ν τ₁ τ₂ = ∫ τ₁ dν - ∫ τ₂ dν`.

## Main results

* `Population.isCommonRegression_iff`: a common regression of `Y(t)` in two populations is a
  version of the conditional mean in each.
* `Population.IsCondMean.integral_eq`, `Population.marginalEffect_eq_linkMarginal`: the arm mean
  is the mean of the conditional mean under the covariate law, so the marginal effect of a
  population is `linkMarginal` of its covariate law.
* `linkMarginal_eq_sub`, `linkMarginal_swap`, `linkMarginal_self`, `linkConditional_eq_sub`:
  antisymmetry and additivity of contrasts.
* `Transport.TransportModel.sourceTrial_ipdLaw`: the individual data law of a source study is the
  `sourceLaw` of the transport model.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure Transport

/-! ### Populations -/

/-- A **population**: a measure `μ` (a probability measure in the results), covariates `X` with
values in `𝒳`, and a potential outcome `Y t` for every treatment `t : ι`. -/
structure Population (Ω 𝒳 ι : Type*) [MeasurableSpace Ω] where
  /-- The law of the population. -/
  μ : Measure Ω
  /-- The covariates. -/
  X : Ω → 𝒳
  /-- The potential outcomes. -/
  Y : ι → Ω → ℝ

namespace Population

variable {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

/-- The covariate law `μ ∘ X⁻¹` of the population. -/
noncomputable def covLaw (P : Population Ω 𝒳 ι) : Measure 𝒳 := P.μ.map P.X

/-- The mean `E[Y(t)]` of the potential outcome of treatment `t` in the population. -/
noncomputable def armMean (P : Population Ω 𝒳 ι) (t : ι) : ℝ := ∫ ω, P.Y t ω ∂P.μ

/-- `m` is a **conditional mean function** of `Y(t)` in the population: `m` is measurable and
`m(X)` is a version of `E[Y(t) | X]`. -/
def IsCondMean (P : Population Ω 𝒳 ι) (t : ι) (m : 𝒳 → ℝ) : Prop :=
  Measurable m ∧
    (fun ω => m (P.X ω)) =ᵐ[P.μ] P.μ[P.Y t | MeasurableSpace.comap P.X inferInstance]

/-- The **marginal effect** of `b` relative to `a` on the scale `g` in the population,
`g(E[Y(b)]) - g(E[Y(a)])`. -/
noncomputable def marginalEffect (g : ℝ → ℝ) (P : Population Ω 𝒳 ι) (a b : ι) : ℝ :=
  g (P.armMean b) - g (P.armMean a)

variable {Ω' : Type*} [MeasurableSpace Ω'] {P : Population Ω 𝒳 ι} {Q : Population Ω' 𝒳 ι}

/-- **A common regression is a conditional mean function in each population.** -/
theorem isCommonRegression_iff (t : ι) (m : 𝒳 → ℝ) :
    IsCommonRegression P.μ P.X (P.Y t) Q.μ Q.X (Q.Y t) m ↔ P.IsCondMean t m ∧ Q.IsCondMean t m :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩, fun h => ⟨h.1.1, h.1.2, h.2.2⟩⟩

/-- Two conditional mean functions of the same arm agree almost everywhere under the covariate
law. -/
theorem IsCondMean.ae_eq {t : ι} {m m' : 𝒳 → ℝ} (hX : Measurable P.X) (h : P.IsCondMean t m)
    (h' : P.IsCondMean t m') : ∀ᵐ x ∂P.covLaw, m x = m' x :=
  (ae_map_iff hX.aemeasurable (measurableSet_eq_fun h.1 h'.1)).2 (h.2.trans h'.2.symm)

/-- A conditional mean function is integrable under the covariate law. -/
theorem IsCondMean.integrable {t : ι} {m : 𝒳 → ℝ} (hX : Measurable P.X) (h : P.IsCondMean t m) :
    Integrable m P.covLaw :=
  (integrable_map_measure h.1.aestronglyMeasurable hX.aemeasurable).2
    (integrable_condExp.congr h.2.symm)

/-- **The arm mean is the mean of the conditional mean under the covariate law**:
`E[Y(t)] = ∫ m dP_X`, for an integrable potential outcome (the tower property). -/
theorem IsCondMean.integral_eq [IsFiniteMeasure P.μ] {t : ι} {m : 𝒳 → ℝ} (hX : Measurable P.X)
    (hY : Integrable (P.Y t) P.μ) (h : P.IsCondMean t m) : ∫ x, m x ∂P.covLaw = P.armMean t :=
  (integral_eq_integral_map_of_condExp hX hY h.1 h.2).symm

/-- **The marginal effect is `linkMarginal` of the covariate law**: if `m a` and `m b` are
conditional mean functions of integrable potential outcomes, then
`g(E[Y(b)]) - g(E[Y(a)]) = linkMarginal g P_X m_a m_b`. -/
theorem marginalEffect_eq_linkMarginal [IsFiniteMeasure P.μ] (g : ℝ → ℝ) {a b : ι}
    {ma mb : 𝒳 → ℝ} (hX : Measurable P.X) (hYa : Integrable (P.Y a) P.μ)
    (hYb : Integrable (P.Y b) P.μ) (ha : P.IsCondMean a ma) (hb : P.IsCondMean b mb) :
    P.marginalEffect g a b = linkMarginal g P.covLaw ma mb := by
  rw [marginalEffect, linkMarginal, ha.integral_eq hX hYa, hb.integral_eq hX hYb]

/-- A probability population has a probability covariate law. -/
theorem isProbabilityMeasure_covLaw [IsProbabilityMeasure P.μ] (hX : Measurable P.X) :
    IsProbabilityMeasure P.covLaw :=
  (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance

end Population

/-! ### Trials and their data -/

/-- **Aggregate data** of a trial: the arm means `armMean t` of the outcome and the means
`covMean k` of `p` covariate features. -/
structure AggregateData (ι : Type*) (p : ℕ) where
  /-- The mean outcome in each arm. -/
  armMean : ι → ℝ
  /-- The means of the covariate features. -/
  covMean : Fin p → ℝ

/-- A **trial**: a population in which each unit is assigned a treatment `A`. -/
structure Trial (Ω 𝒳 ι : Type*) [MeasurableSpace Ω] extends Population Ω 𝒳 ι where
  /-- The assigned treatment. -/
  A : Ω → ι

namespace Trial

variable {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace ι]

/-- The observed outcome `Y(A)`. -/
def obsOutcome (T : Trial Ω 𝒳 ι) : Ω → ℝ := fun ω => T.Y (T.A ω) ω

/-- **Individual data**: the law of the triple `(X, A, Y(A))` of a unit of the trial. -/
noncomputable def ipdLaw (T : Trial Ω 𝒳 ι) : Measure (𝒳 × ι × ℝ) :=
  T.μ.map fun ω => (T.X ω, T.A ω, T.obsOutcome ω)

/-- The **empirical law of individual data** `(x_i, t_i, y_i)`, `i < n`: mass `1/n` at each
observed triple. -/
noncomputable def ipdEmpirical {𝒳' ι' : Type*} [MeasurableSpace 𝒳'] [MeasurableSpace ι']
    {n : ℕ} (x : Fin n → 𝒳') (t : Fin n → ι') (y : Fin n → ℝ) : Measure (𝒳' × ι' × ℝ) :=
  (n : ENNReal)⁻¹ • ∑ i, Measure.dirac (x i, t i, y i)

/-- The empirical law of a nonempty sample is a probability measure. -/
theorem isProbabilityMeasure_ipdEmpirical {𝒳' ι' : Type*} [MeasurableSpace 𝒳']
    [MeasurableSpace ι'] {n : ℕ} (hn : 0 < n) (x : Fin n → 𝒳') (t : Fin n → ι') (y : Fin n → ℝ) :
    IsProbabilityMeasure (ipdEmpirical x t y) := by
  constructor
  have h := ENNReal.inv_mul_cancel (a := (n : ENNReal)) (by exact_mod_cast hn.ne')
    (ENNReal.natCast_ne_top n)
  simpa [ipdEmpirical] using h

/-- The mean outcome among the units assigned to `t`, `E[Y | A = t]`. -/
noncomputable def armSummary (T : Trial Ω 𝒳 ι) (t : ι) : ℝ :=
  ∫ ω, T.obsOutcome ω ∂(T.μ[|T.A ⁻¹' {t}])

/-- **Aggregate data** of the trial for the covariate features `φ : 𝒳 → Fin p → ℝ`: the arm
summaries and the means `E[φ(X)_k]`. -/
noncomputable def aggregate (T : Trial Ω 𝒳 ι) {p : ℕ} (φ : 𝒳 → Fin p → ℝ) : AggregateData ι p :=
  ⟨T.armSummary, fun k => ∫ ω, φ (T.X ω) k ∂T.μ⟩

end Trial

/-! ### The two trial settings

These structures carry the data of an indirect comparison; the results of this folder are stated
on their components. -/

/-- The **anchored setting**: a trial of `a` against the common comparator `c` with individual
data, a trial of `b` against `c` with aggregate data, and a target population; the estimand is a
contrast of `b` against `a` in the target. -/
structure AnchoredSetting (Ω₁ Ω₂ Ω₃ 𝒳 ι : Type*) [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace Ω₃] where
  /-- The trial of `a` against `c`, with individual data. -/
  ipdTrial : Trial Ω₁ 𝒳 ι
  /-- The trial of `b` against `c`, with aggregate data. -/
  agdTrial : Trial Ω₂ 𝒳 ι
  /-- The target population. -/
  target : Population Ω₃ 𝒳 ι
  /-- The active treatment of the individual data trial. -/
  a : ι
  /-- The active treatment of the aggregate data trial. -/
  b : ι
  /-- The common comparator. -/
  c : ι

/-- The **unanchored setting**: a source with outcomes on `a`, a separate source with outcomes on
`b`, no common comparator, and a target population. -/
structure UnanchoredSetting (Ω₁ Ω₂ Ω₃ 𝒳 ι : Type*) [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace Ω₃] where
  /-- The source of outcome data on `a`. -/
  sourceA : Population Ω₁ 𝒳 ι
  /-- The source of outcome data on `b`. -/
  sourceB : Population Ω₂ 𝒳 ι
  /-- The target population. -/
  target : Population Ω₃ 𝒳 ι
  /-- The first treatment. -/
  a : ι
  /-- The second treatment. -/
  b : ι

/-! ### Link positions, contrasts and estimands -/

section Contrasts

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳]

/-- The **link position** `η = g(∫ m dν)` of an arm with conditional mean `m` under the covariate
law `ν`. -/
noncomputable def linkPosition (g : ℝ → ℝ) (ν : Measure 𝒳) (m : 𝒳 → ℝ) : ℝ := g (∫ x, m x ∂ν)

/-- The marginal effect of `b` relative to `a` is the difference of link positions. -/
theorem linkMarginal_eq_linkPosition_sub (g : ℝ → ℝ) (ν : Measure 𝒳) (ma mb : 𝒳 → ℝ) :
    linkMarginal g ν ma mb = linkPosition g ν mb - linkPosition g ν ma := rfl

/-- **Antisymmetry of contrasts**: `d_ab = -d_ba`. -/
theorem linkMarginal_swap (g : ℝ → ℝ) (ν : Measure 𝒳) (ma mb : 𝒳 → ℝ) :
    linkMarginal g ν ma mb = -linkMarginal g ν mb ma := by
  simp only [linkMarginal]; ring

/-- `d_aa = 0`. -/
theorem linkMarginal_self (g : ℝ → ℝ) (ν : Measure 𝒳) (m : 𝒳 → ℝ) : linkMarginal g ν m m = 0 :=
  sub_self _

/-- **Contrasts add along paths**: `d_ab = d_ac - d_bc` in one population; the position of the
intermediate treatment `c` cancels. -/
theorem linkMarginal_eq_sub (g : ℝ → ℝ) (ν : Measure 𝒳) (ma mb mc : 𝒳 → ℝ) :
    linkMarginal g ν ma mb = linkMarginal g ν ma mc - linkMarginal g ν mb mc := by
  simp only [linkMarginal]; ring

omit [MeasurableSpace 𝒳] in
/-- **Pointwise additivity of conditional effects**: `τ_ab = τ_ac - τ_bc`. -/
theorem linkContrast_eq_sub (g : ℝ → ℝ) (ma mb mc : 𝒳 → ℝ) (x : 𝒳) :
    linkContrast g ma mb x = linkContrast g ma mc x - linkContrast g mb mc x := by
  simp only [linkContrast]; ring

/-- **Additivity of average conditional effects**: `Δ_ab = Δ_ac - Δ_bc` for conditional effects
`τ_ac`, `τ_bc` integrable under `ν`. -/
theorem linkConditional_eq_sub {g : ℝ → ℝ} {ν : Measure 𝒳} {ma mb mc : 𝒳 → ℝ}
    (hac : Integrable (linkContrast g ma mc) ν) (hbc : Integrable (linkContrast g mb mc) ν) :
    linkConditional g ν ma mb = linkConditional g ν ma mc - linkConditional g ν mb mc := by
  rw [linkConditional, linkConditional, linkConditional, ← integral_sub hac hbc]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => linkContrast_eq_sub g ma mb mc x)

/-- The **anchored estimand**: two conditional effects against the common comparator, each
from its own trial, standardized to the covariate law `ν` of the target,
`∫ τ_ac dν - ∫ τ_bc dν`. -/
noncomputable def anchoredEstimand (ν : Measure 𝒳) (τac τbc : 𝒳 → ℝ) : ℝ :=
  ∫ x, τac x ∂ν - ∫ x, τbc x ∂ν

/-- **With one conditional mean function per arm the anchored estimand is the average
conditional effect** of `b` relative to `a`, for integrable conditional effects. -/
theorem anchoredEstimand_linkContrast {g : ℝ → ℝ} {ν : Measure 𝒳} {ma mb mc : 𝒳 → ℝ}
    (hac : Integrable (linkContrast g ma mc) ν) (hbc : Integrable (linkContrast g mb mc) ν) :
    anchoredEstimand ν (linkContrast g ma mc) (linkContrast g mb mc) =
      linkConditional g ν ma mb :=
  (linkConditional_eq_sub hac hbc).symm

end Contrasts

end IndirectComparison

/-! ### Bridges to the transport model -/

namespace Transport.TransportModel

open IndirectComparison

variable {Ω₁ Ω₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- The source study of a transport model as a trial with treatments `Bool`. -/
def sourceTrial (M : TransportModel Ω₁ Ω₂ 𝒳) : Trial Ω₁ 𝒳 Bool :=
  ⟨⟨M.μ₁, M.X₁, M.Y₁⟩, M.A⟩

/-- The target of a transport model as a population with treatments `Bool`. -/
def targetPopulation (M : TransportModel Ω₁ Ω₂ 𝒳) : Population Ω₂ 𝒳 Bool :=
  ⟨M.μ₂, M.X₂, M.Y₂⟩

/-- The individual data law of the source trial is the source law of the transport model. -/
theorem sourceTrial_ipdLaw (M : TransportModel Ω₁ Ω₂ 𝒳) :
    (sourceTrial M).ipdLaw = M.sourceLaw := rfl

/-- The covariate law of the target population is the target covariate law. -/
theorem targetPopulation_covLaw (M : TransportModel Ω₁ Ω₂ 𝒳) :
    (targetPopulation M).covLaw = M.targetCovLaw := rfl

omit [MeasurableSpace 𝒳] in
/-- The arm means of the target population are the target means. -/
theorem targetPopulation_armMean (M : TransportModel Ω₁ Ω₂ 𝒳) (t : Bool) :
    (targetPopulation M).armMean t = M.targetMean t := rfl

end Transport.TransportModel

end CausalInference
