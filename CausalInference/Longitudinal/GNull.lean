/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Dynamic
public import CausalInference.Longitudinal.Counterexamples

/-!
# The g-null theorem (mean form) and the g-null paradox setting

Under the sharp null hypothesis of no treatment effect, every potential outcome is the observed
outcome, so sequential exchangeability becomes a statement about observed data (the g-null test)
and the g-formula takes the same value, the mean of the observed outcome, for every regime
(Robins 1986). The finite setting is that of `CausalInference.Longitudinal.Basic`.

## Main results

* `Longitudinal.gFormula_eq_condMean_of_meanIndep`,
  `Longitudinal.gFormulaDyn_eq_condMean_of_meanIndep`: if the observed outcome is mean
  independent of each treatment along the regime given the past, and sequential positivity holds,
  then the static (respectively dynamic) g-formula equals `E[Y]`. No potential outcome appears.
* `Longitudinal.Model.SharpNull`, `Longitudinal.Model.Ypo_eq_Y_of_sharpNull`: under the sharp
  null and outcome consistency, `Y(ā) = Y`.
* `Longitudinal.Model.SharpNullOnSupport`: the sharp null with probability one (Technical Point
  21.3), the hypothesis of the results below; `Longitudinal.Model.Ypo_eq_Y_of_sharpNullOnSupport`:
  with outcome consistency, `Y(ā) = Y` at every point of positive probability.
* `Longitudinal.Model.seqExchangeable_iff_of_sharpNullOnSupport`,
  `Longitudinal.Model.seqExchangeableDyn_iff_of_sharpNullOnSupport`: **the g-null test**
  (Hernán and Robins, Technical Point 20.1), in mean form, for static and dynamic regimes.
* `Longitudinal.Model.gFormula_eq_expect_of_sharpNullOnSupport`,
  `Longitudinal.Model.gFormula_eq_of_sharpNullOnSupport`,
  `Longitudinal.Model.gFormulaDyn_eq_expect_of_sharpNullOnSupport`,
  `Longitudinal.Model.expect_YpoDyn_of_sharpNullOnSupport`: **the g-null theorem, mean form,
  one direction** (Technical Points 20.1 and 21.3): under the sharp null, consistency, sequential
  exchangeability and positivity, the g-formula equals `E[Y]` for every static and every dynamic
  regime, and so does `E[Y^g]`. The pointwise versions `..._of_sharpNull` are corollaries. The
  converse direction of the theorem of Robins (1986), stated for laws over all static and
  dynamic regimes, is not proved.
* `Longitudinal.EqualLawsExample.equal_laws_not_sharpNull`: equal laws under every regime do not
  imply the sharp null. `Longitudinal.StaticLawsExample.static_laws_not_dynamic`: equal laws
  under every static regime do not give the same law under a dynamic regime.
* `Longitudinal.FeedbackExample.gNull_paradox_setting`: in the treatment-confounder feedback
  example of `Counterexamples.lean`, the sharp null holds together with feedback, the g-formula
  is `1/2` for every static regime, both components of the g-formula depend on the regime, and
  the stratified and unadjusted contrasts are nonzero. The incompatibility result of Robins and
  Wasserman (1997) for nonsaturated parametric models is not formalized.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), section 20.2 and Technical
  Points 20.1 and 21.3.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

section General

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [Fintype 𝓛]
  [DecidableEq 𝓛]

/-- **Mean independence of the observed outcome forces the static g-formula to be the mean of
the outcome.** For a nonnegative mass function of positive total mass, if the observed outcome
`Y` is mean independent of `A_t = a_t` within every history event
`L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}` and sequential positivity holds for `ā`, then
`gFormula m A L a Y = E[Y]`. No potential outcome is involved. -/
theorem gFormula_eq_condMean_of_meanIndep {K : ℕ} {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω)
    (hm0 : 0 < wmass m univ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜)
    (Y : Ω → ℝ)
    (hex : ∀ (l : Fin K → 𝓛) (t : Fin K), MeanIndepOn m (histL A L a l t) (ev (A t) (a t)) Y)
    (hpos : ∀ (l : Fin K → 𝓛) (t : Fin K), 0 < wmass m (histL A L a l t) →
      0 < wmass m (histL A L a l t ∩ ev (A t) (a t))) :
    gFormula m A L a Y = condMean m univ Y := by
  rw [gFormula_eq_iceGFormula, condMean_eq_iceGFormula K hm hm0 A L a Y hex hpos]

/-- **Mean independence of the observed outcome forces the dynamic g-formula to be the mean of
the outcome.** For a nonnegative mass function of positive total mass and a dynamic regime `g`,
if `Y` is mean independent of `A_t = a^g_t` within every history event compatible with `g` and
sequential positivity holds for `g`, then `gFormulaDyn m A L g Y = E[Y]`. -/
theorem gFormulaDyn_eq_condMean_of_meanIndep {K : ℕ} {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω)
    (hm0 : 0 < wmass m univ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) (Y : Ω → ℝ) (hex : SeqExchangeableDyn m A L g Y)
    (hpos : SeqPositiveDyn m A L g) :
    gFormulaDyn m A L g Y = condMean m univ Y := by
  rw [gFormulaDyn_eq_iceGFormulaDyn, condMean_eq_iceGFormulaDyn K hm hm0 A L g Y hex hpos]

namespace Model

variable {K : ℕ} (M : Model Ω K 𝒜 𝓛)

/-- The sharp null hypothesis: the potential outcome is the same under every static regime,
`Y(ā) = Y(ā')` for every individual and all `ā`, `ā'`. -/
def SharpNull : Prop :=
  ∀ a a' : Fin K → 𝒜, M.Ypo a = M.Ypo a'

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Under the sharp null and outcome consistency for every static regime, every potential
outcome is the observed outcome: `Y(ā) = Y` (Hernán and Robins, Technical Point 20.1). -/
theorem Ypo_eq_Y_of_sharpNull (hcons : ∀ a, M.OutcomeConsistent a) (hnull : M.SharpNull)
    (a : Fin K → 𝒜) : M.Ypo a = M.Y := by
  funext ω
  rw [hcons (fun t => M.A t ω) ω (fun _ => rfl), hnull a]

/-- The sharp null hypothesis with probability one (Hernán and Robins, Technical Point 21.3): the
potential outcome is the same under every static regime, `Y(ā) = Y(ā')`, for every individual of
positive probability. It is implied by `SharpNull` and is the hypothesis of the results below;
it puts no condition at the points of zero mass, which no mean or law can detect. -/
def SharpNullOnSupport : Prop :=
  ∀ (a a' : Fin K → 𝒜) (ω : Ω), 0 < M.p ω → M.Ypo a ω = M.Ypo a' ω

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- The pointwise sharp null implies the sharp null on the support. -/
theorem sharpNullOnSupport_of_sharpNull (hnull : M.SharpNull) : M.SharpNullOnSupport :=
  fun a a' ω _ => congrFun (hnull a a') ω

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Under the sharp null on the support and outcome consistency for every static regime, every
potential outcome is the observed outcome at every point of nonzero mass. -/
theorem Ypo_eq_Y_of_sharpNullOnSupport (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNullOnSupport) (a : Fin K → 𝒜) {ω : Ω} (hω : M.p ω ≠ 0) :
    M.Ypo a ω = M.Y ω := by
  rw [hcons (fun t => M.A t ω) ω (fun _ => rfl),
    hnull a _ ω ((M.p.nonneg ω).lt_of_ne (Ne.symm hω))]

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Under the sharp null on the support and outcome consistency, `E[Y(ā)] = E[Y]`. -/
theorem expect_Ypo_of_sharpNullOnSupport (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNullOnSupport) (a : Fin K → 𝒜) : M.p.expect (M.Ypo a) = M.p.expect M.Y :=
  wsum_congr_of_ne_zero (s := univ) fun _ _ hω => M.Ypo_eq_Y_of_sharpNullOnSupport hcons hnull a hω

omit [Fintype 𝓛] in
/-- **The g-null test** (Hernán and Robins, Technical Point 20.1, mean form). Under the sharp
null on the support and outcome consistency, sequential exchangeability for the static regime
`ā` is the observable condition that the outcome `Y` is mean independent of `A_t = a_t` within
every history event `L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}`. -/
theorem seqExchangeable_iff_of_sharpNullOnSupport (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNullOnSupport) (a : Fin K → 𝒜) :
    M.SeqExchangeable a ↔
      ∀ (l : Fin K → 𝓛) (t : Fin K),
        MeanIndepOn M.p (histL M.A M.L a l t) (ev (M.A t) (a t)) M.Y := by
  refine forall_congr' fun l => forall_congr' fun t => ?_
  exact meanIndepOn_congr_of_ne_zero fun ω hω => M.Ypo_eq_Y_of_sharpNullOnSupport hcons hnull a hω

omit [Fintype 𝓛] in
/-- **The g-null test** under the pointwise sharp null (`seqExchangeable_iff_of_sharpNullOnSupport`
under the stronger hypothesis). -/
theorem seqExchangeable_iff_of_sharpNull (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNull) (a : Fin K → 𝒜) :
    M.SeqExchangeable a ↔
      ∀ (l : Fin K → 𝓛) (t : Fin K),
        MeanIndepOn M.p (histL M.A M.L a l t) (ev (M.A t) (a t)) M.Y :=
  M.seqExchangeable_iff_of_sharpNullOnSupport hcons (M.sharpNullOnSupport_of_sharpNull hnull) a

/-- **The g-null theorem, mean form, one direction, static regimes** (Robins 1986; Hernán and
Robins, Technical Points 20.1 and 21.3). In a longitudinal model, assume outcome consistency for
every static regime and the sharp null on the support. Then, for every static regime `ā`
satisfying sequential exchangeability and sequential positivity, the g-formula equals the mean of
the observed outcome and the mean of the potential outcome:
`gFormula p A L ā Y = E[Y] = E[Y(ā)]`. The dynamic form is
`gFormulaDyn_eq_expect_of_sharpNullOnSupport`.

This is the mean form of one direction only. The theorem of Robins (1986) is an equivalence
about the laws of `Y^g` over all static and dynamic regimes; the converse (if the law of `Y^g` is
the same for every `g` then the outcome is conditionally independent of each treatment given the
past) is not proved here. Equality of all these laws does not imply the sharp null itself
(`EqualLawsExample.equal_laws_not_sharpNull`), and equality of the laws over the static regimes
alone does not give it over the dynamic ones (`StaticLawsExample.static_laws_not_dynamic`). -/
theorem gFormula_eq_expect_of_sharpNullOnSupport (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNullOnSupport) (a : Fin K → 𝒜) (hex : M.SeqExchangeable a)
    (hpos : M.SeqPositive a) :
    gFormula M.p M.A M.L a M.Y = M.p.expect M.Y ∧ M.p.expect (M.Ypo a) = M.p.expect M.Y := by
  have hY := M.expect_Ypo_of_sharpNullOnSupport hcons hnull a
  exact ⟨by rw [← (M.expect_Ypo_eq_gFormula a (hcons a) hex hpos).1, hY], hY⟩

/-- **The g-null theorem, mean form, one direction**, under the pointwise sharp null
(`gFormula_eq_expect_of_sharpNullOnSupport` under the stronger hypothesis). In particular the
value of the g-formula does not depend on the regime (`gFormula_eq_of_sharpNull`). -/
theorem gFormula_eq_expect_of_sharpNull (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNull) (a : Fin K → 𝒜) (hex : M.SeqExchangeable a)
    (hpos : M.SeqPositive a) :
    gFormula M.p M.A M.L a M.Y = M.p.expect M.Y ∧ M.p.expect (M.Ypo a) = M.p.expect M.Y :=
  M.gFormula_eq_expect_of_sharpNullOnSupport hcons (M.sharpNullOnSupport_of_sharpNull hnull) a
    hex hpos

/-- **Under the sharp null the g-formula does not depend on the regime.** With outcome
consistency for every static regime and the sharp null on the support, for any two static
regimes `ā`, `ā'` satisfying sequential exchangeability and sequential positivity,
`gFormula p A L ā Y = gFormula p A L ā' Y`. -/
theorem gFormula_eq_of_sharpNullOnSupport (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNullOnSupport) {a a' : Fin K → 𝒜} (hex : M.SeqExchangeable a)
    (hpos : M.SeqPositive a) (hex' : M.SeqExchangeable a') (hpos' : M.SeqPositive a') :
    gFormula M.p M.A M.L a M.Y = gFormula M.p M.A M.L a' M.Y := by
  rw [(M.gFormula_eq_expect_of_sharpNullOnSupport hcons hnull a hex hpos).1,
    (M.gFormula_eq_expect_of_sharpNullOnSupport hcons hnull a' hex' hpos').1]

/-- **Under the sharp null the g-formula does not depend on the regime**, pointwise sharp null
form. -/
theorem gFormula_eq_of_sharpNull (hcons : ∀ a, M.OutcomeConsistent a) (hnull : M.SharpNull)
    {a a' : Fin K → 𝒜} (hex : M.SeqExchangeable a) (hpos : M.SeqPositive a)
    (hex' : M.SeqExchangeable a') (hpos' : M.SeqPositive a') :
    gFormula M.p M.A M.L a M.Y = gFormula M.p M.A M.L a' M.Y :=
  M.gFormula_eq_of_sharpNullOnSupport hcons (M.sharpNullOnSupport_of_sharpNull hnull) hex hpos
    hex' hpos'

/-- **The g-null theorem for dynamic regimes, mean form, one direction** (Hernán and Robins,
Technical Points 20.1 and 21.3). In a longitudinal model, assume outcome consistency for every
static regime, the sharp null on the support, sequential exchangeability for each static regime
`ā^g(l̄)` prescribed by the dynamic regime `g` along a covariate path, and sequential positivity
for `g`. Then `gFormulaDyn p A L g Y = E[Y]`. -/
theorem gFormulaDyn_eq_expect_of_sharpNullOnSupport (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNullOnSupport) (g : DynamicRegime K 𝒜 𝓛)
    (hex : ∀ l, M.SeqExchangeable (g.path l)) (hpos : SeqPositiveDyn M.p M.A M.L g) :
    gFormulaDyn M.p M.A M.L g M.Y = M.p.expect M.Y := by
  have hexY : SeqExchangeableDyn M.p M.A M.L g M.Y := fun l t =>
    (meanIndepOn_congr_of_ne_zero fun ω hω =>
      M.Ypo_eq_Y_of_sharpNullOnSupport hcons hnull (g.path l) hω).1 (hex l l t)
  have h1 : wmass M.p univ = 1 := M.p.sum_eq_one
  rw [gFormulaDyn_eq_condMean_of_meanIndep M.p.nonneg (by rw [h1]; exact one_pos) _ _ g _ hexY
    hpos, expect_eq_condMean]

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Under the sharp null on the support and outcome consistency, the potential outcome under
every dynamic regime is the observed outcome at every point of nonzero mass, and so
`E[Y^g] = E[Y]`. -/
theorem expect_YpoDyn_of_sharpNullOnSupport [Inhabited 𝒜] (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNullOnSupport) (g : DynamicRegime K 𝒜 𝓛) :
    M.p.expect (M.YpoDyn g) = M.p.expect M.Y :=
  wsum_congr_of_ne_zero (s := univ) fun _ _ hω =>
    M.Ypo_eq_Y_of_sharpNullOnSupport hcons hnull _ hω

omit [Fintype 𝓛] in
/-- **The g-null test for a dynamic regime** (Hernán and Robins, Technical Point 20.1). Under the
sharp null on the support and outcome consistency, sequential exchangeability for `Y^g` along the
dynamic regime `g` is the observable condition with the observed outcome `Y` in its place. -/
theorem seqExchangeableDyn_iff_of_sharpNullOnSupport [Inhabited 𝒜]
    (hcons : ∀ a, M.OutcomeConsistent a) (hnull : M.SharpNullOnSupport)
    (g : DynamicRegime K 𝒜 𝓛) :
    SeqExchangeableDyn M.p M.A M.L g (M.YpoDyn g) ↔ SeqExchangeableDyn M.p M.A M.L g M.Y := by
  refine forall_congr' fun l => forall_congr' fun t => ?_
  exact meanIndepOn_congr_of_ne_zero fun ω hω => M.Ypo_eq_Y_of_sharpNullOnSupport hcons hnull _ hω

end Model

end General

namespace FeedbackExample

/-! ### The g-null paradox setting on the treatment-confounder feedback example -/

/-- The treatment-confounder feedback example of `Counterexamples.lean` as a longitudinal model
with two time points. -/
noncomputable def model : Model Ω 2 Bool Bool :=
  Model.ofTwoTime p L0 A0 L1 A1 Y Ypo L1po

/-- The sharp null holds in the feedback example. -/
theorem sharpNull : model.SharpNull := fun _ _ => rfl

/-- Outcome consistency holds for every static regime. -/
theorem outcomeConsistent (a : Fin 2 → Bool) : model.OutcomeConsistent a :=
  (Model.ofTwoTime_outcomeConsistent_iff p L0 A0 L1 A1 Y Ypo L1po).2 (fun _ _ _ _ _ => rfl) a

/-- Covariate consistency holds. -/
theorem covariateConsistent : model.CovariateConsistent :=
  (Model.ofTwoTime_covariateConsistent_iff p L0 A0 L1 A1 Y Ypo L1po).2 covariate_consistent

/-- Sequential exchangeability holds for every static regime. -/
theorem model_seqExchangeable (a : Fin 2 → Bool) : model.SeqExchangeable a :=
  (model.seqExchangeable_iff_two a).2 (seqExchangeable (a 0) (a 1))

/-- Sequential positivity holds for every static regime. -/
theorem model_seqPositive (a : Fin 2 → Bool) : model.SeqPositive a :=
  (model.seqPositive_iff_two a).2 (seqPositive (a 0) (a 1))

/-- The first component of the g-formula depends on the regime: the covariate law
`P(L1 = true | L0 = false, A0 = a0)` is `3/4` for `a0 = true` and `1/2` for `a0 = false`. -/
theorem covariate_law_depends :
    condProb p (ev L0 false ∩ ev A0 true) (ev L1 true) = 3 / 4 ∧
      condProb p (ev L0 false ∩ ev A0 false) (ev L1 true) = 1 / 2 := by
  constructor <;>
  simp only [condProb, wmass, ev, filter_inter, inter_filter, univ_inter, filter_filter,
    sum_filter, Fintype.sum_prod_type, Fintype.sum_bool] <;>
  norm_num [p, mass, A0, L0, L1, L1po]

/-- The second component of the g-formula depends on the regime: the outcome mean
`E[Y | L0 = false, A0 = a0, L1 = true, A1 = true]` is `2/3` for `a0 = true` and `1` for
`a0 = false`. -/
theorem outcome_mean_depends :
    condMean p (ev L0 false ∩ ev A0 true ∩ ev L1 true ∩ ev A1 true) Y = 2 / 3 ∧
      condMean p (ev L0 false ∩ ev A0 false ∩ ev L1 true ∩ ev A1 true) Y = 1 := by
  constructor <;>
  simp only [condMean, wsum, wmass, ev, filter_inter, inter_filter, univ_inter, filter_filter,
    sum_filter, Fintype.sum_prod_type, Fintype.sum_bool] <;>
  norm_num [p, mass, A0, A1, L0, L1, L1po, Y]

/-- **The g-null paradox setting** (Hernán and Robins, section 20.2 and Technical Point 21.3). In
the treatment-confounder feedback example: the sharp null holds; the first treatment affects the
covariate at time `1`; sequential exchangeability and positivity hold for every static regime;
by the g-null theorem the general-horizon g-formula equals `E[Y] = 1/2` for every static regime;
yet both components of the g-formula, the covariate law and the outcome mean, depend on the
regime; and the stratified (adjusted for `L1`) and unadjusted contrasts are biased away from the
true null effect.

The result of Robins and Wasserman (1997) on the incompatibility of nonsaturated parametric
models for the two components is not formalized here. -/
theorem gNull_paradox_setting :
    model.SharpNull ∧
      L1po true (false, false, true, false) ≠ L1po false (false, false, true, false) ∧
      (∀ a : Fin 2 → Bool, model.SeqExchangeable a) ∧ (∀ a : Fin 2 → Bool, model.SeqPositive a) ∧
      (∀ a : Fin 2 → Bool, gFormula p model.A model.L a Y = p.expect Y) ∧
      p.expect Y = 1 / 2 ∧
      condProb p (ev L0 false ∩ ev A0 true) (ev L1 true) ≠
        condProb p (ev L0 false ∩ ev A0 false) (ev L1 true) ∧
      condMean p (ev L0 false ∩ ev A0 true ∩ ev L1 true ∩ ev A1 true) Y ≠
        condMean p (ev L0 false ∩ ev A0 false ∩ ev L1 true ∩ ev A1 true) Y ∧
      naiveAdjusted ≠ 0 ∧ unadjusted ≠ 0 := by
  refine ⟨sharpNull, feedback, model_seqExchangeable, model_seqPositive, fun a => ?_,
    expect_Ypo false false, ?_, ?_, (adjustment_fails).2.2.1, (adjustment_fails).2.2.2⟩
  · exact (model.gFormula_eq_expect_of_sharpNull outcomeConsistent sharpNull a
      (model_seqExchangeable a) (model_seqPositive a)).1
  · rw [covariate_law_depends.1, covariate_law_depends.2]; norm_num
  · rw [outcome_mean_depends.1, outcome_mean_depends.2]; norm_num

end FeedbackExample

namespace EqualLawsExample

/-! ### Equal laws under every regime without the sharp null -/

/-- The sample space: a point is `(a, u)`, the treatment and a fair coin. -/
abbrev Sample := Bool × Bool

/-- The uniform distribution: the treatment and the coin are fair and independent. -/
noncomputable def p : FiniteDist Sample where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_eq_one := by simp

/-- The potential outcomes: `Y(0) = U` and `Y(1) = 1 - U` for the coin `U`. -/
noncomputable def Ypo (a : Fin 1 → Bool) (ω : Sample) : ℝ :=
  if a 0 then (if ω.2 then 0 else 1) else (if ω.2 then 1 else 0)

/-- One time point, a constant covariate, a randomized treatment, and the observed outcome
`Y = Y(A)`. -/
noncomputable def model : Model Sample 1 Bool Unit where
  p := p
  A _ ω := ω.1
  L _ _ := ()
  Y ω := Ypo (fun _ => ω.1) ω
  Ypo := Ypo
  Lpo _ _ _ := ()

/-- Each potential outcome has the law of the observed outcome (point masses `1/2` at `0` and
`1`). -/
theorem prob_Ypo_eq (b : Fin 1 → Bool) (y : ℝ) :
    p.probOf (fun ω => Ypo b ω = y) = p.probOf (fun ω => model.Y ω = y) := by
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool]
  cases h : b 0 <;> simp [Ypo, model, h, p] <;> ring

/-- **Equal laws under every regime do not imply the sharp null.** In this randomized trial with
one time point, consistency holds, the potential outcome under every regime, dynamic or static,
has the law of the observed outcome, and the observed outcome is mean independent of the
treatment; yet the treatment changes the outcome of every individual. -/
theorem equal_laws_not_sharpNull :
    (∀ a, model.OutcomeConsistent a) ∧
      (∀ (g : DynamicRegime 1 Bool Unit) (y : ℝ),
        model.p.probOf (fun ω => model.YpoDyn g ω = y) =
          model.p.probOf (fun ω => model.Y ω = y)) ∧
      (∀ (a : Fin 1 → Bool) (l : Fin 1 → Unit) (t : Fin 1),
        MeanIndepOn model.p (histL model.A model.L a l t) (ev (model.A t) (a t)) model.Y) ∧
      (∀ ω, model.Ypo (fun _ => true) ω ≠ model.Ypo (fun _ => false) ω) ∧
      ¬ model.SharpNullOnSupport := by
  have hne : ∀ ω, model.Ypo (fun _ => true) ω ≠ model.Ypo (fun _ => false) ω := by
    rintro ⟨a, u⟩; cases u <;> norm_num [model, Ypo]
  refine ⟨fun a ω h => ?_, fun g y => prob_Ypo_eq _ y, fun a l t => ?_, hne, fun h => ?_⟩
  · have : a = fun _ => ω.1 := funext fun t => (h t).symm
    subst this; rfl
  · fin_cases t
    cases h : a 0 <;>
    simp only [MeanIndepOn, wsum, wmass, histL, hist, ev, filter_inter, inter_filter, univ_inter,
      filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool] <;>
    norm_num [model, Ypo, p, h]
  · exact hne (true, true) (h _ _ _ (by norm_num [model, p]))

end EqualLawsExample

namespace StaticLawsExample

/-! ### Equal laws under every static regime, a different law under a dynamic regime -/

/-- The sample space: a point is `(l, a)`, the covariate and the treatment, fair and
independent. -/
abbrev Sample := Bool × Bool

/-- The uniform distribution. -/
noncomputable def p : FiniteDist Sample where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_eq_one := by simp

/-- The potential outcome `Y(a) = 1{a = L}`. -/
noncomputable def Ypo (a : Fin 1 → Bool) (ω : Sample) : ℝ := if a 0 = ω.1 then 1 else 0

/-- One time point with covariate `L` and treatment `A`, independent and fair, and the observed
outcome `Y = Y(A) = 1{A = L}`. The covariate is measured before treatment, so it is its own
potential version. -/
noncomputable def model : Model Sample 1 Bool Bool where
  p := p
  A _ ω := ω.2
  L _ ω := ω.1
  Y ω := Ypo (fun _ => ω.2) ω
  Ypo := Ypo
  Lpo _ _ ω := ω.1

/-- The regime "treat if and only if the covariate is `true`". -/
def g : DynamicRegime 1 Bool Bool := fun t l _ => l (Fin.last t)

/-- **Equal laws under every static regime do not give equal laws under a dynamic regime.** In
this model consistency and nonanticipation hold and every static potential outcome has the law
of the observed outcome (Bernoulli `1/2`), but the potential outcome under the dynamic regime `g`
is `1` for every individual. So the g-null theorem has to range over dynamic regimes. -/
theorem static_laws_not_dynamic :
    model.Consistent ∧ model.Nonanticipating ∧
      (∀ (a : Fin 1 → Bool) (y : ℝ),
        model.p.probOf (fun ω => model.Ypo a ω = y) = model.p.probOf (fun ω => model.Y ω = y)) ∧
      model.YpoDyn g = (fun _ => 1) ∧ model.p.probOf (fun ω => model.Y ω = 1) = 1 / 2 := by
  refine ⟨⟨fun a ω h => ?_, fun _ _ _ _ => rfl⟩, fun _ _ _ _ => rfl, fun a y => ?_, ?_, ?_⟩
  · have : a = fun _ => ω.2 := funext fun t => (h t).symm
    subst this; rfl
  · simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool]
    cases h : a 0 <;> simp [Ypo, model, h, p] <;> ring
  · funext ω
    simp [Model.YpoDyn, Model.cfPath, Model.cfStep, model, Ypo, g, DynamicRegime.path_zero,
      DynamicRegime.headRule]
  · simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num [model, Ypo, p]

end StaticLawsExample

end Longitudinal

end CausalInference
