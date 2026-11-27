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
* `Longitudinal.Model.seqExchangeable_iff_of_sharpNull`: **the g-null test** (Hernán and Robins,
  Technical Point 20.1), in mean form.
* `Longitudinal.Model.gFormula_eq_expect_of_sharpNull`,
  `Longitudinal.Model.gFormula_eq_of_sharpNull`: **the g-null theorem, mean form, one
  direction** (Technical Points 20.1 and 21.3): under the sharp null, consistency, sequential
  exchangeability and positivity, the g-formula equals `E[Y]` for every static regime and so does
  not depend on the regime. The converse direction of the theorem of Robins (1986), stated for
  laws over all static and dynamic regimes, is not proved.
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

omit [Fintype 𝓛] in
/-- **The g-null test** (Hernán and Robins, Technical Point 20.1, mean form). Under the sharp
null and outcome consistency, sequential exchangeability for the static regime `ā` is the
observable condition that the outcome `Y` is mean independent of `A_t = a_t` within every
history event `L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}`. -/
theorem seqExchangeable_iff_of_sharpNull (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNull) (a : Fin K → 𝒜) :
    M.SeqExchangeable a ↔
      ∀ (l : Fin K → 𝓛) (t : Fin K),
        MeanIndepOn M.p (histL M.A M.L a l t) (ev (M.A t) (a t)) M.Y := by
  rw [SeqExchangeable, M.Ypo_eq_Y_of_sharpNull hcons hnull a]

/-- **The g-null theorem, mean form, one direction** (Robins 1986; Hernán and Robins, Technical
Points 20.1 and 21.3). In a longitudinal model, assume outcome consistency for every static
regime and the sharp null hypothesis. Then, for every static regime `ā` satisfying sequential
exchangeability and sequential positivity, the g-formula equals the mean of the observed
outcome and the mean of the potential outcome:
`gFormula p A L ā Y = E[Y] = E[Y(ā)]`. In particular the value of the g-formula does not depend
on the regime (`gFormula_eq_of_sharpNull`).

This is the mean form of one direction only. The theorem of Robins (1986) is an equivalence
about the laws of `Y^g` over all static and dynamic regimes; the converse (if the law of `Y^g` is
the same for every `g` then the outcome is conditionally independent of each treatment given the
past) is not proved here. -/
theorem gFormula_eq_expect_of_sharpNull (hcons : ∀ a, M.OutcomeConsistent a)
    (hnull : M.SharpNull) (a : Fin K → 𝒜) (hex : M.SeqExchangeable a)
    (hpos : M.SeqPositive a) :
    gFormula M.p M.A M.L a M.Y = M.p.expect M.Y ∧ M.p.expect (M.Ypo a) = M.p.expect M.Y := by
  have hY := M.Ypo_eq_Y_of_sharpNull hcons hnull a
  refine ⟨?_, by rw [hY]⟩
  rw [← (M.expect_Ypo_eq_gFormula a (hcons a) hex hpos).1, hY]

/-- **Under the sharp null the g-formula does not depend on the regime.** With outcome
consistency for every static regime, for any two static regimes `ā`, `ā'` satisfying sequential
exchangeability and sequential positivity, `gFormula p A L ā Y = gFormula p A L ā' Y`. -/
theorem gFormula_eq_of_sharpNull (hcons : ∀ a, M.OutcomeConsistent a) (hnull : M.SharpNull)
    {a a' : Fin K → 𝒜} (hex : M.SeqExchangeable a) (hpos : M.SeqPositive a)
    (hex' : M.SeqExchangeable a') (hpos' : M.SeqPositive a') :
    gFormula M.p M.A M.L a M.Y = gFormula M.p M.A M.L a' M.Y := by
  rw [(M.gFormula_eq_expect_of_sharpNull hcons hnull a hex hpos).1,
    (M.gFormula_eq_expect_of_sharpNull hcons hnull a' hex' hpos').1]

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
      (∀ a : Fin 2 → Bool, gFormula p model.A model.L a Y = p.expect Y) ∧
      p.expect Y = 1 / 2 ∧
      condProb p (ev L0 false ∩ ev A0 true) (ev L1 true) ≠
        condProb p (ev L0 false ∩ ev A0 false) (ev L1 true) ∧
      condMean p (ev L0 false ∩ ev A0 true ∩ ev L1 true ∩ ev A1 true) Y ≠
        condMean p (ev L0 false ∩ ev A0 false ∩ ev L1 true ∩ ev A1 true) Y ∧
      naiveAdjusted ≠ 0 ∧ unadjusted ≠ 0 := by
  refine ⟨sharpNull, feedback, fun a => ?_, expect_Ypo false false, ?_, ?_,
    (adjustment_fails).2.2.1, (adjustment_fails).2.2.2⟩
  · exact (model.gFormula_eq_expect_of_sharpNull outcomeConsistent sharpNull a
      (model_seqExchangeable a) (model_seqPositive a)).1
  · rw [covariate_law_depends.1, covariate_law_depends.2]; norm_num
  · rw [outcome_mean_depends.1, outcome_mean_depends.2]; norm_num

end FeedbackExample

end Longitudinal

end CausalInference
