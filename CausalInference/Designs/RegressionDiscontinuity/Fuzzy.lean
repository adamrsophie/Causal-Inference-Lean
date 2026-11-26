/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.RegressionDiscontinuity.Sharp

/-!
# Fuzzy regression discontinuity: local Wald identification at the cutoff

In a fuzzy design, crossing the cutoff `c` changes the probability of treatment without setting
it to one or zero. Everything is stated through conditional mean functions of the running
variable, so that no conditioning on the null event `X = c` is needed.

## Main definitions

* `CausalInference.RD.Stratum`: principal strata defined by the potential treatments
  `(D1, D0)` (treatment taken when assigned above, resp. below, the cutoff): always-takers,
  compliers, never-takers, defiers.
* `CausalInference.RD.FuzzyModel`: conditional stratum shares and stratum-specific conditional
  means of the potential outcomes, as functions of the running variable.
* `CausalInference.RD.FuzzyModel.treatmentProb` and `CausalInference.RD.FuzzyModel.outcomeReg`:
  the model's treatment probability `p x = P(D = 1 | X = x)` and outcome regression
  `x ↦ E[Y | X = x]`.
* `CausalInference.RD.FuzzyModel.IsValid`: nonnegative shares summing to one.
* `CausalInference.RD.FuzzyModel.ArmsContinuousAtCutoff`: the four one-sided continuity
  hypotheses the complier argument uses; `CausalInference.RD.FuzzyModel.ContinuousAtCutoff` and
  `CausalInference.RD.FuzzyModel.ContinuousAtCutoffExceptDefiers` are sufficient conditions.
* `CausalInference.RD.FuzzyModel.IsCondExpModel`: the link, in product form, between a model
  and a probability space carrying the running variable, a stratum variable and the potential
  outcomes.

## Main results

* `CausalInference.RD.fuzzy_wald_identification`: for any four conditional mean functions
  `q1 q0 a1 a0` (treatment and outcome means under assignment above and below the cutoff), with
  one-sided continuity at `c` and a nonzero jump in treatment probability, the ratio of the jump
  in the observed outcome regression to the jump in the observed treatment probability equals
  `(a1 c - a0 c) / (q1 c - q0 c)`.
* `CausalInference.RD.fuzzy_wald_sharp`: with `q1 = 1` and `q0 = 0` the ratio reduces to the
  sharp identification result.
* `CausalInference.RD.FuzzyModel.fuzzy_wald_complier_of_arms`: the algebraic form, for any
  model: under the one-sided arm continuity, no defiers at the cutoff, and a nonzero treatment
  jump, the jump is the complier share and the Wald ratio is the complier effect.
* `CausalInference.RD.FuzzyModel.fuzzy_rd_complier_identification_of_arms`: for a valid model,
  moreover the complier share is positive and the treatment probability increases across the
  cutoff. `CausalInference.RD.FuzzyModel.fuzzy_rd_complier_identification` (two-sided continuity
  of shares and revealed means) and
  `CausalInference.RD.FuzzyModel.fuzzy_rd_complier_identification_of_noDefiersNear` (no
  defiers in a neighborhood of `c`, defier means unrestricted) are corollaries.
* `CausalInference.RD.FuzzyModel.fuzzy_rd_cutoff_sharp`: for a valid model whose treatment
  probability jumps from `0` to `1` at `c`, the complier share at `c` is one and the outcome
  jump is the average treatment effect at `c`, whatever compliance is away from `c`.
* `CausalInference.RD.FuzzyModel.sharp_outcomeReg` and
  `CausalInference.RD.FuzzyModel.sharp_treatmentProb`: the sharp design is the fuzzy model in
  which everyone is a complier; `CausalInference.RD.FuzzyModel.sharp_of_complier_identification`
  recovers the sharp result, under its one-sided hypotheses, from the complier theorem.
* `CausalInference.RD.FuzzyModel.IsCondExpModel.condExp_treatment_eq_treatmentProb` and
  `CausalInference.RD.FuzzyModel.IsCondExpModel.condExp_outcome_eq_outcomeReg`: the
  measure-theoretic bridge; `treatmentProb c ∘ X` and `outcomeReg c ∘ X` are versions of
  `E[1{D} | σ(X)]` and `E[Y | σ(X)]`.
* `CausalInference.RD.FuzzyModel.fuzzy_rd_complier_identification_of_condExp`: with support of
  the running variable on both sides of `c`, the complier effect is identified from arbitrary
  versions of the observed conditional means, that is, from the law of `(X, D, Y)`.

## Sources

J. Hahn, P. Todd, W. Van der Klaauw (2001), Identification and estimation of treatment effects
with a regression-discontinuity design, Econometrica 69(1).
G. W. Imbens, T. Lemieux (2008), Regression discontinuity designs: a guide to practice,
Journal of Econometrics 142(2).
-/

@[expose] public section

open Filter Topology

namespace CausalInference

namespace RD

/-- Principal strata of a fuzzy regression discontinuity design, classified by the pair of
potential treatments `(D1, D0)`, where `D1` is the treatment taken when assigned above the
cutoff and `D0` when assigned below: always-takers `(1, 1)`, compliers `(1, 0)`, never-takers
`(0, 0)`, defiers `(0, 1)`. -/
inductive Stratum
  | alwaysTaker
  | complier
  | neverTaker
  | defier
  deriving DecidableEq

/-- `Stratum.treated t above` is the potential treatment of stratum `t` when assigned above the
cutoff (`above = true`) or below it (`above = false`). -/
def Stratum.treated : Stratum → Bool → Bool
  | .alwaysTaker, _ => true
  | .complier, above => above
  | .neverTaker, _ => false
  | .defier, above => !above

/-- The sum of a real quantity over the four principal strata. -/
def Stratum.sum (f : Stratum → ℝ) : ℝ :=
  f .alwaysTaker + f .complier + f .neverTaker + f .defier

/-! ### The local Wald ratio for general conditional mean functions -/

/-- **Fuzzy regression discontinuity: the local Wald ratio.** Let `q1 x` and `q0 x` be versions
of `E[D1 | X = x]` and `E[D0 | X = x]` (treatment taken under assignment above, resp. below, the
cutoff), and `a1 x`, `a0 x` versions of the conditional means of the outcome under assignment
above, resp. below, the cutoff. The observed treatment probability is
`observedRegression c q1 q0` and the observed outcome regression is `observedRegression c a1 a0`.
Assume `q1`, `a1` right-continuous at `c` and `q0`, `a0` left-continuous at `c`. If the
treatment probability jumps at the cutoff (`pPlus ≠ pMinus`, the hypothesis that makes the ratio
meaningful), then `q1 c ≠ q0 c` and the ratio of the outcome jump to the treatment jump equals
`(a1 c - a0 c) / (q1 c - q0 c)`. -/
theorem fuzzy_wald_identification {c : ℝ} {q1 q0 a1 a0 : ℝ → ℝ}
    (hq1 : Tendsto q1 (𝓝[>] c) (𝓝 (q1 c))) (hq0 : Tendsto q0 (𝓝[<] c) (𝓝 (q0 c)))
    (ha1 : Tendsto a1 (𝓝[>] c) (𝓝 (a1 c))) (ha0 : Tendsto a0 (𝓝[<] c) (𝓝 (a0 c)))
    {pPlus pMinus yPlus yMinus : ℝ}
    (hpPlus : Tendsto (observedRegression c q1 q0) (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto (observedRegression c q1 q0) (𝓝[<] c) (𝓝 pMinus))
    (hyPlus : Tendsto (observedRegression c a1 a0) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (observedRegression c a1 a0) (𝓝[<] c) (𝓝 yMinus))
    (hjump : pPlus ≠ pMinus) :
    q1 c ≠ q0 c ∧ (yPlus - yMinus) / (pPlus - pMinus) = (a1 c - a0 c) / (q1 c - q0 c) := by
  have hp := sharp_rd_identification hq1 hq0 hpPlus hpMinus
  have hy := sharp_rd_identification ha1 ha0 hyPlus hyMinus
  refine ⟨fun h => hjump (sub_eq_zero.mp (hp.trans (sub_eq_zero.mpr h))), ?_⟩
  rw [hp, hy]

/-- **The sharp design as a special case of the fuzzy one.** With `q1 = 1` and `q0 = 0` (every
unit at or above the cutoff is treated, every unit below is not), the observed treatment
probability jumps from `0` to `1`, the local Wald ratio equals the observed outcome jump, and the
fuzzy identification result `fuzzy_wald_identification` gives exactly the sharp result
`sharp_rd_identification`: the ratio equals `m1 c - m0 c`. -/
theorem fuzzy_wald_sharp {c : ℝ} {m1 m0 : ℝ → ℝ}
    (h1 : Tendsto m1 (𝓝[>] c) (𝓝 (m1 c))) (h0 : Tendsto m0 (𝓝[<] c) (𝓝 (m0 c)))
    {pPlus pMinus yPlus yMinus : ℝ}
    (hpPlus : Tendsto (observedRegression c (fun _ => 1) (fun _ => 0)) (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto (observedRegression c (fun _ => 1) (fun _ => 0)) (𝓝[<] c) (𝓝 pMinus))
    (hyPlus : Tendsto (observedRegression c m1 m0) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (observedRegression c m1 m0) (𝓝[<] c) (𝓝 yMinus)) :
    (yPlus - yMinus) / (pPlus - pMinus) = yPlus - yMinus ∧
      (yPlus - yMinus) / (pPlus - pMinus) = m1 c - m0 c := by
  have hp1 : pPlus = 1 :=
    tendsto_nhds_unique hpPlus (tendsto_observedRegression_right _ tendsto_const_nhds)
  have hp0 : pMinus = 0 :=
    tendsto_nhds_unique hpMinus (tendsto_observedRegression_left _ tendsto_const_nhds)
  have hW := (fuzzy_wald_identification tendsto_const_nhds tendsto_const_nhds h1 h0
    hpPlus hpMinus hyPlus hyMinus (by rw [hp1, hp0]; norm_num)).2
  refine ⟨by rw [hp1, hp0]; norm_num, ?_⟩
  rw [hW]
  norm_num

/-! ### Principal strata and the complier interpretation -/

/-- A fuzzy regression discontinuity model in terms of conditional mean functions of the running
variable. For each principal stratum `t` and running variable value `x`:
* `share t x` is a version of `P(stratum = t | X = x)`;
* `mean1 t x` is a version of `E[Y(1) | stratum = t, X = x]`;
* `mean0 t x` is a version of `E[Y(0) | stratum = t, X = x]`.
No constraint is imposed by the structure itself: the algebraic identities below hold for
arbitrary real functions. The causal statements additionally require `FuzzyModel.IsValid`
(nonnegative shares summing to one at every `x`). -/
structure FuzzyModel where
  /-- Conditional share of stratum `t` given `X = x`. -/
  share : Stratum → ℝ → ℝ
  /-- Conditional mean of the treated potential outcome in stratum `t` given `X = x`. -/
  mean1 : Stratum → ℝ → ℝ
  /-- Conditional mean of the untreated potential outcome in stratum `t` given `X = x`. -/
  mean0 : Stratum → ℝ → ℝ

namespace FuzzyModel

variable (M : FuzzyModel)

/-- Conditional mean of the potential treatment under assignment `above` given `X = x`:
`E[D(above) | X = x] = ∑ₜ P(t | X = x) · D_t(above)`. -/
def armTreat (above : Bool) (x : ℝ) : ℝ :=
  Stratum.sum fun t => if t.treated above then M.share t x else 0

/-- Conditional mean of the outcome under assignment `above` given `X = x`. The definition
encodes, as modeling assumptions: the law of total expectation over principal strata (taken as
the definition of the arm mean here; `IsCondExpModel.condExp_armMean` derives it on a
probability space); consistency (a unit of stratum `t` assigned `above` takes treatment
`t.treated above` and reveals the corresponding potential outcome); and exclusion (`mean1` and
`mean0` do not depend on the assignment side). Both arms use the same shares `share t x` at a
given `x`, which says only that the strata are a property of the units at `x`; it places no
restriction on how the composition of the population changes across the cutoff (a share function
may, for instance, make everyone below `c` a never-taker and everyone above `c` an always-taker).
That restriction is the continuity of the shares at `c` in `ContinuousAtCutoff`, or, in its
minimal form, the one-sided continuity of the arm means in `ArmsContinuousAtCutoff`. -/
def armMean (above : Bool) (x : ℝ) : ℝ :=
  Stratum.sum fun t => M.share t x * (if t.treated above then M.mean1 t x else M.mean0 t x)

/-- The treatment probability `p x = P(D = 1 | X = x)` of the model. This encodes the
assignment rule: assignment is above the cutoff exactly when `c ≤ x`. On a probability space it
is a version of the conditional probability of treatment by
`IsCondExpModel.condExp_treatment_eq_treatmentProb`. -/
noncomputable def treatmentProb (c : ℝ) : ℝ → ℝ :=
  observedRegression c (M.armTreat true) (M.armTreat false)

/-- The outcome regression `x ↦ E[Y | X = x]` of the model, under the same assignment rule
(above the cutoff exactly when `c ≤ x`) and the assumptions encoded in `armMean`. On a
probability space it is a version of the conditional expectation of the observed outcome by
`IsCondExpModel.condExp_outcome_eq_outcomeReg`. -/
noncomputable def outcomeReg (c : ℝ) : ℝ → ℝ :=
  observedRegression c (M.armMean true) (M.armMean false)

/-- The difference of the arm treatment means is the complier share minus the defier share. -/
theorem armTreat_sub (x : ℝ) :
    M.armTreat true x - M.armTreat false x = M.share .complier x - M.share .defier x := by
  simp only [armTreat, Stratum.sum, Stratum.treated]
  simp

/-- The difference of the arm outcome means is the complier share times the complier effect
minus the defier share times the defier effect. -/
theorem armMean_sub (x : ℝ) :
    M.armMean true x - M.armMean false x =
      M.share .complier x * (M.mean1 .complier x - M.mean0 .complier x) -
        M.share .defier x * (M.mean1 .defier x - M.mean0 .defier x) := by
  simp only [armMean, Stratum.sum, Stratum.treated]
  simp
  ring


/-- Validity of a fuzzy model as a probability model: at every value `x` of the running
variable, the stratum shares are nonnegative and sum to one. The algebraic identities of this
file do not need it; the causal statements (positivity of the complier share, the reduction to
the sharp design at the cutoff) do. -/
structure IsValid (M : FuzzyModel) : Prop where
  /-- Every stratum share is nonnegative. -/
  share_nonneg : ∀ t x, 0 ≤ M.share t x
  /-- The stratum shares sum to one at every value of the running variable. -/
  share_sum : ∀ x, Stratum.sum (fun t => M.share t x) = 1

/-- The average treatment effect at `x`, `E[Y(1) - Y(0) | X = x]`, written as the share-weighted
sum over strata of the stratum effects `mean1 t x - mean0 t x`. It involves the never-revealed
means `mean1 neverTaker` and `mean0 alwaysTaker`. -/
def averageEffect (x : ℝ) : ℝ :=
  Stratum.sum fun t => M.share t x * (M.mean1 t x - M.mean0 t x)

/-- The one-sided continuity hypotheses that the complier argument uses: the treatment and
outcome means of the arm assigned above the cutoff are right-continuous at `c`, and those of the
arm assigned below the cutoff are left-continuous at `c`. -/
structure ArmsContinuousAtCutoff (M : FuzzyModel) (c : ℝ) : Prop where
  /-- `x ↦ E[D(above) | X = x]` is right-continuous at `c`. -/
  treat_right : Tendsto (M.armTreat true) (𝓝[>] c) (𝓝 (M.armTreat true c))
  /-- `x ↦ E[D(below) | X = x]` is left-continuous at `c`. -/
  treat_left : Tendsto (M.armTreat false) (𝓝[<] c) (𝓝 (M.armTreat false c))
  /-- The outcome mean of the arm assigned above the cutoff is right-continuous at `c`. -/
  mean_right : Tendsto (M.armMean true) (𝓝[>] c) (𝓝 (M.armMean true c))
  /-- The outcome mean of the arm assigned below the cutoff is left-continuous at `c`. -/
  mean_left : Tendsto (M.armMean false) (𝓝[<] c) (𝓝 (M.armMean false c))

variable {M}

/-- Two-sided continuity at `c` of all four arm means gives `ArmsContinuousAtCutoff`. -/
theorem armsContinuousAtCutoff_of_continuousAt {c : ℝ}
    (hT : ∀ above, ContinuousAt (M.armTreat above) c)
    (hM : ∀ above, ContinuousAt (M.armMean above) c) : M.ArmsContinuousAtCutoff c where
  treat_right := (hT true).tendsto.mono_left nhdsWithin_le_nhds
  treat_left := (hT false).tendsto.mono_left nhdsWithin_le_nhds
  mean_right := (hM true).tendsto.mono_left nhdsWithin_le_nhds
  mean_left := (hM false).tendsto.mono_left nhdsWithin_le_nhds

variable (M) in
/-- A sufficient condition for `ArmsContinuousAtCutoff`: every stratum share is continuous at
`c`, and so is every stratum-specific potential outcome mean that some assignment reveals
(`mean1 t` when stratum `t` is treated under some assignment, `mean0 t` when it is untreated
under some assignment). The never-revealed means, `E[Y(1) | never-taker, X = x]` and
`E[Y(0) | always-taker, X = x]`, are unrestricted. This continuity of the shares is the
restriction on how the composition of the population may change across the cutoff. -/
def ContinuousAtCutoff (c : ℝ) : Prop :=
  ∀ t, ContinuousAt (M.share t) c ∧
    ((∃ b, t.treated b = true) → ContinuousAt (M.mean1 t) c) ∧
    ((∃ b, t.treated b = false) → ContinuousAt (M.mean0 t) c)

theorem ContinuousAtCutoff.armTreat {c : ℝ} (h : M.ContinuousAtCutoff c) (above : Bool) :
    ContinuousAt (M.armTreat above) c := by
  have key : ∀ t : Stratum,
      ContinuousAt (fun x => if t.treated above then M.share t x else 0) c := by
    intro t
    split_ifs
    · exact (h t).1
    · exact continuousAt_const
  exact (((key .alwaysTaker).add (key .complier)).add (key .neverTaker)).add (key .defier)

theorem ContinuousAtCutoff.armMean {c : ℝ} (h : M.ContinuousAtCutoff c) (above : Bool) :
    ContinuousAt (M.armMean above) c := by
  have key : ∀ t : Stratum, ContinuousAt
      (fun x => M.share t x * (if t.treated above then M.mean1 t x else M.mean0 t x)) c := by
    intro t
    split_ifs with ht
    · exact (h t).1.mul ((h t).2.1 ⟨above, ht⟩)
    · exact (h t).1.mul ((h t).2.2 ⟨above, Bool.eq_false_iff.mpr ht⟩)
  exact (((key .alwaysTaker).add (key .complier)).add (key .neverTaker)).add (key .defier)

/-- `ContinuousAtCutoff` implies the four one-sided hypotheses `ArmsContinuousAtCutoff`. -/
theorem ContinuousAtCutoff.arms {c : ℝ} (h : M.ContinuousAtCutoff c) :
    M.ArmsContinuousAtCutoff c :=
  armsContinuousAtCutoff_of_continuousAt h.armTreat h.armMean

variable (M) in
/-- The continuity condition of `ContinuousAtCutoff` imposed on every stratum except the
defiers: the defier share and the defier means are unrestricted. -/
def ContinuousAtCutoffExceptDefiers (c : ℝ) : Prop :=
  ∀ t, t ≠ .defier → ContinuousAt (M.share t) c ∧
    ((∃ b, t.treated b = true) → ContinuousAt (M.mean1 t) c) ∧
    ((∃ b, t.treated b = false) → ContinuousAt (M.mean0 t) c)

/-- If the defier share vanishes in a neighborhood of `c` and every other stratum satisfies the
continuity condition of `ContinuousAtCutoff`, the four one-sided hypotheses
`ArmsContinuousAtCutoff` hold, whatever the defier means are. -/
theorem ContinuousAtCutoffExceptDefiers.arms {c : ℝ} (h : M.ContinuousAtCutoffExceptDefiers c)
    (hdef : M.share .defier =ᶠ[𝓝 c] 0) : M.ArmsContinuousAtCutoff c := by
  refine armsContinuousAtCutoff_of_continuousAt (fun above => ?_) (fun above => ?_)
  · have key : ∀ t : Stratum,
        ContinuousAt (fun x => if t.treated above then M.share t x else 0) c := by
      intro t
      by_cases ht : t = .defier
      · subst ht
        exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) c).congr
          (hdef.mono fun x hx => by simp [hx])
      · split_ifs
        · exact (h t ht).1
        · exact continuousAt_const
    exact (((key .alwaysTaker).add (key .complier)).add (key .neverTaker)).add (key .defier)
  · have key : ∀ t : Stratum, ContinuousAt
        (fun x => M.share t x * (if t.treated above then M.mean1 t x else M.mean0 t x)) c := by
      intro t
      by_cases ht : t = .defier
      · subst ht
        exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) c).congr
          (hdef.mono fun x hx => by simp [hx])
      · split_ifs with hb
        · exact (h t ht).1.mul ((h t ht).2.1 ⟨above, hb⟩)
        · exact (h t ht).1.mul ((h t ht).2.2 ⟨above, Bool.eq_false_iff.mpr hb⟩)
    exact (((key .alwaysTaker).add (key .complier)).add (key .neverTaker)).add (key .defier)

/-- **The complier ratio, algebraic form.** For any fuzzy model (no sign or normalization
constraint on the shares) satisfying the one-sided continuity hypotheses
`ArmsContinuousAtCutoff` at `c`, with defier share `0` at `c` and a jump `pPlus ≠ pMinus` in the
observed treatment probability, the treatment jump equals the complier share at `c` and the
local Wald ratio equals `mean1 complier c - mean0 complier c`. -/
theorem fuzzy_wald_complier_of_arms {c : ℝ} (hcont : M.ArmsContinuousAtCutoff c)
    (hmono : M.share .defier c = 0) {pPlus pMinus yPlus yMinus : ℝ}
    (hpPlus : Tendsto (M.treatmentProb c) (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto (M.treatmentProb c) (𝓝[<] c) (𝓝 pMinus))
    (hyPlus : Tendsto (M.outcomeReg c) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (M.outcomeReg c) (𝓝[<] c) (𝓝 yMinus))
    (hjump : pPlus ≠ pMinus) :
    pPlus - pMinus = M.share .complier c ∧
      (yPlus - yMinus) / (pPlus - pMinus) = M.mean1 .complier c - M.mean0 .complier c := by
  have hp := sharp_rd_identification hcont.treat_right hcont.treat_left hpPlus hpMinus
  rw [armTreat_sub, hmono, sub_zero] at hp
  obtain ⟨-, hW⟩ := fuzzy_wald_identification hcont.treat_right hcont.treat_left
    hcont.mean_right hcont.mean_left hpPlus hpMinus hyPlus hyMinus hjump
  have hC : M.share .complier c ≠ 0 := by
    rw [← hp]
    exact sub_ne_zero.mpr hjump
  refine ⟨hp, ?_⟩
  rw [hW, armTreat_sub, armMean_sub, hmono]
  field_simp
  ring

/-- In a valid model, a nonzero first stage equal to the complier share makes that share
positive. -/
theorem IsValid.share_complier_pos (hM : M.IsValid) {c pPlus pMinus : ℝ}
    (hfirst : pPlus - pMinus = M.share .complier c) (hjump : pPlus ≠ pMinus) :
    0 < M.share .complier c :=
  lt_of_le_of_ne (hM.share_nonneg _ _) (by rw [← hfirst]; exact (sub_ne_zero.mpr hjump).symm)

/-- **Fuzzy regression discontinuity: the complier interpretation, minimal continuity** (Hahn,
Todd and Van der Klaauw 2001; Imbens and Lemieux 2008). Assume
* the model is valid: nonnegative shares summing to one (`IsValid`);
* the one-sided continuity hypotheses `ArmsContinuousAtCutoff` at the cutoff `c`;
* local monotonicity at the cutoff: `share defier c = 0`;
* a jump in the treatment probability: `pPlus ≠ pMinus` for the right and left limits of the
  observed treatment probability at `c`.
Then the treatment probability increases across the cutoff (`pMinus < pPlus`), the complier
share at `c` is positive and equals the treatment jump, and the local Wald ratio equals
`mean1 complier c - mean0 complier c`, a version of `E[Y(1) - Y(0) | complier, X = c]`. This is a
conditional moment formulation of the complier argument: the link of the model to a probability
space is `IsCondExpModel`. -/
theorem fuzzy_rd_complier_identification_of_arms {c : ℝ} (hM : M.IsValid)
    (hcont : M.ArmsContinuousAtCutoff c) (hmono : M.share .defier c = 0)
    {pPlus pMinus yPlus yMinus : ℝ}
    (hpPlus : Tendsto (M.treatmentProb c) (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto (M.treatmentProb c) (𝓝[<] c) (𝓝 pMinus))
    (hyPlus : Tendsto (M.outcomeReg c) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (M.outcomeReg c) (𝓝[<] c) (𝓝 yMinus))
    (hjump : pPlus ≠ pMinus) :
    pMinus < pPlus ∧ 0 < M.share .complier c ∧ pPlus - pMinus = M.share .complier c ∧
      (yPlus - yMinus) / (pPlus - pMinus) = M.mean1 .complier c - M.mean0 .complier c := by
  obtain ⟨hp, hW⟩ := fuzzy_wald_complier_of_arms hcont hmono hpPlus hpMinus hyPlus hyMinus hjump
  have hpos := hM.share_complier_pos hp hjump
  exact ⟨sub_pos.mp (hp ▸ hpos), hpos, hp, hW⟩

/-- **Fuzzy regression discontinuity: the complier interpretation** under the sufficient
condition `ContinuousAtCutoff` (continuity at `c` of every stratum share and every revealed
stratum mean), for a valid model with `share defier c = 0` and a jump `pPlus ≠ pMinus`. The
conclusions are those of `fuzzy_rd_complier_identification_of_arms`. -/
theorem fuzzy_rd_complier_identification {c : ℝ} (hM : M.IsValid)
    (hcont : M.ContinuousAtCutoff c) (hmono : M.share .defier c = 0)
    {pPlus pMinus yPlus yMinus : ℝ}
    (hpPlus : Tendsto (M.treatmentProb c) (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto (M.treatmentProb c) (𝓝[<] c) (𝓝 pMinus))
    (hyPlus : Tendsto (M.outcomeReg c) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (M.outcomeReg c) (𝓝[<] c) (𝓝 yMinus))
    (hjump : pPlus ≠ pMinus) :
    pMinus < pPlus ∧ 0 < M.share .complier c ∧ pPlus - pMinus = M.share .complier c ∧
      (yPlus - yMinus) / (pPlus - pMinus) = M.mean1 .complier c - M.mean0 .complier c :=
  fuzzy_rd_complier_identification_of_arms hM hcont.arms hmono hpPlus hpMinus hyPlus hyMinus
    hjump

/-- **Fuzzy regression discontinuity with no defiers near the cutoff.** For a valid model in
which the defier share vanishes in a neighborhood of `c` and every other stratum satisfies the
continuity condition of `ContinuousAtCutoff` (the defier means are unrestricted), a jump
`pPlus ≠ pMinus` gives the conclusions of `fuzzy_rd_complier_identification_of_arms`. -/
theorem fuzzy_rd_complier_identification_of_noDefiersNear {c : ℝ} (hM : M.IsValid)
    (hcont : M.ContinuousAtCutoffExceptDefiers c) (hdef : M.share .defier =ᶠ[𝓝 c] 0)
    {pPlus pMinus yPlus yMinus : ℝ}
    (hpPlus : Tendsto (M.treatmentProb c) (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto (M.treatmentProb c) (𝓝[<] c) (𝓝 pMinus))
    (hyPlus : Tendsto (M.outcomeReg c) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (M.outcomeReg c) (𝓝[<] c) (𝓝 yMinus))
    (hjump : pPlus ≠ pMinus) :
    pMinus < pPlus ∧ 0 < M.share .complier c ∧ pPlus - pMinus = M.share .complier c ∧
      (yPlus - yMinus) / (pPlus - pMinus) = M.mean1 .complier c - M.mean0 .complier c :=
  fuzzy_rd_complier_identification_of_arms hM (hcont.arms hdef) hdef.eq_of_nhds hpPlus hpMinus
    hyPlus hyMinus hjump

/-- **A fuzzy design that is sharp at the cutoff.** For a valid model satisfying the one-sided
continuity hypotheses `ArmsContinuousAtCutoff` at `c`, if the observed treatment probability has
right limit `1` and left limit `0` at `c`, then the complier share at `c` is one, and the outcome
jump equals both the average treatment effect at `c` and the complier effect at `c`. No
assumption is made on the shares away from `c`, so compliance may vary there; no monotonicity
assumption is needed, since the left limit `0` forces the defier share at `c` to vanish. -/
theorem fuzzy_rd_cutoff_sharp {c : ℝ} (hM : M.IsValid) (hcont : M.ArmsContinuousAtCutoff c)
    {yPlus yMinus : ℝ} (hpPlus : Tendsto (M.treatmentProb c) (𝓝[>] c) (𝓝 1))
    (hpMinus : Tendsto (M.treatmentProb c) (𝓝[<] c) (𝓝 0))
    (hyPlus : Tendsto (M.outcomeReg c) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (M.outcomeReg c) (𝓝[<] c) (𝓝 yMinus)) :
    M.share .complier c = 1 ∧ yPlus - yMinus = M.averageEffect c ∧
      yPlus - yMinus = M.mean1 .complier c - M.mean0 .complier c := by
  have h1 : M.armTreat true c = 1 :=
    tendsto_nhds_unique (tendsto_observedRegression_right _ hcont.treat_right) hpPlus
  have h0 : M.armTreat false c = 0 :=
    tendsto_nhds_unique (tendsto_observedRegression_left _ hcont.treat_left) hpMinus
  have hy := sharp_rd_identification hcont.mean_right hcont.mean_left hyPlus hyMinus
  simp [armTreat, Stratum.sum, Stratum.treated] at h1 h0
  have hs := hM.share_sum c
  simp only [Stratum.sum] at hs
  have nA := hM.share_nonneg .alwaysTaker c
  have nC := hM.share_nonneg .complier c
  have nN := hM.share_nonneg .neverTaker c
  have nD := hM.share_nonneg .defier c
  have hA : M.share .alwaysTaker c = 0 := by linarith
  have hD : M.share .defier c = 0 := by linarith
  have hC : M.share .complier c = 1 := by linarith
  have hN : M.share .neverTaker c = 0 := by linarith
  rw [armMean_sub, hC, hD] at hy
  refine ⟨hC, ?_, ?_⟩
  · rw [hy, averageEffect]
    simp only [Stratum.sum, hA, hC, hN, hD]
    ring
  · rw [hy]
    ring

/-! ### The sharp design inside the fuzzy model -/

/-- The sharp design as a fuzzy model: every unit is a complier, and the potential outcome means
are `m1` and `m0` in every stratum. -/
def sharp (m1 m0 : ℝ → ℝ) : FuzzyModel where
  share t _ := if t = .complier then 1 else 0
  mean1 _ := m1
  mean0 _ := m0

/-- The all-complier model is valid. -/
theorem sharp_isValid (m1 m0 : ℝ → ℝ) : (sharp m1 m0).IsValid where
  share_nonneg t x := by
    simp only [sharp]
    split_ifs <;> norm_num
  share_sum x := by simp [sharp, Stratum.sum]

/-- In the all-complier model the treatment mean of the arm assigned above the cutoff is `1`. -/
theorem sharp_armTreat_true (m1 m0 : ℝ → ℝ) : (sharp m1 m0).armTreat true = fun _ => 1 := by
  funext x
  simp [armTreat, sharp, Stratum.sum, Stratum.treated]

/-- In the all-complier model the treatment mean of the arm assigned below the cutoff is `0`. -/
theorem sharp_armTreat_false (m1 m0 : ℝ → ℝ) : (sharp m1 m0).armTreat false = fun _ => 0 := by
  funext x
  simp [armTreat, sharp, Stratum.sum, Stratum.treated]

/-- In the all-complier model the outcome mean of the arm assigned above the cutoff is `m1`. -/
theorem sharp_armMean_true (m1 m0 : ℝ → ℝ) : (sharp m1 m0).armMean true = m1 := by
  funext x
  simp [armMean, sharp, Stratum.sum, Stratum.treated]

/-- In the all-complier model the outcome mean of the arm assigned below the cutoff is `m0`. -/
theorem sharp_armMean_false (m1 m0 : ℝ → ℝ) : (sharp m1 m0).armMean false = m0 := by
  funext x
  simp [armMean, sharp, Stratum.sum, Stratum.treated]

/-- In the all-complier model the observed outcome regression is the sharp observed
regression. -/
theorem sharp_outcomeReg (c : ℝ) (m1 m0 : ℝ → ℝ) :
    (sharp m1 m0).outcomeReg c = observedRegression c m1 m0 := by
  funext x
  simp [outcomeReg, observedRegression, armMean, sharp, Stratum.sum, Stratum.treated]

/-- In the all-complier model the treatment probability is the sharp rule `1{x ≥ c}`. -/
theorem sharp_treatmentProb (c : ℝ) (m1 m0 : ℝ → ℝ) :
    (sharp m1 m0).treatmentProb c = observedRegression c (fun _ => 1) (fun _ => 0) := by
  funext x
  simp [treatmentProb, observedRegression, armTreat, sharp, Stratum.sum, Stratum.treated]

/-- The complier theorem `fuzzy_rd_complier_identification_of_arms`, applied to the valid
all-complier model `sharp m1 m0` under the hypotheses of `sharp_rd_identification` (`m1`
right-continuous and `m0` left-continuous at `c`), gives the sharp identification result: the
jump of the sharp observed regression equals `m1 c - m0 c`. -/
theorem sharp_of_complier_identification {c : ℝ} {m1 m0 : ℝ → ℝ}
    (h1 : Tendsto m1 (𝓝[>] c) (𝓝 (m1 c))) (h0 : Tendsto m0 (𝓝[<] c) (𝓝 (m0 c)))
    {yPlus yMinus : ℝ}
    (hyPlus : Tendsto (observedRegression c m1 m0) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (observedRegression c m1 m0) (𝓝[<] c) (𝓝 yMinus)) :
    yPlus - yMinus = m1 c - m0 c := by
  have hcont : (sharp m1 m0).ArmsContinuousAtCutoff c :=
    { treat_right := by rw [sharp_armTreat_true]; exact tendsto_const_nhds
      treat_left := by rw [sharp_armTreat_false]; exact tendsto_const_nhds
      mean_right := by rw [sharp_armMean_true]; exact h1
      mean_left := by rw [sharp_armMean_false]; exact h0 }
  have hpPlus : Tendsto ((sharp m1 m0).treatmentProb c) (𝓝[>] c) (𝓝 1) := by
    rw [sharp_treatmentProb]
    exact tendsto_observedRegression_right _ tendsto_const_nhds
  have hpMinus : Tendsto ((sharp m1 m0).treatmentProb c) (𝓝[<] c) (𝓝 0) := by
    rw [sharp_treatmentProb]
    exact tendsto_observedRegression_left _ tendsto_const_nhds
  rw [← sharp_outcomeReg] at hyPlus hyMinus
  have h := (fuzzy_rd_complier_identification_of_arms (sharp_isValid m1 m0) hcont
    (by simp [sharp]) hpPlus hpMinus hyPlus hyMinus one_ne_zero).2.2.2
  simpa [sharp] using h

/-! ### Measure-theoretic bridge and law-level identification -/

open MeasureTheory

/-- The conditional expectation of a sum over the four strata is the sum of the conditional
expectations. -/
theorem condExp_stratumSum {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Stratum → Ω → ℝ} (hf : ∀ t, Integrable (f t) μ) (hg : ∀ t, μ[f t | m] =ᵐ[μ] g t) :
    μ[fun ω => Stratum.sum fun t => f t ω | m] =ᵐ[μ] fun ω => Stratum.sum fun t => g t ω := by
  have heq : (fun ω => Stratum.sum fun t => f t ω) =
      f .alwaysTaker + f .complier + f .neverTaker + f .defier := rfl
  rw [heq]
  filter_upwards [condExp_add (((hf _).add (hf _)).add (hf _)) (hf _) m,
    condExp_add ((hf _).add (hf _)) (hf _) m, condExp_add (hf _) (hf _) m, hg .alwaysTaker,
    hg .complier, hg .neverTaker, hg .defier] with ω h1 h2 h3 ga gc gn gd
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.add_apply, ga, gc, gn, gd]
  rfl

/-- A fuzzy model `M` describes, in product form, the conditional law given the running variable
`X` of the stratum variable `T` and the potential outcomes `Y1`, `Y0` on a measure space:
* for every stratum `t`, `M.share t ∘ X` is a version of `E[1{T = t} | σ(X)]`;
* for every stratum `t` and assignment `above`, writing `Y_t` for the potential outcome that `t`
  reveals under `above` (`Y1` if `t.treated above`, else `Y0`), the function
  `ω ↦ M.share t (X ω) * m (X ω)`, with `m` the matching stratum mean, is a version of
  `E[1{T = t} Y_t | σ(X)]`.
The product form avoids conditioning on strata of probability zero. -/
structure IsCondExpModel (M : FuzzyModel) {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (X : Ω → ℝ) (T : Ω → Stratum) (Y1 Y0 : Ω → ℝ) : Prop where
  /-- `M.share t ∘ X` is a version of `E[1{T = t} | σ(X)]`. -/
  share_condExp : ∀ t, μ[(T ⁻¹' {t}).indicator (1 : Ω → ℝ) | MeasurableSpace.comap X inferInstance]
    =ᵐ[μ] M.share t ∘ X
  /-- The share-weighted stratum mean of the revealed outcome is a version of
  `E[1{T = t} Y_t | σ(X)]`. -/
  mean_condExp : ∀ t above, μ[(T ⁻¹' {t}).indicator (if t.treated above then Y1 else Y0) |
      MeasurableSpace.comap X inferInstance]
    =ᵐ[μ] fun ω => M.share t (X ω) * (if t.treated above then M.mean1 t (X ω) else M.mean0 t (X ω))

section Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {T : Ω → Stratum}
  {Y1 Y0 : Ω → ℝ}

/-- Arm treatment: the indicator that a unit takes treatment under assignment `above` is
integrable, and `M.armTreat above ∘ X` is a version of its conditional expectation given `X`. -/
theorem IsCondExpModel.condExp_armTreat [IsFiniteMeasure μ] (hM : M.IsCondExpModel μ X T Y1 Y0)
    (hT : ∀ t, MeasurableSet (T ⁻¹' {t})) (above : Bool) :
    Integrable (fun ω => if (T ω).treated above then (1 : ℝ) else 0) μ ∧
      μ[fun ω => if (T ω).treated above then (1 : ℝ) else 0 |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ] M.armTreat above ∘ X := by
  set f : Stratum → Ω → ℝ := fun t =>
    if t.treated above then (T ⁻¹' {t}).indicator (1 : Ω → ℝ) else 0
  have heq : (fun ω => if (T ω).treated above then (1 : ℝ) else 0) =
      fun ω => Stratum.sum fun t => f t ω := by
    funext ω
    cases h : T ω <;> cases above <;> simp [f, Stratum.sum, Stratum.treated, Set.indicator, h]
  have hf : ∀ t, Integrable (f t) μ := fun t => by
    simp only [f]
    split_ifs
    · exact (integrable_const 1).indicator (hT t)
    · exact integrable_zero _ _ _
  rw [heq]
  refine ⟨(((hf _).add (hf _)).add (hf _)).add (hf _), ?_⟩
  refine condExp_stratumSum (g := fun t ω => if t.treated above then M.share t (X ω) else 0) hf
    fun t => ?_
  simp only [f]
  cases t.treated above
  · simp only [Bool.false_eq_true, ↓reduceIte, condExp_zero]
    rfl
  · simp only [↓reduceIte]
    exact hM.share_condExp t

/-- Arm outcome: the potential outcome revealed under assignment `above` is integrable, and
`M.armMean above ∘ X` is a version of its conditional expectation given `X`. -/
theorem IsCondExpModel.condExp_armMean (hM : M.IsCondExpModel μ X T Y1 Y0)
    (hT : ∀ t, MeasurableSet (T ⁻¹' {t})) (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ)
    (above : Bool) :
    Integrable (fun ω => if (T ω).treated above then Y1 ω else Y0 ω) μ ∧
      μ[fun ω => if (T ω).treated above then Y1 ω else Y0 ω |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ] M.armMean above ∘ X := by
  set f : Stratum → Ω → ℝ := fun t =>
    (T ⁻¹' {t}).indicator (if t.treated above then Y1 else Y0)
  have heq : (fun ω => if (T ω).treated above then Y1 ω else Y0 ω) =
      fun ω => Stratum.sum fun t => f t ω := by
    funext ω
    cases h : T ω <;> cases above <;> simp [f, Stratum.sum, Stratum.treated, h]
  have hf : ∀ t, Integrable (f t) μ := fun t => by
    simp only [f]
    split_ifs
    · exact hY1.indicator (hT t)
    · exact hY0.indicator (hT t)
  rw [heq]
  exact ⟨(((hf _).add (hf _)).add (hf _)).add (hf _),
    condExp_stratumSum (g := fun t ω => M.share t (X ω) *
      (if t.treated above then M.mean1 t (X ω) else M.mean0 t (X ω))) hf
      fun t => hM.mean_condExp t above⟩

/-- **Bridge for the treatment.** On a probability space with measurable running variable `X`
and a stratum variable `T` with measurable level sets, let the received treatment be
`D = T.treated (decide (c ≤ X))` (assignment above the cutoff exactly when `c ≤ X`). If `M`
describes the conditional law of `T` given `X` (`IsCondExpModel`), then `M.treatmentProb c ∘ X`
is a version of `E[1{D} | σ(X)]`. -/
theorem IsCondExpModel.condExp_treatment_eq_treatmentProb [IsProbabilityMeasure μ]
    (hM : M.IsCondExpModel μ X T Y1 Y0) (hX : Measurable X)
    (hT : ∀ t, MeasurableSet (T ⁻¹' {t})) (c : ℝ) :
    μ[fun ω => if (T ω).treated (decide (c ≤ X ω)) then (1 : ℝ) else 0 |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ] M.treatmentProb c ∘ X := by
  have heq : (fun ω => if (T ω).treated (decide (c ≤ X ω)) then (1 : ℝ) else 0) =
      fun ω => if c ≤ X ω then (if (T ω).treated true then (1 : ℝ) else 0)
        else (if (T ω).treated false then (1 : ℝ) else 0) := by
    funext ω
    by_cases h : c ≤ X ω <;> simp [h]
  rw [heq]
  obtain ⟨i1, e1⟩ := hM.condExp_armTreat hT true
  obtain ⟨i0, e0⟩ := hM.condExp_armTreat hT false
  exact condExp_observed_eq_observedRegression hX i1 i0 c e1 e0

/-- **Bridge for the outcome.** Under the hypotheses of
`IsCondExpModel.condExp_treatment_eq_treatmentProb`, with integrable potential outcomes and
observed outcome `Y = if D then Y1 else Y0` (consistency), `M.outcomeReg c ∘ X` is a version of
`E[Y | σ(X)]`. -/
theorem IsCondExpModel.condExp_outcome_eq_outcomeReg [IsProbabilityMeasure μ]
    (hM : M.IsCondExpModel μ X T Y1 Y0) (hX : Measurable X)
    (hT : ∀ t, MeasurableSet (T ⁻¹' {t})) (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ)
    (c : ℝ) :
    μ[fun ω => if (T ω).treated (decide (c ≤ X ω)) then Y1 ω else Y0 ω |
      MeasurableSpace.comap X inferInstance] =ᵐ[μ] M.outcomeReg c ∘ X := by
  have heq : (fun ω => if (T ω).treated (decide (c ≤ X ω)) then Y1 ω else Y0 ω) =
      fun ω => if c ≤ X ω then (if (T ω).treated true then Y1 ω else Y0 ω)
        else (if (T ω).treated false then Y1 ω else Y0 ω) := by
    funext ω
    by_cases h : c ≤ X ω <;> simp [h]
  rw [heq]
  obtain ⟨i1, e1⟩ := hM.condExp_armMean hT hY1 hY0 true
  obtain ⟨i0, e0⟩ := hM.condExp_armMean hT hY1 hY0 false
  exact condExp_observed_eq_observedRegression hX i1 i0 c e1 e0

/-- **Fuzzy regression discontinuity: identification of the complier effect from the observed
law.** On a probability space with measurable running variable `X`, a stratum variable `T` with
measurable level sets, integrable potential outcomes `Y1`, `Y0`, received treatment
`D = T.treated (decide (c ≤ X))` and observed outcome `Y = if D then Y1 else Y0`, assume:
* `M` describes the conditional law of `(T, Y1, Y0)` given `X` (`IsCondExpModel`) and is valid
  (`IsValid`);
* the one-sided continuity hypotheses `ArmsContinuousAtCutoff` and `share defier c = 0`;
* the running variable has mass on both sides arbitrarily close to `c` (`RightSupport`,
  `LeftSupport`).
Let `p` and `r` be any functions such that `p ∘ X` and `r ∘ X` are versions of `E[1{D} | σ(X)]`
and `E[Y | σ(X)]`, with right limits `pPlus`, `yPlus` and left limits `pMinus`, `yMinus` at `c`,
and assume `pPlus ≠ pMinus`. Then `pMinus < pPlus`, the complier share at `c` is positive and
equals `pPlus - pMinus`, and `(yPlus - yMinus) / (pPlus - pMinus)` equals the complier effect
`mean1 complier c - mean0 complier c`. The left sides are functionals of the joint law of
`(X, D, Y)`. -/
theorem fuzzy_rd_complier_identification_of_condExp [IsProbabilityMeasure μ] {c : ℝ}
    (hX : Measurable X) (hT : ∀ t, MeasurableSet (T ⁻¹' {t})) (hY1 : Integrable Y1 μ)
    (hY0 : Integrable Y0 μ) (hmodel : M.IsCondExpModel μ X T Y1 Y0) (hM : M.IsValid)
    (hcont : M.ArmsContinuousAtCutoff c) (hmono : M.share .defier c = 0)
    (hright : RightSupport μ X c) (hleft : LeftSupport μ X c) {p r : ℝ → ℝ}
    (hp : p ∘ X =ᵐ[μ] μ[fun ω => if (T ω).treated (decide (c ≤ X ω)) then (1 : ℝ) else 0 |
      MeasurableSpace.comap X inferInstance])
    (hr : r ∘ X =ᵐ[μ] μ[fun ω => if (T ω).treated (decide (c ≤ X ω)) then Y1 ω else Y0 ω |
      MeasurableSpace.comap X inferInstance])
    {pPlus pMinus yPlus yMinus : ℝ} (hpPlus : Tendsto p (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto p (𝓝[<] c) (𝓝 pMinus)) (hyPlus : Tendsto r (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto r (𝓝[<] c) (𝓝 yMinus)) (hjump : pPlus ≠ pMinus) :
    pMinus < pPlus ∧ 0 < M.share .complier c ∧ pPlus - pMinus = M.share .complier c ∧
      (yPlus - yMinus) / (pPlus - pMinus) = M.mean1 .complier c - M.mean0 .complier c := by
  have hpae := hp.trans (hmodel.condExp_treatment_eq_treatmentProb hX hT c)
  have hrae := hr.trans (hmodel.condExp_outcome_eq_outcomeReg hX hT hY1 hY0 c)
  have tpR := tendsto_observedRegression_right (M.armTreat false) hcont.treat_right
  have tpL := tendsto_observedRegression_left (M.armTreat true) hcont.treat_left
  have tyR := tendsto_observedRegression_right (M.armMean false) hcont.mean_right
  have tyL := tendsto_observedRegression_left (M.armMean true) hcont.mean_left
  obtain rfl := tendsto_right_unique_of_ae_eq hpae hright hpPlus tpR
  obtain rfl := tendsto_left_unique_of_ae_eq hpae hleft hpMinus tpL
  obtain rfl := tendsto_right_unique_of_ae_eq hrae hright hyPlus tyR
  obtain rfl := tendsto_left_unique_of_ae_eq hrae hleft hyMinus tyL
  exact fuzzy_rd_complier_identification_of_arms hM hcont hmono tpR tpL tyR tyL hjump

end Bridge

end FuzzyModel

end RD

end CausalInference
