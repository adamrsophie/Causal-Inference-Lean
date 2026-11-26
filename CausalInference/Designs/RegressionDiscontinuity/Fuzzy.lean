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
  the observed treatment probability `p x = P(D = 1 | X = x)` and observed regression
  `x ↦ E[Y | X = x]`.

## Main results

* `CausalInference.RD.fuzzy_wald_identification`: for any four conditional mean functions
  `q1 q0 a1 a0` (treatment and outcome means under assignment above and below the cutoff), with
  one-sided continuity at `c` and a nonzero jump in treatment probability, the ratio of the jump
  in the observed outcome regression to the jump in the observed treatment probability equals
  `(a1 c - a0 c) / (q1 c - q0 c)`.
* `CausalInference.RD.fuzzy_wald_sharp`: with `q1 = 1` and `q0 = 0` the ratio reduces to the
  sharp identification result.
* `CausalInference.RD.FuzzyModel.fuzzy_rd_complier_identification`: under local monotonicity
  (no defiers at the cutoff), continuity at `c` of the stratum shares and stratum means, and a
  nonzero jump in treatment probability, the Wald ratio equals the average effect for compliers
  at the cutoff.
* `CausalInference.RD.FuzzyModel.sharp_outcomeReg` and
  `CausalInference.RD.FuzzyModel.sharp_treatmentProb`: the sharp design is the fuzzy model in
  which everyone is a complier; `CausalInference.RD.FuzzyModel.sharp_of_complier_identification`
  recovers the sharp result from the complier theorem.

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
No constraint (nonnegativity, summing to one) is imposed: the identification results below do not
need one. -/
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
the definition of the arm mean, not derived from a probability space); consistency (a unit of
stratum `t` assigned `above` takes treatment `t.treated above` and reveals the corresponding
potential outcome); exclusion (`mean1` and `mean0` do not depend on the assignment side); and no
sorting at the cutoff (the same shares `share t x` apply on both sides). -/
def armMean (above : Bool) (x : ℝ) : ℝ :=
  Stratum.sum fun t => M.share t x * (if t.treated above then M.mean1 t x else M.mean0 t x)

/-- The observed treatment probability `p x = P(D = 1 | X = x)`. This encodes the assignment
rule: assignment is above the cutoff exactly when `c ≤ x`. -/
noncomputable def treatmentProb (c : ℝ) : ℝ → ℝ :=
  observedRegression c (M.armTreat true) (M.armTreat false)

/-- The observed outcome regression `x ↦ E[Y | X = x]`, under the same assignment rule
(above the cutoff exactly when `c ≤ x`) and the assumptions encoded in `armMean`. -/
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

/-- The local continuity assumption of the fuzzy design: every stratum share is continuous at
`c`, and so is every stratum-specific potential outcome mean that some assignment reveals
(`mean1 t` when stratum `t` is treated under some assignment, `mean0 t` when it is untreated
under some assignment). The never-revealed means, `E[Y(1) | never-taker, X = x]` and
`E[Y(0) | always-taker, X = x]`, are unrestricted. -/
def ContinuousAtCutoff (c : ℝ) : Prop :=
  ∀ t, ContinuousAt (M.share t) c ∧
    ((∃ b, t.treated b = true) → ContinuousAt (M.mean1 t) c) ∧
    ((∃ b, t.treated b = false) → ContinuousAt (M.mean0 t) c)

variable {M}

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

/-- **Fuzzy regression discontinuity: the complier interpretation** (Hahn, Todd and
Van der Klaauw 2001; Imbens and Lemieux 2008). In a fuzzy model, assume
* local continuity: every stratum share and every revealed stratum-specific potential outcome
  mean is continuous at the cutoff `c` (`ContinuousAtCutoff`);
* local monotonicity: the defier share vanishes at the cutoff, `share defier c = 0` (implied by
  the usual "no defiers in a neighborhood of `c`");
* a jump in the treatment probability: `pPlus ≠ pMinus` for the right and left limits of the
  observed treatment probability at `c`.
Then the treatment jump equals the complier share at the cutoff, and the ratio of the jump in
the observed outcome regression to the jump in the treatment probability equals
`mean1 complier c - mean0 complier c`, a version of `E[Y(1) - Y(0) | complier, X = c]`: the
local average treatment effect for compliers at the cutoff. -/
theorem fuzzy_rd_complier_identification {c : ℝ} (hcont : M.ContinuousAtCutoff c)
    (hmono : M.share .defier c = 0) {pPlus pMinus yPlus yMinus : ℝ}
    (hpPlus : Tendsto (M.treatmentProb c) (𝓝[>] c) (𝓝 pPlus))
    (hpMinus : Tendsto (M.treatmentProb c) (𝓝[<] c) (𝓝 pMinus))
    (hyPlus : Tendsto (M.outcomeReg c) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (M.outcomeReg c) (𝓝[<] c) (𝓝 yMinus))
    (hjump : pPlus ≠ pMinus) :
    pPlus - pMinus = M.share .complier c ∧
      (yPlus - yMinus) / (pPlus - pMinus) = M.mean1 .complier c - M.mean0 .complier c := by
  have right : ∀ {f : ℝ → ℝ}, ContinuousAt f c → Tendsto f (𝓝[>] c) (𝓝 (f c)) :=
    fun hf => hf.tendsto.mono_left nhdsWithin_le_nhds
  have left : ∀ {f : ℝ → ℝ}, ContinuousAt f c → Tendsto f (𝓝[<] c) (𝓝 (f c)) :=
    fun hf => hf.tendsto.mono_left nhdsWithin_le_nhds
  have hp := sharp_rd_identification (right (hcont.armTreat true)) (left (hcont.armTreat false))
    hpPlus hpMinus
  rw [armTreat_sub, hmono, sub_zero] at hp
  obtain ⟨-, hW⟩ := fuzzy_wald_identification (right (hcont.armTreat true))
    (left (hcont.armTreat false)) (right (hcont.armMean true)) (left (hcont.armMean false))
    hpPlus hpMinus hyPlus hyMinus hjump
  have hC : M.share .complier c ≠ 0 := by
    rw [← hp]
    exact sub_ne_zero.mpr hjump
  refine ⟨hp, ?_⟩
  rw [hW, armTreat_sub, armMean_sub, hmono]
  field_simp
  ring

/-! ### The sharp design inside the fuzzy model -/

/-- The sharp design as a fuzzy model: every unit is a complier, and the potential outcome means
are `m1` and `m0` in every stratum. -/
def sharp (m1 m0 : ℝ → ℝ) : FuzzyModel where
  share t _ := if t = .complier then 1 else 0
  mean1 _ := m1
  mean0 _ := m0

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

/-- The complier theorem `fuzzy_rd_complier_identification`, applied to the all-complier model
`sharp m1 m0` with `m1` and `m0` continuous at `c`, gives the sharp identification result: the
jump of the sharp observed regression equals `m1 c - m0 c`. -/
theorem sharp_of_complier_identification {c : ℝ} {m1 m0 : ℝ → ℝ} (h1 : ContinuousAt m1 c)
    (h0 : ContinuousAt m0 c) {yPlus yMinus : ℝ}
    (hyPlus : Tendsto (observedRegression c m1 m0) (𝓝[>] c) (𝓝 yPlus))
    (hyMinus : Tendsto (observedRegression c m1 m0) (𝓝[<] c) (𝓝 yMinus)) :
    yPlus - yMinus = m1 c - m0 c := by
  have hcont : (sharp m1 m0).ContinuousAtCutoff c :=
    fun _ => ⟨continuousAt_const, fun _ => h1, fun _ => h0⟩
  have hpPlus : Tendsto ((sharp m1 m0).treatmentProb c) (𝓝[>] c) (𝓝 1) := by
    rw [sharp_treatmentProb]
    exact tendsto_observedRegression_right _ tendsto_const_nhds
  have hpMinus : Tendsto ((sharp m1 m0).treatmentProb c) (𝓝[<] c) (𝓝 0) := by
    rw [sharp_treatmentProb]
    exact tendsto_observedRegression_left _ tendsto_const_nhds
  rw [← sharp_outcomeReg] at hyPlus hyMinus
  have h := (fuzzy_rd_complier_identification hcont (by simp [sharp]) hpPlus hpMinus hyPlus
    hyMinus one_ne_zero).2
  simpa [sharp] using h

end FuzzyModel

end RD

end CausalInference
