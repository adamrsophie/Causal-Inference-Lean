/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Interaction.Synergism

/-!
# Excess fractions for two treatments

Hernán and Robins, *Causal Inference: What If* (2020), Fine Point 5.4 (and Fine Point 3.5 for
the definition). With deterministic counterfactuals, observed treatments `A`, `E` and observed
outcome `Y = Y^{A,E}`, the excess fraction for a (single or joint) intervention is the share of
the observed cases that would not occur under that intervention:
`(Pr[Y = 1] - Pr[Y^{intervention} = 1]) / Pr[Y = 1]`. Intervening on `A` alone leaves `E` at
its observed value, so `Y^{a=0} = Y^{0,E}`.

## Main definitions

* `Population.obsRisk`, `Population.excessFractionA`, `Population.excessFractionE`,
  `Population.excessFractionJoint`.

## Main results

* `Population.excessFractionA_le_one`, `excessFractionE_le_one`, `excessFractionJoint_le_one`:
  each excess fraction is at most one (when there are cases).
* `excessFractions_sum_gt_one`: the excess fractions of `A` and `E` can sum to more than one.
  When everyone is of type 8 (Zeus in Fine Point 5.4: only `U5`) and receives both treatments,
  both single excess fractions equal one, their sum is two, and the joint excess fraction is one:
  each case is counted twice.
-/

@[expose] public section

namespace CausalInference

namespace Interaction

namespace Population

variable {ι : Type*} [Fintype ι] (P : Population ι) (A E : ι → Bool)

/-- The observed risk `Pr[Y = 1]` with `Y = Y^{A,E}` (consistency). -/
def obsRisk : ℝ := ∑ i, P.weight i * ((P.resp i (A i) (E i)).toNat : ℝ)

/-- The risk `Pr[Y^{a=0} = 1]` when everybody is set to `a = 0` and `E` keeps its observed
value. -/
def riskA0 : ℝ := ∑ i, P.weight i * ((P.resp i false (E i)).toNat : ℝ)

/-- The risk `Pr[Y^{e=0} = 1]` when everybody is set to `e = 0` and `A` keeps its observed
value. -/
def riskE0 : ℝ := ∑ i, P.weight i * ((P.resp i (A i) false).toNat : ℝ)

/-- The excess fraction for `A`: `(Pr[Y = 1] - Pr[Y^{a=0} = 1]) / Pr[Y = 1]`. -/
noncomputable def excessFractionA : ℝ := (P.obsRisk A E - P.riskA0 E) / P.obsRisk A E

/-- The excess fraction for `E`: `(Pr[Y = 1] - Pr[Y^{e=0} = 1]) / Pr[Y = 1]`. -/
noncomputable def excessFractionE : ℝ := (P.obsRisk A E - P.riskE0 A) / P.obsRisk A E

/-- The excess fraction for the joint intervention `a = 0, e = 0`:
`(Pr[Y = 1] - Pr[Y^{0,0} = 1]) / Pr[Y = 1]`. -/
noncomputable def excessFractionJoint : ℝ :=
  (P.obsRisk A E - P.risk false false) / P.obsRisk A E

omit [Fintype ι] in
private theorem frac_le_one {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) : (x - y) / x ≤ 1 := by
  rw [div_le_one hx]; linarith

private theorem sum_nonneg' (f : ι → Bool) :
    0 ≤ ∑ i, P.weight i * ((f i).toNat : ℝ) :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.weight_nonneg i) (Nat.cast_nonneg _)

/-- The excess fraction for `A` is at most one, provided `Pr[Y = 1] > 0` (What If,
Fine Point 5.4). It can be negative, when `A` prevents more cases than it causes. -/
theorem excessFractionA_le_one (h : 0 < P.obsRisk A E) : P.excessFractionA A E ≤ 1 :=
  frac_le_one h (P.sum_nonneg' _)

/-- The excess fraction for `E` is at most one, provided `Pr[Y = 1] > 0`. -/
theorem excessFractionE_le_one (h : 0 < P.obsRisk A E) : P.excessFractionE A E ≤ 1 :=
  frac_le_one h (P.sum_nonneg' _)

/-- The excess fraction for the joint intervention on `A` and `E` is at most one, provided
`Pr[Y = 1] > 0` (What If, Fine Point 5.4). -/
theorem excessFractionJoint_le_one (h : 0 < P.obsRisk A E) : P.excessFractionJoint A E ≤ 1 :=
  frac_le_one h (P.sum_nonneg' _)

end Population

/-- Fine Point 5.4 of What If: excess fractions do not add. When everybody has type 8
(`1000`, the outcome only under joint exposure, as for an individual whose only background
factor is `U5`) and receives `A = 1` and `E = 1`, there are cases (`Pr[Y = 1] = 1`), the excess
fractions of `A` and of `E` are both one, so their sum is two, while the joint excess fraction
is one. -/
theorem excessFractions_sum_gt_one :
    let P := pointPopulation (ResponseType.ofBits true false false false)
    0 < P.obsRisk (fun _ => true) (fun _ => true) ∧
      P.excessFractionA (fun _ => true) (fun _ => true) = 1 ∧
      P.excessFractionE (fun _ => true) (fun _ => true) = 1 ∧
      1 < P.excessFractionA (fun _ => true) (fun _ => true) +
        P.excessFractionE (fun _ => true) (fun _ => true) ∧
      P.excessFractionJoint (fun _ => true) (fun _ => true) = 1 := by
  simp [Population.obsRisk, Population.excessFractionA, Population.excessFractionE,
    Population.excessFractionJoint, Population.riskA0, Population.riskE0, Population.risk,
    pointPopulation, ResponseType.ofBits]

end Interaction

end CausalInference
