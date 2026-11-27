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
outcome `Y = Y^{A,E}`, the excess fraction for an intervention with outcome `Y^g` is
`(Pr[Y = 1] - Pr[Y^g = 1]) / Pr[Y = 1]`.

The excess fraction is a net quantity. Its numerator is
`Pr[Y = 1, Y^g = 0] - Pr[Y = 0, Y^g = 1]`: the observed cases that the intervention would
prevent, minus the new cases it would create. So the excess fraction equals the prevented-case
fraction `Pr[Y^g = 0 | Y = 1]` (the share of the observed cases that would not occur under the
intervention) minus `Pr[Y = 0, Y^g = 1] / Pr[Y = 1]`, and the two agree when the intervention
harms no one. Fine Point 3.5 draws a related distinction between the excess fraction and the
etiologic fraction (the proportion of cases mechanically caused by exposure), and in its example
states that the excess fraction is a lower bound for the etiologic fraction. The prevented-case
fraction defined here is the counterfactual share of observed cases that would not occur; we do
not identify it with the book's etiologic fraction, which refers to the causal mechanism.

The single interventions are defined with the other treatment held at its observed value:
`riskA0` uses `Y^{0,E}`. This is the risk under `do(A = 0)` only when `E` does not respond to
`A`; if `E` has counterfactual values `E^{a=0}`, the risk under `do(A = 0)` is `riskA0` at
`E^{a=0}` instead (`riskA0_responding_example`). The same holds for `riskE0`.

## Main definitions

* `Population.obsRisk`, `Population.riskA0`, `Population.riskE0`,
  `Population.excessFractionA`, `Population.excessFractionE`,
  `Population.excessFractionJoint`.
* `Population.massOf`, `Population.preventedFraction`, `Population.harmedMass`: the
  probability of an event, the prevented-case fraction `Pr[Y^g = 0 | Y = 1]`, and the mass
  `Pr[Y = 0, Y^g = 1]` of new cases, for an arbitrary post-intervention outcome `Y^g`.

## Main results

* `Population.excessFractionA_le_one`, `excessFractionE_le_one`, `excessFractionJoint_le_one`:
  each excess fraction is at most one (when there are cases).
* `Population.excessFraction_eq_preventedFraction_sub` and its instances
  `excessFractionA_eq`, `excessFractionE_eq`, `excessFractionJoint_eq`: the excess fraction is
  the prevented-case fraction minus `Pr[Y = 0, Y^g = 1] / Pr[Y = 1]`.
* `Population.excessFraction_eq_preventedFraction_of_no_harm`: equality when no individual of
  positive mass becomes a case under the intervention.
* `Population.excessFraction_le_preventedFraction`: the excess fraction is a lower bound.
* `excessFraction_ne_preventedFraction`: the two can differ: excess fraction zero, prevented
  fraction one.
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

/-- The risk `Pr[Y^{0,E} = 1]` of the joint intervention that sets `a = 0` and holds `E` at the
value given by the argument `E` (its observed value in the excess fractions below). This is the
risk under the single intervention `do(A = 0)` only when `E` does not respond to `A`; when `E`
has counterfactual values `E^{a=0}`, the risk under `do(A = 0)` is `riskA0` evaluated at
`E^{a=0}` (see `riskA0_responding_example`). -/
def riskA0 : ℝ := ∑ i, P.weight i * ((P.resp i false (E i)).toNat : ℝ)

/-- The risk `Pr[Y^{A,0} = 1]` of the joint intervention that sets `e = 0` and holds `A` at the
value given by the argument `A` (its observed value in the excess fractions below). This is the
risk under the single intervention `do(E = 0)` only when `A` does not respond to `E`; when `A`
has counterfactual values `A^{e=0}`, the risk under `do(E = 0)` is `riskE0` evaluated at
`A^{e=0}`. -/
def riskE0 : ℝ := ∑ i, P.weight i * ((P.resp i (A i) false).toNat : ℝ)

/-- The excess fraction for `A`: `(Pr[Y = 1] - Pr[Y^{0,E} = 1]) / Pr[Y = 1]`, with `E` held at
its observed value. -/
noncomputable def excessFractionA : ℝ := (P.obsRisk A E - P.riskA0 E) / P.obsRisk A E

/-- The excess fraction for `E`: `(Pr[Y = 1] - Pr[Y^{A,0} = 1]) / Pr[Y = 1]`, with `A` held at
its observed value. -/
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

/-- The probability `Pr[f = true]` of an event given as a Boolean function of individuals. -/
def massOf (f : ι → Bool) : ℝ := ∑ i, P.weight i * ((f i).toNat : ℝ)

/-- The prevented-case fraction `Pr[Y^g = 0 | Y = 1]` for an intervention with post-intervention
outcome `Yg i = Y_i^g`: the share of the observed cases that would not occur under the
intervention. -/
noncomputable def preventedFraction (Yg : ι → Bool) : ℝ :=
  P.massOf (fun i => P.resp i (A i) (E i) && !Yg i) / P.obsRisk A E

/-- The mass `Pr[Y = 0, Y^g = 1]` of the individuals who are not cases but would become cases
under the intervention with post-intervention outcome `Yg`. -/
def harmedMass (Yg : ι → Bool) : ℝ := P.massOf (fun i => !P.resp i (A i) (E i) && Yg i)

/-- The numerator of an excess fraction is a net count:
`Pr[Y = 1] - Pr[Y^g = 1] = Pr[Y = 1, Y^g = 0] - Pr[Y = 0, Y^g = 1]`. -/
theorem obsRisk_sub_massOf (Yg : ι → Bool) :
    P.obsRisk A E - P.massOf Yg =
      P.massOf (fun i => P.resp i (A i) (E i) && !Yg i) - P.harmedMass A E Yg := by
  simp only [obsRisk, harmedMass, massOf, ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases P.resp i (A i) (E i) <;> cases Yg i <;> norm_num

/-- The excess fraction for an intervention with post-intervention outcome `Yg` is the
prevented-case fraction minus `Pr[Y = 0, Y^g = 1] / Pr[Y = 1]`. The identity holds for every
value of `Pr[Y = 1]` (both sides are `0` when it is `0`); it is meaningful only when
`Pr[Y = 1] > 0`. -/
theorem excessFraction_eq_preventedFraction_sub (Yg : ι → Bool) :
    (P.obsRisk A E - P.massOf Yg) / P.obsRisk A E =
      P.preventedFraction A E Yg - P.harmedMass A E Yg / P.obsRisk A E := by
  rw [obsRisk_sub_massOf, sub_div, preventedFraction]

/-- The excess fraction for `A` is the prevented-case fraction of the intervention
`Y^{0,E}` minus `Pr[Y = 0, Y^{0,E} = 1] / Pr[Y = 1]` (meaningful only when `Pr[Y = 1] > 0`). -/
theorem excessFractionA_eq :
    P.excessFractionA A E =
      P.preventedFraction A E (fun i => P.resp i false (E i)) -
        P.harmedMass A E (fun i => P.resp i false (E i)) / P.obsRisk A E :=
  P.excessFraction_eq_preventedFraction_sub A E _

/-- The excess fraction for `E` is the prevented-case fraction of the intervention
`Y^{A,0}` minus `Pr[Y = 0, Y^{A,0} = 1] / Pr[Y = 1]` (meaningful only when `Pr[Y = 1] > 0`). -/
theorem excessFractionE_eq :
    P.excessFractionE A E =
      P.preventedFraction A E (fun i => P.resp i (A i) false) -
        P.harmedMass A E (fun i => P.resp i (A i) false) / P.obsRisk A E :=
  P.excessFraction_eq_preventedFraction_sub A E _

/-- The joint excess fraction is the prevented-case fraction of the intervention `Y^{0,0}`
minus `Pr[Y = 0, Y^{0,0} = 1] / Pr[Y = 1]` (meaningful only when `Pr[Y = 1] > 0`). -/
theorem excessFractionJoint_eq :
    P.excessFractionJoint A E =
      P.preventedFraction A E (fun i => P.resp i false false) -
        P.harmedMass A E (fun i => P.resp i false false) / P.obsRisk A E :=
  P.excessFraction_eq_preventedFraction_sub A E _

/-- If no individual of positive mass is a noncase who would become a case under the
intervention, the excess fraction equals the prevented-case fraction. The identity also holds
when `Pr[Y = 1] = 0` (both sides are `0`); it is meaningful only when `Pr[Y = 1] > 0`. -/
theorem excessFraction_eq_preventedFraction_of_no_harm (Yg : ι → Bool)
    (h : ∀ i, 0 < P.weight i → P.resp i (A i) (E i) = false → Yg i = false) :
    (P.obsRisk A E - P.massOf Yg) / P.obsRisk A E = P.preventedFraction A E Yg := by
  have h0 : P.harmedMass A E Yg = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases (P.weight_nonneg i).lt_or_eq with hi | hi
    · cases hY : P.resp i (A i) (E i)
      · simp [h i hi hY]
      · simp [hY]
    · rw [← hi, zero_mul]
  rw [excessFraction_eq_preventedFraction_sub, h0, zero_div, sub_zero]

/-- The excess fraction is at most the prevented-case fraction, provided `Pr[Y = 1] > 0`.
Fine Point 3.5 states the analogous bound for the etiologic fraction in its example. -/
theorem excessFraction_le_preventedFraction (Yg : ι → Bool) (h : 0 < P.obsRisk A E) :
    (P.obsRisk A E - P.massOf Yg) / P.obsRisk A E ≤ P.preventedFraction A E Yg := by
  rw [excessFraction_eq_preventedFraction_sub, sub_le_self_iff]
  exact div_nonneg (P.sum_nonneg' _) h.le

end Population

/-- The excess fraction is not the share of observed cases prevented. In the population with
mass `1/2` on type 6 (`1010`, `Y^{a,e} = a`) and mass `1/2` on type 11 (`0101`,
`Y^{a,e} = 1 - a`), with everybody treated (`A = E = 1`), there are cases
(`Pr[Y = 1] = 1/2`), removing `A` prevents every observed case (prevented-case fraction one)
but creates as many new cases, and the excess fraction for `A` is zero. -/
theorem excessFraction_ne_preventedFraction :
    let P := halfPopulation (ResponseType.ofBits true false true false)
      (ResponseType.ofBits false true false true)
    0 < P.obsRisk (fun _ => true) (fun _ => true) ∧
      P.excessFractionA (fun _ => true) (fun _ => true) = 0 ∧
      P.preventedFraction (fun _ => true) (fun _ => true) (fun i => P.resp i false true) = 1 := by
  norm_num [Population.obsRisk, Population.excessFractionA, Population.riskA0,
    Population.preventedFraction, Population.massOf, halfPopulation, ResponseType.ofBits]

/-- A single intervention can differ from the joint intervention that holds the other treatment
at its observed value. Let the outcome be `Y^{a,e} = e` (type 4, `1100`) and let `E` respond to
`A` with `E = A`, so that observed `A = E = 1` and `E^{a=0} = 0`. Then `riskA0` at observed `E`
is `Pr[Y^{0,1} = 1] = 1`, while the risk under `do(A = 0)`, which is `riskA0` at `E^{a=0}`, is
`Pr[Y^{0,E^{a=0}} = 1] = 0`. -/
theorem riskA0_responding_example :
    let P := pointPopulation (ResponseType.ofBits true true false false)
    P.riskA0 (fun _ => true) = 1 ∧ P.riskA0 (fun _ => false) = 0 := by
  simp [Population.riskA0, pointPopulation, ResponseType.ofBits]

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
