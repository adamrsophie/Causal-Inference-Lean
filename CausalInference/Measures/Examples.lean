/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import CausalInference.Measures.EffectMeasures

/-!
# Elementary probability examples

Checked finite computations from the opening chapters of the causal inference primer and from
Pearl's discussion of confounding. Each example is a real-valued mass function on a small finite
type; probabilities are finite sums and conditional probabilities are ratios whose denominators
are shown to be positive in the same statement.

## Main definitions

* `Paradoxes.IsDist m`: `m` is a probability mass function (nonnegative, sums to one); an
  abbreviation of `EffectMeasure.IsWeights`.
* `Paradoxes.probOf m P`, `Paradoxes.condProb m P Q`, `Paradoxes.expect m f`,
  `Paradoxes.cov m X Y`: probability, conditional probability, expectation, covariance.

## Main results

* `zeroCov_not_indep`: `X` uniform on `{-1, 0, 1}` and `Y = X²` have zero covariance but are
  dependent (Pearl, Glymour and Jewell 2016, Study question 1.3.6(b); a valid replacement for the
  example in the solution manual).
* `coinBell_collider`: two independent fair coins and a bell that rings when at least one coin
  shows heads (Pearl, Glymour and Jewell 2016, Section 2.3, Tables 2.1 and 2.2): the coins are
  independent, `P(X = H | Z = 1) = 2/3` and `P(X = H | Y = H, Z = 1) = 1/2`, so conditioning on
  the common effect makes them dependent.
* `twoCoin_confounding`: Pearl (2009), Section 6.3.1: two fair coins `Z₁`, `Z₂`, `X` occurs when
  they agree and `Y` when they differ. Each coin is independent of `X` and of `Y`, but `X` and
  `Y` are dependent.
* `montyHall`: the Monty Hall problem (Pearl, Glymour and Jewell 2016, Section 1.3): having
  chosen door A and seen Monty open door C, the car is behind door B with probability `2/3` and
  behind door A with probability `1/3`.

## References

* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer* (2016),
  Sections 1.3 and 2.3.
* J. Pearl, *Causality*, 2nd ed. (2009), Section 6.3.1.
-/

@[expose] public section

namespace CausalInference

namespace Paradoxes

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- `m` is a probability mass function on the finite type `Ω`: nonnegative values summing to
one. This is `EffectMeasure.IsWeights` under the name used in this file. -/
abbrev IsDist (m : Ω → ℝ) : Prop := EffectMeasure.IsWeights m

/-- The probability `∑_{ω ∈ P} m ω` of the event `P`. -/
def probOf (m : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] : ℝ := ∑ ω ∈ univ.filter P, m ω

/-- The conditional probability `P(P | Q) = P(P ∧ Q) / P(Q)`. Every use below states that
`P(Q) > 0`. -/
noncomputable def condProb (m : Ω → ℝ) (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q] :
    ℝ :=
  probOf m (fun ω => P ω ∧ Q ω) / probOf m Q

/-- The expectation `∑ ω, m ω * f ω`. -/
def expect (m : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, m ω * f ω

/-- The covariance `E[X Y] - E[X] E[Y]`. -/
def cov (m : Ω → ℝ) (X Y : Ω → ℝ) : ℝ :=
  expect m (fun ω => X ω * Y ω) - expect m X * expect m Y

/-! ### Zero covariance without independence -/

/-- The uniform distribution on three points. -/
noncomputable def unif3 : Fin 3 → ℝ := fun _ => 1 / 3

/-- `X` takes the values `-1`, `0`, `1`. -/
def X3 : Fin 3 → ℝ := ![-1, 0, 1]

/-- `Y = X²`. -/
def Y3 (i : Fin 3) : ℝ := X3 i ^ 2

/-- **Zero covariance does not imply independence.** For `X` uniform on `{-1, 0, 1}` and
`Y = X²`, the covariance is `0`, but `P(X = 0, Y = 0) = 1/3 ≠ 1/9 = P(X = 0) P(Y = 0)`. -/
theorem zeroCov_not_indep :
    IsDist unif3 ∧ cov unif3 X3 Y3 = 0 ∧
      probOf unif3 (fun i => X3 i = 0 ∧ Y3 i = 0) ≠
        probOf unif3 (fun i => X3 i = 0) * probOf unif3 (fun i => Y3 i = 0) := by
  refine ⟨⟨fun _ => by norm_num [unif3], by norm_num [unif3, Fin.sum_univ_three]⟩, ?_, ?_⟩
  · norm_num [cov, expect, unif3, X3, Y3, Fin.sum_univ_three]
  · simp only [probOf, Finset.sum_filter]
    simp only [Fin.sum_univ_three]
    norm_num [X3, Y3, unif3]

/-! ### The coin and bell collider -/

/-- Two independent fair coins (`true` for heads): each outcome has probability `1/4`. -/
noncomputable def twoCoins : Bool × Bool → ℝ := fun _ => 1 / 4

/-- **Coin and bell** (Pearl, Glymour and Jewell 2016, Section 2.3). With coins `X`, `Y` and
the bell `Z = X ∨ Y`: the coins are independent; `P(X = H | Z = 1) = 2/3`; and
`P(X = H | Y = H, Z = 1) = 1/2`. Conditioning on the collider `Z` makes the coins dependent. -/
theorem coinBell_collider :
    IsDist twoCoins ∧
      (∀ x y : Bool, probOf twoCoins (fun ω => ω.1 = x ∧ ω.2 = y) =
        probOf twoCoins (fun ω => ω.1 = x) * probOf twoCoins (fun ω => ω.2 = y)) ∧
      0 < probOf twoCoins (fun ω => (ω.1 || ω.2) = true) ∧
      condProb twoCoins (fun ω => ω.1 = true) (fun ω => (ω.1 || ω.2) = true) = 2 / 3 ∧
      0 < probOf twoCoins (fun ω => ω.2 = true ∧ (ω.1 || ω.2) = true) ∧
      condProb twoCoins (fun ω => ω.1 = true)
        (fun ω => ω.2 = true ∧ (ω.1 || ω.2) = true) = 1 / 2 := by
  refine ⟨⟨fun _ => by norm_num [twoCoins], ?_⟩, fun x y => ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [twoCoins, Fintype.sum_prod_type]
  all_goals
    simp only [condProb, probOf, Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  · cases x <;> cases y <;> norm_num [twoCoins]
  all_goals norm_num [twoCoins]

/-! ### Pearl's two-coin example of joint confounding -/

/-- **Two coins confound jointly** (Pearl 2009, Section 6.3.1). Two fair coins `Z₁`, `Z₂`;
`X` occurs when they agree and `Y` when they differ. Each coin is independent of `X` and of `Y`
(the product rule holds for every pair of values), yet `X` and `Y` are dependent:
`P(X, Y) = 0 ≠ 1/4 = P(X) P(Y)`. -/
theorem twoCoin_confounding :
    (∀ z x : Bool, probOf twoCoins (fun ω => ω.1 = z ∧ (ω.1 == ω.2) = x) =
        probOf twoCoins (fun ω => ω.1 = z) * probOf twoCoins (fun ω => (ω.1 == ω.2) = x)) ∧
      (∀ z x : Bool, probOf twoCoins (fun ω => ω.2 = z ∧ (ω.1 == ω.2) = x) =
        probOf twoCoins (fun ω => ω.2 = z) * probOf twoCoins (fun ω => (ω.1 == ω.2) = x)) ∧
      (∀ z y : Bool, probOf twoCoins (fun ω => ω.1 = z ∧ (ω.1 != ω.2) = y) =
        probOf twoCoins (fun ω => ω.1 = z) * probOf twoCoins (fun ω => (ω.1 != ω.2) = y)) ∧
      (∀ z y : Bool, probOf twoCoins (fun ω => ω.2 = z ∧ (ω.1 != ω.2) = y) =
        probOf twoCoins (fun ω => ω.2 = z) * probOf twoCoins (fun ω => (ω.1 != ω.2) = y)) ∧
      probOf twoCoins (fun ω => (ω.1 == ω.2) = true ∧ (ω.1 != ω.2) = true) ≠
        probOf twoCoins (fun ω => (ω.1 == ω.2) = true) *
          probOf twoCoins (fun ω => (ω.1 != ω.2) = true) := by
  refine ⟨fun z x => ?_, fun z x => ?_, fun z x => ?_, fun z x => ?_, ?_⟩
  all_goals
    simp only [probOf, Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  all_goals first
    | (cases z <;> cases x <;> norm_num [twoCoins])
    | norm_num [twoCoins]

/-! ### Monty Hall -/

/-- The Monty Hall model when the contestant has chosen door `0` (door A). An outcome is a pair
(door hiding the car, door Monty opens). The car is uniform over the three doors; Monty never
opens the chosen door or the car door, and chooses uniformly between doors `1` and `2` when the
car is behind door `0`. -/
noncomputable def montyHallDist : Fin 3 × Fin 3 → ℝ := fun ω =>
  if ω.1 = 0 then (if ω.2 = 0 then 0 else 1 / 6)
  else if ω.2 = 0 ∨ ω.2 = ω.1 then 0 else 1 / 3

/-- **Monty Hall** (Pearl, Glymour and Jewell 2016, Section 1.3 and Study question 1.3.5). The
model is a distribution in which Monty never opens the chosen door or the car door. Given that
Monty opened door `2` (door C), the car is behind door `1` (door B) with probability `2/3` and
behind the chosen door `0` with probability `1/3`: switching doubles the chance of winning. -/
theorem montyHall :
    IsDist montyHallDist ∧
      probOf montyHallDist (fun ω => ω.2 = 0 ∨ ω.2 = ω.1) = 0 ∧
      0 < probOf montyHallDist (fun ω => ω.2 = 2) ∧
      condProb montyHallDist (fun ω => ω.1 = 1) (fun ω => ω.2 = 2) = 2 / 3 ∧
      condProb montyHallDist (fun ω => ω.1 = 0) (fun ω => ω.2 = 2) = 1 / 3 := by
  refine ⟨⟨fun ω => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · unfold montyHallDist; split_ifs <;> norm_num
  all_goals
    try simp only [condProb, probOf, Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
    norm_num [montyHallDist]

end Paradoxes

end CausalInference
