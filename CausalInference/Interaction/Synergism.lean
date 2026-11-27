/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Interaction.ResponseTypes

/-!
# Empirical tests for synergism

Hernán and Robins, *Causal Inference: What If* (2020), Fine Point 5.1 and Technical Point 5.2,
after VanderWeele and Robins (2007, 2008) and Greenland, Lash and Rothman (2008).

An individual is synergistic, in the sense of Fine Point 5.1, when the outcome occurs under
joint exposure but under neither single exposure: `Y^{11} = 1` and `Y^{01} = Y^{10} = 0`. These
are types 7 (`1001`) and 8 (`1000`) of Table 5.2; the outcome under no exposure is free.

## Main definitions

* `ResponseType.IsSynergistic`: `Y^{11} = 1`, `Y^{01} = 0`, `Y^{10} = 0` (types 7 and 8).
* `ResponseType.IsType8`: the outcome occurs only under joint exposure (type 8, `1000`).
* `ResponseType.IsMonotone`: the counterfactual outcomes are nondecreasing in `a` and in `e`
  (Technical Point 5.2).

## Main results

* `Population.exists_synergistic_of_risk_sub_pos`: `p11 - p01 - p10 > 0` implies positive mass
  on synergistic types.
* `Population.exists_type8_of_interactionContrast_pos`: if every individual of positive mass
  is monotone, `IC = p11 - p01 - p10 + p00 > 0` implies positive mass on type 8.
* `monotonicity_needed`: without monotonicity, `IC > 0` does not imply synergism (all mass on
  type 15, `0001`).
* `oneSidedMonotonicity_not_enough`: monotonicity in `E` alone is not enough either (all mass
  on type 3, `1101`).
* `riskTest_not_necessary`: the test `p11 - p01 - p10 > 0` can fail although synergistic types
  have positive mass (half type 8, half type 1).
* `icTest_not_necessary`: under monotonicity, `IC > 0` can fail although type 8 has positive
  mass (half type 8, half type 2).
-/

@[expose] public section

namespace CausalInference

namespace Interaction

namespace ResponseType

/-- Synergism of a response type in the sense of What If, Fine Point 5.1: the outcome occurs
under joint exposure `A = 1, E = 1` but under neither single exposure. These are types 7 and 8
of Table 5.2. -/
def IsSynergistic (r : ResponseType) : Prop :=
  r true true = true ∧ r false true = false ∧ r true false = false

instance (r : ResponseType) : Decidable (IsSynergistic r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Type 8 of Table 5.2: the outcome occurs only under joint exposure (the form of interaction
called compositional epistasis in genetics). -/
def IsType8 (r : ResponseType) : Prop := r = ofBits true false false false

instance (r : ResponseType) : Decidable (IsType8 r) := inferInstanceAs (Decidable (_ = _))

/-- Monotonicity of the effects of both treatments (What If, Technical Point 5.2): the
counterfactual outcome is nondecreasing in `a` at each `e`, and in `e` at each `a`. -/
def IsMonotone (r : ResponseType) : Prop :=
  ∀ a e : Bool, r false e ≤ r true e ∧ r a false ≤ r a true

instance (r : ResponseType) : Decidable (IsMonotone r) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- The synergistic types are exactly types 7 and 8 of Table 5.2. -/
theorem isSynergistic_iff_bookNumber (r : ResponseType) :
    IsSynergistic r ↔ bookNumber r ∈ ({7, 8} : Finset ℕ) := by
  revert r; refine forall_iff.2 ?_; decide

/-- Type 8 is synergistic. -/
theorem IsType8.isSynergistic {r : ResponseType} (h : IsType8 r) : IsSynergistic r := by
  subst h; decide

/-- Monotonicity rules out type 7 (What If, Fine Point 5.1): a monotone synergistic type is
type 8. -/
theorem isType8_of_isMonotone_of_isSynergistic (r : ResponseType) (hm : IsMonotone r)
    (hs : IsSynergistic r) : IsType8 r := by
  revert r; refine forall_iff.2 ?_; decide

/-- Pointwise core of the first test: for a type that is not synergistic,
`Y^{11} ≤ Y^{01} + Y^{10}`. -/
theorem toNat_le_of_not_isSynergistic (r : ResponseType) (h : ¬ IsSynergistic r) :
    (r true true).toNat ≤ (r false true).toNat + (r true false).toNat := by
  revert r; refine forall_iff.2 ?_; decide

/-- Pointwise core of the second test: a monotone type other than type 8 has a nonpositive
individual interaction contrast. -/
theorem indContrast_nonpos_of_isMonotone (r : ResponseType) (hm : IsMonotone r)
    (h : ¬ IsType8 r) : indContrast r ≤ 0 := by
  revert r; refine forall_iff.2 ?_; decide

end ResponseType

namespace Population

variable {ι : Type*} [Fintype ι] (P : Population ι)

/-- The first empirical test for synergism (What If, Fine Point 5.1; VanderWeele and Robins):
if `Pr[Y^{11} = 1] - Pr[Y^{01} = 1] - Pr[Y^{10} = 1] > 0`, then some individual of positive mass
has `Y^{11} = 1` and `Y^{01} = Y^{10} = 0` (type 7 or 8). No monotonicity is assumed. -/
theorem exists_synergistic_of_risk_sub_pos
    (h : 0 < P.risk true true - P.risk false true - P.risk true false) :
    ∃ i, 0 < P.weight i ∧ ResponseType.IsSynergistic (P.resp i) := by
  by_contra hcon
  refine absurd h (not_lt.2 ?_)
  simp only [risk, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases (P.weight_nonneg i).lt_or_eq with hi | hi
  · have hle := ResponseType.toNat_le_of_not_isSynergistic (P.resp i)
      fun hs => hcon ⟨i, hi, hs⟩
    have hle' : ((P.resp i true true).toNat : ℝ) ≤
        ((P.resp i false true).toNat : ℝ) + ((P.resp i true false).toNat : ℝ) := by
      exact_mod_cast hle
    nlinarith
  · rw [← hi]; simp

/-- The second empirical test for synergism (What If, Fine Point 5.1; Greenland, Lash and
Rothman, 2008): if every individual of positive mass has monotone effects of both treatments,
then superadditive interaction `IC > 0` implies positive mass on type 8. -/
theorem exists_type8_of_interactionContrast_pos
    (hm : ∀ i, 0 < P.weight i → ResponseType.IsMonotone (P.resp i))
    (h : 0 < P.interactionContrast) :
    ∃ i, 0 < P.weight i ∧ ResponseType.IsType8 (P.resp i) := by
  by_contra hcon
  refine absurd h (not_lt.2 ?_)
  rw [interactionContrast_eq_sum]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases (P.weight_nonneg i).lt_or_eq with hi | hi
  · have hle := ResponseType.indContrast_nonpos_of_isMonotone (P.resp i) (hm i hi)
      fun h8 => hcon ⟨i, hi, h8⟩
    have hle' : ((ResponseType.indContrast (P.resp i) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle
    exact mul_nonpos_of_nonneg_of_nonpos hi.le hle'
  · rw [← hi, zero_mul]

end Population

/-- The population in which every individual has the single response type `r`. -/
noncomputable def pointPopulation (r : ResponseType) : Population Unit where
  weight _ := 1
  weight_nonneg _ := zero_le_one
  weight_sum := by simp
  resp _ := r

/-- The population with mass `1/2` on each of two response types `r` and `s`. -/
noncomputable def halfPopulation (r s : ResponseType) : Population Bool where
  weight _ := 1 / 2
  weight_nonneg _ := by norm_num
  weight_sum := by simp
  resp b := if b then r else s

/-- Monotonicity cannot be dropped from the second test: when everyone has type 15 (`0001`,
the outcome occurs only under no exposure), `IC = 1 > 0`, yet nobody is synergistic. -/
theorem monotonicity_needed :
    0 < (pointPopulation (ResponseType.ofBits false false false true)).interactionContrast ∧
      ∀ i, ¬ ResponseType.IsSynergistic
        ((pointPopulation (ResponseType.ofBits false false false true)).resp i) := by
  refine ⟨?_, fun i => by cases i; decide⟩
  simp [Population.interactionContrast, Population.risk, pointPopulation, ResponseType.ofBits]

/-- Monotonicity in one treatment only is not enough: type 3 (`1101`) is monotone in `E` at
each level of `A`, has `IC = 1 > 0`, and is not synergistic. -/
theorem oneSidedMonotonicity_not_enough :
    (∀ a, ResponseType.ofBits true true false true a false ≤
        ResponseType.ofBits true true false true a true) ∧
      0 < (pointPopulation (ResponseType.ofBits true true false true)).interactionContrast ∧
      ∀ i, ¬ ResponseType.IsSynergistic
        ((pointPopulation (ResponseType.ofBits true true false true)).resp i) := by
  refine ⟨by decide, ?_, fun i => by cases i; decide⟩
  simp [Population.interactionContrast, Population.risk, pointPopulation, ResponseType.ofBits]

/-- The first test is sufficient but not necessary (What If, Fine Point 5.1): with mass `1/2`
on type 8 and `1/2` on type 1 (doomed), synergism is present, every individual is monotone, and
yet `p11 - p01 - p10 = 0`. -/
theorem riskTest_not_necessary :
    (∃ i, 0 < (halfPopulation (ResponseType.ofBits true false false false)
        (ResponseType.ofBits true true true true)).weight i ∧
        ResponseType.IsSynergistic ((halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true true)).resp i)) ∧
      (∀ i, ResponseType.IsMonotone ((halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true true)).resp i)) ∧
      (halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true true)).risk true true -
        (halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true true)).risk false true -
        (halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true true)).risk true false = 0 := by
  refine ⟨⟨true, by norm_num [halfPopulation], by decide⟩, fun i => by cases i <;> decide, ?_⟩
  simp [Population.risk, halfPopulation, ResponseType.ofBits]

/-- The second test is also not necessary: with mass `1/2` on type 8 and `1/2` on type 2
(`1110`), every individual is monotone and type 8 has positive mass, yet `IC = 0`. -/
theorem icTest_not_necessary :
    (∃ i, 0 < (halfPopulation (ResponseType.ofBits true false false false)
        (ResponseType.ofBits true true true false)).weight i ∧
        ResponseType.IsType8 ((halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true false)).resp i)) ∧
      (∀ i, ResponseType.IsMonotone ((halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true false)).resp i)) ∧
      (halfPopulation (ResponseType.ofBits true false false false)
          (ResponseType.ofBits true true true false)).interactionContrast = 0 := by
  refine ⟨⟨true, by norm_num [halfPopulation], by decide⟩, fun i => by cases i <;> decide, ?_⟩
  simp [Population.interactionContrast, Population.risk, halfPopulation, ResponseType.ofBits]

end Interaction

end CausalInference
