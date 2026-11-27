/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Counterfactual response types, additive and multiplicative interaction

Deterministic counterfactual response types for two binary treatments `A`, `E` and a binary
outcome `Y` (Hernán and Robins, *Causal Inference: What If*, 2020, Chapter 5, Sections 5.1
and 5.3, Technical Point 5.1).

A response type is a function `r : Bool → Bool → Bool` with `r a e = Y^{a,e}`; there are 16 of
them (Table 5.2, after Miettinen 1982). A population is a finite type of individuals with
nonnegative weights summing to one and a response type for each individual; taking the
individuals to be the response types themselves gives a distribution over the 16 types.

## Main definitions

* `ResponseType`, `ResponseType.ofBits`, `ResponseType.bookNumber`: the 16 types and their
  numbering in Table 5.2 (columns `(1,1), (0,1), (1,0), (0,0)`; type 1 is `1111`, type 16 is
  `0000`).
* `ResponseType.indContrast`: the individual contrast `Y^{11} - Y^{01} - Y^{10} + Y^{00}`.
* `ResponseType.NoIndividualInteraction`: the effect of `A` does not depend on `E` and the
  effect of `E` does not depend on `A` for this type.
* `ResponseType.Class1`, `Class2`, `Class3`: the three classes of interacting types of
  Greenland and Poole (1988).
* `Population`, `Population.risk`, `Population.interactionContrast`: counterfactual risks
  `p a e = Pr[Y^{a,e} = 1]` and `IC = p11 - p10 - p01 + p00`.
* `Population.multInteraction`: the multiplicative contrast `p11 * p00 - p10 * p01`.

## Main results

* `ResponseType.noIndividualInteraction_iff_bookNumber`: exactly the types numbered
  1, 4, 6, 11, 13, 16 have no individual interaction (Section 5.3).
* `ResponseType.not_noIndividualInteraction_iff_class`: the interacting types are exactly the
  union of the three Greenland and Poole classes, which are types 8, 12, 14, 15; types 7, 10;
  and types 2, 3, 5, 9.
* `ResponseType.class1_recode`, `class2_recode`, `class3_recode`: the classes are invariant
  under recoding of `A` and of `E`; `ResponseType.bookNumber_recodeA_ofBits`: the book
  numbering is not.
* `Population.additive_interaction_iff`, `Population.additive_interaction_iff'`: the
  equivalent forms of additive interaction (Section 5.1, Technical Point 5.1).
* `ResponseType.existsUnique_bookNumber_eq`: the book numbering is a bijection onto
  `1, ..., 16`.
* `Population.multiplicative_interaction_iff`: for `p00 > 0`, the risk ratio form of
  multiplicative interaction is equivalent to `p11 * p00 ≠ p10 * p01`, with the
  supermultiplicative and submultiplicative cases (Technical Point 5.1).
* `Population.no_effect_of_no_additive_no_multiplicative`: no interaction on both the additive
  and the multiplicative scale forces `A` to have no effect at `E = 0` or `E` to have no effect
  at `A = 0`.
* `Population.interactionContrast_eq_sum`: `IC` is the mean individual contrast.
* `Population.exists_interacting_of_interactionContrast_ne_zero`: a nonzero additive
  interaction contrast forces positive mass on an interacting type.
* `cancellation_example`: the converse fails; in `cancellationPopulation`, equal shares of
  types 7 and 10 give `IC = 0` (Section 5.3, exact cancellation).

All declarations live in the namespace `CausalInference.Interaction`.
-/

@[expose] public section

namespace CausalInference

namespace Interaction

/-- A deterministic counterfactual response type for two binary treatments: `r a e` is the
outcome `Y^{a,e}` under the joint intervention setting `A = a` and `E = e`. -/
abbrev ResponseType := Bool → Bool → Bool

namespace ResponseType

/-- The response type with `Y^{11} = y11`, `Y^{01} = y01`, `Y^{10} = y10`, `Y^{00} = y00`,
in the column order of Table 5.2 of What If. -/
def ofBits (y11 y01 y10 y00 : Bool) : ResponseType := fun a e =>
  match a, e with
  | true, true => y11
  | false, true => y01
  | true, false => y10
  | false, false => y00

/-- Every response type is determined by its four counterfactual outcomes. -/
theorem eq_ofBits (r : ResponseType) :
    r = ofBits (r true true) (r false true) (r true false) (r false false) := by
  funext a e
  cases a <;> cases e <;> rfl

/-- To prove a property of all 16 response types it suffices to check the 16 bit patterns. -/
theorem forall_iff {P : ResponseType → Prop} :
    (∀ r, P r) ↔ ∀ y11 y01 y10 y00 : Bool, P (ofBits y11 y01 y10 y00) := by
  refine ⟨fun h _ _ _ _ => h _, fun h r => ?_⟩
  rw [eq_ofBits r]
  exact h _ _ _ _

/-- The number of a response type in Table 5.2 of What If: reading the outcomes
`Y^{11} Y^{01} Y^{10} Y^{00}` as a binary number `n`, the type number is `16 - n`. Thus type 1
is `1111` (doomed), type 8 is `1000`, and type 16 is `0000` (immune). -/
def bookNumber (r : ResponseType) : ℕ :=
  16 - (8 * (r true true).toNat + 4 * (r false true).toNat + 2 * (r true false).toNat +
    (r false false).toNat)

/-- The book numbering takes values in `1, ..., 16`. -/
theorem bookNumber_mem (r : ResponseType) : bookNumber r ∈ Finset.Icc 1 16 := by
  revert r
  refine forall_iff.2 ?_
  decide

/-- The book numbering is injective. -/
theorem bookNumber_injective : Function.Injective bookNumber := by
  refine forall_iff.2 fun a b c d => forall_iff.2 fun a' b' c' d' => ?_
  revert a b c d a' b' c' d'
  decide

/-- The book numbering is a bijection from the 16 response types onto `1, ..., 16`: every
number `n` in that range is the number of exactly one type, the type whose outcomes
`Y^{11} Y^{01} Y^{10} Y^{00}` are the binary digits of `16 - n`. -/
theorem existsUnique_bookNumber_eq : ∀ n ∈ Finset.Icc 1 16, ∃! r, bookNumber r = n := by
  have hex : ∀ n ∈ Finset.Icc 1 16, bookNumber
      (ofBits ((16 - n).testBit 3) ((16 - n).testBit 2) ((16 - n).testBit 1)
        ((16 - n).testBit 0)) = n := by decide
  exact fun n hn => ⟨_, hex n hn, fun r hr => bookNumber_injective (hr.trans (hex n hn).symm)⟩

/-- The individual interaction contrast `Y^{11} - Y^{01} - Y^{10} + Y^{00}` of a response type,
as an integer. -/
def indContrast (r : ResponseType) : ℤ :=
  (r true true).toNat - (r false true).toNat - (r true false).toNat + (r false false).toNat

/-- The individual causal effect of `A` at a fixed level `e` of `E`, `Y^{1,e} - Y^{0,e}`. -/
def effectA (r : ResponseType) (e : Bool) : ℤ := (r true e).toNat - (r false e).toNat

/-- The individual causal effect of `E` at a fixed level `a` of `A`, `Y^{a,1} - Y^{a,0}`. -/
def effectE (r : ResponseType) (a : Bool) : ℤ := (r a true).toNat - (r a false).toNat

/-- No individual interaction (What If, Section 5.3): for this type the causal effect of `A` is
the same whatever the value of `E`, and the causal effect of `E` is the same whatever the value
of `A`. -/
def NoIndividualInteraction (r : ResponseType) : Prop :=
  effectA r true = effectA r false ∧ effectE r true = effectE r false

instance (r : ResponseType) : Decidable (NoIndividualInteraction r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Either half of the definition suffices: the effect of `A` does not depend on `E` exactly
when the individual contrast vanishes, and likewise for `E`. -/
theorem noIndividualInteraction_iff_indContrast (r : ResponseType) :
    NoIndividualInteraction r ↔ indContrast r = 0 := by
  unfold NoIndividualInteraction effectA effectE indContrast
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; constructor <;> linarith

/-- Exactly the types numbered 1, 4, 6, 11, 13, 16 in Table 5.2 of What If have no individual
interaction: the doomed `1111`, the immune `0000`, and the types `1100`, `1010`, `0101`, `0011`
in which only one of the two treatments matters. -/
theorem noIndividualInteraction_iff_bookNumber (r : ResponseType) :
    NoIndividualInteraction r ↔ bookNumber r ∈ ({1, 4, 6, 11, 13, 16} : Finset ℕ) := by
  revert r
  refine forall_iff.2 ?_
  decide

/-- The number of the four joint interventions under which the outcome occurs. -/
def numCases (r : ResponseType) : ℕ :=
  (r true true).toNat + (r false true).toNat + (r true false).toNat + (r false false).toNat

/-- Greenland and Poole class 1: the outcome occurs under exactly one of the four joint
interventions (types 8, 12, 14, 15 of Table 5.2). -/
def Class1 (r : ResponseType) : Prop := numCases r = 1

/-- Greenland and Poole class 2: the outcome occurs under exactly two joint interventions, and
the effect of each treatment is reversed by the other (types 7 and 10 of Table 5.2). -/
def Class2 (r : ResponseType) : Prop :=
  r true true = r false false ∧ r false true = r true false ∧ r true true ≠ r false true

/-- Greenland and Poole class 3: the outcome occurs under exactly three of the four joint
interventions (types 2, 3, 5, 9 of Table 5.2). -/
def Class3 (r : ResponseType) : Prop := numCases r = 3

instance (r : ResponseType) : Decidable (Class1 r) := inferInstanceAs (Decidable (_ = _))
instance (r : ResponseType) : Decidable (Class2 r) := inferInstanceAs (Decidable (_ ∧ _))
instance (r : ResponseType) : Decidable (Class3 r) := inferInstanceAs (Decidable (_ = _))

/-- The book numbers of the three classes (What If, Section 5.3). -/
theorem class_iff_bookNumber (r : ResponseType) :
    (Class1 r ↔ bookNumber r ∈ ({8, 12, 14, 15} : Finset ℕ)) ∧
    (Class2 r ↔ bookNumber r ∈ ({7, 10} : Finset ℕ)) ∧
    (Class3 r ↔ bookNumber r ∈ ({2, 3, 5, 9} : Finset ℕ)) := by
  revert r
  refine forall_iff.2 ?_
  decide

/-- A type has individual interaction exactly when it lies in one of the three classes of
Greenland and Poole (What If, Section 5.3). -/
theorem not_noIndividualInteraction_iff_class (r : ResponseType) :
    ¬ NoIndividualInteraction r ↔ Class1 r ∨ Class2 r ∨ Class3 r := by
  revert r
  refine forall_iff.2 ?_
  decide

/-- Recoding of `A`: the labels `0` and `1` of the first treatment are switched. -/
def recodeA (r : ResponseType) : ResponseType := fun a e => r (!a) e

/-- Recoding of `E`: the labels `0` and `1` of the second treatment are switched. -/
def recodeE (r : ResponseType) : ResponseType := fun a e => r a (!e)

/-- Absence of individual interaction is invariant under recoding of `A`. -/
theorem noIndividualInteraction_recodeA (r : ResponseType) :
    NoIndividualInteraction (recodeA r) ↔ NoIndividualInteraction r := by
  revert r; refine forall_iff.2 ?_; decide

/-- Absence of individual interaction is invariant under recoding of `E`. -/
theorem noIndividualInteraction_recodeE (r : ResponseType) :
    NoIndividualInteraction (recodeE r) ↔ NoIndividualInteraction r := by
  revert r; refine forall_iff.2 ?_; decide

/-- Class 1 is invariant under recoding of `A` and of `E` (Greenland and Poole, 1988). -/
theorem class1_recode (r : ResponseType) :
    (Class1 (recodeA r) ↔ Class1 r) ∧ (Class1 (recodeE r) ↔ Class1 r) := by
  revert r; refine forall_iff.2 ?_; decide

/-- Class 2 is invariant under recoding of `A` and of `E` (Greenland and Poole, 1988). -/
theorem class2_recode (r : ResponseType) :
    (Class2 (recodeA r) ↔ Class2 r) ∧ (Class2 (recodeE r) ↔ Class2 r) := by
  revert r; refine forall_iff.2 ?_; decide

/-- Class 3 is invariant under recoding of `A` and of `E` (Greenland and Poole, 1988). -/
theorem class3_recode (r : ResponseType) :
    (Class3 (recodeA r) ↔ Class3 r) ∧ (Class3 (recodeE r) ↔ Class3 r) := by
  revert r; refine forall_iff.2 ?_; decide

/-- In contrast, the book numbering of Miettinen is not invariant under recoding: recoding `A`
sends type 6 (`1010`, only `A` matters) to type 11 (`0101`). -/
theorem bookNumber_recodeA_ofBits :
    bookNumber (ofBits true false true false) = 6 ∧
      bookNumber (recodeA (ofBits true false true false)) = 11 := by
  decide

end ResponseType

/-- A finite population of individuals for two binary treatments: nonnegative weights summing
to one and a deterministic response type for each individual. With `ι = ResponseType` and
`resp = id` this is a probability distribution over the 16 response types. -/
structure Population (ι : Type*) [Fintype ι] where
  /-- The probability mass of each individual. -/
  weight : ι → ℝ
  /-- Masses are nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Masses sum to one. -/
  weight_sum : ∑ i, weight i = 1
  /-- The response type of each individual. -/
  resp : ι → ResponseType

namespace Population

variable {ι : Type*} [Fintype ι] (P : Population ι)

/-- The counterfactual risk `p a e = Pr[Y^{a,e} = 1]`. -/
def risk (a e : Bool) : ℝ := ∑ i, P.weight i * ((P.resp i a e).toNat : ℝ)

/-- The additive interaction contrast `IC = p11 - p10 - p01 + p00` (What If, Section 5.1). -/
def interactionContrast : ℝ :=
  P.risk true true - P.risk true false - P.risk false true + P.risk false false

/-- The three equivalent forms of additive interaction (What If, Section 5.1 and Technical
Point 5.1): the effect of `A` differs across levels of `E`, the effect of `E` differs across
levels of `A`, and the joint effect is not the sum of the separate effects; each is equivalent to
a nonzero interaction contrast. -/
theorem additive_interaction_iff :
    (P.risk true true - P.risk false true ≠ P.risk true false - P.risk false false ↔
        P.interactionContrast ≠ 0) ∧
      (P.risk true true - P.risk true false ≠ P.risk false true - P.risk false false ↔
        P.interactionContrast ≠ 0) ∧
      (P.risk true true - P.risk false false ≠
          (P.risk true false - P.risk false false) + (P.risk false true - P.risk false false) ↔
        P.interactionContrast ≠ 0) := by
  unfold interactionContrast
  refine ⟨⟨fun h h' => h (by linarith), fun h h' => h (by linarith)⟩,
    ⟨fun h h' => h (by linarith), fun h h' => h (by linarith)⟩,
    ⟨fun h h' => h (by linarith), fun h h' => h (by linarith)⟩⟩

/-- Superadditive interaction (the joint effect exceeds the sum of the separate effects) is a
positive interaction contrast; subadditive interaction is a negative one (What If,
Technical Point 5.1). -/
theorem additive_interaction_iff' :
    (P.risk true true - P.risk false false >
        (P.risk true false - P.risk false false) + (P.risk false true - P.risk false false) ↔
      0 < P.interactionContrast) ∧
    (P.risk true true - P.risk false false <
        (P.risk true false - P.risk false false) + (P.risk false true - P.risk false false) ↔
      P.interactionContrast < 0) := by
  unfold interactionContrast
  constructor <;> constructor <;> intro h <;> linarith

/-- The multiplicative interaction contrast `p11 * p00 - p10 * p01` (What If, Technical
Point 5.1, cleared of denominators). -/
def multInteraction : ℝ :=
  P.risk true true * P.risk false false - P.risk true false * P.risk false true

/-- For a positive reference risk `p00`, the risk ratio form of Technical Point 5.1 differs from
the product form by the factor `1 / p00 ^ 2`:
`p11 / p00 - (p10 / p00) * (p01 / p00) = (p11 * p00 - p10 * p01) / p00 ^ 2`. -/
theorem ratio_sub_ratio_mul_ratio (h : 0 < P.risk false false) :
    P.risk true true / P.risk false false -
        P.risk true false / P.risk false false * (P.risk false true / P.risk false false) =
      P.multInteraction / P.risk false false ^ 2 := by
  unfold multInteraction
  field_simp

/-- Interaction on the multiplicative scale (What If, Technical Point 5.1): for a positive
reference risk `p00`, the joint risk ratio `p11 / p00` differs from the product of the separate
risk ratios `(p10 / p00) * (p01 / p00)` exactly when `p11 * p00 ≠ p10 * p01`; the interaction
is supermultiplicative (`>`) exactly when the contrast is positive and submultiplicative (`<`)
exactly when it is negative. -/
theorem multiplicative_interaction_iff (h : 0 < P.risk false false) :
    (P.risk true true / P.risk false false ≠
        P.risk true false / P.risk false false * (P.risk false true / P.risk false false) ↔
      P.multInteraction ≠ 0) ∧
    (P.risk true true / P.risk false false >
        P.risk true false / P.risk false false * (P.risk false true / P.risk false false) ↔
      0 < P.multInteraction) ∧
    (P.risk true true / P.risk false false <
        P.risk true false / P.risk false false * (P.risk false true / P.risk false false) ↔
      P.multInteraction < 0) := by
  have key := P.ratio_sub_ratio_mul_ratio h
  have h2 : 0 < P.risk false false ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Ne, ← sub_eq_zero, key, div_eq_zero_iff, not_or]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', h2.ne'⟩⟩
  · rw [gt_iff_lt, ← sub_pos, key, div_pos_iff_of_pos_right h2]
  · rw [← sub_neg, key, div_lt_iff₀ h2, zero_mul]

/-- No interaction on both scales forces a null effect (What If, Technical Point 5.1): if there
is no additive interaction (`IC = 0`) and no multiplicative interaction
(`p11 * p00 = p10 * p01`), then `(p10 - p00) * (p01 - p00) = 0`, so `A` has no effect at
`E = 0` or `E` has no effect at `A = 0`. Writing `p10 = c + x`, `p01 = c + y`, additivity gives
`p11 = c + x + y` and multiplicativity then reads `x * y = 0`. No positivity is needed. -/
theorem no_effect_of_no_additive_no_multiplicative (hA : P.interactionContrast = 0)
    (hM : P.risk true true * P.risk false false = P.risk true false * P.risk false true) :
    (P.risk true false - P.risk false false) * (P.risk false true - P.risk false false) = 0 := by
  unfold interactionContrast at hA
  linear_combination P.risk false false * hA - hM

/-- The interaction contrast is the population mean of the individual contrasts. -/
theorem interactionContrast_eq_sum :
    P.interactionContrast = ∑ i, P.weight i * ((ResponseType.indContrast (P.resp i) : ℤ) : ℝ) := by
  simp only [interactionContrast, risk, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ResponseType.indContrast]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- If every individual of positive mass has a type without individual interaction (types 1, 4,
6, 11, 13, 16), there is no additive interaction (What If, Section 5.3). -/
theorem interactionContrast_eq_zero_of_noInteraction
    (h : ∀ i, 0 < P.weight i → ResponseType.NoIndividualInteraction (P.resp i)) :
    P.interactionContrast = 0 := by
  rw [interactionContrast_eq_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases (P.weight_nonneg i).lt_or_eq with hi | hi
  · rw [(ResponseType.noIndividualInteraction_iff_indContrast _).1 (h i hi)]
    simp
  · rw [← hi, zero_mul]

/-- A nonzero additive interaction contrast forces positive mass on some type with individual
interaction, that is, on one of the Greenland and Poole classes (types 8, 12, 14, 15; 7, 10;
or 2, 3, 5, 9) (What If, Section 5.3). -/
theorem exists_interacting_of_interactionContrast_ne_zero (h : P.interactionContrast ≠ 0) :
    ∃ i, 0 < P.weight i ∧ ¬ ResponseType.NoIndividualInteraction (P.resp i) := by
  by_contra hcon
  exact h (P.interactionContrast_eq_zero_of_noInteraction fun i hi => by
    by_contra hni
    exact hcon ⟨i, hi, hni⟩)

end Population

/-- The population with mass `1/2` on type 7 (`1001`) and mass `1/2` on type 10 (`0110`) of
Table 5.2: both types interact, but their deviations from additivity cancel. -/
noncomputable def cancellationPopulation : Population Bool where
  weight _ := 1 / 2
  weight_nonneg _ := by norm_num
  weight_sum := by simp
  resp b := if b then ResponseType.ofBits true false false true
    else ResponseType.ofBits false true true false

/-- The converse of `Population.exists_interacting_of_interactionContrast_ne_zero` fails:
in `cancellationPopulation` every individual has a type with individual interaction (types 7
and 10) and positive mass, yet the additive interaction contrast is zero (What If, Section 5.3:
"an equal proportion of individuals of types 7 and 10"). -/
theorem cancellation_example :
    (∀ i, 0 < cancellationPopulation.weight i ∧
        ¬ ResponseType.NoIndividualInteraction (cancellationPopulation.resp i)) ∧
      cancellationPopulation.interactionContrast = 0 := by
  refine ⟨fun i => ⟨by norm_num [cancellationPopulation], ?_⟩, ?_⟩
  · cases i <;> decide
  · simp [Population.interactionContrast, Population.risk, cancellationPopulation,
      ResponseType.ofBits]

end Interaction

end CausalInference
