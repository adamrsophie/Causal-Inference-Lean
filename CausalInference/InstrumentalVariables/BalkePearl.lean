/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.ResponseTypes
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# The sharp bounds of Balke and Pearl

Sharp bounds on the average causal effect in the binary instrumental variable model, from the
observed table `p_{yx.z} = P(y, x | z)`: Balke and Pearl (1997, *Bounds on treatment effects from
studies with imperfect compliance*), presented in Pearl (2009, *Causality*, 2nd edition,
Section 8.2.3, equations (8.14a) and (8.14b)). The model is the response-type model of
`CausalInference.IVResponse`: a weight `q` on the sixteen compliance and response types, the
observable `obs q = R q` and the effect `ace q`.

## Main definitions

* `CausalInference.IVResponse.lowerTerm`, `IVResponse.upperTerm`: the eight terms of (8.14a) and
  of (8.14b).
* `IVResponse.lower`, `IVResponse.upper`: their maximum and minimum, the Balke and Pearl bounds.
* `IVResponse.BinaryIVConstraints`: nonnegativity, normalization of each instrument arm, and the
  four instrumental inequalities (8.21).

## Main results

* `IVResponse.lowerTerm_le_ace`, `IVResponse.ace_le_upperTerm`: each of the sixteen terms is a
  valid bound for every weight `q`; `IVResponse.ace_mem_Icc`: `ace q ∈ [lower, upper]`.
* `IVResponse.binaryIVConstraints_obs`: every induced observable satisfies the constraints.
* `IVResponse.exists_weights_ace_eq_lower`, `IVResponse.exists_weights_ace_eq_upper`: for every
  table satisfying the constraints both endpoints are attained by weights inducing that table.
* `IVResponse.identifiedSet_ace`: sharpness. For a table satisfying the constraints the
  identified set of the average causal effect is exactly `[lower p, upper p]`;
  `IVResponse.identifiedSet_ace_obs` states it at the observable of any weight.
* `IVResponse.lowerTerm_zero_eq`, `IVResponse.upperTerm_zero_eq`: the first terms are the
  natural bounds (8.17) of Robins (1989) and Manski (1990).
* `IVModel.ate_mem_Icc_balkePearl`: for an `IVModel` with binary outcomes satisfying exclusion
  and instrument independence, the average treatment effect lies between the Balke and Pearl
  bounds of its observed conditional law.
* Numerical examples of Pearl (2009, Chapter 8), each checked by `norm_num` from the printed
  table: Table 8.1 (`identifiedSet_table81`: point identification at `0.55` despite `45%`
  noncompliance), the cholestyramine data of Section 8.2.6 (`identifiedSet_lipid`:
  `[0.392, 0.780]`), the PeptAid data of Section 8.3 (`identifiedSet_pepAid`:
  `[-0.23, -0.15]`, with `itt_pepAid_not_mem` and `wald_pepAid_not_mem`: the intent to treat
  estimate `0.45` and the Wald estimate `-15/11` lie outside it), and the vitamin A data of
  Table 8.2 (`lower_vitaminA`, `upper_vitaminA`).

## Implementation notes

Sharpness is proved by an explicit construction, not by linear programming duality. Given a
table `p` satisfying the constraints, the always-taker share `t` is set to the largest value
compatible with `p`. For the lower bound, every never-taker gets treated outcome `y0` and every
always-taker untreated outcome `y1`; the treated-outcome mass `u3` of the always-takers is as
large as possible and the untreated-outcome mass `v0` of the never-takers as small as possible
(both given `t`); the masses of the compliers and defiers are then fixed by `p`. The two
potential outcomes are coupled within each compliance type (`exists_weights_of_margins`). The
upper bound follows by exchanging the two outcome values (`swapWeights`).

The printed text of Sections 8.2.6 and 8.3 calls the bounds `[0.392, 0.780]` and
`[-0.23, -0.15]` bounds on "ETT"; they are bounds on the average causal effect, as stated here.
The vitamin A bounds are printed as `[-0.19, 0.01]`; computed from the counts of Table 8.2 they
are `-0.1946...` and `0.0053...`, of which the printed values are roundings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace IVResponse

/-! ### The sixteen terms -/

/-- The eight lower terms of (8.14a), in Pearl's notation `p_{yx.z} = p y x z` (with `0` for
`false` and `1` for `true`): `p11.1 + p00.0 - 1`, `p11.0 + p00.1 - 1`,
`p11.0 - p11.1 - p10.1 - p01.0 - p10.0`, `p11.1 - p11.0 - p10.0 - p01.1 - p10.1`,
`-p01.1 - p10.1`, `-p01.0 - p10.0`, `p00.1 - p01.1 - p10.1 - p01.0 - p00.0` and
`p00.0 - p01.0 - p10.0 - p01.1 - p00.1`. -/
def lowerTerm (p : Observable) : Fin 8 → ℝ := ![
  p true true true + p false false false - 1,
  p true true false + p false false true - 1,
  p true true false - p true true true - p true false true - p false true false -
    p true false false,
  p true true true - p true true false - p true false false - p false true true -
    p true false true,
  -p false true true - p true false true,
  -p false true false - p true false false,
  p false false true - p false true true - p true false true - p false true false -
    p false false false,
  p false false false - p false true false - p true false false - p false true true -
    p false false true]

/-- The eight upper terms of (8.14b): `1 - p01.1 - p10.0`, `1 - p01.0 - p10.1`,
`-p01.0 + p01.1 + p00.1 + p11.0 + p00.0`, `-p01.1 + p11.1 + p00.1 + p01.0 + p00.0`,
`p11.1 + p00.1`, `p11.0 + p00.0`, `-p10.1 + p11.1 + p00.1 + p11.0 + p10.0` and
`-p10.0 + p11.0 + p00.0 + p11.1 + p10.1`. -/
def upperTerm (p : Observable) : Fin 8 → ℝ := ![
  1 - p false true true - p true false false,
  1 - p false true false - p true false true,
  -p false true false + p false true true + p false false true + p true true false +
    p false false false,
  -p false true true + p true true true + p false false true + p false true false +
    p false false false,
  p true true true + p false false true,
  p true true false + p false false false,
  -p true false true + p true true true + p false false true + p true true false +
    p true false false,
  -p true false false + p true true false + p false false false + p true true true +
    p true false true]

/-- The Balke and Pearl lower bound (8.14a): the maximum of the eight lower terms. -/
def lower (p : Observable) : ℝ :=
  max (max (max (lowerTerm p 0) (lowerTerm p 1)) (max (lowerTerm p 2) (lowerTerm p 3)))
    (max (max (lowerTerm p 4) (lowerTerm p 5)) (max (lowerTerm p 6) (lowerTerm p 7)))

/-- The Balke and Pearl upper bound (8.14b): the minimum of the eight upper terms. -/
def upper (p : Observable) : ℝ :=
  min (min (min (upperTerm p 0) (upperTerm p 1)) (min (upperTerm p 2) (upperTerm p 3)))
    (min (min (upperTerm p 4) (upperTerm p 5)) (min (upperTerm p 6) (upperTerm p 7)))

theorem lowerTerm_le_lower (p : Observable) (i : Fin 8) : lowerTerm p i ≤ lower p := by
  simp only [lower, le_max_iff]
  fin_cases i <;> simp

theorem upper_le_upperTerm (p : Observable) (i : Fin 8) : upper p ≤ upperTerm p i := by
  simp only [upper, min_le_iff]
  fin_cases i <;> simp

theorem lower_le_iff {p : Observable} {c : ℝ} : lower p ≤ c ↔ ∀ i, lowerTerm p i ≤ c := by
  refine ⟨fun h i ↦ (lowerTerm_le_lower p i).trans h, fun h ↦ ?_⟩
  simp only [lower, max_le_iff]
  exact ⟨⟨⟨h 0, h 1⟩, h 2, h 3⟩, ⟨h 4, h 5⟩, h 6, h 7⟩

theorem le_upper_iff {p : Observable} {c : ℝ} : c ≤ upper p ↔ ∀ i, c ≤ upperTerm p i := by
  refine ⟨fun h i ↦ h.trans (upper_le_upperTerm p i), fun h ↦ ?_⟩
  simp only [upper, le_min_iff]
  exact ⟨⟨⟨h 0, h 1⟩, h 2, h 3⟩, ⟨h 4, h 5⟩, h 6, h 7⟩

/-- A bound is equal to `v` when one term equals `v` and all terms are at most `v`. -/
theorem lower_eq_of {p : Observable} {v : ℝ} (i : Fin 8) (hi : lowerTerm p i = v)
    (h : ∀ j, lowerTerm p j ≤ v) : lower p = v :=
  le_antisymm (lower_le_iff.2 h) (hi ▸ lowerTerm_le_lower p i)

/-- The upper bound is equal to `v` when one term equals `v` and all terms are at least `v`. -/
theorem upper_eq_of {p : Observable} {v : ℝ} (i : Fin 8) (hi : upperTerm p i = v)
    (h : ∀ j, v ≤ upperTerm p j) : upper p = v :=
  le_antisymm (hi ▸ upper_le_upperTerm p i) (le_upper_iff.2 h)

/-! ### Validity -/

/-- The sixteen weights are nonnegative. -/
theorem weights_nonneg (q : Weights) :
    0 ≤ q (0, 0) ∧ 0 ≤ q (0, 1) ∧ 0 ≤ q (0, 2) ∧ 0 ≤ q (0, 3) ∧ 0 ≤ q (1, 0) ∧ 0 ≤ q (1, 1) ∧
      0 ≤ q (1, 2) ∧ 0 ≤ q (1, 3) ∧ 0 ≤ q (2, 0) ∧ 0 ≤ q (2, 1) ∧ 0 ≤ q (2, 2) ∧
      0 ≤ q (2, 3) ∧ 0 ≤ q (3, 0) ∧ 0 ≤ q (3, 1) ∧ 0 ≤ q (3, 2) ∧ 0 ≤ q (3, 3) :=
  ⟨q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _,
    q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _, q.nonneg _,
    q.nonneg _, q.nonneg _⟩

/-- **Validity of the lower terms of (8.14a).** Each of the eight lower terms, evaluated at the
observable induced by any weight `q`, is at most the average causal effect `ace q`. -/
theorem lowerTerm_le_ace (q : Weights) (i : Fin 8) : lowerTerm (obs q) i ≤ ace q := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    weights_nonneg q
  have hs := sum_weights q
  fin_cases i <;>
    simp [lowerTerm, obs_fff, obs_fft, obs_ftf, obs_ftt, obs_tff, obs_tft, obs_ttf, obs_ttt,
      ace_eq] <;> linarith

/-- **Validity of the upper terms of (8.14b).** The average causal effect `ace q` is at most
each of the eight upper terms evaluated at the observable induced by `q`. -/
theorem ace_le_upperTerm (q : Weights) (i : Fin 8) : ace q ≤ upperTerm (obs q) i := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    weights_nonneg q
  have hs := sum_weights q
  fin_cases i <;>
    simp [upperTerm, obs_fff, obs_fft, obs_ftf, obs_ftt, obs_tff, obs_tft, obs_ttf, obs_ttt,
      ace_eq] <;> linarith

/-- **The Balke and Pearl bounds are valid** (Pearl 2009, (8.14a) and (8.14b)): for every
weight `q` on the sixteen compliance and response types, the average causal effect lies between
the maximum of the lower terms and the minimum of the upper terms of the induced observable. -/
theorem ace_mem_Icc (q : Weights) : ace q ∈ Icc (lower (obs q)) (upper (obs q)) :=
  ⟨lower_le_iff.2 (lowerTerm_le_ace q), le_upper_iff.2 (ace_le_upperTerm q)⟩

/-! ### The constraints on an observable table -/

/-- Linear constraints on a table `p y x z`: nonnegative entries, each instrument arm summing to
one, and the four instrumental inequalities (8.21) of Pearl (2009):
`p00.0 + p10.1 ≤ 1`, `p01.0 + p11.1 ≤ 1`, `p10.0 + p00.1 ≤ 1` and `p11.0 + p01.1 ≤ 1`.
Every induced observable satisfies them (`binaryIVConstraints_obs`); conversely every table
satisfying them is induced by some weight (`exists_weights_ace_eq_lower`). -/
structure BinaryIVConstraints (p : Observable) : Prop where
  nonneg : ∀ y x z, 0 ≤ p y x z
  sum_eq_one : ∀ z, p false false z + p false true z + p true false z + p true true z = 1
  ineq₁ : p false false false + p true false true ≤ 1
  ineq₂ : p false true false + p true true true ≤ 1
  ineq₃ : p true false false + p false false true ≤ 1
  ineq₄ : p true true false + p false true true ≤ 1

/-- Every observable induced by a weight satisfies the constraints. The four inequalities are
the instrumental inequalities (8.21), obtained in Pearl (2009) by requiring each upper term of
(8.14b) to be at least the corresponding lower term of (8.14a). -/
theorem binaryIVConstraints_obs (q : Weights) : BinaryIVConstraints (obs q) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    weights_nonneg q
  have hs := sum_weights q
  refine ⟨obs_nonneg q, obs_sum q, ?_, ?_, ?_, ?_⟩ <;>
    simp only [obs_fff, obs_fft, obs_ftf, obs_ftt, obs_tff, obs_tft, obs_ttf, obs_ttt] <;>
    linarith

/-! ### A coupling of the two potential outcomes within each compliance type -/

/-- The weights of the four response types inside a compliance type of total weight `a`, with
`P(Y 1 = 1) = u` and `P(Y 0 = 1) = v` inside the type: the maximal coupling, which puts weight
`min u v` on "always recover". -/
noncomputable def cellWeights (a u v : ℝ) : Fin 4 → ℝ :=
  ![a - u - v + min u v, u - min u v, v - min u v, min u v]

/-- **Weights with prescribed margins.** Given compliance shares `a j` summing to one and, for
each compliance type, values `0 ≤ u j ≤ a j` and `0 ≤ v j ≤ a j`, there is a weight `q` whose
compliance type `j` has total weight `a j`, treated-outcome mass `q j1 + q j3 = u j` and
untreated-outcome mass `q j2 + q j3 = v j`. -/
theorem exists_weights_of_margins (a u v : Fin 4 → ℝ) (hu : ∀ j, 0 ≤ u j ∧ u j ≤ a j)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ a j) (ha : a 0 + a 1 + a 2 + a 3 = 1) :
    ∃ q : Weights, ∀ j, q (j, 0) + q (j, 1) + q (j, 2) + q (j, 3) = a j ∧
      q (j, 1) + q (j, 3) = u j ∧ q (j, 2) + q (j, 3) = v j := by
  refine ⟨⟨fun s ↦ cellWeights (a s.1) (u s.1) (v s.1) s.2, ?_, ?_⟩, fun j ↦ ?_⟩
  · rintro ⟨j, k⟩
    obtain ⟨hu0, hua⟩ := hu j
    obtain ⟨hv0, hva⟩ := hv j
    rcases le_total (u j) (v j) with h | h
    · fin_cases k <;> simp [cellWeights, min_eq_left h] <;> linarith
    · fin_cases k <;> simp [cellWeights, min_eq_right h] <;> linarith
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_four, cellWeights]
    simp
    linarith
  · simp only [cellWeights]
    refine ⟨?_, ?_, ?_⟩ <;> simp
    ring

/-- The minimum of six reals, as an opaque witness with its defining properties. -/
theorem exists_min_six (a b c d e f : ℝ) :
    ∃ m, m ≤ a ∧ m ≤ b ∧ m ≤ c ∧ m ≤ d ∧ m ≤ e ∧ m ≤ f ∧
      (m = a ∨ m = b ∨ m = c ∨ m = d ∨ m = e ∨ m = f) := by
  refine ⟨min (min (min a b) (min c d)) (min e f), by simp, by simp, by simp, by simp, by simp,
    by simp, ?_⟩
  rcases min_choice (min (min a b) (min c d)) (min e f) with h5 | h5 <;> rw [h5]
  · rcases min_choice (min a b) (min c d) with h4 | h4 <;> rw [h4]
    · rcases min_choice a b with h1 | h1 <;> rw [h1] <;> simp
    · rcases min_choice c d with h2 | h2 <;> rw [h2] <;> simp
  · rcases min_choice e f with h3 | h3 <;> rw [h3] <;> simp

/-- The minimum of three reals, as an opaque witness. -/
theorem exists_min_three (a b c : ℝ) :
    ∃ m, m ≤ a ∧ m ≤ b ∧ m ≤ c ∧ (m = a ∨ m = b ∨ m = c) := by
  refine ⟨min (min a b) c, by simp, by simp, by simp, ?_⟩
  rcases min_choice (min a b) c with h2 | h2 <;> rw [h2]
  · rcases min_choice a b with h1 | h1 <;> rw [h1] <;> simp
  · simp

/-- The maximum of three reals, as an opaque witness. -/
theorem exists_max_three (a b c : ℝ) :
    ∃ m, a ≤ m ∧ b ≤ m ∧ c ≤ m ∧ (m = a ∨ m = b ∨ m = c) := by
  refine ⟨max (max a b) c, by simp, by simp, by simp, ?_⟩
  rcases max_choice (max a b) c with h2 | h2 <;> rw [h2]
  · rcases max_choice a b with h1 | h1 <;> rw [h1] <;> simp
  · simp

/-! ### Attaining the lower bound -/

/-- The value of the constructed weight is at most the lower bound. Here `t` is the minimum of
the six upper limits on the always-taker share, `u3` the largest treated-outcome mass of the
always-takers and `v0` the smallest untreated-outcome mass of the never-takers compatible with
`t`; the value of the construction is `p11.1 + p11.0 - u3 - p10.0 - p10.1 + v0 - t`. -/
theorem construction_le_lower {p : Observable} (hp : BinaryIVConstraints p) {t u3 v0 : ℝ}
    (ht : t = p true true false + p false true false ∨ t = p true true true + p false true true ∨
      t = p true true true + p false true false ∨ t = p true true false + p false true true ∨
      t = p true true true + p false true true - p true false false + p true false true ∨
      t = p true true false + p false true false + p true false false - p true false true)
    (hu : u3 = t ∨ u3 = p true true false ∨ u3 = p true true true)
    (hv : v0 = 0 ∨ v0 = t - (p true true true + p false true true) + p true false false ∨
      v0 = t - (p true true false + p false true false) + p true false true) :
    p true true true + p true true false - u3 - p true false false - p true false true + v0 - t ≤
      lower p := by
  have n := hp.nonneg
  have n1 := n false false false; have n2 := n false false true; have n3 := n false true false
  have n4 := n false true true; have n5 := n true false false; have n6 := n true false true
  have n7 := n true true false; have n8 := n true true true
  have s0 := hp.sum_eq_one false
  have s1 := hp.sum_eq_one true
  have i1 := hp.ineq₁; have i2 := hp.ineq₂; have i3 := hp.ineq₃; have i4 := hp.ineq₄
  by_contra hlt
  rw [not_le] at hlt
  have l := fun i ↦ (lowerTerm_le_lower p i).trans_lt hlt
  have l0 := l 0; have l1 := l 1; have l2 := l 2; have l3 := l 3
  have l4 := l 4; have l5 := l 5; have l6 := l 6; have l7 := l 7
  simp only [lowerTerm, Matrix.cons_val] at l0 l1 l2 l3 l4 l5 l6 l7
  clear l hlt n
  rcases ht with h | h | h | h | h | h <;> rcases hu with h' | h' | h' <;>
    rcases hv with h'' | h'' | h'' <;> subst h h' h'' <;> linarith

/-- **The lower bound is attained.** For every table `p` satisfying the constraints there is a
weight `q` inducing `p` whose average causal effect equals the Balke and Pearl lower bound
`lower p`. In particular every such table is induced by some weight. -/
theorem exists_weights_ace_eq_lower {p : Observable} (hp : BinaryIVConstraints p) :
    ∃ q : Weights, obs q = p ∧ ace q = lower p := by
  have n := hp.nonneg
  have n1 := n false false false; have n2 := n false false true; have n3 := n false true false
  have n4 := n false true true; have n5 := n true false false; have n6 := n true false true
  have n7 := n true true false; have n8 := n true true true
  have s0 := hp.sum_eq_one false
  have s1 := hp.sum_eq_one true
  have i1 := hp.ineq₁; have i2 := hp.ineq₂; have i3 := hp.ineq₃; have i4 := hp.ineq₄
  -- the always-taker share
  obtain ⟨t, t1, t2, t3, t4, t5, t6, ht⟩ := exists_min_six
    (p true true false + p false true false) (p true true true + p false true true)
    (p true true true + p false true false) (p true true false + p false true true)
    (p true true true + p false true true - p true false false + p true false true)
    (p true true false + p false true false + p true false false - p true false true)
  -- the treated-outcome mass of the always-takers
  obtain ⟨u3, u1, u2, u4, hu⟩ := exists_min_three t (p true true false) (p true true true)
  -- the untreated-outcome mass of the never-takers
  obtain ⟨v0, v1, v2, v4, hv⟩ := exists_max_three 0
    (t - (p true true true + p false true true) + p true false false)
    (t - (p true true false + p false true false) + p true false true)
  have ht0 : 0 ≤ t := by rcases ht with h | h | h | h | h | h <;> linarith
  have ht1 : p true true false + p false true false + p true true true + p false true true - 1 ≤
      t := by rcases ht with h | h | h | h | h | h <;> linarith
  have hu0 : 0 ≤ u3 := by rcases hu with h | h | h <;> linarith
  have hu1 : t - p false true false ≤ u3 := by rcases hu with h | h | h <;> linarith
  have hu2 : t - p false true true ≤ u3 := by rcases hu with h | h | h <;> linarith
  have hv0 : v0 ≤ 1 - (p true true false + p false true false) -
      (p true true true + p false true true) + t := by
    rcases hv with h | h | h <;> linarith
  have hv1 : v0 ≤ p true false false := by rcases hv with h | h | h <;> linarith
  have hv2 : v0 ≤ p true false true := by rcases hv with h | h | h <;> linarith
  obtain ⟨q, hq⟩ := exists_weights_of_margins
    ![1 - (p true true false + p false true false) - (p true true true + p false true true) + t,
      p true true true + p false true true - t, p true true false + p false true false - t, t]
    ![0, p true true true - u3, p true true false - u3, u3]
    ![v0, p true false false - v0, p true false true - v0, t]
    (by intro j; fin_cases j <;> refine ⟨?_, ?_⟩ <;> simp <;> linarith)
    (by intro j; fin_cases j <;> refine ⟨?_, ?_⟩ <;> simp <;> linarith)
    (by simp)
  obtain ⟨a0, b0, c0⟩ := hq 0
  obtain ⟨a1, b1, c1⟩ := hq 1
  obtain ⟨a2, b2, c2⟩ := hq 2
  obtain ⟨a3, b3, c3⟩ := hq 3
  simp only [Matrix.cons_val] at a0 b0 c0 a1 b1 c1 a2 b2 c2 a3 b3 c3
  have hobs : obs q = p := by
    funext y x z
    cases y <;> cases x <;> cases z <;>
      simp only [obs_fff, obs_fft, obs_ftf, obs_ftt, obs_tff, obs_tft, obs_ttf, obs_ttt] <;>
      linarith
  refine ⟨q, hobs, le_antisymm ?_ (hobs ▸ (ace_mem_Icc q).1)⟩
  have hace : ace q = p true true true + p true true false - u3 - p true false false -
      p true false true + v0 - t := by
    rw [ace_eq]; linarith
  rw [hace]
  exact construction_le_lower hp ht hu (by rcases hv with h | h | h <;> simp [h])

/-! ### Attaining the upper bound, by exchanging the outcome values -/

/-- The table with the two outcome values exchanged: `(swapY p) y x z = p (!y) x z`. -/
def swapY (p : Observable) : Observable := fun y x z ↦ p (!y) x z

@[simp] theorem swapY_swapY (p : Observable) : swapY (swapY p) = p := by
  funext y x z; simp [swapY]

theorem BinaryIVConstraints.swapY {p : Observable} (hp : BinaryIVConstraints p) :
    BinaryIVConstraints (IVResponse.swapY p) where
  nonneg y x z := hp.nonneg (!y) x z
  sum_eq_one z := by have := hp.sum_eq_one z; simp only [IVResponse.swapY]; simp; linarith
  ineq₁ := by have := hp.ineq₃; simp only [IVResponse.swapY]; simp; linarith
  ineq₂ := by have := hp.ineq₄; simp only [IVResponse.swapY]; simp; linarith
  ineq₃ := by have := hp.ineq₁; simp only [IVResponse.swapY]; simp; linarith
  ineq₄ := by have := hp.ineq₂; simp only [IVResponse.swapY]; simp; linarith

/-- Exchanging the outcome values on response types: never recover and always recover are
exchanged, and so are helped and hurt. -/
def revType : Fin 4 → Fin 4 := ![3, 2, 1, 0]

/-- The weight with the outcome values exchanged: `(swapWeights q) (j, k) = q (j, revType k)`. -/
def swapWeights (q : Weights) : Weights where
  mass s := q (s.1, revType s.2)
  nonneg s := q.nonneg _
  sum_eq_one := by
    have := sum_weights q
    simp only [Fintype.sum_prod_type, Fin.sum_univ_four, revType]
    simp
    linarith

theorem swapWeights_apply (q : Weights) (j k : Fin 4) :
    swapWeights q (j, k) = q (j, revType k) := rfl

theorem obs_swapWeights (q : Weights) : obs (swapWeights q) = swapY (obs q) := by
  funext y x z
  cases y <;> cases x <;> cases z <;>
    simp only [swapY, Bool.not_false, Bool.not_true, obs_fff, obs_fft, obs_ftf, obs_ftt, obs_tff,
      obs_tft, obs_ttf, obs_ttt, swapWeights_apply, revType] <;> simp <;> ring

theorem ace_swapWeights (q : Weights) : ace (swapWeights q) = -ace q := by
  simp only [ace_eq, swapWeights_apply, revType]; simp; ring

theorem upperTerm_eq_neg (p : Observable) (i : Fin 8) :
    upperTerm p i = -lowerTerm (swapY p) i := by
  fin_cases i <;> simp [upperTerm, lowerTerm, swapY] <;> ring

/-- The upper bound is minus the lower bound of the table with the outcome values exchanged. -/
theorem upper_eq_neg_lower (p : Observable) : upper p = -lower (swapY p) := by
  simp only [upper, upperTerm_eq_neg, lower, min_neg_neg]

/-- **The upper bound is attained.** For every table `p` satisfying the constraints there is a
weight `q` inducing `p` whose average causal effect equals the Balke and Pearl upper bound
`upper p`. -/
theorem exists_weights_ace_eq_upper {p : Observable} (hp : BinaryIVConstraints p) :
    ∃ q : Weights, obs q = p ∧ ace q = upper p := by
  obtain ⟨q, hq, hace⟩ := exists_weights_ace_eq_lower hp.swapY
  exact ⟨swapWeights q, by rw [obs_swapWeights, hq, swapY_swapY],
    by rw [ace_swapWeights, hace, upper_eq_neg_lower]⟩

/-- Every table satisfying the constraints is induced by some weight. -/
theorem exists_obs_eq {p : Observable} (hp : BinaryIVConstraints p) : ∃ q : Weights, obs q = p :=
  (exists_weights_ace_eq_lower hp).imp fun _ h ↦ h.1

/-! ### The identified set -/

/-- The mixture `a q + b q'` of two weights, for `a, b ≥ 0` with `a + b = 1`. -/
def mixWeights (q q' : Weights) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Weights where
  mass s := a * q s + b * q' s
  nonneg s := add_nonneg (mul_nonneg ha (q.nonneg s)) (mul_nonneg hb (q'.nonneg s))
  sum_eq_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, q.sum_eq_one,
      q'.sum_eq_one, mul_one, mul_one, hab]

theorem obs_mixWeights (q q' : Weights) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (y x z : Bool) :
    obs (mixWeights q q' ha hb hab) y x z = a * obs q y x z + b * obs q' y x z := by
  simp only [obs, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  split_ifs <;> simp [mixWeights]

theorem ace_mixWeights (q q' : Weights) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ace (mixWeights q q' ha hb hab) = a * ace q + b * ace q' := by
  simp only [ace, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [mixWeights]
  change a * q (j, 1) + b * q' (j, 1) - (a * q (j, 2) + b * q' (j, 2)) = _
  ring

/-- **Sharpness of the Balke and Pearl bounds** (Balke and Pearl 1997; Pearl 2009, Section
8.2.3). For every table `p` satisfying the constraints (nonnegativity, normalization and the
instrumental inequalities (8.21)), the identified set of the average causal effect, over all
weights on the sixteen compliance and response types inducing `p`, is exactly the interval
`[lower p, upper p]` between (8.14a) and (8.14b). Both endpoints are attained
(`exists_weights_ace_eq_lower`, `exists_weights_ace_eq_upper`) and every intermediate value is
attained by a mixture of the two endpoint weights. -/
theorem identifiedSet_ace {p : Observable} (hp : BinaryIVConstraints p) :
    identifiedSet (Set.univ : Set Weights) obs ace p = Icc (lower p) (upper p) := by
  ext c
  constructor
  · rintro ⟨q, ⟨-, rfl⟩, rfl⟩
    exact ace_mem_Icc q
  · intro hc
    obtain ⟨qL, hqL, hL⟩ := exists_weights_ace_eq_lower hp
    obtain ⟨qU, hqU, hU⟩ := exists_weights_ace_eq_upper hp
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := Manski.exists_combo_of_mem_Icc hc
    refine mem_identifiedSet.2 ⟨mixWeights qL qU ha hb hab, mem_univ _, ?_, ?_⟩
    · funext y x z
      rw [obs_mixWeights, hqL, hqU, ← add_mul, hab, one_mul]
    · rw [ace_mixWeights, hL, hU]

/-- Sharpness at the observable of any weight `q`: the identified set at `obs q` is
`[lower (obs q), upper (obs q)]`. -/
theorem identifiedSet_ace_obs (q : Weights) :
    identifiedSet (Set.univ : Set Weights) obs ace (obs q) =
      Icc (lower (obs q)) (upper (obs q)) :=
  identifiedSet_ace (binaryIVConstraints_obs q)

/-! ### The natural bounds -/

/-- The first lower term is the natural lower bound (8.17) of Robins (1989) and Manski (1990):
`p11.1 + p00.0 - 1 = P(y1 | z1) - P(y1 | z0) - P(y1, x0 | z1) - P(y0, x1 | z0)` when the arm
`z0` sums to one. With `lo = 0`, `hi = 1` it is `IVBounds.lowerBound` of `Bounds.lean`. -/
theorem lowerTerm_zero_eq {p : Observable}
    (h : p false false false + p false true false + p true false false + p true true false = 1) :
    lowerTerm p 0 = (p true false true + p true true true) -
      (p true false false + p true true false) - p true false true - p false true false := by
  simp only [lowerTerm, Matrix.cons_val]; linarith

/-- The first upper term is the natural upper bound (8.17):
`1 - p01.1 - p10.0 = P(y1 | z1) - P(y1 | z0) + P(y0, x0 | z1) + P(y1, x1 | z0)` when the arm
`z1` sums to one. -/
theorem upperTerm_zero_eq {p : Observable}
    (h : p false false true + p false true true + p true false true + p true true true = 1) :
    upperTerm p 0 = (p true false true + p true true true) -
      (p true false false + p true true false) + p false false true + p true true false := by
  simp only [upperTerm, Matrix.cons_val]; linarith

end IVResponse

/-! ### The bounds for an `IVModel` with binary outcomes -/

namespace IVModel

open IVResponse

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- The observed conditional law `P(Dobs = x, Yobs = y | Z = z)` of a model, as a table (with
`y` coded `0` or `1`). -/
noncomputable def obsTable (μ : Measure Ω) : Observable := fun y x z ↦
  (μ[|M.instrumentEq z]).real {ω | M.Dobs ω = x ∧ M.Yobs ω = boolToReal y}

/-- Under exclusion, instrument independence, binary outcomes and positive instrument
probabilities, the observed table is induced by the law of the response type. -/
theorem obsTable_eq [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hB : M.BinaryOutcome)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) :
    M.obsTable μ = obs (M.responseLaw μ) := by
  funext y x z
  cases z
  · exact M.obs_responseLaw hE hI hB h₀ y x
  · exact M.obs_responseLaw hE hI hB h₁ y x

/-- **Balke and Pearl bounds for an `IVModel`.** Assume the exclusion restriction, instrument
independence, binary potential outcomes and `P(Z = z) ≠ 0` for both `z`. Then the average
treatment effect `E[Y z 1 - Y z 0]` lies between the Balke and Pearl bounds (8.14a), (8.14b) of
the observed conditional law `P(Dobs = x, Yobs = y | Z = z)`. Monotonicity is not assumed. -/
theorem ate_mem_Icc_balkePearl [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hB : M.BinaryOutcome)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) (z : Bool) :
    M.ate μ z ∈ Icc (lower (M.obsTable μ)) (upper (M.obsTable μ)) := by
  rw [M.obsTable_eq hE hI hB h₁ h₀, ← M.ace_responseLaw hE hB z]
  exact ace_mem_Icc _

end IVModel

/-! ### Numerical examples from Pearl (2009, Chapter 8) -/

namespace IVResponse

/-- A table given by its eight entries in the order printed by Pearl (2009, Section 8.2.3):
`p00.0, p00.1, p01.0, p01.1, p10.0, p10.1, p11.0, p11.1`. -/
def mkTable (a b c d e f g h : ℝ) : Observable
  | false, false, false => a
  | false, false, true => b
  | false, true, false => c
  | false, true, true => d
  | true, false, false => e
  | true, false, true => f
  | true, true, false => g
  | true, true, true => h

/-- The intent to treat effect `P(y1 | z1) - P(y1 | z0)` of a table. -/
def itt (p : Observable) : ℝ :=
  (p true false true + p true true true) - (p true false false + p true true false)

/-- The compliance difference `P(x1 | z1) - P(x1 | z0)` of a table. -/
def complianceDiff (p : Observable) : ℝ :=
  (p false true true + p true true true) - (p false true false + p true true false)

/-- The instrumental variable (Wald) estimate: the intent to treat effect divided by the
compliance difference. -/
noncomputable def wald (p : Observable) : ℝ := itt p / complianceDiff p

/-- Table 8.1 of Pearl (2009): the joint distribution `P(x, y, z)` with `P(z0) = P(z1) = 0.5`,
divided by `P(z)`: `P(y0, x0 | z0) = 0.55`, `P(y0, x1 | z0) = 0.45`, `P(y0, x0 | z1) = 0.45`,
`P(y1, x1 | z1) = 0.55`, all other entries `0`. -/
noncomputable def table81 : Observable := mkTable (11 / 20) (9 / 20) (9 / 20) 0 0 0 0 (11 / 20)

theorem binaryIVConstraints_table81 : BinaryIVConstraints table81 := by
  refine ⟨fun y x z ↦ ?_, fun z ↦ ?_, ?_, ?_, ?_, ?_⟩
  · cases y <;> cases x <;> cases z <;> norm_num [table81, mkTable]
  · cases z <;> norm_num [table81, mkTable]
  all_goals norm_num [table81, mkTable]

/-- **Point identification despite noncompliance** (Pearl 2009, Section 8.2.4 and Table 8.1).
For Table 8.1, where `45%` of the subjects in each arm do not comply, the Balke and Pearl
bounds collapse: the identified set of the average causal effect is the single value `0.55`. -/
theorem identifiedSet_table81 :
    identifiedSet (Set.univ : Set Weights) obs ace table81 = {11 / 20} := by
  rw [identifiedSet_ace binaryIVConstraints_table81,
    lower_eq_of (v := 11 / 20) 3 (by norm_num [lowerTerm, table81, mkTable])
      (fun j ↦ by fin_cases j <;> norm_num [lowerTerm, table81, mkTable]),
    upper_eq_of (v := 11 / 20) 1 (by norm_num [upperTerm, table81, mkTable])
      (fun j ↦ by fin_cases j <;> norm_num [upperTerm, table81, mkTable]),
    Icc_self]

/-- The cholestyramine data of Pearl (2009, Section 8.2.6) (Lipid Research Clinics Coronary
Primary Prevention Trial, after thresholding): `p00.0 = 0.919`, `p00.1 = 0.315`, `p01.0 = 0`,
`p01.1 = 0.139`, `p10.0 = 0.081`, `p10.1 = 0.073`, `p11.0 = 0`, `p11.1 = 0.473`. -/
noncomputable def lipid : Observable :=
  mkTable (919 / 1000) (315 / 1000) 0 (139 / 1000) (81 / 1000) (73 / 1000) 0 (473 / 1000)

theorem binaryIVConstraints_lipid : BinaryIVConstraints lipid := by
  refine ⟨fun y x z ↦ ?_, fun z ↦ ?_, ?_, ?_, ?_, ?_⟩
  · cases y <;> cases x <;> cases z <;> norm_num [lipid, mkTable]
  · cases z <;> norm_num [lipid, mkTable]
  all_goals norm_num [lipid, mkTable]

theorem lower_lipid : lower lipid = 49 / 125 :=
  lower_eq_of 0 (by norm_num [lowerTerm, lipid, mkTable])
    (fun j ↦ by fin_cases j <;> norm_num [lowerTerm, lipid, mkTable])

theorem upper_lipid : upper lipid = 39 / 50 :=
  upper_eq_of 0 (by norm_num [upperTerm, lipid, mkTable])
    (fun j ↦ by fin_cases j <;> norm_num [upperTerm, lipid, mkTable])

/-- **The cholestyramine bounds** (Pearl 2009, Section 8.2.6; the text calls them bounds on
"ETT", but they are bounds on the average causal effect): the identified set of the average
causal effect is `[0.392, 0.780]`. -/
theorem identifiedSet_lipid :
    identifiedSet (Set.univ : Set Weights) obs ace lipid = Icc (392 / 1000) (780 / 1000) := by
  rw [identifiedSet_ace binaryIVConstraints_lipid, lower_lipid, upper_lipid]
  norm_num

/-- The PeptAid data of Pearl (2009, Section 8.3): `p00.0 = 0.32`, `p00.1 = 0.02`,
`p01.0 = 0.32`, `p01.1 = 0.17`, `p10.0 = 0.04`, `p10.1 = 0.67`, `p11.0 = 0.32`,
`p11.1 = 0.14`. -/
noncomputable def pepAid : Observable :=
  mkTable (32 / 100) (2 / 100) (32 / 100) (17 / 100) (4 / 100) (67 / 100) (32 / 100) (14 / 100)

theorem binaryIVConstraints_pepAid : BinaryIVConstraints pepAid := by
  refine ⟨fun y x z ↦ ?_, fun z ↦ ?_, ?_, ?_, ?_, ?_⟩
  · cases y <;> cases x <;> cases z <;> norm_num [pepAid, mkTable]
  · cases z <;> norm_num [pepAid, mkTable]
  all_goals norm_num [pepAid, mkTable]

/-- **The PeptAid bounds** (Pearl 2009, Section 8.3): the identified set of the average causal
effect of PeptAid consumption on peptic ulceration is `[-0.23, -0.15]`. -/
theorem identifiedSet_pepAid :
    identifiedSet (Set.univ : Set Weights) obs ace pepAid = Icc (-23 / 100) (-15 / 100) := by
  rw [identifiedSet_ace binaryIVConstraints_pepAid,
    lower_eq_of (v := -23 / 100) 7 (by norm_num [lowerTerm, pepAid, mkTable])
      (fun j ↦ by fin_cases j <;> norm_num [lowerTerm, pepAid, mkTable]),
    upper_eq_of (v := -15 / 100) 6 (by norm_num [upperTerm, pepAid, mkTable])
      (fun j ↦ by fin_cases j <;> norm_num [upperTerm, pepAid, mkTable])]

theorem itt_pepAid : itt pepAid = 45 / 100 := by norm_num [itt, pepAid, mkTable]

theorem wald_pepAid : wald pepAid = -15 / 11 := by
  norm_num [wald, itt, complianceDiff, pepAid, mkTable]

/-- **The intent to treat estimate lies outside the sharp bounds** (Pearl 2009, Section 8.6):
for the PeptAid data the intent to treat effect `0.45` is not in the identified set. -/
theorem itt_pepAid_not_mem :
    itt pepAid ∉ identifiedSet (Set.univ : Set Weights) obs ace pepAid := by
  rw [identifiedSet_pepAid, itt_pepAid]; norm_num

/-- **The instrumental variable estimate lies outside the sharp bounds**: for the PeptAid data
the Wald estimate `0.45 / (0.31 - 0.64) = -15/11` is not in the identified set. -/
theorem wald_pepAid_not_mem :
    wald pepAid ∉ identifiedSet (Set.univ : Set Weights) obs ace pepAid := by
  rw [identifiedSet_pepAid, wald_pepAid]; norm_num

/-- The vitamin A data of Table 8.2 of Pearl (2009) (Sommer et al. 1986), as conditional
frequencies: the arm `z0` has `11588` children (`74` with `y0, x0` and `11514` with `y1, x0`),
the arm `z1` has `12094` (`34` with `y0, x0`, `2385` with `y1, x0`, `12` with `y0, x1` and
`9663` with `y1, x1`). -/
noncomputable def vitaminA : Observable :=
  mkTable (74 / 11588) (34 / 12094) 0 (12 / 12094) (11514 / 11588) (2385 / 12094) 0
    (9663 / 12094)

theorem binaryIVConstraints_vitaminA : BinaryIVConstraints vitaminA := by
  refine ⟨fun y x z ↦ ?_, fun z ↦ ?_, ?_, ?_, ?_, ?_⟩
  · cases y <;> cases x <;> cases z <;> norm_num [vitaminA, mkTable]
  · cases z <;> norm_num [vitaminA, mkTable]
  all_goals norm_num [vitaminA, mkTable]

theorem lower_vitaminA : lower vitaminA = -3409434 / 17518159 :=
  lower_eq_of 0 (by norm_num [lowerTerm, vitaminA, mkTable])
    (fun j ↦ by fin_cases j <;> norm_num [lowerTerm, vitaminA, mkTable])

theorem upper_vitaminA : upper vitaminA = 188975 / 35036318 :=
  upper_eq_of 0 (by norm_num [upperTerm, vitaminA, mkTable])
    (fun j ↦ by fin_cases j <;> norm_num [upperTerm, vitaminA, mkTable])

/-- **The vitamin A bounds** (Pearl 2009, Section 8.5.3, printed as `[-0.19, 0.01]`): computed
exactly from the counts of Table 8.2 the identified set is
`[-3409434/17518159, 188975/35036318]`, whose endpoints satisfy `-0.195 < lower < -0.19` and
`0.005 < upper < 0.01`; the printed values are their roundings. -/
theorem identifiedSet_vitaminA :
    identifiedSet (Set.univ : Set Weights) obs ace vitaminA =
        Icc (-3409434 / 17518159) (188975 / 35036318) ∧
      -195 / 1000 < lower vitaminA ∧ lower vitaminA < -19 / 100 ∧
      5 / 1000 < upper vitaminA ∧ upper vitaminA < 1 / 100 := by
  rw [identifiedSet_ace binaryIVConstraints_vitaminA, lower_vitaminA, upper_vitaminA]
  norm_num

end IVResponse

end CausalInference
