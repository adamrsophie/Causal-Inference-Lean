/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Rosenbaum sensitivity analysis for matched pairs

A finite, combinatorial treatment of Rosenbaum's model for hidden bias in matched pair
studies and of the sensitivity bounds for the sign test.

There are `S` matched pairs and exactly one unit of each pair is treated. The assignment is
encoded by `z : Fin S → Bool`, where `z s = true` means that the first unit of pair `s` is the
treated one; this happens with probability `p s`, independently across pairs, so `z` has the
product weight `bernWeight p z`. The sensitivity model with parameter `Γ` asks `1 ≤ Γ` and
`1 / (1 + Γ) ≤ p s ≤ Γ / (1 + Γ)` for every `s` (`InSensitivityModel`).

## Main results

* `pairProb_eq_cond`, `exactlyOneProb_pos`: for two units treated independently with
  probabilities `π₁, π₂`, the closed form `pairProb π₁ π₂` is the conditional probability, computed
  from the product weights, that the first unit is treated given that exactly one is treated; the
  conditioning event has positive probability for `π₁, π₂ ∈ (0, 1)`.
* `inSensitivityModel_pairProb_iff`: this conditional probability satisfies the model with
  parameter `Γ` if and only if the treatment odds of the two units differ by at most the factor
  `Γ`.
* `inSensitivityModel_one_iff`: `Γ = 1` forces `p = 1 / 2`, the randomized paired experiment.
* `tailProb_zero`, `sum_bernWeight`, `tailProb_le_one`, `tailProb_eq_zero_of_lt`: the product
  weights form a probability distribution.
* `tailProb_mono`: the upper tail of a sum of independent Bernoulli variables, written as a finite
  sum over `Fin n → Bool` with product weights, is monotone in each success probability.
* `countProb_const`, `tailProb_const`: with equal success probabilities `r` the law of the count
  is `Binomial(n, r)`, with the usual closed form. The link to Mathlib's binomial distribution is
  `binomialTail_eq_binomial_real` in `CausalInference.Sensitivity.Probability`.
* `signTestTail_le_binomialTail`, `binomialTail_le_signTestTail`: under the sharp null hypothesis
  with discordant binary pairs and `Γ ≥ 1`, the tail probability of the sign statistic lies
  between the `Binomial(S, 1 / (1 + Γ))` and `Binomial(S, Γ / (1 + Γ))` tails.
* `isGreatest_signTestTail`, `isLeast_signTestTail`: both bounds are sharp for every outcome
  pattern `f`, attained by `alignedAssign f`.
* `weightedTail_mono`, `signScoreTail_le`, `le_signScoreTail`, `isGreatest_signScoreTail`,
  `isLeast_signScoreTail`, `wilcoxon_signScoreTail_bounds`: the same bounds for sign-score
  statistics `∑ s, d s * 1{treated unit of pair s has the larger outcome}` with `d s ≥ 0`, in
  particular the Wilcoxon signed rank statistic.
* `InSensitivityModel.mono`, `binomialTail_upper_mono`: the model grows with `Γ` and the upper
  bound on the p-value is nondecreasing in `Γ`.

## References

* P. R. Rosenbaum, *Sensitivity analysis for certain permutation inferences in matched
  observational studies*, Biometrika (1987).
* P. R. Rosenbaum, *Observational Studies*, 2nd ed., Springer (2002), chapter 4.
-/

@[expose] public section

namespace CausalInference

namespace Rosenbaum

/-- The product weight `∏ i, (if x i then q i else 1 - q i)` of the outcome `x : Fin n → Bool`:
the probability of `x` when the coordinates are independent Bernoulli variables with success
probabilities `q i`. -/
def bernWeight {n : ℕ} (q : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, if x i then q i else 1 - q i

/-- The number of coordinates `i` with `x i = true`. -/
def count {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, if x i then 1 else 0

/-- The upper tail probability `P(count ≥ k)` of the number of successes among `n` independent
Bernoulli variables with success probabilities `q i`, as a finite sum with product weights. -/
def tailProb {n : ℕ} (q : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ x : Fin n → Bool, if k ≤ count x then bernWeight q x else 0

/-- Conditioning on the first coordinate: the tail is an affine function of `q 0`. -/
theorem tailProb_succ {n : ℕ} (q : Fin (n + 1) → ℝ) (k : ℕ) :
    tailProb q k =
      q 0 * tailProb (Fin.tail q) (k - 1) + (1 - q 0) * tailProb (Fin.tail q) k := by
  unfold tailProb
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  simp [bernWeight, count, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.mul_sum, Fin.tail,
    add_comm]


/-- Product weights with success probabilities in `[0, 1]` are nonnegative. -/
theorem bernWeight_nonneg {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (x : Fin n → Bool) : 0 ≤ bernWeight q x := by
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact (hq i).1
  · linarith [(hq i).2]

/-- The tail probability is nonincreasing in the threshold. -/
theorem tailProb_antitone {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {k k' : ℕ}
    (hk : k ≤ k') : tailProb q k' ≤ tailProb q k := by
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (hk.trans h1) h2
  · exact bernWeight_nonneg hq x
  · exact le_rfl

/-- Monotonicity of the upper tail of a sum of independent Bernoulli variables in the success
probabilities: if `q i ≤ q' i` for all `i`, with all values in `[0, 1]`, then
`P(count ≥ k)` under `q` is at most the same probability under `q'`, for every `k`. -/
theorem tailProb_mono {n : ℕ} {q q' : Fin n → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hq' : ∀ i, 0 ≤ q' i ∧ q' i ≤ 1) (hle : ∀ i, q i ≤ q' i) (k : ℕ) :
    tailProb q k ≤ tailProb q' k := by
  induction n generalizing k with
  | zero => simp [tailProb, bernWeight]
  | succ n ih =>
    rw [tailProb_succ q, tailProb_succ q']
    have hA := ih (q := Fin.tail q) (q' := Fin.tail q') (fun i => hq i.succ)
      (fun i => hq' i.succ) (fun i => hle i.succ) (k - 1)
    have hB := ih (q := Fin.tail q) (q' := Fin.tail q') (fun i => hq i.succ)
      (fun i => hq' i.succ) (fun i => hle i.succ) k
    have hBA := tailProb_antitone (q := Fin.tail q') (fun i => hq' i.succ) (Nat.sub_le k 1)
    have h0 := hq 0
    have h0' := hle 0
    nlinarith [mul_le_mul_of_nonneg_left hA h0.1,
      mul_le_mul_of_nonneg_left hB (sub_nonneg.2 h0.2),
      mul_le_mul_of_nonneg_left hBA (sub_nonneg.2 h0')]

/-- The probability `P(count = j)` that exactly `j` of the `n` independent Bernoulli variables
with success probabilities `q i` equal `true`. -/
def countProb {n : ℕ} (q : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ x : Fin n → Bool, if count x = j then bernWeight q x else 0

/-- Conditioning on the first coordinate for the event of no successes. -/
theorem countProb_succ_zero {n : ℕ} (q : Fin (n + 1) → ℝ) :
    countProb q 0 = (1 - q 0) * countProb (Fin.tail q) 0 := by
  unfold countProb
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  simp [bernWeight, count, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.mul_sum, Fin.tail]

/-- Conditioning on the first coordinate for the event of `j + 1` successes. -/
theorem countProb_succ_succ {n : ℕ} (q : Fin (n + 1) → ℝ) (j : ℕ) :
    countProb q (j + 1) =
      q 0 * countProb (Fin.tail q) j + (1 - q 0) * countProb (Fin.tail q) (j + 1) := by
  unfold countProb
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
  simp [bernWeight, count, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.mul_sum, Fin.tail]
  simp only [add_comm 1, Nat.add_right_cancel_iff]

/-- With all success probabilities equal to `r`, the count is `Binomial(n, r)`:
`P(count = j) = (n choose j) r ^ j (1 - r) ^ (n - j)`. -/
theorem countProb_const (n : ℕ) (r : ℝ) (j : ℕ) :
    countProb (fun _ : Fin n => r) j = (n.choose j : ℝ) * r ^ j * (1 - r) ^ (n - j) := by
  induction n generalizing j with
  | zero =>
    cases j <;> simp [countProb, count, bernWeight]
  | succ n ih =>
    have ht : Fin.tail (fun _ : Fin (n + 1) => r) = fun _ => r := rfl
    cases j with
    | zero =>
      rw [countProb_succ_zero]
      rw [ht, ih]
      simp [pow_succ, mul_comm]
    | succ j =>
      rw [countProb_succ_succ]
      rw [ht, ih, ih, Nat.choose_succ_succ, Nat.cast_add]
      rcases lt_or_ge j n with h | h
      · have : n - j = (n - (j + 1)) + 1 := by omega
        rw [Nat.succ_sub_succ, this]
        ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < j + 1), Nat.succ_sub_succ]
        simp only [Nat.cast_zero]
        ring

/-- At most `n` of `n` coordinates are successes. -/
theorem count_le {n : ℕ} (x : Fin n → Bool) : count x ≤ n := by
  calc count x ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by split_ifs <;> simp
    _ = n := by simp

/-- The upper tail is the sum of the point probabilities of the values at least `k`. -/
theorem tailProb_eq_sum_countProb {n : ℕ} (q : Fin n → ℝ) (k : ℕ) :
    tailProb q k = ∑ j ∈ Finset.range (n + 1), if k ≤ j then countProb q j else 0 := by
  unfold tailProb countProb
  symm
  calc (∑ j ∈ Finset.range (n + 1), if k ≤ j then
          ∑ x : Fin n → Bool, (if count x = j then bernWeight q x else 0) else 0)
      = ∑ j ∈ Finset.range (n + 1), ∑ x : Fin n → Bool,
          if count x = j then (if k ≤ j then bernWeight q x else 0) else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
    _ = ∑ x : Fin n → Bool, ∑ j ∈ Finset.range (n + 1),
          if count x = j then (if k ≤ j then bernWeight q x else 0) else 0 := Finset.sum_comm
    _ = ∑ x : Fin n → Bool, if k ≤ count x then bernWeight q x else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite_eq]
        simp [Nat.lt_succ_of_le (count_le x)]

/-- The upper tail `P(X ≥ k)` of `X ∼ Binomial(n, r)`,
`∑_{k ≤ j ≤ n} (n choose j) r ^ j (1 - r) ^ (n - j)`. -/
def binomialTail (n : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), if k ≤ j then (n.choose j : ℝ) * r ^ j * (1 - r) ^ (n - j) else 0

/-- Equal success probabilities give the binomial tail. -/
theorem tailProb_const (n : ℕ) (r : ℝ) (k : ℕ) :
    tailProb (fun _ : Fin n => r) k = binomialTail n r k := by
  rw [tailProb_eq_sum_countProb, binomialTail]
  simp only [countProb_const]

/-! ### The product weights form a probability distribution -/

/-- The product weights have total mass one: `P(count ≥ 0) = 1`. No hypothesis on `q` is needed
for this identity. -/
theorem tailProb_zero {n : ℕ} (q : Fin n → ℝ) : tailProb q 0 = 1 := by
  induction n with
  | zero => simp [tailProb, bernWeight]
  | succ n ih =>
    rw [tailProb_succ, Nat.zero_sub, ih]
    ring

/-- The product weights sum to one over all outcomes `x : Fin n → Bool`. -/
theorem sum_bernWeight {n : ℕ} (q : Fin n → ℝ) : ∑ x : Fin n → Bool, bernWeight q x = 1 := by
  rw [← tailProb_zero q, tailProb]
  simp

/-- The tail probability is nonnegative for success probabilities in `[0, 1]`. -/
theorem tailProb_nonneg {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (k : ℕ) :
    0 ≤ tailProb q k :=
  Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact bernWeight_nonneg hq x
    · exact le_rfl

/-- The tail probability is at most one for success probabilities in `[0, 1]`. -/
theorem tailProb_le_one {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (k : ℕ) :
    tailProb q k ≤ 1 :=
  (tailProb_antitone hq (Nat.zero_le k)).trans (tailProb_zero q).le

/-- The tail probability vanishes beyond `n`: `P(count ≥ k) = 0` for `k > n`. -/
theorem tailProb_eq_zero_of_lt {n : ℕ} (q : Fin n → ℝ) {k : ℕ} (hk : n < k) :
    tailProb q k = 0 :=
  Finset.sum_eq_zero fun x _ =>
    ite_eq_right_iff.2 fun h => absurd (h.trans (count_le x)) (by omega)

/-- The binomial tail is a probability for `r ∈ [0, 1]`. -/
theorem binomialTail_mem_unit {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (k : ℕ) :
    0 ≤ binomialTail n r k ∧ binomialTail n r k ≤ 1 := by
  rw [← tailProb_const]
  exact ⟨tailProb_nonneg (fun _ => ⟨hr, hr'⟩) k, tailProb_le_one (fun _ => ⟨hr, hr'⟩) k⟩

/-- Rosenbaum's sensitivity model with parameter `Γ ≥ 1` for the probability `p` that the first
unit of a pair is the treated one: `1 ≤ Γ` and `1 / (1 + Γ) ≤ p ≤ Γ / (1 + Γ)`. The bound
`1 ≤ Γ` is part of the predicate, so that the predicate never holds for a parameter outside the
model (for `Γ < 1` the interval would be empty or, for `Γ ≤ -1`, would not consist of
probabilities). -/
def InSensitivityModel (Γ p : ℝ) : Prop := 1 ≤ Γ ∧ 1 / (1 + Γ) ≤ p ∧ p ≤ Γ / (1 + Γ)

/-- A sensitivity parameter allowed by the model is at least one. -/
theorem InSensitivityModel.one_le {Γ p : ℝ} (h : InSensitivityModel Γ p) : 1 ≤ Γ := h.1

/-- The lower end of the model interval. -/
theorem InSensitivityModel.lower_le {Γ p : ℝ} (h : InSensitivityModel Γ p) :
    1 / (1 + Γ) ≤ p := h.2.1

/-- The upper end of the model interval. -/
theorem InSensitivityModel.le_upper {Γ p : ℝ} (h : InSensitivityModel Γ p) :
    p ≤ Γ / (1 + Γ) := h.2.2

/-- The odds `π / (1 - π)` of a probability `π`. -/
noncomputable def odds (π : ℝ) : ℝ := π / (1 - π)

/-- The closed form `π₁ (1 - π₂) / (π₁ (1 - π₂) + π₂ (1 - π₁))`. By `pairProb_eq_cond` it is
the conditional probability that the first of two independently treated units (with treatment
probabilities `π₁` and `π₂`) is treated, given that exactly one of them is treated. -/
noncomputable def pairProb (π₁ π₂ : ℝ) : ℝ := π₁ * (1 - π₂) / (π₁ * (1 - π₂) + π₂ * (1 - π₁))

/-- The product weight of an assignment of two units treated independently with probabilities
`π₁` and `π₂`. -/
theorem bernWeight_pair (π₁ π₂ : ℝ) (z : Fin 2 → Bool) :
    bernWeight ![π₁, π₂] z =
      (if z 0 then π₁ else 1 - π₁) * (if z 1 then π₂ else 1 - π₂) := by
  simp [bernWeight, Fin.prod_univ_two]

/-- The probability `P(Z₁ + Z₂ = 1)` that exactly one of two units, treated independently with
probabilities `π₁` and `π₂`, is treated. -/
def exactlyOneProb (π₁ π₂ : ℝ) : ℝ :=
  ∑ z : Fin 2 → Bool, if count z = 1 then bernWeight ![π₁, π₂] z else 0

/-- The probability `P(Z₁ = 1, Z₂ = 0)` that the first unit, and only the first unit, is
treated. -/
def firstOnlyProb (π₁ π₂ : ℝ) : ℝ :=
  ∑ z : Fin 2 → Bool, if count z = 1 ∧ z 0 = true then bernWeight ![π₁, π₂] z else 0

/-- The probability that exactly one unit is treated, computed from the four product weights. -/
theorem exactlyOneProb_eq (π₁ π₂ : ℝ) :
    exactlyOneProb π₁ π₂ = π₁ * (1 - π₂) + π₂ * (1 - π₁) := by
  unfold exactlyOneProb
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [bernWeight, count, Fin.prod_univ_two, Fin.sum_univ_two]
  simp
  ring

/-- The probability that only the first unit is treated, computed from the product weights. -/
theorem firstOnlyProb_eq (π₁ π₂ : ℝ) : firstOnlyProb π₁ π₂ = π₁ * (1 - π₂) := by
  unfold firstOnlyProb
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [bernWeight, count, Fin.prod_univ_two, Fin.sum_univ_two]
  simp

/-- For treatment probabilities in `(0, 1)` the event that exactly one unit is treated has
positive probability, so conditioning on it is not degenerate. -/
theorem exactlyOneProb_pos {π₁ π₂ : ℝ} (h₁ : 0 < π₁) (h₁' : π₁ < 1) (h₂ : 0 < π₂)
    (h₂' : π₂ < 1) : 0 < exactlyOneProb π₁ π₂ := by
  rw [exactlyOneProb_eq]
  have := mul_pos h₁ (sub_pos.2 h₂')
  have := mul_pos h₂ (sub_pos.2 h₁')
  linarith

/-- `pairProb` is a conditional probability: for two units treated independently with
probabilities `π₁` and `π₂`, `P(Z₁ = 1 | Z₁ + Z₂ = 1) = pairProb π₁ π₂`, where both
probabilities are computed from the product weights `bernWeight ![π₁, π₂]`. The conditioning
event has positive probability when `π₁, π₂ ∈ (0, 1)` (`exactlyOneProb_pos`). -/
theorem pairProb_eq_cond (π₁ π₂ : ℝ) :
    firstOnlyProb π₁ π₂ / exactlyOneProb π₁ π₂ = pairProb π₁ π₂ := by
  rw [firstOnlyProb_eq, exactlyOneProb_eq, pairProb]

/-- Odds-ratio form of Rosenbaum's model: for treatment probabilities `π₁, π₂ ∈ (0, 1)` and
`Γ > 0`, the conditional probability `pairProb π₁ π₂` satisfies the sensitivity model with
parameter `Γ` (in particular `Γ ≥ 1`) if and only if `odds π₁ ≤ Γ * odds π₂` and
`odds π₂ ≤ Γ * odds π₁`, that is, the treatment odds of the two units differ by at most a
factor `Γ`. -/
theorem inSensitivityModel_pairProb_iff {Γ π₁ π₂ : ℝ} (hΓ : 0 < Γ) (h₁ : 0 < π₁)
    (h₁' : π₁ < 1) (h₂ : 0 < π₂) (h₂' : π₂ < 1) :
    InSensitivityModel Γ (pairProb π₁ π₂) ↔
      odds π₁ ≤ Γ * odds π₂ ∧ odds π₂ ≤ Γ * odds π₁ := by
  have ha : 0 < π₁ * (1 - π₂) := mul_pos h₁ (by linarith)
  have hb : 0 < π₂ * (1 - π₁) := mul_pos h₂ (by linarith)
  have hc₁ : 0 < 1 - π₁ := by linarith
  have hc₂ : 0 < 1 - π₂ := by linarith
  unfold InSensitivityModel pairProb odds
  rw [div_le_div_iff₀ (by linarith) (by linarith), div_le_div_iff₀ (by linarith) (by linarith),
    mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hc₁ hc₂, div_le_div_iff₀ hc₂ hc₁]
  constructor
  · rintro ⟨-, h, h'⟩
    constructor <;> nlinarith
  · rintro ⟨h, h'⟩
    have hΓ1 : 1 ≤ Γ := by
      by_contra hlt
      rw [not_le] at hlt
      nlinarith [mul_pos ha hb, mul_pos hΓ ha, mul_pos hΓ hb]
    exact ⟨hΓ1, by nlinarith, by nlinarith⟩

/-- With `Γ = 1` the model forces `p = 1 / 2`: the randomized paired experiment. -/
theorem inSensitivityModel_one_iff {p : ℝ} : InSensitivityModel 1 p ↔ p = 1 / 2 := by
  unfold InSensitivityModel
  norm_num
  constructor
  · rintro ⟨h, h'⟩
    linarith
  · rintro rfl
    norm_num

/-- The sensitivity model grows with `Γ`: every probability allowed at `Γ` is allowed at every
`Γ' ≥ Γ`. -/
theorem InSensitivityModel.mono {Γ Γ' p : ℝ} (hle : Γ ≤ Γ')
    (h : InSensitivityModel Γ p) : InSensitivityModel Γ' p := by
  obtain ⟨hΓ, h₁, h₂⟩ := h
  refine ⟨hΓ.trans hle, ?_, ?_⟩
  · refine le_trans ?_ h₁
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · refine h₂.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- A probability allowed by the model is nonnegative. -/
theorem InSensitivityModel.nonneg {Γ p : ℝ} (h : InSensitivityModel Γ p) : 0 ≤ p :=
  le_trans (by have := h.1; positivity) h.2.1

/-- A probability allowed by the model is at most one. -/
theorem InSensitivityModel.le_one {Γ p : ℝ} (h : InSensitivityModel Γ p) : p ≤ 1 :=
  h.2.2.trans ((div_le_one (by linarith [h.1])).2 (by linarith))

/-- The model is symmetric under exchanging the two units of a pair. -/
theorem InSensitivityModel.one_sub {Γ p : ℝ} (h : InSensitivityModel Γ p) :
    InSensitivityModel Γ (1 - p) := by
  obtain ⟨hΓ, h₁, h₂⟩ := h
  have e : 1 - Γ / (1 + Γ) = 1 / (1 + Γ) := by field_simp; ring
  exact ⟨hΓ, by linarith, by linarith⟩

/-- The sign statistic under the sharp null hypothesis with binary discordant pairs. The fixed
pattern `f s = true` records that the first unit of pair `s` has the larger outcome (outcomes are
fixed under the sharp null, and in a discordant pair exactly one unit has the larger outcome). The
statistic counts the pairs in which the treated unit has the larger outcome, that is, the `s` with
`z s = f s`. -/
def signStat {S : ℕ} (f : Fin S → Bool) (z : Fin S → Bool) : ℕ :=
  count fun s => z s == f s

/-- The tail probability `P(T ≥ k)` of the sign statistic `T` when the first unit of pair `s` is
treated with probability `p s`, independently across pairs. -/
def signTestTail {S : ℕ} (p : Fin S → ℝ) (f : Fin S → Bool) (k : ℕ) : ℝ :=
  ∑ z : Fin S → Bool, if k ≤ signStat f z then bernWeight p z else 0

/-- The probability that the treated unit of pair `s` has the larger outcome: `p s` if the first
unit has the larger outcome and `1 - p s` otherwise. -/
def successProb {S : ℕ} (p : Fin S → ℝ) (f : Fin S → Bool) (s : Fin S) : ℝ :=
  if f s then p s else 1 - p s

/-- The involution `z ↦ (s ↦ (z s == f s))` of `Fin S → Bool`, which sends an assignment to the
indicator of the pairs in which the treated unit has the larger outcome. -/
def matchEquiv {S : ℕ} (f : Fin S → Bool) : (Fin S → Bool) ≃ (Fin S → Bool) where
  toFun z s := z s == f s
  invFun z s := z s == f s
  left_inv z := by
    funext s
    change ((z s == f s) == f s) = z s
    cases z s <;> cases f s <;> rfl
  right_inv z := by
    funext s
    change ((z s == f s) == f s) = z s
    cases z s <;> cases f s <;> rfl

/-- The sign statistic is a sum of independent Bernoulli variables with success probabilities
`successProb p f s`. -/
theorem signTestTail_eq_tailProb {S : ℕ} (p : Fin S → ℝ) (f : Fin S → Bool) (k : ℕ) :
    signTestTail p f k = tailProb (successProb p f) k := by
  unfold signTestTail tailProb
  rw [← (matchEquiv f).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hw : bernWeight p (matchEquiv f z) = bernWeight (successProb p f) z := by
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [matchEquiv, Equiv.coe_fn_mk, successProb]
    rcases Bool.eq_false_or_eq_true (z s) with hz | hz <;>
      rcases Bool.eq_false_or_eq_true (f s) with hf | hf <;> simp [hz, hf]
  have hc : signStat f (matchEquiv f z) = count z := by
    unfold signStat
    congr 1
    funext s
    change ((z s == f s) == f s) = z s
    cases z s <;> cases f s <;> rfl
  rw [hw, hc]

/-- Under the sensitivity model the success probabilities of the sign statistic lie in
`[1 / (1 + Γ), Γ / (1 + Γ)]`. -/
theorem successProb_mem {S : ℕ} {Γ : ℝ} {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (f : Fin S → Bool) (s : Fin S) :
    InSensitivityModel Γ (successProb p f s) := by
  unfold successProb
  split_ifs
  · exact hp s
  · exact (hp s).one_sub

/-- `Γ / (1 + Γ)` is a probability for `Γ ≥ 0`. -/
theorem upper_mem_unit {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ Γ / (1 + Γ) ∧ Γ / (1 + Γ) ≤ 1 :=
  ⟨by positivity, (div_le_one (by linarith)).2 (by linarith)⟩

/-- `1 / (1 + Γ)` is a probability for `Γ ≥ 0`. -/
theorem lower_mem_unit {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ 1 / (1 + Γ) ∧ 1 / (1 + Γ) ≤ 1 :=
  ⟨by positivity, (div_le_one (by linarith)).2 (by linarith)⟩

/-- Rosenbaum's upper bound for the sign test: under the sensitivity model with parameter
`Γ ≥ 1`, `P(T ≥ k)` is at most the upper tail of `Binomial(S, Γ / (1 + Γ))`, for every `k`. -/
theorem signTestTail_le_binomialTail {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (f : Fin S → Bool) (k : ℕ) :
    signTestTail p f k ≤ binomialTail S (Γ / (1 + Γ)) k := by
  have hm := successProb_mem hp f
  rw [signTestTail_eq_tailProb, ← tailProb_const]
  exact tailProb_mono (fun s => ⟨(hm s).nonneg, (hm s).le_one⟩)
    (fun _ => upper_mem_unit (by linarith)) (fun s => (hm s).le_upper) k

/-- Rosenbaum's lower bound for the sign test: under the sensitivity model with parameter
`Γ ≥ 1`, `P(T ≥ k)` is at least the upper tail of `Binomial(S, 1 / (1 + Γ))`, for every `k`. -/
theorem binomialTail_le_signTestTail {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (f : Fin S → Bool) (k : ℕ) :
    binomialTail S (1 / (1 + Γ)) k ≤ signTestTail p f k := by
  have hm := successProb_mem hp f
  rw [signTestTail_eq_tailProb, ← tailProb_const]
  exact tailProb_mono (fun _ => lower_mem_unit (by linarith))
    (fun s => ⟨(hm s).nonneg, (hm s).le_one⟩) (fun s => (hm s).lower_le) k

/-- The upper bound is attained by the assignment probabilities `p s = Γ / (1 + Γ)` when the first
unit of every pair has the larger outcome; these lie in the model when `Γ ≥ 1`
(`inSensitivityModel_upper`). See `signTestTail_upperAssign` for every outcome pattern. -/
theorem signTestTail_upper_attained {S : ℕ} (Γ : ℝ) (k : ℕ) :
    signTestTail (fun _ : Fin S => Γ / (1 + Γ)) (fun _ => true) k =
      binomialTail S (Γ / (1 + Γ)) k := by
  rw [signTestTail_eq_tailProb, ← tailProb_const]
  rfl

/-- With `Γ = 1` the sign statistic has exactly the `Binomial(S, 1 / 2)` tail, as in a randomized
paired experiment. -/
theorem signTestTail_eq_binomialTail_half {S : ℕ} {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel 1 (p s)) (f : Fin S → Bool) (k : ℕ) :
    signTestTail p f k = binomialTail S (1 / 2) k := by
  have h₁ := signTestTail_le_binomialTail le_rfl hp f k
  have h₂ := binomialTail_le_signTestTail le_rfl hp f k
  norm_num at h₁ h₂
  exact le_antisymm h₁ h₂

/-- The upper bound on the sign test p-value is nondecreasing in `Γ`. -/
theorem binomialTail_upper_mono {S : ℕ} {Γ Γ' : ℝ} (hΓ : 0 ≤ Γ) (hle : Γ ≤ Γ') (k : ℕ) :
    binomialTail S (Γ / (1 + Γ)) k ≤ binomialTail S (Γ' / (1 + Γ')) k := by
  rw [← tailProb_const, ← tailProb_const]
  refine tailProb_mono (fun _ => upper_mem_unit hΓ) (fun _ => upper_mem_unit (hΓ.trans hle))
    (fun _ => ?_) k
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The lower bound on the sign test p-value is nonincreasing in `Γ`. -/
theorem binomialTail_lower_anti {S : ℕ} {Γ Γ' : ℝ} (hΓ : 0 ≤ Γ) (hle : Γ ≤ Γ') (k : ℕ) :
    binomialTail S (1 / (1 + Γ')) k ≤ binomialTail S (1 / (1 + Γ)) k := by
  rw [← tailProb_const, ← tailProb_const]
  exact tailProb_mono (fun _ => lower_mem_unit (hΓ.trans hle)) (fun _ => lower_mem_unit hΓ)
    (fun _ => one_div_le_one_div_of_le (by linarith) (by linarith)) k

/-- For `Γ ≥ 1`, the value `Γ / (1 + Γ)` is allowed by the sensitivity model. -/
theorem inSensitivityModel_upper {Γ : ℝ} (hΓ : 1 ≤ Γ) : InSensitivityModel Γ (Γ / (1 + Γ)) :=
  ⟨hΓ, div_le_div_of_nonneg_right hΓ (by linarith), le_rfl⟩

/-- For `Γ ≥ 1`, the value `1 / (1 + Γ)` is allowed by the sensitivity model. -/
theorem inSensitivityModel_lower {Γ : ℝ} (hΓ : 1 ≤ Γ) : InSensitivityModel Γ (1 / (1 + Γ)) :=
  ⟨hΓ, le_rfl, div_le_div_of_nonneg_right hΓ (by linarith)⟩

/-! ### Sharpness for every outcome pattern -/

/-- The assignment probabilities that make the success probability of every pair equal to `r`:
the first unit of pair `s` is treated with probability `r` if it has the larger outcome and with
probability `1 - r` otherwise. -/
def alignedAssign {S : ℕ} (f : Fin S → Bool) (r : ℝ) (s : Fin S) : ℝ :=
  if f s then r else 1 - r

/-- Under `alignedAssign f r` every success probability equals `r`. -/
theorem successProb_alignedAssign {S : ℕ} (f : Fin S → Bool) (r : ℝ) :
    successProb (alignedAssign f r) f = fun _ => r := by
  funext s
  unfold successProb alignedAssign
  split_ifs <;> ring

/-- For `Γ ≥ 1`, `alignedAssign f (Γ / (1 + Γ))` satisfies the sensitivity model. -/
theorem alignedAssign_upper_mem {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) (f : Fin S → Bool) (s : Fin S) :
    InSensitivityModel Γ (alignedAssign f (Γ / (1 + Γ)) s) := by
  unfold alignedAssign
  split_ifs
  · exact inSensitivityModel_upper hΓ
  · exact (inSensitivityModel_upper hΓ).one_sub

/-- For `Γ ≥ 1`, `alignedAssign f (1 / (1 + Γ))` satisfies the sensitivity model. -/
theorem alignedAssign_lower_mem {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) (f : Fin S → Bool) (s : Fin S) :
    InSensitivityModel Γ (alignedAssign f (1 / (1 + Γ)) s) := by
  unfold alignedAssign
  split_ifs
  · exact inSensitivityModel_lower hΓ
  · exact (inSensitivityModel_lower hΓ).one_sub

/-- For every outcome pattern `f`, the assignment `alignedAssign f (Γ / (1 + Γ))` attains the
upper bound: its sign test tail is the `Binomial(S, Γ / (1 + Γ))` tail. -/
theorem signTestTail_upperAssign {S : ℕ} (Γ : ℝ) (f : Fin S → Bool) (k : ℕ) :
    signTestTail (alignedAssign f (Γ / (1 + Γ))) f k = binomialTail S (Γ / (1 + Γ)) k := by
  rw [signTestTail_eq_tailProb, successProb_alignedAssign, tailProb_const]

/-- For every outcome pattern `f`, the assignment `alignedAssign f (1 / (1 + Γ))` attains the
lower bound: its sign test tail is the `Binomial(S, 1 / (1 + Γ))` tail. -/
theorem signTestTail_lowerAssign {S : ℕ} (Γ : ℝ) (f : Fin S → Bool) (k : ℕ) :
    signTestTail (alignedAssign f (1 / (1 + Γ))) f k = binomialTail S (1 / (1 + Γ)) k := by
  rw [signTestTail_eq_tailProb, successProb_alignedAssign, tailProb_const]

/-- Sharp upper bound: for `Γ ≥ 1` and every outcome pattern `f`, the largest value of the sign
test tail `P(T ≥ k)` over all assignment probabilities in the sensitivity model is the
`Binomial(S, Γ / (1 + Γ))` tail. -/
theorem isGreatest_signTestTail {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) (f : Fin S → Bool) (k : ℕ) :
    IsGreatest {t | ∃ p : Fin S → ℝ, (∀ s, InSensitivityModel Γ (p s)) ∧ t = signTestTail p f k}
      (binomialTail S (Γ / (1 + Γ)) k) := by
  refine ⟨⟨_, alignedAssign_upper_mem hΓ f, (signTestTail_upperAssign Γ f k).symm⟩, ?_⟩
  rintro t ⟨p, hp, rfl⟩
  exact signTestTail_le_binomialTail hΓ hp f k

/-- Sharp lower bound: for `Γ ≥ 1` and every outcome pattern `f`, the smallest value of the sign
test tail `P(T ≥ k)` over all assignment probabilities in the sensitivity model is the
`Binomial(S, 1 / (1 + Γ))` tail. -/
theorem isLeast_signTestTail {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) (f : Fin S → Bool) (k : ℕ) :
    IsLeast {t | ∃ p : Fin S → ℝ, (∀ s, InSensitivityModel Γ (p s)) ∧ t = signTestTail p f k}
      (binomialTail S (1 / (1 + Γ)) k) := by
  refine ⟨⟨_, alignedAssign_lower_mem hΓ f, (signTestTail_lowerAssign Γ f k).symm⟩, ?_⟩
  rintro t ⟨p, hp, rfl⟩
  exact binomialTail_le_signTestTail hΓ hp f k


/-! ### Sign-score statistics

A sign-score statistic gives pair `s` a fixed nonnegative score `d s` and adds up the scores of
the pairs in which the treated unit has the larger outcome. With `d s = 1` it is the sign
statistic; with `d s` the rank of the absolute paired difference it is the Wilcoxon signed rank
statistic. Under the sharp null hypothesis both the scores and the outcome pattern are fixed. -/

/-- The weighted count `∑ i, d i * 1{x i}` of the coordinates with `x i = true`. -/
def weightedScore {n : ℕ} (d : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, if x i then d i else 0

/-- The upper tail probability `P(∑ i, d i * 1{x i} ≥ c)` for independent Bernoulli coordinates
with success probabilities `q i`, as a finite sum with product weights. -/
noncomputable def weightedTail {n : ℕ} (q d : Fin n → ℝ) (c : ℝ) : ℝ :=
  ∑ x : Fin n → Bool, if c ≤ weightedScore d x then bernWeight q x else 0

/-- Splitting off the first coordinate of the weighted count. -/
theorem weightedScore_cons {n : ℕ} (d : Fin (n + 1) → ℝ) (b : Bool) (t : Fin n → Bool) :
    weightedScore d (Fin.cons b t) = (if b then d 0 else 0) + weightedScore (Fin.tail d) t := by
  simp [weightedScore, Fin.sum_univ_succ, Fin.tail]

/-- Splitting off the first coordinate of the product weight. -/
theorem bernWeight_cons {n : ℕ} (q : Fin (n + 1) → ℝ) (b : Bool) (t : Fin n → Bool) :
    bernWeight q (Fin.cons b t) = (if b then q 0 else 1 - q 0) * bernWeight (Fin.tail q) t := by
  simp [bernWeight, Fin.prod_univ_succ, Fin.tail]

/-- Conditioning on the first coordinate in the weighted tail. -/
theorem weightedTail_succ {n : ℕ} (q d : Fin (n + 1) → ℝ) (c : ℝ) :
    weightedTail q d c = q 0 * weightedTail (Fin.tail q) (Fin.tail d) (c - d 0) +
      (1 - q 0) * weightedTail (Fin.tail q) (Fin.tail d) c := by
  unfold weightedTail
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.mul_sum, Finset.mul_sum]
  simp [Fin.consEquiv, weightedScore_cons, bernWeight_cons, mul_ite]
  simp only [add_comm]

/-- The weighted tail is nonincreasing in the threshold. -/
theorem weightedTail_antitone {n : ℕ} {q : Fin n → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (d : Fin n → ℝ) {c c' : ℝ} (hc : c ≤ c') : weightedTail q d c' ≤ weightedTail q d c := by
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (hc.trans h1) h2
  · exact bernWeight_nonneg hq x
  · exact le_rfl

/-- Weighted monotonicity: for nonnegative scores `d i` and success probabilities
`q i ≤ q' i` in `[0, 1]`, `P(∑ i, d i * 1{x i} ≥ c)` under `q` is at most the same probability
under `q'`, for every threshold `c`. -/
theorem weightedTail_mono {n : ℕ} {q q' d : Fin n → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hq' : ∀ i, 0 ≤ q' i ∧ q' i ≤ 1) (hle : ∀ i, q i ≤ q' i) (hd : ∀ i, 0 ≤ d i) (c : ℝ) :
    weightedTail q d c ≤ weightedTail q' d c := by
  induction n generalizing c with
  | zero => simp [weightedTail, bernWeight]
  | succ n ih =>
    rw [weightedTail_succ q, weightedTail_succ q']
    have hA := ih (q := Fin.tail q) (q' := Fin.tail q') (d := Fin.tail d) (fun i => hq i.succ)
      (fun i => hq' i.succ) (fun i => hle i.succ) (fun i => hd i.succ) (c - d 0)
    have hB := ih (q := Fin.tail q) (q' := Fin.tail q') (d := Fin.tail d) (fun i => hq i.succ)
      (fun i => hq' i.succ) (fun i => hle i.succ) (fun i => hd i.succ) c
    have hBA := weightedTail_antitone (q := Fin.tail q') (fun i => hq' i.succ) (Fin.tail d)
      (by linarith [hd 0] : c - d 0 ≤ c)
    have h0 := hq 0
    have h0' := hle 0
    nlinarith [mul_le_mul_of_nonneg_left hA h0.1,
      mul_le_mul_of_nonneg_left hB (sub_nonneg.2 h0.2),
      mul_le_mul_of_nonneg_left hBA (sub_nonneg.2 h0')]

/-- The sign-score statistic `∑ s, d s * 1{z s = f s}`: the total score of the pairs in which the
treated unit has the larger outcome. -/
def signScore {S : ℕ} (d : Fin S → ℝ) (f z : Fin S → Bool) : ℝ :=
  weightedScore d fun s => z s == f s

/-- The tail probability `P(T ≥ c)` of the sign-score statistic `T` when the first unit of pair
`s` is treated with probability `p s`, independently across pairs. -/
noncomputable def signScoreTail {S : ℕ} (p d : Fin S → ℝ) (f : Fin S → Bool) (c : ℝ) : ℝ :=
  ∑ z : Fin S → Bool, if c ≤ signScore d f z then bernWeight p z else 0

/-- The sign-score statistic is a weighted sum of independent Bernoulli variables with success
probabilities `successProb p f s`. -/
theorem signScoreTail_eq_weightedTail {S : ℕ} (p d : Fin S → ℝ) (f : Fin S → Bool) (c : ℝ) :
    signScoreTail p d f c = weightedTail (successProb p f) d c := by
  unfold signScoreTail weightedTail
  rw [← (matchEquiv f).sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hw : bernWeight p (matchEquiv f z) = bernWeight (successProb p f) z := by
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [matchEquiv, Equiv.coe_fn_mk, successProb]
    rcases Bool.eq_false_or_eq_true (z s) with hz | hz <;>
      rcases Bool.eq_false_or_eq_true (f s) with hf | hf <;> simp [hz, hf]
  have hc : signScore d f (matchEquiv f z) = weightedScore d z := by
    unfold signScore
    congr 1
    funext s
    change ((z s == f s) == f s) = z s
    cases z s <;> cases f s <;> rfl
  rw [hw, hc]

/-- Rosenbaum's upper bound for sign-score statistics: under the sensitivity model with
parameter `Γ ≥ 1` and nonnegative scores, `P(T ≥ c)` is at most the tail of
`∑ s, d s * B s` with `B s` independent Bernoulli variables of mean `Γ / (1 + Γ)`. -/
theorem signScoreTail_le {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) {p d : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (hd : ∀ s, 0 ≤ d s) (f : Fin S → Bool) (c : ℝ) :
    signScoreTail p d f c ≤ weightedTail (fun _ => Γ / (1 + Γ)) d c := by
  have hm := successProb_mem hp f
  rw [signScoreTail_eq_weightedTail]
  exact weightedTail_mono (fun s => ⟨(hm s).nonneg, (hm s).le_one⟩)
    (fun _ => upper_mem_unit (by linarith)) (fun s => (hm s).le_upper) hd c

/-- Rosenbaum's lower bound for sign-score statistics: under the sensitivity model with
parameter `Γ ≥ 1` and nonnegative scores, `P(T ≥ c)` is at least the tail of
`∑ s, d s * B s` with `B s` independent Bernoulli variables of mean `1 / (1 + Γ)`. -/
theorem le_signScoreTail {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) {p d : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (hd : ∀ s, 0 ≤ d s) (f : Fin S → Bool) (c : ℝ) :
    weightedTail (fun _ => 1 / (1 + Γ)) d c ≤ signScoreTail p d f c := by
  have hm := successProb_mem hp f
  rw [signScoreTail_eq_weightedTail]
  exact weightedTail_mono (fun _ => lower_mem_unit (by linarith))
    (fun s => ⟨(hm s).nonneg, (hm s).le_one⟩) (fun s => (hm s).lower_le) hd c

/-- Sharpness for sign-score statistics: for `Γ ≥ 1`, nonnegative scores, and every outcome
pattern `f`, the largest value of `P(T ≥ c)` over the sensitivity model is the upper bound of
`signScoreTail_le`, attained by `alignedAssign f (Γ / (1 + Γ))`. -/
theorem isGreatest_signScoreTail {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) {d : Fin S → ℝ}
    (hd : ∀ s, 0 ≤ d s) (f : Fin S → Bool) (c : ℝ) :
    IsGreatest
      {t | ∃ p : Fin S → ℝ, (∀ s, InSensitivityModel Γ (p s)) ∧ t = signScoreTail p d f c}
      (weightedTail (fun _ => Γ / (1 + Γ)) d c) := by
  refine ⟨⟨_, alignedAssign_upper_mem hΓ f, ?_⟩, ?_⟩
  · rw [signScoreTail_eq_weightedTail, successProb_alignedAssign]
  · rintro t ⟨p, hp, rfl⟩
    exact signScoreTail_le hΓ hp hd f c

/-- Sharpness of the lower bound for sign-score statistics, attained by
`alignedAssign f (1 / (1 + Γ))`. -/
theorem isLeast_signScoreTail {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) {d : Fin S → ℝ}
    (hd : ∀ s, 0 ≤ d s) (f : Fin S → Bool) (c : ℝ) :
    IsLeast
      {t | ∃ p : Fin S → ℝ, (∀ s, InSensitivityModel Γ (p s)) ∧ t = signScoreTail p d f c}
      (weightedTail (fun _ => 1 / (1 + Γ)) d c) := by
  refine ⟨⟨_, alignedAssign_lower_mem hΓ f, ?_⟩, ?_⟩
  · rw [signScoreTail_eq_weightedTail, successProb_alignedAssign]
  · rintro t ⟨p, hp, rfl⟩
    exact le_signScoreTail hΓ hp hd f c

/-- Rosenbaum's bounds for the Wilcoxon signed rank statistic. Under the sharp null hypothesis
the absolute paired differences, hence their ranks `rk s`, and the pattern `f` of which unit
has the larger outcome are fixed; the statistic is the sum of the ranks of the pairs in which the
treated unit has the larger outcome. Under the sensitivity model with `Γ ≥ 1`, its tail
`P(T ≥ c)` lies between the tails of `∑ s, rk s * B s` with `B s` independent Bernoulli variables
of mean `1 / (1 + Γ)` and of mean `Γ / (1 + Γ)`. -/
theorem wilcoxon_signScoreTail_bounds {S : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ) {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (rk : Fin S → ℕ) (f : Fin S → Bool) (c : ℝ) :
    weightedTail (fun _ => 1 / (1 + Γ)) (fun s => (rk s : ℝ)) c ≤
        signScoreTail p (fun s => (rk s : ℝ)) f c ∧
      signScoreTail p (fun s => (rk s : ℝ)) f c ≤
        weightedTail (fun _ => Γ / (1 + Γ)) (fun s => (rk s : ℝ)) c :=
  ⟨le_signScoreTail hΓ hp (fun s => Nat.cast_nonneg (rk s)) f c,
    signScoreTail_le hΓ hp (fun s => Nat.cast_nonneg (rk s)) f c⟩

end Rosenbaum

end CausalInference
