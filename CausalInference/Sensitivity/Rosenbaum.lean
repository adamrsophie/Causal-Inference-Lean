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
product weight `bernWeight p z`. The sensitivity model with parameter `Γ` asks
`1 / (1 + Γ) ≤ p s ≤ Γ / (1 + Γ)` for every `s` (`InSensitivityModel`).

## Main results

* `inSensitivityModel_pairProb_iff`: if two units are treated independently with probabilities
  `π₁, π₂ ∈ (0, 1)`, the conditional probability that the first one is treated given that
  exactly one is treated lies in `[1 / (1 + Γ), Γ / (1 + Γ)]` if and only if the treatment odds
  of the two units differ by at most the factor `Γ`.
* `inSensitivityModel_one_iff`: `Γ = 1` forces `p = 1 / 2`, the randomized paired experiment.
* `tailProb_mono`: the upper tail of a sum of independent Bernoulli variables, written as a finite
  sum over `Fin n → Bool` with product weights, is monotone in each success probability.
* `countProb_const`, `tailProb_const`: with equal success probabilities `r` the law of the count
  is `Binomial(n, r)`, with the usual closed form.
* `signTestTail_le_binomialTail`, `binomialTail_le_signTestTail`: under the sharp null hypothesis
  with discordant binary pairs, the tail probability of the sign statistic lies between the
  `Binomial(S, 1 / (1 + Γ))` and `Binomial(S, Γ / (1 + Γ))` tails, and the upper bound is attained
  (`signTestTail_upper_attained`).
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

/-- Rosenbaum's sensitivity model with parameter `Γ` for the probability `p` that the first unit
of a pair is the treated one: `1 / (1 + Γ) ≤ p ≤ Γ / (1 + Γ)`. The model is meant for `Γ ≥ 1`;
that hypothesis is added where it is used. -/
def InSensitivityModel (Γ p : ℝ) : Prop := 1 / (1 + Γ) ≤ p ∧ p ≤ Γ / (1 + Γ)

/-- The odds `π / (1 - π)` of a probability `π`. -/
noncomputable def odds (π : ℝ) : ℝ := π / (1 - π)

/-- If two units are treated independently with probabilities `π₁` and `π₂`, the conditional
probability that the first unit is treated given that exactly one of them is treated:
`π₁ (1 - π₂) / (π₁ (1 - π₂) + π₂ (1 - π₁))`. -/
noncomputable def pairProb (π₁ π₂ : ℝ) : ℝ := π₁ * (1 - π₂) / (π₁ * (1 - π₂) + π₂ * (1 - π₁))

/-- Odds-ratio form of Rosenbaum's model: for treatment probabilities `π₁, π₂ ∈ (0, 1)` and
`Γ > 0`, the conditional probability `pairProb π₁ π₂` lies in `[1 / (1 + Γ), Γ / (1 + Γ)]` if and
only if `odds π₁ ≤ Γ * odds π₂` and `odds π₂ ≤ Γ * odds π₁`, that is, the treatment odds of the
two units differ by at most a factor `Γ`. -/
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
  · rintro ⟨h, h'⟩
    constructor <;> nlinarith
  · rintro ⟨h, h'⟩
    constructor <;> nlinarith

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
theorem InSensitivityModel.mono {Γ Γ' p : ℝ} (hΓ : 0 ≤ Γ) (hle : Γ ≤ Γ')
    (h : InSensitivityModel Γ p) : InSensitivityModel Γ' p := by
  obtain ⟨h₁, h₂⟩ := h
  constructor
  · refine le_trans ?_ h₁
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · refine h₂.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- A probability allowed by the model is nonnegative. -/
theorem InSensitivityModel.nonneg {Γ p : ℝ} (hΓ : 0 ≤ Γ) (h : InSensitivityModel Γ p) :
    0 ≤ p :=
  le_trans (by positivity) h.1

/-- A probability allowed by the model is at most one. -/
theorem InSensitivityModel.le_one {Γ p : ℝ} (hΓ : 0 ≤ Γ) (h : InSensitivityModel Γ p) :
    p ≤ 1 :=
  h.2.trans ((div_le_one (by linarith)).2 (by linarith))

/-- The model is symmetric under exchanging the two units of a pair. -/
theorem InSensitivityModel.one_sub {Γ p : ℝ} (hΓ : 0 ≤ Γ) (h : InSensitivityModel Γ p) :
    InSensitivityModel Γ (1 - p) := by
  obtain ⟨h₁, h₂⟩ := h
  have e : 1 - Γ / (1 + Γ) = 1 / (1 + Γ) := by field_simp; ring
  constructor <;> [skip; skip] <;> linarith [e]

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
theorem successProb_mem {S : ℕ} {Γ : ℝ} (hΓ : 0 ≤ Γ) {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (f : Fin S → Bool) (s : Fin S) :
    InSensitivityModel Γ (successProb p f s) := by
  unfold successProb
  split_ifs
  · exact hp s
  · exact (hp s).one_sub hΓ

/-- `Γ / (1 + Γ)` is a probability for `Γ ≥ 0`. -/
theorem upper_mem_unit {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ Γ / (1 + Γ) ∧ Γ / (1 + Γ) ≤ 1 :=
  ⟨by positivity, (div_le_one (by linarith)).2 (by linarith)⟩

/-- `1 / (1 + Γ)` is a probability for `Γ ≥ 0`. -/
theorem lower_mem_unit {Γ : ℝ} (hΓ : 0 ≤ Γ) : 0 ≤ 1 / (1 + Γ) ∧ 1 / (1 + Γ) ≤ 1 :=
  ⟨by positivity, (div_le_one (by linarith)).2 (by linarith)⟩

/-- Rosenbaum's upper bound for the sign test: under the sensitivity model with parameter `Γ`,
`P(T ≥ k)` is at most the upper tail of `Binomial(S, Γ / (1 + Γ))`, for every `k`. -/
theorem signTestTail_le_binomialTail {S : ℕ} {Γ : ℝ} (hΓ : 0 ≤ Γ) {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (f : Fin S → Bool) (k : ℕ) :
    signTestTail p f k ≤ binomialTail S (Γ / (1 + Γ)) k := by
  have hm := successProb_mem hΓ hp f
  rw [signTestTail_eq_tailProb, ← tailProb_const]
  exact tailProb_mono (fun s => ⟨(hm s).nonneg hΓ, (hm s).le_one hΓ⟩)
    (fun _ => upper_mem_unit hΓ) (fun s => (hm s).2) k

/-- Rosenbaum's lower bound for the sign test: under the sensitivity model with parameter `Γ`,
`P(T ≥ k)` is at least the upper tail of `Binomial(S, 1 / (1 + Γ))`, for every `k`. -/
theorem binomialTail_le_signTestTail {S : ℕ} {Γ : ℝ} (hΓ : 0 ≤ Γ) {p : Fin S → ℝ}
    (hp : ∀ s, InSensitivityModel Γ (p s)) (f : Fin S → Bool) (k : ℕ) :
    binomialTail S (1 / (1 + Γ)) k ≤ signTestTail p f k := by
  have hm := successProb_mem hΓ hp f
  rw [signTestTail_eq_tailProb, ← tailProb_const]
  exact tailProb_mono (fun _ => lower_mem_unit hΓ)
    (fun s => ⟨(hm s).nonneg hΓ, (hm s).le_one hΓ⟩) (fun s => (hm s).1) k

/-- The upper bound is attained by the assignment probabilities `p s = Γ / (1 + Γ)` when the first
unit of every pair has the larger outcome; these lie in the model when `Γ ≥ 1`
(`inSensitivityModel_upper`). -/
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
  have h₁ := signTestTail_le_binomialTail zero_le_one hp f k
  have h₂ := binomialTail_le_signTestTail zero_le_one hp f k
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
  ⟨div_le_div_of_nonneg_right hΓ (by linarith), le_rfl⟩

end Rosenbaum

end CausalInference
