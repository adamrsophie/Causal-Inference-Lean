/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Finset.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite probability distributions

A finite probability distribution on a finite type `Ω` is a real-valued mass function that is
nonnegative and sums to one. Real values (rather than `ENNReal`, as in Mathlib's `PMF`) keep the
arithmetic of the finite theory easy; the bridge `FiniteDist.toPMF` and `FiniteDist.toMeasure`
connects it to Mathlib's measure theory.

## Main definitions

* `CausalInference.FiniteDist Ω`: a nonnegative mass function on a finite type summing to one.
* `FiniteDist.prob p s`, `FiniteDist.probOf p P`: the probability of a finset `s` and of the
  event described by a decidable predicate `P`.
* `FiniteDist.expect p f`: the expectation of a real function.
* `FiniteDist.map p f`: the pushforward (law) of `p` along `f`.
* `FiniteDist.pure a`, `FiniteDist.uniform`, `FiniteDist.prod p q`, `FiniteDist.pi p`: the point
  mass, the uniform distribution, the product distribution and the product of a family.
* `FiniteDist.cond p P h`: the conditional distribution given an event `P` of positive
  probability.
* `FiniteDist.toPMF`, `FiniteDist.toMeasure`: the associated `PMF` and probability measure.
* `FiniteDist.marginal p S`: for a joint distribution on configurations `x : ∀ v, α v`, the
  marginal on the coordinates in `S : Finset V`, a distribution on `∀ v : S, α v`.
* `FiniteDist.margAt p S x`: the marginal mass of the cylinder of configurations that agree with
  `x` on `S`. It equals `p.marginal S (S.restrict x)` (`FiniteDist.marginal_restrict`).
* `FiniteDist.condMargAt p S T s t h`: the coordinate conditional probability
  `P(X_S = s_S | X_T = t_T)` for `h : 0 < P(X_T = t_T)`.

## Representation of marginals

Configurations of a set `S` of coordinates are the dependent functions `∀ v : S, α v`, and the
passage from a full configuration is Mathlib's `Finset.restrict`. This makes `marginal p S` a
genuine distribution, so all lemmas about `map` apply to it. For computations it is often more
readable to keep a full configuration `x` and evaluate the marginal at its restriction; this is
`margAt p S x`, a function of full configurations that depends only on the coordinates in `S`.
Statements about conditional independence and factorization are phrased with `margAt`, which
avoids casts between the configuration types of different finsets.

## Main results

* `FiniteDist.map_map`, `FiniteDist.marginal_marginal` (marginalizing twice),
  `FiniteDist.margAt_univ` (the marginal onto everything is `p`), `FiniteDist.margAt_empty`,
  and `FiniteDist.margAt_eq_sum_margAt` (marginalizing a marginal, in cylinder form).
* `FiniteDist.toMeasure_apply_finset`: the measure of a finset is the sum of the masses;
  `FiniteDist.integral_toMeasure`, the integral is the expectation; `FiniteDist.toMeasure_map`,
  the measure of a pushforward is the pushforward measure.
* `FiniteDist.probOf_map`, `FiniteDist.prob_piFinset`, `FiniteDist.map_pi_eval`,
  `FiniteDist.map_pi_eval_pair`: probabilities under pushforwards and product laws.
* `FiniteDist.probOf_cond`: `P(Q | P) = P(P ∧ Q) / P(P)`.
* `FiniteDist.condMargAt_self`, `FiniteDist.margAt_union_eq_condMargAt_mul`,
  `FiniteDist.condMargAt_union` (the chain rule), `FiniteDist.sum_condMargAt` (normalization),
  `FiniteDist.condMargAt_eq_zero_of_ne` (inconsistent assignments on an overlap).

Conditional probabilities are defined only given events of positive probability. Conditional
independence and factorization are stated in product form, which needs no division.

This is the finite discrete setting of Lauritzen (1996), Graphical Models, chapter 3.
-/

@[expose] public section

namespace CausalInference

open Finset

/-- A finite probability distribution on a finite type `Ω`: a real-valued mass function that is
nonnegative and sums to one. -/
structure FiniteDist (Ω : Type*) [Fintype Ω] where
  /-- The probability mass of each outcome. -/
  mass : Ω → ℝ
  /-- Masses are nonnegative. -/
  nonneg : ∀ ω, 0 ≤ mass ω
  /-- Masses sum to one. -/
  sum_eq_one : ∑ ω, mass ω = 1

namespace FiniteDist

variable {Ω Ω' Ω'' : Type*} [Fintype Ω] [Fintype Ω'] [Fintype Ω'']

instance : CoeFun (FiniteDist Ω) (fun _ => Ω → ℝ) := ⟨FiniteDist.mass⟩

@[ext] theorem ext {p q : FiniteDist Ω} (h : ∀ ω, p ω = q ω) : p = q := by
  cases p; cases q; congr; exact funext h

/-- A finite distribution lives on a nonempty type. -/
theorem nonempty (p : FiniteDist Ω) : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := p.sum_eq_one
  simp at this

/-- Each mass is at most one. -/
theorem le_one (p : FiniteDist Ω) (ω : Ω) : p ω ≤ 1 := by
  rw [← p.sum_eq_one]
  exact single_le_sum (fun ω _ => p.nonneg ω) (mem_univ ω)

/-! ### Probability and expectation -/

/-- The probability of the event `s`: the sum of the masses of its outcomes. -/
def prob (p : FiniteDist Ω) (s : Finset Ω) : ℝ := ∑ ω ∈ s, p ω

theorem prob_nonneg (p : FiniteDist Ω) (s : Finset Ω) : 0 ≤ p.prob s :=
  sum_nonneg fun ω _ => p.nonneg ω

@[simp] theorem prob_univ (p : FiniteDist Ω) : p.prob univ = 1 := p.sum_eq_one

@[simp] theorem prob_empty (p : FiniteDist Ω) : p.prob ∅ = 0 := sum_empty

/-- Probability is monotone. -/
theorem prob_mono (p : FiniteDist Ω) {s t : Finset Ω} (h : s ⊆ t) : p.prob s ≤ p.prob t :=
  sum_le_sum_of_subset_of_nonneg h fun ω _ _ => p.nonneg ω

theorem prob_le_one (p : FiniteDist Ω) (s : Finset Ω) : p.prob s ≤ 1 :=
  (p.prob_mono (subset_univ s)).trans_eq p.prob_univ

/-- Probability of a disjoint union. -/
theorem prob_union [DecidableEq Ω] (p : FiniteDist Ω) {s t : Finset Ω} (h : Disjoint s t) :
    p.prob (s ∪ t) = p.prob s + p.prob t :=
  sum_union h

/-- The probability of the event described by a decidable predicate `P`. -/
def probOf (p : FiniteDist Ω) (P : Ω → Prop) [DecidablePred P] : ℝ := p.prob (univ.filter P)

section probOf

variable (p : FiniteDist Ω) {P Q : Ω → Prop} [DecidablePred P] [DecidablePred Q]

theorem probOf_nonneg : 0 ≤ p.probOf P := p.prob_nonneg _

/-- Events described by equivalent predicates have the same probability. -/
theorem probOf_congr (h : ∀ ω, P ω ↔ Q ω) : p.probOf P = p.probOf Q := by
  rw [probOf, probOf, filter_congr fun ω _ => h ω]

/-- Probability is monotone under implication of predicates. -/
theorem probOf_mono (h : ∀ ω, P ω → Q ω) : p.probOf P ≤ p.probOf Q :=
  p.prob_mono fun ω => by simpa using h ω

/-- An impossible event has probability zero. -/
theorem probOf_eq_zero (h : ∀ ω, ¬ P ω) : p.probOf P = 0 := by
  rw [probOf, filter_false_of_mem fun ω _ => h ω, prob_empty]

/-- The mass of an outcome in an event is at most the probability of the event. -/
theorem le_probOf (ω : Ω) (h : P ω) : p ω ≤ p.probOf P :=
  single_le_sum (fun ω _ => p.nonneg ω) (by simpa using h)

/-- Law of total probability: split an event along the values of a random variable `Y` that
lands in `t` on the event. -/
theorem probOf_eq_sum {γ : Type*} [DecidableEq γ] (Y : Ω → γ) (t : Finset γ)
    (h : ∀ ω, P ω → Y ω ∈ t) :
    p.probOf P = ∑ b ∈ t, p.probOf (fun ω => P ω ∧ Y ω = b) := by
  unfold probOf prob
  rw [← sum_fiberwise_of_maps_to (s := univ.filter P) (t := t) (g := Y)
    (fun ω hω => h ω (mem_filter.1 hω).2)]
  refine sum_congr rfl fun b _ => ?_
  rw [filter_filter]

/-- Law of total probability over all values of a random variable with finite codomain. -/
theorem probOf_eq_sum_univ {γ : Type*} [Fintype γ] [DecidableEq γ] (Y : Ω → γ) :
    p.probOf P = ∑ b, p.probOf (fun ω => P ω ∧ Y ω = b) :=
  p.probOf_eq_sum Y univ fun _ _ => mem_univ _

/-- Law of total probability over the values that a random variable actually takes; no
finiteness of the codomain is needed. -/
theorem probOf_eq_sum_image {γ : Type*} [DecidableEq γ] (Y : Ω → γ) :
    p.probOf P = ∑ b ∈ univ.image Y, p.probOf (fun ω => P ω ∧ Y ω = b) :=
  p.probOf_eq_sum Y _ fun ω _ => mem_image_of_mem Y (mem_univ ω)

end probOf

/-- The expectation of a real function `f`. -/
def expect (p : FiniteDist Ω) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

@[simp] theorem expect_const (p : FiniteDist Ω) (c : ℝ) : p.expect (fun _ => c) = c := by
  simp [expect, ← sum_mul, p.sum_eq_one]

theorem expect_add (p : FiniteDist Ω) (f g : Ω → ℝ) :
    p.expect (f + g) = p.expect f + p.expect g := by
  simp [expect, mul_add, sum_add_distrib]

theorem expect_smul (p : FiniteDist Ω) (c : ℝ) (f : Ω → ℝ) :
    p.expect (c • f) = c * p.expect f := by
  simp [expect, mul_sum, mul_left_comm]

/-- The probability of an event is the expectation of its indicator. -/
theorem prob_eq_expect (p : FiniteDist Ω) (s : Finset Ω) [DecidablePred (· ∈ s)] :
    p.prob s = p.expect (fun ω => if ω ∈ s then 1 else 0) := by
  simp [prob, expect]

/-- Expectation is monotone. -/
theorem expect_mono (p : FiniteDist Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    p.expect f ≤ p.expect g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω)

/-! ### Pushforward, point mass, product -/

/-- The pushforward of `p` along `f`, that is, the law of the random variable `f`:
the mass of `b` is the probability that `f` takes the value `b`. -/
def map [DecidableEq Ω'] (p : FiniteDist Ω) (f : Ω → Ω') : FiniteDist Ω' where
  mass b := ∑ ω ∈ univ.filter (fun ω => f ω = b), p ω
  nonneg b := sum_nonneg fun ω _ => p.nonneg ω
  sum_eq_one := by
    rw [sum_fiberwise univ f (fun ω => p ω)]
    exact p.sum_eq_one

theorem map_apply [DecidableEq Ω'] (p : FiniteDist Ω) (f : Ω → Ω') (b : Ω') :
    p.map f b = ∑ ω ∈ univ.filter (fun ω => f ω = b), p ω := rfl

theorem map_apply_eq_prob [DecidableEq Ω'] (p : FiniteDist Ω) (f : Ω → Ω') (b : Ω') :
    p.map f b = p.prob (univ.filter fun ω => f ω = b) := rfl

/-- The expectation of a function of `f` under `p` is the expectation under the law of `f`. -/
theorem expect_map [DecidableEq Ω'] (p : FiniteDist Ω) (f : Ω → Ω') (g : Ω' → ℝ) :
    (p.map f).expect g = p.expect (g ∘ f) := by
  simp only [expect, map_apply, sum_mul, Function.comp]
  rw [← sum_fiberwise univ f (fun ω => p ω * g (f ω))]
  refine sum_congr rfl fun b _ => sum_congr rfl fun ω hω => ?_
  rw [(mem_filter.1 hω).2]

/-- The probability of an event under a pushforward is the probability of its preimage. -/
theorem probOf_map [DecidableEq Ω'] (p : FiniteDist Ω) (f : Ω → Ω') (P : Ω' → Prop)
    [DecidablePred P] : (p.map f).probOf P = p.probOf (fun ω => P (f ω)) := by
  unfold probOf prob
  simp only [map_apply]
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun ω => P (f ω))
    (t := univ.filter P) (g := f) (fun ω hω => by simpa using hω)]
  refine sum_congr rfl fun b hb => sum_congr ?_ fun _ _ => rfl
  ext ω
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact ⟨fun h => ⟨h ▸ hb, h⟩, fun h => h.2⟩

/-- Pushing forward twice is pushing forward along the composite. -/
theorem map_map [DecidableEq Ω'] [DecidableEq Ω''] (p : FiniteDist Ω) (f : Ω → Ω')
    (g : Ω' → Ω'') : (p.map f).map g = p.map (g ∘ f) := by
  ext c
  simp only [map_apply, Function.comp]
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun ω => g (f ω) = c)
    (t := univ.filter fun b => g b = c) (g := f) (by simp)]
  refine sum_congr rfl fun b hb => sum_congr ?_ fun _ _ => rfl
  ext ω
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact ⟨fun h => ⟨h ▸ hb, h⟩, fun h => h.2⟩

/-- The point mass at `a`. -/
def pure [DecidableEq Ω] (a : Ω) : FiniteDist Ω where
  mass ω := if ω = a then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp

@[simp] theorem pure_apply [DecidableEq Ω] (a ω : Ω) :
    pure a ω = if ω = a then 1 else 0 := rfl

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform [Nonempty Ω] : FiniteDist Ω where
  mass _ := 1 / Fintype.card Ω
  nonneg _ := by positivity
  sum_eq_one := by simp

@[simp] theorem uniform_apply [Nonempty Ω] (ω : Ω) :
    (uniform : FiniteDist Ω) ω = 1 / Fintype.card Ω := rfl

/-- The product of two distributions: the joint law of two independent coordinates. -/
def prod (p : FiniteDist Ω) (q : FiniteDist Ω') : FiniteDist (Ω × Ω') where
  mass ω := p ω.1 * q ω.2
  nonneg ω := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp [← mul_sum, q.sum_eq_one, p.sum_eq_one]

@[simp] theorem prod_apply (p : FiniteDist Ω) (q : FiniteDist Ω') (ω : Ω × Ω') :
    p.prod q ω = p ω.1 * q ω.2 := rfl

/-- The first marginal of a product distribution. -/
theorem map_fst_prod [DecidableEq Ω] (p : FiniteDist Ω) (q : FiniteDist Ω') :
    (p.prod q).map Prod.fst = p := by
  ext a
  rw [map_apply, ← univ_product_univ, filter_product_left (fun ω => ω = a), sum_product]
  simp [← mul_sum, q.sum_eq_one, filter_eq']

/-- The second marginal of a product distribution. -/
theorem map_snd_prod [DecidableEq Ω'] (p : FiniteDist Ω) (q : FiniteDist Ω') :
    (p.prod q).map Prod.snd = q := by
  ext b
  rw [map_apply, ← univ_product_univ, filter_product_right (fun ω => ω = b), sum_product]
  simp [filter_eq', ← sum_mul, p.sum_eq_one]

/-! ### Products of families -/

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- The product of a family of finite distributions: the joint law of independent coordinates,
with mass `∏ i, p i (ω i)`. -/
def pi (p : ∀ i, FiniteDist (κ i)) : FiniteDist (∀ i, κ i) where
  mass ω := ∏ i, p i (ω i)
  nonneg ω := prod_nonneg fun i _ => (p i).nonneg _
  sum_eq_one := by
    rw [← Fintype.prod_sum]
    exact prod_eq_one fun i _ => (p i).sum_eq_one

@[simp] theorem pi_apply (p : ∀ i, FiniteDist (κ i)) (ω : ∀ i, κ i) :
    pi p ω = ∏ i, p i (ω i) := rfl

/-- The product law of a rectangle `∏ i, t i` is the product of the probabilities of its
sides. -/
theorem prob_piFinset (p : ∀ i, FiniteDist (κ i)) (t : ∀ i, Finset (κ i)) :
    (pi p).prob (Fintype.piFinset t) = ∏ i, (p i).prob (t i) := by
  simp only [prob, pi_apply]
  exact (prod_univ_sum t fun i e => p i e).symm

/-- The coordinate `i` of a product law has law `p i`. -/
theorem map_pi_eval [∀ i, DecidableEq (κ i)] (p : ∀ i, FiniteDist (κ i))
    (i : ι) : (pi p).map (fun ω => ω i) = p i := by
  ext a
  rw [map_apply_eq_prob]
  have h : (univ.filter fun ω : ∀ i, κ i => ω i = a) =
      Fintype.piFinset (Function.update (fun _ => univ) i {a}) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · intro h
      simpa using h i
  rw [h, prob_piFinset, Fintype.prod_eq_single i]
  · simp [prob]
  · intro j hj
    simp [Function.update_of_ne hj]

/-- The probability that the coordinate `i` of a product law satisfies `P` is the probability
of `P` under `p i`. -/
theorem probOf_pi_eval (p : ∀ i, FiniteDist (κ i)) (i : ι) (P : κ i → Prop)
    [DecidablePred P] : (pi p).probOf (fun ω => P (ω i)) = (p i).probOf P := by
  classical
  rw [← probOf_map, map_pi_eval]

/-- Two distinct coordinates of a product law are independent with the given laws: the joint law
of `(ω i, ω j)` is the product of `p i` and `p j`. -/
theorem map_pi_eval_pair [∀ i, DecidableEq (κ i)] (p : ∀ i, FiniteDist (κ i)) {i j : ι}
    (hij : i ≠ j) : (pi p).map (fun ω => (ω i, ω j)) = (p i).prod (p j) := by
  ext ⟨a, b⟩
  rw [map_apply_eq_prob]
  have h : (univ.filter fun ω : ∀ i, κ i => (ω i, ω j) = (a, b)) =
      Fintype.piFinset (Function.update (Function.update (fun _ => univ) i {a}) j {b}) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩ k
      by_cases hkj : k = j
      · subst hkj; simp
      · rw [Function.update_of_ne hkj]
        by_cases hki : k = i
        · subst hki; simp
        · simp [Function.update_of_ne hki]
    · intro h
      refine ⟨?_, by simpa using h j⟩
      have := h i
      rwa [Function.update_of_ne hij, Function.update_self, mem_singleton] at this
  rw [h, prob_piFinset, Fintype.prod_eq_mul i j hij]
  · rw [Function.update_of_ne hij, Function.update_self, Function.update_self]
    simp [prob]
  · intro k hk
    rw [Function.update_of_ne hk.2, Function.update_of_ne hk.1]
    simpa [prob] using (p k).sum_eq_one

end Pi

/-! ### Conditioning on an event of positive probability -/

/-- The conditional distribution of `p` given an event `P` of positive probability: mass
`p ω / P(P)` on the outcomes of `P` and `0` elsewhere. -/
noncomputable def cond (p : FiniteDist Ω) (P : Ω → Prop) [DecidablePred P]
    (h : 0 < p.probOf P) : FiniteDist Ω where
  mass ω := if P ω then p ω / p.probOf P else 0
  nonneg ω := by
    split_ifs
    · exact div_nonneg (p.nonneg ω) h.le
    · exact le_rfl
  sum_eq_one := by
    rw [← sum_filter, ← sum_div]
    exact div_self h.ne'

/-- Probabilities under a conditional distribution: `P(Q | P) = P(P ∧ Q) / P(P)`. -/
theorem probOf_cond (p : FiniteDist Ω) (P : Ω → Prop) [DecidablePred P] (h : 0 < p.probOf P)
    (Q : Ω → Prop) [DecidablePred Q] :
    (p.cond P h).probOf Q = p.probOf (fun ω => P ω ∧ Q ω) / p.probOf P := by
  unfold probOf prob
  rw [sum_filter, sum_filter, sum_div]
  refine sum_congr rfl fun ω _ => ?_
  change (if Q ω then (if P ω then p ω / p.probOf P else 0) else 0) = _
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ, probOf, prob]

/-! ### Bridge to Mathlib's `PMF` and measures -/

/-- The `PMF` with the same masses (converted to `ENNReal`). -/
noncomputable def toPMF (p : FiniteDist Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (p ω)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => p.nonneg ω, p.sum_eq_one, ENNReal.ofReal_one]

@[simp] theorem toPMF_apply (p : FiniteDist Ω) (ω : Ω) :
    p.toPMF ω = ENNReal.ofReal (p ω) := rfl

/-- The probability measure with the same masses, on any measurable space structure in which
singletons are measurable. -/
noncomputable def toMeasure [MeasurableSpace Ω] (p : FiniteDist Ω) :
    MeasureTheory.Measure Ω :=
  p.toPMF.toMeasure

instance [MeasurableSpace Ω] (p : FiniteDist Ω) :
    MeasureTheory.IsProbabilityMeasure p.toMeasure :=
  PMF.toMeasure.isProbabilityMeasure _

/-- The measure of a finset is the sum of the masses of its points. -/
theorem toMeasure_apply_finset [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : FiniteDist Ω) (s : Finset Ω) : p.toMeasure s = ENNReal.ofReal (p.prob s) := by
  rw [toMeasure, PMF.toMeasure_apply_finset, prob,
    ENNReal.ofReal_sum_of_nonneg fun ω _ => p.nonneg ω]
  rfl

/-- The real-valued measure of a finset is its probability. -/
theorem toMeasure_real_finset [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : FiniteDist Ω) (s : Finset Ω) : (p.toMeasure s).toReal = p.prob s := by
  rw [toMeasure_apply_finset, ENNReal.toReal_ofReal (p.prob_nonneg s)]

/-- The integral of a real function against the associated measure is the expectation. -/
theorem integral_toMeasure [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : FiniteDist Ω) (f : Ω → ℝ) : ∫ ω, f ω ∂p.toMeasure = p.expect f := by
  rw [MeasureTheory.integral_fintype (MeasureTheory.Integrable.of_finite), expect]
  refine sum_congr rfl fun ω _ => ?_
  have h := p.toMeasure_real_finset {ω}
  rw [coe_singleton] at h
  rw [MeasureTheory.measureReal_def, h, smul_eq_mul]
  simp [prob]

/-- The measure associated with a pushforward is the pushforward of the associated measure. -/
theorem toMeasure_map [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [MeasurableSpace Ω']
    [MeasurableSingletonClass Ω'] [DecidableEq Ω'] (p : FiniteDist Ω) (f : Ω → Ω') :
    (p.map f).toMeasure = p.toMeasure.map f := by
  classical
  have hf : Measurable f := fun s _ => (Set.toFinite _).measurableSet
  ext s hs
  rw [MeasureTheory.Measure.map_apply hf hs, ← (Set.toFinite (f ⁻¹' s)).coe_toFinset,
    toMeasure_apply_finset]
  conv_lhs => rw [← (Set.toFinite s).coe_toFinset, toMeasure_apply_finset]
  congr 1
  have : (Set.toFinite (f ⁻¹' s)).toFinset = univ.filter fun ω => f ω ∈ s := by
    ext ω; simp
  rw [this, show p.prob (univ.filter fun ω => f ω ∈ s) = p.probOf (fun ω => f ω ∈ s) from rfl,
    ← probOf_map (P := (· ∈ s))]
  unfold probOf
  congr 1
  ext b; simp

/-! ### Joint distributions of several variables and their marginals -/

section Marginal

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- The configurations that agree with `x` on the coordinates in `S` (a cylinder set). -/
def agreeOn (S : Finset V) (x : ∀ v, α v) : Finset (∀ v, α v) :=
  univ.filter fun y => ∀ v ∈ S, y v = x v

@[simp] theorem mem_agreeOn {S : Finset V} {x y : ∀ v, α v} :
    y ∈ agreeOn S x ↔ ∀ v ∈ S, y v = x v := by
  simp [agreeOn]

theorem mem_agreeOn_self (S : Finset V) (x : ∀ v, α v) : x ∈ agreeOn S x := by simp

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- Two configurations have the same restriction to `S` iff they agree on `S`. -/
theorem restrict_eq_restrict_iff {S : Finset V} {x y : ∀ v, α v} :
    S.restrict y = S.restrict x ↔ ∀ v ∈ S, y v = x v := by
  simp [funext_iff, Finset.restrict]

theorem agreeOn_congr {S : Finset V} {x x' : ∀ v, α v} (h : ∀ v ∈ S, x v = x' v) :
    agreeOn S x = agreeOn S x' := by
  ext y
  simp only [mem_agreeOn]
  exact forall₂_congr fun v hv => by rw [h v hv]

/-- The marginal of a joint distribution on the coordinates in `S`: the law of the restriction
of the configuration to `S`. -/
def marginal (p : FiniteDist (∀ v, α v)) (S : Finset V) : FiniteDist (∀ v : S, α v) :=
  p.map S.restrict

/-- The marginal mass at `x` on `S`: the probability that the configuration agrees with `x` on
`S`. This depends only on the coordinates of `x` in `S` (`FiniteDist.margAt_congr`). -/
def margAt (p : FiniteDist (∀ v, α v)) (S : Finset V) (x : ∀ v, α v) : ℝ :=
  p.prob (agreeOn S x)

/-- The marginal mass at `x` is the marginal distribution evaluated at the restriction of `x`.
-/
theorem marginal_restrict (p : FiniteDist (∀ v, α v)) (S : Finset V) (x : ∀ v, α v) :
    p.marginal S (S.restrict x) = p.margAt S x := by
  simp only [marginal, map_apply, margAt, prob, agreeOn, restrict_eq_restrict_iff]

theorem margAt_eq_probOf (p : FiniteDist (∀ v, α v)) (S : Finset V) (x : ∀ v, α v) :
    p.margAt S x = p.probOf (fun y => ∀ v ∈ S, y v = x v) := rfl

theorem margAt_nonneg (p : FiniteDist (∀ v, α v)) (S : Finset V) (x : ∀ v, α v) :
    0 ≤ p.margAt S x :=
  p.prob_nonneg _

theorem margAt_le_one (p : FiniteDist (∀ v, α v)) (S : Finset V) (x : ∀ v, α v) :
    p.margAt S x ≤ 1 :=
  p.prob_le_one _

/-- The marginal mass is antitone in the set of coordinates. -/
theorem margAt_anti (p : FiniteDist (∀ v, α v)) {S T : Finset V} (h : S ⊆ T) (x : ∀ v, α v) :
    p.margAt T x ≤ p.margAt S x := by
  simp only [margAt_eq_probOf]
  exact p.probOf_mono fun y hy v hv => hy v (h hv)

theorem margAt_congr (p : FiniteDist (∀ v, α v)) (S : Finset V) {x x' : ∀ v, α v}
    (h : ∀ v ∈ S, x v = x' v) : p.margAt S x = p.margAt S x' := by
  rw [margAt, margAt, agreeOn_congr h]

/-- The marginal onto all coordinates is the distribution itself. -/
@[simp] theorem margAt_univ (p : FiniteDist (∀ v, α v)) (x : ∀ v, α v) :
    p.margAt univ x = p x := by
  have : agreeOn univ x = {x} := by
    ext y
    simp [funext_iff]
  rw [margAt, this, prob, sum_singleton]

/-- The marginal onto no coordinates has mass one. -/
@[simp] theorem margAt_empty (p : FiniteDist (∀ v, α v)) (x : ∀ v, α v) :
    p.margAt ∅ x = 1 := by
  have : agreeOn (∅ : Finset V) x = univ := by
    ext y
    simp
  rw [margAt, this, prob_univ]

/-- Marginalizing twice: the marginal on `S` of the marginal on `T ⊇ S` is the marginal on `S`.
-/
theorem marginal_marginal (p : FiniteDist (∀ v, α v)) {S T : Finset V} (hST : S ⊆ T) :
    (p.marginal T).map (Finset.restrict₂ hST) = p.marginal S := by
  rw [marginal, map_map]
  rfl

/-- Marginalizing a marginal, in cylinder form: for `A ⊆ B`, the marginal mass on `A` at `x` is
the sum of the marginal masses on `B` over the configurations that agree with `x` outside
`B \ A`. -/
theorem margAt_eq_sum_margAt (p : FiniteDist (∀ v, α v)) {A B : Finset V} (hAB : A ⊆ B)
    (x : ∀ v, α v) :
    p.margAt A x = ∑ y ∈ agreeOn (B \ A)ᶜ x, p.margAt B y := by
  unfold margAt prob
  rw [← sum_fiberwise_of_maps_to (s := agreeOn A x) (t := agreeOn (B \ A)ᶜ x)
    (g := fun z v => if v ∈ B then z v else x v) ?_]
  · refine sum_congr rfl fun y hy => sum_congr ?_ fun _ _ => rfl
    simp only [mem_agreeOn, mem_compl, mem_sdiff, not_and, not_not] at hy
    ext z
    simp only [mem_filter, mem_agreeOn]
    constructor
    · rintro ⟨_, hg⟩ v hv
      rw [← hg]
      simp [hv]
    · intro hz
      refine ⟨fun v hv => (hz v (hAB hv)).trans (hy v fun _ => hv), funext fun v => ?_⟩
      by_cases hv : v ∈ B
      · simp [hv, hz v hv]
      · simpa [hv] using (hy v fun h => absurd h hv).symm
  · intro z hz
    simp only [mem_agreeOn, mem_compl, mem_sdiff, not_and, not_not] at hz ⊢
    intro v hv
    by_cases hvB : v ∈ B
    · simp [hvB, hz v (hv hvB)]
    · simp [hvB]

/-- Summing over the configurations that agree with `x` except at one coordinate `s` is summing
over the values at `s`. -/
theorem sum_agreeOn_compl_singleton {M : Type*} [AddCommMonoid M] (f : (∀ v, α v) → M)
    (s : V) (x : ∀ v, α v) :
    ∑ y ∈ agreeOn ({s} : Finset V)ᶜ x, f y = ∑ a : α s, f (Function.update x s a) := by
  have : agreeOn ({s} : Finset V)ᶜ x = univ.image (fun a => Function.update x s a) := by
    ext y
    simp only [mem_agreeOn, mem_compl, mem_singleton, mem_image, mem_univ, true_and]
    constructor
    · intro hy
      refine ⟨y s, funext fun v => ?_⟩
      by_cases hv : v = s
      · subst hv; simp
      · simp [hv, hy v hv]
    · rintro ⟨a, rfl⟩ v hv
      simp [hv]
  rw [this, sum_image fun a _ b _ h => Function.update_injective x s h]

/-! ### Coordinate conditional probabilities -/

/-- The coordinate conditional probability `P(X_S = s_S | X_T = t_T)`, for a conditioning value
of positive probability: the marginal mass on `S` at `s` under the conditional distribution given
that the configuration agrees with `t` on `T`. The values on `S` and on `T` are taken from two
separate configurations, so an assignment that is inconsistent on `S ∩ T` gets probability zero
(`FiniteDist.condMargAt_eq_zero_of_ne`). -/
noncomputable def condMargAt (p : FiniteDist (∀ v, α v)) (S T : Finset V) (s t : ∀ v, α v)
    (h : 0 < p.margAt T t) : ℝ :=
  (p.cond (fun y => ∀ v ∈ T, y v = t v) (p.margAt_eq_probOf T t ▸ h)).margAt S s

variable (p : FiniteDist (∀ v, α v)) {S T U : Finset V}

/-- The coordinate conditional probability as a ratio:
`P(X_S = s_S | X_T = t_T) = P(X_S = s_S, X_T = t_T) / P(X_T = t_T)`. -/
theorem condMargAt_eq (s t : ∀ v, α v) (h : 0 < p.margAt T t) :
    p.condMargAt S T s t h =
      p.probOf (fun y => (∀ v ∈ S, y v = s v) ∧ ∀ v ∈ T, y v = t v) / p.margAt T t := by
  rw [condMargAt, margAt_eq_probOf _ S s, probOf_cond]
  congr 1
  exact p.probOf_congr fun y => and_comm

theorem condMargAt_nonneg (s t : ∀ v, α v) (h : 0 < p.margAt T t) :
    0 ≤ p.condMargAt S T s t h :=
  margAt_nonneg _ _ _

/-- At a single configuration the coordinate conditional probability is the ratio of two
marginal masses, `p(x_{S ∪ T}) / p(x_T)`. -/
theorem condMargAt_self (x : ∀ v, α v) (h : 0 < p.margAt T x) :
    p.condMargAt S T x x h = p.margAt (S ∪ T) x / p.margAt T x := by
  rw [condMargAt_eq, margAt_eq_probOf]
  congr 1
  exact p.probOf_congr fun y => by simp only [mem_union, or_imp, forall_and]

/-- An assignment that is inconsistent on the overlap `S ∩ T` has conditional probability
zero. -/
theorem condMargAt_eq_zero_of_ne (s t : ∀ v, α v) (h : 0 < p.margAt T t) {v : V} (hvS : v ∈ S)
    (hvT : v ∈ T) (hst : s v ≠ t v) : p.condMargAt S T s t h = 0 := by
  rw [condMargAt_eq, p.probOf_eq_zero fun y hy => hst ((hy.1 v hvS).symm.trans (hy.2 v hvT)),
    zero_div]

/-- The chain rule, first form: `p(x_{S ∪ T}) = P(x_S | x_T) * p(x_T)`. -/
theorem margAt_union_eq_condMargAt_mul (x : ∀ v, α v) (h : 0 < p.margAt T x) :
    p.margAt (S ∪ T) x = p.condMargAt S T x x h * p.margAt T x := by
  rw [condMargAt_self, div_mul_cancel₀ _ h.ne']

/-- The chain rule: `P(x_{S ∪ T} | x_U) = P(x_S | x_{T ∪ U}) * P(x_T | x_U)`. -/
theorem condMargAt_union (x : ∀ v, α v) (hTU : 0 < p.margAt (T ∪ U) x)
    (hU : 0 < p.margAt U x) :
    p.condMargAt (S ∪ T) U x x hU = p.condMargAt S (T ∪ U) x x hTU * p.condMargAt T U x x hU := by
  rw [condMargAt_self, condMargAt_self, condMargAt_self, union_assoc,
    div_mul_div_cancel₀ hTU.ne']

/-- Normalization: summing the coordinate conditional probability over the configurations of `S`
(the configurations that agree with a fixed `x` outside `S`) gives one. -/
theorem sum_condMargAt (x t : ∀ v, α v) (h : 0 < p.margAt T t) :
    ∑ y ∈ agreeOn Sᶜ x, p.condMargAt S T y t h = 1 := by
  have := (p.cond (fun y => ∀ v ∈ T, y v = t v)
    (p.margAt_eq_probOf T t ▸ h)).margAt_eq_sum_margAt (empty_subset S) x
  rw [margAt_empty, sdiff_empty] at this
  exact this.symm

end Marginal

end FiniteDist

end CausalInference
