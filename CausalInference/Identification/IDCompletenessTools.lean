/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessBow
public import CausalInference.Identification.CFactor
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Tools for the completeness of the identification algorithm

General facts about finite distributions and Boolean structural causal models, used to build the
two models of the completeness proof for the identification algorithm.

## Main definitions

* `IDCompleteness.quarterBit`: the law of a Boolean bit that is true with probability `1/4`.
* `IDCompleteness.chi`: the sign character `b ↦ (-1)^b` of the two-element field.
* `IDCompleteness.ReadsParents`, `IDCompleteness.boolSCM`: a Boolean structural causal model
  given by mechanisms that read the full configuration but depend only on the parents.

## Main results

* `FiniteDist.map_comp_eq_of_bijective`: pushing a law forward along `g ∘ Φ`, for a bijection
  `Φ` that preserves the masses, is pushing it forward along `g`.
* `FiniteDist.pi_add_eq`: a product law of bits is invariant under adding a vector supported on
  fair coordinates.
* `FiniteDist.expect_pi_prod`: under a product law, the expectation of a product of coordinate
  functions is the product of the expectations.
* `IDCompleteness.probOf_parity`: the law of the parity of a set of independent bits; with
  biased bits (`IDCompleteness.probOf_parity_ne_half`) it is not fair.
* `IDCompleteness.solve_boolSCM_iff`, `IDCompleteness.solve_intervene_boolSCM_iff`: the solution
  of a model of `boolSCM` and of its submodels are characterized by the mechanisms.
* `IDCompleteness.solve_boolSCM_eq_on`: the solution on a set closed under reading depends only
  on the noise on that set.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace FiniteDist

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

/-- **Pushforward under a mass preserving bijection.** If `Φ` is a bijection of `Ω` with
`P (Φ ω) = P ω` for every `ω`, then the law of `g ∘ Φ` under `P` is the law of `g`. -/
theorem map_comp_eq_of_bijective [DecidableEq Ω'] (P : FiniteDist Ω) {Φ : Ω → Ω}
    (hΦ : Function.Bijective Φ) (hP : ∀ ω, P (Φ ω) = P ω) (g : Ω → Ω') :
    P.map (g ∘ Φ) = P.map g := by
  ext b
  rw [map_apply, map_apply, sum_filter, sum_filter]
  refine Fintype.sum_equiv (Equiv.ofBijective Φ hΦ) _ _ fun ω => ?_
  simp [hP]

/-- **Translation by fair coordinates.** A product law of bits is invariant under adding a
vector `δ` whose true coordinates carry the uniform law. -/
theorem pi_add_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → FiniteDist Bool)
    (ω δ : ι → Bool) (h : ∀ i, δ i = true → p i = uniform) : pi p (ω + δ) = pi p ω := by
  rw [pi_apply, pi_apply]
  refine prod_congr rfl fun i _ => ?_
  by_cases hi : δ i = true
  · rw [h i hi, uniform_apply, uniform_apply]
  · rw [Bool.not_eq_true] at hi
    rw [Pi.add_apply, hi, show (false : Bool) = 0 from rfl, add_zero]

/-- **Independent coordinates.** Under a product law, the expectation of the product over `S`
of functions of the coordinates is the product of the coordinate expectations. -/
theorem expect_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (p : ∀ i, FiniteDist (κ i)) (S : Finset ι) (f : ∀ i, κ i → ℝ) :
    (pi p).expect (fun ω => ∏ i ∈ S, f i (ω i)) = ∏ i ∈ S, (p i).expect (f i) := by
  unfold expect
  simp only [pi_apply]
  have key : ∀ ω : ∀ i, κ i, (∏ i, p i (ω i)) * ∏ i ∈ S, f i (ω i) =
      ∏ i, (p i (ω i) * if i ∈ S then f i (ω i) else 1) := by
    intro ω
    rw [prod_mul_distrib, prod_ite_mem univ S, univ_inter]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun i x => p i x * if i ∈ S then f i x else 1),
    ← show ∏ i, (if i ∈ S then ∑ x, p i x * f i x else 1) = ∏ i ∈ S, ∑ x, p i x * f i x by
      rw [prod_ite_mem, univ_inter]]
  refine prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, (p i).sum_eq_one]

end FiniteDist

namespace IDCompleteness

/-! ### Bits and parities -/

/-- The law of a Boolean bit that is true with probability `1/4`. -/
noncomputable def quarterBit : FiniteDist Bool where
  mass b := if b then 1 / 4 else 3 / 4
  nonneg b := by cases b <;> norm_num
  sum_eq_one := by norm_num

@[simp] theorem quarterBit_apply (b : Bool) : quarterBit b = if b then 1 / 4 else 3 / 4 := rfl

/-- Every value of `quarterBit` has positive mass. -/
theorem quarterBit_pos (b : Bool) : 0 < quarterBit b := by
  cases b <;> norm_num

/-- The sign character of the two-element field: `chi b = (-1)^b`. -/
def chi (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem chi_false : chi false = 1 := rfl

@[simp] theorem chi_true : chi true = -1 := rfl

/-- The sign character turns sums (exclusive or) into products. -/
theorem chi_add (a b : Bool) : chi (a + b) = chi a * chi b := by
  cases a <;> cases b <;> norm_num [chi, Bool.add_eq_xor]

/-- The sign character of a sum is the product of the signs. -/
theorem chi_sum {ι : Type*} (S : Finset ι) (g : ι → Bool) :
    chi (∑ i ∈ S, g i) = ∏ i ∈ S, chi (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, chi_add, ih]

/-- The expected sign of a `quarterBit` is `1/2`. -/
theorem expect_chi_quarterBit : quarterBit.expect chi = 1 / 2 := by
  simp [FiniteDist.expect, chi]
  norm_num

/-- **The law of a parity.** Under a product law of bits with expected signs `c i` on `S`, the
probability that the bits of `S` sum to `b` is `(1 + (-1)^b ∏_{i ∈ S} c i) / 2`. -/
theorem probOf_parity {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → FiniteDist Bool)
    (S : Finset ι) (b : Bool) :
    (FiniteDist.pi p).probOf (fun ω => ∑ i ∈ S, ω i = b) =
      (1 + chi b * ∏ i ∈ S, (p i).expect chi) / 2 := by
  have hind : ∀ a : Bool, (if a = b then (1 : ℝ) else 0) = (1 + chi b * chi a) / 2 := by
    intro a
    cases a <;> cases b <;> norm_num [chi]
  rw [← FiniteDist.expect_pi_prod]
  simp_rw [← chi_sum]
  unfold FiniteDist.probOf FiniteDist.prob FiniteDist.expect
  rw [sum_filter]
  have : ∀ ω : ι → Bool, (if ∑ i ∈ S, ω i = b then (FiniteDist.pi p) ω else 0) =
      (FiniteDist.pi p) ω * ((1 + chi b * chi (∑ i ∈ S, ω i)) / 2) := by
    intro ω
    rw [← hind]
    split_ifs <;> ring
  simp_rw [this]
  have h2 : ∀ ω : ι → Bool, (FiniteDist.pi p) ω * ((1 + chi b * chi (∑ i ∈ S, ω i)) / 2) =
      ((FiniteDist.pi p) ω + chi b * ((FiniteDist.pi p) ω * chi (∑ i ∈ S, ω i))) / 2 := by
    intro ω
    ring
  simp_rw [h2]
  rw [mul_sum, ← sum_div, sum_add_distrib, (FiniteDist.pi p).sum_eq_one]

/-- **A parity of biased bits is not fair.** Under a product law of bits in which every bit of
`S` is a `quarterBit`, the probability that the bits of `S` sum to `b` is not `1/2`. -/
theorem probOf_parity_ne_half {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → FiniteDist Bool)
    (S : Finset ι) (hS : ∀ i ∈ S, p i = quarterBit) (b : Bool) :
    (FiniteDist.pi p).probOf (fun ω => ∑ i ∈ S, ω i = b) ≠ 1 / 2 := by
  rw [probOf_parity, prod_congr rfl fun i hi => by rw [hS i hi, expect_chi_quarterBit],
    prod_const]
  have hpos : (0 : ℝ) < (1 / 2) ^ S.card := by positivity
  cases b
  · rw [chi_false]
    intro h
    linarith
  · rw [chi_true]
    intro h
    linarith

/-! ### Two laws with the same marginal masses -/

/-- Two laws with the same marginal masses on `O` at every configuration have the same marginal
law on `O`. -/
theorem marginal_eq_of_margAt_eq {V : Type*} [Fintype V] [DecidableEq V] {β : V → Type*}
    [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)] {p q : FiniteDist (∀ v, β v)}
    {O : Finset V} (h : ∀ c, p.margAt O c = q.margAt O c) : p.marginal O = q.marginal O := by
  ext a
  obtain ⟨w₀⟩ := p.nonempty
  rw [← FiniteDist.restrict_override O a w₀, FiniteDist.marginal_restrict,
    FiniteDist.marginal_restrict, h]

/-! ### Boolean models from mechanisms that read the parents -/

section BoolSCM

variable {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]

/-- The mechanism `mech v σ e` of every vertex `v` (a Boolean function of a full configuration
`σ` and of the noise bit `e` of `v`) depends on `σ` only through the parents of `v` in `D`. -/
def ReadsParents (mech : W → (W → Bool) → Bool → Bool) : Prop :=
  ∀ v σ σ' e, (∀ u, D.Adj u v → σ u = σ' u) → mech v σ e = mech v σ' e

/-- The Boolean structural causal model on `D` with one noise bit per vertex, of law
`noise v`, whose structural function at `v` is the mechanism `mech v` applied to the parent
values extended by `false`. -/
def boolSCM (hD : D.IsAcyclic) (mech : W → (W → Bool) → Bool → Bool)
    (noise : W → FiniteDist Bool) : SCM D (fun _ => Bool) (fun _ => Bool) where
  acyclic := hD
  f v z e := mech v (IDCompletenessBow.extendPar D v z) e
  noise := noise

variable {D} {hD : D.IsAcyclic} {mech : W → (W → Bool) → Bool → Bool}
  {noise : W → FiniteDist Bool}

/-- The structural function of `boolSCM` at the parent values of `σ` is the mechanism at `σ`. -/
theorem boolSCM_f (hm : ReadsParents D mech) (v : W) (σ : W → Bool) (e : Bool) :
    (boolSCM D hD mech noise).f v ((D.parentsFinset v).restrict σ) e = mech v σ e :=
  hm v _ _ e fun _ hu => IDCompletenessBow.extendPar_restrict_of_adj D hu σ

/-- **The solution of `boolSCM`**: `σ` is the solution at the noise `ν` if and only if every
vertex follows its mechanism, `σ v = mech v σ (ν v)`. -/
theorem solve_boolSCM_iff (hm : ReadsParents D mech) {ν σ : W → Bool} :
    (boolSCM D hD mech noise).solve ν = σ ↔ ∀ v, σ v = mech v σ (ν v) := by
  rw [eq_comm, ← SCM.isSolution_iff]
  exact forall_congr' fun v => by rw [boolSCM_f hm]

/-- **The solution of a submodel of `boolSCM`**: under `do(X := x)`, `σ` is the solution at the
noise `ν` if and only if it agrees with `x` on `X` and every other vertex follows its
mechanism. -/
theorem solve_intervene_boolSCM_iff (hm : ReadsParents D mech) (X : Finset W) (x : W → Bool)
    {ν σ : W → Bool} :
    ((boolSCM D hD mech noise).intervene X x).solve ν = σ ↔
      (∀ v ∈ X, σ v = x v) ∧ ∀ v ∉ X, σ v = mech v σ (ν v) := by
  rw [eq_comm, ← SCM.isSolution_iff, SCM.isSolution_intervene_iff]
  exact and_congr_right' (forall₂_congr fun v _ => by rw [boolSCM_f hm])

/-- The solution of `boolSCM` follows the mechanisms. -/
theorem solve_boolSCM_apply (hm : ReadsParents D mech) (ν : W → Bool) (v : W) :
    (boolSCM D hD mech noise).solve ν v = mech v ((boolSCM D hD mech noise).solve ν) (ν v) :=
  (solve_boolSCM_iff hm).1 rfl v

/-- **Locality of the solution.** If the mechanisms of the vertices of `A` read only vertices of
`A` among their parents, two noise values that agree on `A` give solutions that agree on
`A`. -/
theorem solve_boolSCM_eq_on (hm : ReadsParents D mech) (A : Set W)
    (hA : ∀ v ∈ A, ∀ σ σ' e, (∀ u ∈ A, D.Adj u v → σ u = σ' u) → mech v σ e = mech v σ' e)
    {ν ν' : W → Bool} (hν : ∀ v ∈ A, ν v = ν' v) :
    ∀ v ∈ A, (boolSCM D hD mech noise).solve ν v = (boolSCM D hD mech noise).solve ν' v := by
  intro v
  induction v using hD.wellFounded_adj.induction with
  | _ v ih =>
    intro hv
    rw [solve_boolSCM_apply hm ν v, solve_boolSCM_apply hm ν' v, hν v hv]
    exact hA v hv _ _ _ fun u hu huv => ih u huv hu

end BoolSCM

end IDCompleteness

end CausalInference
