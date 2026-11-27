/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Counterfactuals

/-!
# Actual causation

The Halpern and Pearl definition of actual causation (Pearl 2009, Definition 10.4.2; Halpern and
Pearl 2005) and sustenance (Pearl 2009, Definition 10.2.1) in a finite structural causal model at
a fixed noise value, with a decidable checker, and the standard examples checked by `decide`.

## Main definitions

* `SCM.iterSolve M u y₀`: the solution computed by iterating the structural equations `card V`
  times; `SCM.iterSolve_eq` proves it is `M.solve u`. Unlike `SCM.solve` (well-founded
  recursion), it reduces in the kernel, which makes the checkers below usable by `decide`.
* `HPCause.AC1`, `HPCause.AC2`, `HPCause.IsActualCause`, `HPCause.Sustains`: the definitions on
  an abstract response function `R`, where `R S s` is the world after `do(S := s)`. Every
  assignment passed to `R S` agrees with the actual world off `S` (`HPCause.assign`), so only
  the values on the intervened set matter. Sustenance requires the contingency set `W` to be
  disjoint from `X`. They are decidable when all value types are finite with decidable
  equality and the effect is a decidable predicate.
* `SCM.IsActualCause M u X x φ`, `SCM.Sustains M u X x W φ`: the definitions for the world
  `(M, u)`, with `R S s = (M.intervene S s).solve u`. The effect `φ` is any decidable property
  of the configuration (an event `Y = y`, or a Boolean combination as in Pearl's remarks on
  multivariate events). Both are decidable, through the iterated solver, so `decide` applies
  to them directly.

## Main results

* `HPCause.isActualCause_singleton_iff`, `SCM.isActualCause_singleton_iff`: for a single cause,
  the minimality condition AC3 is automatic. `HPCause.not_isActualCause_empty`: the empty set
  is never an actual cause, for any response function.
* `HPCause.sustainsOverlapping_iff`, `Overlap.sustainsOverlapping_self`: the reading of
  sustenance without disjointness is sustenance relative to `W \ X`; in the model `Y := X` it
  accepts the contingency set `W = {X}`, which `SCM.Sustains` rejects (the joint intervention of
  Definition 10.2.1 presupposes disjointness).
* Desert traveler (Pearl 2009, Example 10.1.1): the shot is an actual cause of death, the poison
  is not (exhaustive search), the shot is not a but-for cause; both sustain death relative to
  suitable contingencies, which illustrates the caution of section 10.2.
* Disjunctive scenario (overdetermination, section 10.3.2): each of two sufficient causes is an
  actual cause, neither is a but-for cause.
* Voting machine (Example 10.4.1): the vote `V₁ = 1` is an actual cause of the outcome under
  Definition 10.4.2, with the contingency `V₂ = 0`.
* Path switching (Example 10.3.6): each switch position is an actual cause of the light in its
  own world, and neither is a but-for cause.

Causal beams (Definitions 10.3.1 to 10.3.4) are not formalized.

Sources: Pearl (2009), *Causality*, 2nd edition, chapter 10; Halpern and Pearl (2005).
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

/-! ### A computable solver -/

section IterSolve

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- One round of the structural equations at the noise value `u`: every vertex is recomputed
from the current values of its parents. -/
def step (u : ∀ v, ε v) (y : ∀ v, α v) : ∀ v, α v :=
  fun v => M.f v ((G.parentsFinset v).restrict y) (u v)

/-- The solution computed by iterating the structural equations `card V` times from an arbitrary
starting configuration `y₀`. Unlike `SCM.solve`, which uses well-founded recursion, this is
evaluated by `decide`. -/
def iterSolve (u : ∀ v, ε v) (y₀ : ∀ v, α v) : ∀ v, α v :=
  (M.step u)^[Fintype.card V] y₀

/-- The vertices that are correct after `n` rounds: none after `0` rounds, and after `n + 1`
rounds those whose parents are all correct after `n` rounds. -/
def solvedAfter : ℕ → Finset V
  | 0 => ∅
  | n + 1 => univ.filter fun v => G.parentsFinset v ⊆ solvedAfter n

include M in
/-- After `n` steps, the iterated solver agrees with the solution on `solvedAfter n`. -/
theorem iterate_step_eq_solve (u : ∀ v, ε v) (y₀ : ∀ v, α v) :
    ∀ n, ∀ v ∈ solvedAfter (G := G) n, (M.step u)^[n] y₀ v = M.solve u v
  | 0, v, hv => absurd hv (notMem_empty v)
  | n + 1, v, hv => by
    rw [Function.iterate_succ_apply', step, M.solve_eq u v]
    congr 1
    funext p
    exact iterate_step_eq_solve u y₀ n p ((mem_filter.1 hv).2 p.2)

theorem solvedAfter_mono : ∀ n, solvedAfter (G := G) n ⊆ solvedAfter (G := G) (n + 1)
  | 0 => empty_subset _
  | n + 1 => fun v hv => mem_filter.2 ⟨mem_univ v,
      ((mem_filter.1 hv).2).trans (solvedAfter_mono n)⟩

include M in
theorem card_solvedAfter (n : ℕ) :
    n ≤ (solvedAfter (G := G) n).card ∨ solvedAfter (G := G) n = univ := by
  induction n with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ n ih =>
    by_cases hu : solvedAfter (G := G) n = univ
    · right
      exact eq_univ_of_forall fun v => solvedAfter_mono n (hu ▸ mem_univ v)
    · left
      have hne : {v | v ∉ solvedAfter (G := G) n}.Nonempty := by
        by_contra h
        exact hu (eq_univ_of_forall fun v => by
          by_contra hv
          exact h ⟨v, hv⟩)
      obtain ⟨v, hv, hmin⟩ := M.acyclic.wellFounded_adj.has_min _ hne
      have hv' : v ∈ solvedAfter (G := G) (n + 1) := mem_filter.2 ⟨mem_univ v, fun p hp => by
        by_contra h
        exact hmin p h (Digraph.mem_parentsFinset.1 hp)⟩
      have hss : solvedAfter (G := G) n ⊂ solvedAfter (G := G) (n + 1) :=
        Finset.ssubset_iff_subset_ne.2 ⟨solvedAfter_mono n, fun h => hv (h ▸ hv')⟩
      have := card_lt_card hss
      rcases ih with ih | ih
      · omega
      · exact absurd ih hu

omit [DecidableEq V] in
/-- **The iterated equations reach the solution**: `card V` rounds of the structural equations,
from any starting configuration, give the unique solution. -/
theorem iterSolve_eq (u : ∀ v, ε v) (y₀ : ∀ v, α v) : M.iterSolve u y₀ = M.solve u := by
  classical
  have huniv : solvedAfter (G := G) (Fintype.card V) = univ := by
    rcases M.card_solvedAfter (Fintype.card V) with h | h
    · exact eq_univ_of_card _ (le_antisymm (card_le_univ _) h)
    · exact h
  funext v
  exact M.iterate_step_eq_solve u y₀ _ v (huniv ▸ mem_univ v)

end IterSolve

end SCM

/-! ### The Halpern and Pearl definition, on a response function -/

namespace HPCause

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}

/-- **AC1**: the cause and the effect hold in the actual world: the actual configuration agrees
with `x` on `X`, and satisfies the effect `φ`. -/
def AC1 (actual : ∀ v, α v) (X : Finset V) (x : ∀ v, α v) (φ : (∀ v, α v) → Prop) : Prop :=
  (∀ v ∈ X, actual v = x v) ∧ φ actual

/-- The assignment that agrees with `s` on the intervention set `S` and with the actual
configuration `actual` off `S`. Every intervention below passes through it, so a response
function is only ever evaluated at assignments that carry no information off the intervened
set: the definitions do not depend on what `R S s` does with the values of `s` off `S`. -/
def assign (actual : ∀ v, α v) (S : Finset V) (s : ∀ v, α v) : ∀ v, α v :=
  fun v => if v ∈ S then s v else actual v

/-- **AC2** of Halpern and Pearl (2005), on a response function `R`, where `R S s` is the world
after the intervention `do(S := s)`. Only the values of the assignment on `S` are used: off `S`
it carries the actual values (`assign`). There is a set `W` disjoint from `X` (its complement is
`Z ⊇ X`) and a configuration `c`, carrying an alternative setting `x'` of `X` and a contingency
`w` of `W`, such that
(a) under `do(X := x', W := w)` the effect `φ` fails, and
(b) for every `W' ⊆ W` and every `Z' ⊆ Z`, under `do(X := x, W' := w, Z' := z*)`, where `z*` are
the actual values, the effect `φ` holds. -/
def AC2 (R : Finset V → (∀ v, α v) → (∀ v, α v)) (actual : ∀ v, α v) (X : Finset V)
    (x : ∀ v, α v) (φ : (∀ v, α v) → Prop) : Prop :=
  ∃ W : Finset V, Disjoint X W ∧ ∃ c : ∀ v, α v, ¬ φ (R (X ∪ W) (assign actual (X ∪ W) c)) ∧
    ∀ W' : Finset V, W' ⊆ W → ∀ Z' : Finset V, Z' ⊆ Wᶜ →
      φ (R (X ∪ W' ∪ Z') fun v => if v ∈ W' then c v else if v ∈ X then x v else actual v)

/-- **Actual causation** (Halpern and Pearl 2005; Pearl 2009, Definition 10.4.2): `X = x` is an
actual cause of the effect `φ` when AC1 and AC2 hold and (AC3) no proper subset of `X` satisfies
AC1 and AC2. The printed AC3 reads "W is minimal"; minimality of `X` is meant, as in Halpern and
Pearl (2005). -/
def IsActualCause (R : Finset V → (∀ v, α v) → (∀ v, α v)) (actual : ∀ v, α v) (X : Finset V)
    (x : ∀ v, α v) (φ : (∀ v, α v) → Prop) : Prop :=
  AC1 actual X x φ ∧ AC2 R actual X x φ ∧
    ∀ X' : Finset V, X' ⊂ X → ¬ (AC1 actual X' x φ ∧ AC2 R actual X' x φ)

/-- **Sustenance** (Pearl 2009, Definition 10.2.1): `X = x` causally sustains the effect `φ`
relative to contingencies in `W`, a set disjoint from `X` (otherwise the joint intervention
`do(X := x, W := w)` of (iii) would assign two values to the vertices of `X ∩ W`): (i), (ii)
cause and effect hold actually; (iii) with `X` set to `x`, the effect holds under every setting
of `W`; (iv) some alternative setting `x'` of `X` (differing from `x` somewhere on `X`) together
with some setting of `W` makes the effect fail. The configuration `c` in (iv) carries both `x'`
and the setting of `W`. Off `X ∪ W` the assignments carry the actual values (`assign`). -/
def Sustains (R : Finset V → (∀ v, α v) → (∀ v, α v)) (actual : ∀ v, α v) (X : Finset V)
    (x : ∀ v, α v) (W : Finset V) (φ : (∀ v, α v) → Prop) : Prop :=
  Disjoint X W ∧ AC1 actual X x φ ∧
    (∀ w : ∀ v, α v, φ (R (X ∪ W) (assign actual (X ∪ W) fun v => if v ∈ X then x v else w v))) ∧
    ∃ c : ∀ v, α v, (∃ v ∈ X, c v ≠ x v) ∧ ¬ φ (R (X ∪ W) (assign actual (X ∪ W) c))

/-- The reading of Definition 10.2.1 without the disjointness of `X` and `W`, in which a vertex
of `X ∩ W` silently takes its value from `x` and the contingency assignment there is discarded.
It is recorded only to show what disjointness changes: by `sustainsOverlapping_iff` it is
sustenance relative to `W \ X`, so it accepts contingency sets that Definition 10.2.1 does not
make sense of (`Overlap.sustainsOverlapping_self`). -/
def SustainsOverlapping (R : Finset V → (∀ v, α v) → (∀ v, α v)) (actual : ∀ v, α v)
    (X : Finset V) (x : ∀ v, α v) (W : Finset V) (φ : (∀ v, α v) → Prop) : Prop :=
  AC1 actual X x φ ∧ (∀ w : ∀ v, α v, φ (R (X ∪ W) fun v => if v ∈ X then x v else w v)) ∧
    ∃ c : ∀ v, α v, (∃ v ∈ X, c v ≠ x v) ∧ ¬ φ (R (X ∪ W) c)

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  (R : Finset V → (∀ v, α v) → (∀ v, α v)) (actual : ∀ v, α v) (X : Finset V) (x : ∀ v, α v)
  (φ : (∀ v, α v) → Prop) [DecidablePred φ]

instance : Decidable (AC1 actual X x φ) :=
  inferInstanceAs (Decidable ((∀ v ∈ X, actual v = x v) ∧ φ actual))

instance : Decidable (AC2 R actual X x φ) :=
  inferInstanceAs (Decidable (∃ W : Finset V, Disjoint X W ∧ ∃ c : ∀ v, α v,
    ¬ φ (R (X ∪ W) (assign actual (X ∪ W) c)) ∧ ∀ W' : Finset V, W' ⊆ W → ∀ Z' : Finset V,
      Z' ⊆ Wᶜ →
      φ (R (X ∪ W' ∪ Z') fun v => if v ∈ W' then c v else if v ∈ X then x v else actual v)))

instance : Decidable (IsActualCause R actual X x φ) :=
  inferInstanceAs (Decidable (AC1 actual X x φ ∧ AC2 R actual X x φ ∧
    ∀ X' : Finset V, X' ⊂ X → ¬ (AC1 actual X' x φ ∧ AC2 R actual X' x φ)))

instance (W : Finset V) : Decidable (Sustains R actual X x W φ) :=
  inferInstanceAs (Decidable (Disjoint X W ∧ AC1 actual X x φ ∧
    (∀ w : ∀ v, α v, φ (R (X ∪ W) (assign actual (X ∪ W) fun v => if v ∈ X then x v else w v))) ∧
    ∃ c : ∀ v, α v, (∃ v ∈ X, c v ≠ x v) ∧ ¬ φ (R (X ∪ W) (assign actual (X ∪ W) c))))

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [DecidablePred φ] in
/-- The empty set never satisfies AC2, for any response function: AC2(a) and AC2(b) with
`W' = W`, `Z' = ∅` evaluate `R` at the same intervention and contradict each other. -/
theorem not_ac2_empty : ¬ AC2 R actual ∅ x φ := by
  rintro ⟨W, -, c, ha, hb⟩
  refine ha ?_
  have := hb W subset_rfl ∅ (empty_subset _)
  simp only [empty_union, union_empty, notMem_empty, ite_false] at this ⊢
  exact this

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [DecidablePred φ] in
/-- **The empty set is never an actual cause**, for any response function `R`, even one that
reads the assignment off the intervention set (such as `R S s = s`): the response is only
evaluated at assignments that agree with the actual world off the intervened set. -/
theorem not_isActualCause_empty : ¬ IsActualCause R actual ∅ x φ :=
  fun h => not_ac2_empty R actual x φ h.2.1

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [DecidablePred φ] in
/-- For a single cause, minimality (AC3) is automatic: `X = {i}` is an actual cause exactly when
AC1 and AC2 hold. -/
theorem isActualCause_singleton_iff (i : V) :
    IsActualCause R actual {i} x φ ↔ AC1 actual {i} x φ ∧ AC2 R actual {i} x φ := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun X' hX' h' => ?_⟩⟩
  rw [ssubset_singleton_iff] at hX'
  subst hX'
  exact not_ac2_empty R actual x φ h'.2

omit [Fintype V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [DecidablePred φ] in
/-- **What disjointness changes in sustenance**: for a response function that depends only on
the values assigned to the intervened set, the reading without disjointness relative to `W` is
sustenance relative to `W \ X`. So it never gives a verdict that some disjoint contingency set
does not give, but it accepts sets `W` that meet `X`, for which the intervention
`do(X := x, W := w)` of Definition 10.2.1 is not defined. -/
theorem sustainsOverlapping_iff (hR : ∀ S s s', (∀ v ∈ S, s v = s' v) → R S s = R S s')
    (W : Finset V) :
    SustainsOverlapping R actual X x W φ ↔ Sustains R actual X x (W \ X) φ := by
  have hU : X ∪ W \ X = X ∪ W := union_sdiff_self_eq_union
  simp only [SustainsOverlapping, Sustains, hU, disjoint_sdiff, true_and]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun w => ?_) (exists_congr fun c => ?_))
  · rw [hR (X ∪ W) (assign actual (X ∪ W) fun v => if v ∈ X then x v else w v)
      (fun v => if v ∈ X then x v else w v) fun v hv => by simp [assign, hv]]
  · rw [hR (X ∪ W) (assign actual (X ∪ W) c) c fun v hv => by simp [assign, hv]]

end HPCause

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- The response function of the model at the noise value `u`: the world after `do(S := s)`. It
is the potential response `SCM.potentialResponse` with the noise value as the first argument,
the form taken by the abstract definitions of `HPCause` (`SCM.response_eq_potentialResponse`). -/
noncomputable def response (u : ∀ v, ε v) (S : Finset V) (s : ∀ v, α v) : ∀ v, α v :=
  M.potentialResponse S s u

/-- The response function is the potential response: `M.response u S s = V_s(u)`. -/
theorem response_eq_potentialResponse (u : ∀ v, ε v) (S : Finset V) (s : ∀ v, α v) :
    M.response u S s = M.potentialResponse S s u := rfl

/-- The response to an intervention depends only on the values assigned to the intervened
set. -/
theorem response_congr (u : ∀ v, ε v) (S : Finset V) (s s' : ∀ v, α v)
    (h : ∀ v ∈ S, s v = s' v) : M.response u S s = M.response u S s' := by
  rw [response, response, potentialResponse_eq, potentialResponse_eq, M.solve_intervene_congr h]

/-- **Actual causation in a structural model** (Halpern and Pearl 2005; Pearl 2009,
Definition 10.4.2): in the world `(M, u)`, `X = x` is an actual cause of the effect `φ`. -/
def IsActualCause (u : ∀ v, ε v) (X : Finset V) (x : ∀ v, α v) (φ : (∀ v, α v) → Prop) :
    Prop :=
  HPCause.IsActualCause (M.response u) (M.solve u) X x φ

/-- Actual causation can be checked with the iterated solver, which `decide` evaluates. -/
theorem isActualCause_iff_iterSolve (u : ∀ v, ε v) (y₀ : ∀ v, α v) (X : Finset V)
    (x : ∀ v, α v) (φ : (∀ v, α v) → Prop) :
    M.IsActualCause u X x φ ↔ HPCause.IsActualCause
      (fun S s => (M.intervene S s).iterSolve u y₀) (M.iterSolve u y₀) X x φ := by
  simp only [iterSolve_eq]
  rfl

/-- For a single cause, actual causation is AC1 and AC2, computed with the iterated solver. -/
theorem isActualCause_singleton_iff (u : ∀ v, ε v) (y₀ : ∀ v, α v) (i : V) (x : ∀ v, α v)
    (φ : (∀ v, α v) → Prop) :
    M.IsActualCause u {i} x φ ↔
      HPCause.AC1 (M.iterSolve u y₀) {i} x φ ∧
        HPCause.AC2 (fun S s => (M.intervene S s).iterSolve u y₀) (M.iterSolve u y₀) {i} x φ
    := by
  rw [IsActualCause, HPCause.isActualCause_singleton_iff]
  simp only [iterSolve_eq]
  rfl

/-- Sustenance in a structural model (Pearl 2009, Definition 10.2.1). -/
def Sustains (u : ∀ v, ε v) (X : Finset V) (x : ∀ v, α v) (W : Finset V)
    (φ : (∀ v, α v) → Prop) : Prop :=
  HPCause.Sustains (M.response u) (M.solve u) X x W φ

/-- Sustenance can be checked with the iterated solver, which `decide` evaluates. -/
theorem sustains_iff_iterSolve (u : ∀ v, ε v) (y₀ : ∀ v, α v) (X : Finset V) (x : ∀ v, α v)
    (W : Finset V) (φ : (∀ v, α v) → Prop) :
    M.Sustains u X x W φ ↔ HPCause.Sustains
      (fun S s => (M.intervene S s).iterSolve u y₀) (M.iterSolve u y₀) X x W φ := by
  simp only [Sustains, iterSolve_eq]
  rfl

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- Actual causation in a finite structural model is decidable, through the iterated solver
seeded with the configuration `x` (`isActualCause_iff_iterSolve`); `decide` evaluates it. -/
instance (u : ∀ v, ε v) (X : Finset V) (x : ∀ v, α v) (φ : (∀ v, α v) → Prop)
    [DecidablePred φ] : Decidable (M.IsActualCause u X x φ) :=
  decidable_of_iff _ (M.isActualCause_iff_iterSolve u x X x φ).symm

/-- Sustenance in a finite structural model is decidable, through the iterated solver seeded
with the configuration `x` (`sustains_iff_iterSolve`); `decide` evaluates it. -/
instance (u : ∀ v, ε v) (X : Finset V) (x : ∀ v, α v) (W : Finset V) (φ : (∀ v, α v) → Prop)
    [DecidablePred φ] : Decidable (M.Sustains u X x W φ) :=
  decidable_of_iff _ (M.sustains_iff_iterSolve u x X x W φ).symm

end SCM

/-! ### Why the contingency set is disjoint from the cause -/

namespace Overlap

open GraphExamples

/-- The model `Y := X` on the chain `0 → 1 → 2` (the vertex `2` is a copy of its noise): `X = 0`
is read off the noise and `Y = 1` copies it. -/
noncomputable def model : SCM chain (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide
  f v z e := if h : v = 1 then z ⟨0, by subst h; exact Digraph.mem_parentsFinset.2 rfl⟩ else e
  noise _ := FiniteDist.uniform

/-- The actual world: `X = 1`. -/
def world : Fin 3 → Bool := fun _ => true

/-- **The reading without disjointness accepts `W = {X}`**: in the model `Y := X` with
`X = 1`, it declares that `X = 1` sustains `Y = 1` relative to the contingency set `{X}`; the
contingency setting `X = 0` in (iii) is discarded in favor of `X = 1`. `SCM.Sustains`, which
requires `W` disjoint from `X` (the joint intervention `do(X := x, W := w)` of Definition 10.2.1
presupposes it), rejects this contingency set; the verdict of the reading without disjointness
is that of the empty contingency set (`HPCause.sustainsOverlapping_iff`). -/
theorem sustainsOverlapping_self :
    HPCause.SustainsOverlapping (model.response world) (model.solve world) {0} (fun _ => true)
        {0} (fun y => y 1 = true) ∧
      ¬ model.Sustains world {0} (fun _ => true) {0} (fun y => y 1 = true) ∧
      model.Sustains world {0} (fun _ => true) ∅ (fun y => y 1 = true) := by
  have h : model.Sustains world {0} (fun _ => true) ∅ (fun y => y 1 = true) := by decide +kernel
  refine ⟨?_, fun h' => absurd h'.1 (by decide), h⟩
  rw [HPCause.sustainsOverlapping_iff _ _ _ _ _ (model.response_congr world), sdiff_self]
  exact h

end Overlap

/-! ### The desert traveler -/

namespace DesertTraveler

/-- The desert-traveler graph (Pearl 2009, Example 10.1.1, Figure 10.2) on `Fin 5`: the shot
`X = 0` and the poison `P = 1` feed the cyanide intake `C = 2`, the shot feeds the dehydration
`D = 3`, and `C`, `D` feed the death `Y = 4`. -/
def graph : Digraph (Fin 5) where
  Adj i j := (i, j) ∈ ({(0, 2), (1, 2), (0, 3), (2, 4), (3, 4)} : Finset (Fin 5 × Fin 5))

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem mem_parents {i j : Fin 5} (h : graph.Adj i j) : i ∈ graph.parentsFinset j :=
  Digraph.mem_parentsFinset.2 h

theorem mem_parents_four {v : Fin 5} (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≠ 2) (h3 : v ≠ 3)
    {i : Fin 5} (hi : i = 2 ∨ i = 3) : i ∈ graph.parentsFinset v := by
  fin_cases v
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · rcases hi with rfl | rfl <;> exact mem_parents (by decide)

/-- The model (Pearl 2009, equation (10.1)): `X` and `P` are read off the noise, `c = p x'`,
`d = x`, `y = c ∨ d`. -/
noncomputable def model : SCM graph (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide
  f v z e :=
    if h0 : v = 0 then e
    else if h1 : v = 1 then e
    else if h2 : v = 2 then
      z ⟨1, by subst h2; exact mem_parents (by decide)⟩ &&
        !z ⟨0, by subst h2; exact mem_parents (by decide)⟩
    else if h3 : v = 3 then z ⟨0, by subst h3; exact mem_parents (by decide)⟩
    else z ⟨2, mem_parents_four h0 h1 h2 h3 (Or.inl rfl)⟩ ||
      z ⟨3, mem_parents_four h0 h1 h2 h3 (Or.inr rfl)⟩
  noise _ := FiniteDist.uniform

/-- The actual world: the enemy shot and the canteen was poisoned. -/
def world : Fin 5 → Bool := fun _ => true

/-- The traveler dies in the actual world, and would still die had the enemy not shot (the
poison would then act): the shot is not a but-for cause. -/
theorem dies_without_shot :
    model.solve world 4 = true ∧ (model.intervene {0} fun _ => false).solve world 4 = true := by
  rw [← model.iterSolve_eq world (fun _ => false),
    ← (model.intervene {0} fun _ => false).iterSolve_eq world (fun _ => false)]
  decide +kernel

/-- **The shot is an actual cause of death** (Pearl 2009, section 10.1.2 and Definition 10.4.2):
`X = true` is an actual cause of `Y = true`. -/
theorem shot_isActualCause :
    model.IsActualCause world {0} (fun _ => true) (fun y => y 4 = true) := by
  rw [model.isActualCause_singleton_iff world (fun _ => false)]
  decide +kernel

/-- **The poison is not an actual cause of death** (Pearl 2009, section 10.1.2 and
Definition 10.4.2): `P = true` is not an actual cause of `Y = true`; the cyanide path is
preempted by the shot. Checked by an exhaustive search over the contingencies. -/
theorem poison_not_isActualCause :
    ¬ model.IsActualCause world {1} (fun _ => true) (fun y => y 4 = true) := by
  rw [model.isActualCause_singleton_iff world (fun _ => false)]
  decide +kernel

/-- **The shot sustains death against the poison** (Pearl 2009, Definition 10.2.1): with
`W = {P}`, setting `X = true` keeps the traveler dead whatever `P` is, and `X = P = false` would
keep him alive. -/
theorem shot_sustains :
    model.Sustains world {0} (fun _ => true) {1} (fun y => y 4 = true) := by
  rw [model.sustains_iff_iterSolve world (fun _ => false)]
  decide +kernel

/-- **Why `W` must be chosen with caution** (Pearl 2009, section 10.2): relative to the
contingency set `W = {X}`, the poison also sustains death, although it is not an actual cause
(`poison_not_isActualCause`). Setting `X = false` removes the preemption. -/
theorem poison_sustains :
    model.Sustains world {1} (fun _ => true) {0} (fun y => y 4 = true) := by
  rw [model.sustains_iff_iterSolve world (fun _ => false)]
  decide +kernel

end DesertTraveler

/-! ### Overdetermination: the disjunctive scenario -/

namespace Disjunctive

open GraphExamples

/-- Two sufficient causes of one effect (Pearl 2009, sections 10.3.2 and 10.4): on the collider
`0 → 2 ← 1`, the actions `A₁ = 0` and `A₂ = 1` are read off the noise and the effect is
`E = A₁ ∨ A₂`. -/
noncomputable def model : SCM collider (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide
  f v z e := if h : v = 2 then
      z ⟨0, Digraph.mem_parentsFinset.2 ⟨by decide, h⟩⟩ ||
        z ⟨1, Digraph.mem_parentsFinset.2 ⟨by decide, h⟩⟩
    else e
  noise _ := FiniteDist.uniform

/-- The actual world: both actions occur. -/
def world : Fin 3 → Bool := fun _ => true

/-- `A₁` is not a but-for cause: without it the effect still occurs. -/
theorem effect_without_first :
    (model.intervene {0} fun _ => false).solve world 2 = true := by
  rw [← (model.intervene {0} fun _ => false).iterSolve_eq world (fun _ => false)]
  decide +kernel

/-- **Overdetermination** (Pearl 2009, section 10.3.2 and Definition 10.4.2): `A₁ = true` is an
actual cause of `E = true`, with the contingency `A₂ = false`. By symmetry so is `A₂`. -/
theorem first_isActualCause :
    model.IsActualCause world {0} (fun _ => true) (fun y => y 2 = true) := by
  rw [model.isActualCause_singleton_iff world (fun _ => false)]
  decide +kernel

/-- `A₂ = true` is an actual cause of `E = true`, with the contingency `A₁ = false`. -/
theorem second_isActualCause :
    model.IsActualCause world {1} (fun _ => true) (fun y => y 2 = true) := by
  decide +kernel

end Disjunctive

/-! ### The voting machine -/

namespace VotingMachine

/-- The voting-machine graph (Pearl 2009, Example 10.4.1, Figure 10.8) on `Fin 4`: the votes
`V₁ = 0` and `V₂ = 1` feed the count `M = 2`, which feeds the outcome `Y = 3`. -/
def graph : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ({(0, 2), (1, 2), (2, 3)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem mem_parents {i j : Fin 4} (h : graph.Adj i j) : i ∈ graph.parentsFinset j :=
  Digraph.mem_parentsFinset.2 h

theorem two_mem_parents {v : Fin 4} (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≠ 2) :
    (2 : Fin 4) ∈ graph.parentsFinset v := by
  fin_cases v
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact mem_parents (by decide)

/-- The number of values of each variable: the count `M` takes the values `0, 1, 2`, every
other variable is binary. -/
def card (v : Fin 4) : ℕ := if v = 2 then 3 else 2

theorem card_of_ne {v : Fin 4} (h : v ≠ 2) : card v = 2 := by simp [card, h]


/-- The voting machine (Pearl 2009, Example 10.4.1): each vote is read off the noise,
`M = V₁ + V₂`, and `Y = 1` exactly when `M ≥ 1`. -/
noncomputable def model : SCM graph (fun v => Fin (card v)) (fun _ => Bool) where
  acyclic := by decide
  f v z e :=
    if h2 : v = 2 then
      ⟨(z ⟨0, by subst h2; exact mem_parents (by decide)⟩).val +
          (z ⟨1, by subst h2; exact mem_parents (by decide)⟩).val, by
        subst h2
        have a : (z ⟨0, mem_parents (by decide)⟩).val < 2 := (z _).isLt
        have b : (z ⟨1, mem_parents (by decide)⟩).val < 2 := (z _).isLt
        change _ < 3
        omega⟩
    else if h3 : v = 3 then
      ⟨if 1 ≤ (z ⟨2, two_mem_parents (by subst h3; decide) (by subst h3; decide) h2⟩).val
        then 1 else 0, by rw [card_of_ne h2]; split <;> omega⟩
    else ⟨if e then 1 else 0, by rw [card_of_ne h2]; split <;> omega⟩
  noise _ := FiniteDist.uniform

/-- The actual world: both vote in favor. -/
def world : Fin 4 → Bool := fun _ => true

/-- The value `1` of every variable (both votes in favor; the outcome passes). -/
def ones : ∀ v : Fin 4, Fin (card v) := fun v => ⟨1, by unfold card; split <;> omega⟩

/-- A starting configuration for the iterated solver. -/
def zeros : ∀ v : Fin 4, Fin (card v) := fun v => ⟨0, by unfold card; split <;> omega⟩

/-- **The voting machine** (Pearl 2009, Example 10.4.1 and the discussion of
Definition 10.4.2): the vote `V₁ = 1` is an actual cause of the outcome `Y = 1`, with the
contingency `V₂ = 0`. -/
theorem vote_isActualCause :
    model.IsActualCause world {0} ones (fun y => y 3 = ones 3) := by
  rw [model.isActualCause_singleton_iff world zeros]
  decide +kernel

end VotingMachine

/-! ### Path switching -/

namespace PathSwitching

/-- The path-switching graph (Pearl 2009, Example 10.3.6) on `Fin 4`: the switch `X = 0` feeds the
lamp `Z = 1` and the flashlight `W = 2`, which both feed the light `Y = 3`. -/
def graph : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ({(0, 1), (0, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem mem_parents {i j : Fin 4} (h : graph.Adj i j) : i ∈ graph.parentsFinset j :=
  Digraph.mem_parentsFinset.2 h

theorem mem_parents_three {v : Fin 4} (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≠ 2) {i : Fin 4}
    (hi : i = 1 ∨ i = 2) : i ∈ graph.parentsFinset v := by
  fin_cases v
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rcases hi with rfl | rfl <;> exact mem_parents (by decide)

/-- The model (Pearl 2009, Example 10.3.6): the switch is read off the noise; in position `1`
it turns on the lamp and off the flashlight, in position `0` the reverse: `Z = X`, `W = ¬X`,
`Y = Z ∨ W`. -/
noncomputable def model : SCM graph (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide
  f v z e :=
    if h0 : v = 0 then e
    else if h1 : v = 1 then z ⟨0, by subst h1; exact mem_parents (by decide)⟩
    else if h2 : v = 2 then !z ⟨0, by subst h2; exact mem_parents (by decide)⟩
    else z ⟨1, mem_parents_three h0 h1 h2 (Or.inl rfl)⟩ ||
      z ⟨2, mem_parents_three h0 h1 h2 (Or.inr rfl)⟩
  noise _ := FiniteDist.uniform

/-- The room is lit in either switch position: the switch is not a but-for cause. -/
theorem lit_either_way (b : Bool) :
    (model.intervene {0} fun _ => b).solve (fun _ => true) 3 = true := by
  rw [← (model.intervene {0} fun _ => b).iterSolve_eq (fun _ => true) (fun _ => false)]
  cases b <;> decide +kernel

/-- **Path switching** (Pearl 2009, Example 10.3.6): in the world where the switch is in
position `1`, `X = 1` is an actual cause of the light `Y = 1`; in the world where it is in
position `0`, `X = 0` is. -/
theorem switch_isActualCause (b : Bool) :
    model.IsActualCause (fun _ => b) {0} (fun _ => b) (fun y => y 3 = true) := by
  rw [model.isActualCause_singleton_iff (fun _ => b) (fun _ => false)]
  cases b <;> decide +kernel

end PathSwitching

end CausalInference
