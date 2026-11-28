/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessTools

/-!
# Boundaries of bidirected edges over the two-element field

For a directed mixed graph `G` on `V` and a finset `A`, the ordered pairs `p = (a, b)` with
`a ↔ b` in `G` and both ends in `A` (`IDCompleteness.bedges G A`) index the latent vertices
`Sum.inr p` of the canonical DAG that lie between vertices of `A`. A Boolean vector `u` on these
pairs has a boundary `IDCompleteness.bnd G A u : V → Bool`: at `v`, the sum (exclusive or) of
`u p` over the pairs with an end at `v`.

## Main results

* `IDCompleteness.bnd_add`, `IDCompleteness.bnd_sum`: the boundary is additive.
* `IDCompleteness.sum_bnd_self`: the boundary sums to zero over `A`, since every pair has two
  ends in `A`.
* `IDCompleteness.exists_bnd_eq` (**even boundaries**): if `A` is bidirected connected, every
  vector on `A` with sum zero is a boundary.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

variable {V : Type} [Fintype V] [DecidableEq V] (G : ADMG V) [DecidableRel G.bidirected.Adj]

/-- The ordered pairs `(a, b)` with a bidirected edge `a ↔ b` of `G` and both ends in `A`. -/
def bedges (A : Finset V) : Finset (V × V) :=
  univ.filter fun p => G.bidirected.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A

/-- The boundary at `v` of a Boolean vector `u` on the pairs of `bedges G A`: the sum over the
pairs of `bedges G A` with an end at `v` of their values, each pair counted once per end. -/
def bnd (A : Finset V) (u : V × V → Bool) (v : V) : Bool :=
  ∑ p ∈ bedges G A, ((if p.1 = v then u p else 0) + (if p.2 = v then u p else 0))

variable {G}

theorem mem_bedges {A : Finset V} {p : V × V} :
    p ∈ bedges G A ↔ G.bidirected.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A := by
  simp [bedges]

/-- `bedges` is monotone in the set. -/
theorem bedges_mono {A B : Finset V} (h : A ⊆ B) : bedges G A ⊆ bedges G B := fun p hp => by
  rw [mem_bedges] at hp ⊢
  exact ⟨hp.1, h hp.2.1, h hp.2.2⟩

/-- The boundary of the zero vector is zero. -/
@[simp] theorem bnd_zero (A : Finset V) (v : V) : bnd G A 0 v = 0 := by
  simp [bnd]

/-- The boundary is additive. -/
theorem bnd_add (A : Finset V) (u u' : V × V → Bool) (v : V) :
    bnd G A (u + u') v = bnd G A u v + bnd G A u' v := by
  unfold bnd
  rw [← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  split_ifs <;> simp only [Pi.add_apply, add_zero] <;> ring

/-- The boundary of a sum of vectors is the sum of the boundaries. -/
theorem bnd_sum {ι : Type*} (A : Finset V) (s : Finset ι) (f : ι → V × V → Bool) (v : V) :
    bnd G A (∑ i ∈ s, f i) v = ∑ i ∈ s, bnd G A (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, bnd_add, ih]

/-- The boundary only reads the pairs of `bedges G A`. -/
theorem bnd_congr {A : Finset V} {u u' : V × V → Bool} (h : ∀ p ∈ bedges G A, u p = u' p)
    (v : V) : bnd G A u v = bnd G A u' v :=
  sum_congr rfl fun p hp => by rw [h p hp]

/-- The boundary at `v` only reads the pairs with an end at `v`. -/
theorem bnd_congr_at {A : Finset V} {u u' : V × V → Bool} {v : V}
    (h : ∀ p ∈ bedges G A, (p.1 = v ∨ p.2 = v) → u p = u' p) : bnd G A u v = bnd G A u' v := by
  refine sum_congr rfl fun p hp => ?_
  by_cases h1 : p.1 = v
  · rw [h p hp (.inl h1)]
  by_cases h2 : p.2 = v
  · rw [h p hp (.inr h2)]
  simp [h1, h2]

/-- The boundary vanishes outside the set. -/
theorem bnd_eq_zero_of_notMem {A : Finset V} {v : V} (hv : v ∉ A) (u : V × V → Bool) :
    bnd G A u v = 0 := by
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨-, h1, h2⟩ := mem_bedges.1 hp
  have e1 : p.1 ≠ v := fun e => hv (e ▸ h1)
  have e2 : p.2 ≠ v := fun e => hv (e ▸ h2)
  simp [e1, e2]

/-- A vector restricted to the pairs of `bedges G A` has, relative to any `B ⊇ A`, the boundary
of the vector relative to `A`. -/
theorem bnd_mask {A B : Finset V} (hAB : A ⊆ B) (m : V × V → Bool) (v : V) :
    bnd G B (fun p => if p ∈ bedges G A then m p else 0) v = bnd G A m v := by
  unfold bnd
  rw [← sum_subset (bedges_mono hAB)]
  · exact sum_congr rfl fun p hp => by simp [hp]
  · intro p _ hp
    simp [hp]

/-- The vector with a single true coordinate at `q`. -/
def single (q : V × V) : V × V → Bool := fun p => if p = q then 1 else 0

/-- The boundary of a single pair of `bedges G A` is the sum of the indicators of its ends. -/
theorem bnd_single {A : Finset V} {q : V × V} (hq : q ∈ bedges G A) (v : V) :
    bnd G A (single q) v = (if q.1 = v then 1 else 0) + (if q.2 = v then 1 else 0) := by
  unfold bnd
  rw [sum_eq_single q]
  · simp [single]
  · intro p _ hp
    simp [single, hp]
  · exact fun h => absurd hq h

/-- A Boolean sum of a value with itself is zero. -/
theorem bool_add_self (a : Bool) : a + a = 0 := by
  cases a <;> rfl

/-- **The boundary sums to zero over the set**: every pair of `bedges G A` has its two ends in
`A`. -/
theorem sum_bnd_self (A : Finset V) (u : V × V → Bool) : ∑ v ∈ A, bnd G A u v = 0 := by
  unfold bnd
  rw [sum_comm]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨-, h1, h2⟩ := mem_bedges.1 hp
  rw [sum_add_distrib, sum_ite_eq, sum_ite_eq]
  simp [h1, h2, bool_add_self]

/-- The indicator of the vertex `a`. -/
def delta (a v : V) : Bool := if a = v then 1 else 0

/-- Along a path of bidirected edges inside `A` from `a` to `v` there is a vector whose
boundary is the sum of the indicators of `a` and `v`. -/
theorem exists_bnd_eq_delta {A : Finset V} {a v : V}
    (h : Relation.ReflTransGen (G.restrict ↑A).bidirected.Adj a v) :
    ∃ u : V × V → Bool, ∀ x, bnd G A u x = delta a x + delta v x := by
  induction h with
  | refl => exact ⟨0, fun x => by rw [bnd_zero, bool_add_self]⟩
  | tail _ hbc ih =>
    rename_i b c _
    obtain ⟨u, hu⟩ := ih
    have hq : (b, c) ∈ bedges G A := mem_bedges.2 ⟨hbc.1, hbc.2.1, hbc.2.2⟩
    refine ⟨u + single (b, c), fun x => ?_⟩
    rw [bnd_add, hu, bnd_single hq]
    simp only [delta]
    have := bool_add_self (if b = x then (1 : Bool) else 0)
    calc _ = (if a = x then (1 : Bool) else 0) + (if c = x then 1 else 0) +
        ((if b = x then (1 : Bool) else 0) + (if b = x then 1 else 0)) := by ring
      _ = _ := by rw [this, add_zero]

/-- **Even boundaries.** If `A` is bidirected connected, every Boolean vector `b` on `A` with
`∑_{v ∈ A} b v = 0` is the boundary of a vector on the pairs of `bedges G A`. -/
theorem exists_bnd_eq {A : Finset V} (hA : BiConnected G A) (b : V → Bool)
    (hb : ∑ v ∈ A, b v = 0) : ∃ u : V × V → Bool, ∀ v ∈ A, bnd G A u v = b v := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · exact ⟨0, fun v hv => absurd hv (notMem_empty v)⟩
  have hpath : ∀ v ∈ A, ∃ u : V × V → Bool, ∀ x, bnd G A u x = delta a₀ x + delta v x :=
    fun v hv => exists_bnd_eq_delta
      ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (hA a₀ ha₀ v hv))
  choose! π hπ using hpath
  set F := A.filter fun v => b v = true
  have hF : ∑ v ∈ F, (1 : Bool) = 0 := by
    rw [← hb, sum_filter]
    refine sum_congr rfl fun v _ => ?_
    cases b v <;> rfl
  refine ⟨∑ v ∈ F, π v, fun x hx => ?_⟩
  rw [bnd_sum, sum_congr rfl fun v hv => hπ v (mem_filter.1 hv).1 x, sum_add_distrib]
  have h1 : ∑ v ∈ F, delta a₀ x = 0 := by
    rw [← mul_one (delta a₀ x), ← mul_sum, hF, mul_zero]
  rw [h1, zero_add]
  simp only [delta]
  rw [sum_ite_eq']
  by_cases hbx : b x = true <;> simp [hx, hbx, Bool.zero_eq_false, Bool.one_eq_true]

end IDCompleteness

end CausalInference
