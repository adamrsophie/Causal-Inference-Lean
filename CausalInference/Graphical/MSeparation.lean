/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.DSeparation
public import CausalInference.Graphical.ADMG

/-!
# m-separation in directed mixed graphs

m-separation in a directed mixed graph `G : ADMG V` (Richardson 2003), in two forms, and their
agreement.

## The trail definition

A trail in `G` uses directed edges `u → v` and bidirected edges `u ↔ v`; a bidirected edge has
an arrowhead at both ends. An interior vertex `m` of a trail is a *collider* when both trail
edges at `m` have an arrowhead at `m` (`· → m ← ·`, `· ↔ m ← ·`, `· → m ↔ ·`, `· ↔ m ↔ ·`);
every other vertex, both endpoints included, is a *non-collider*. A trail is *active* given `Z`
when every collider lies in `G.ancestorsOf Z` (ancestors along directed edges) and every
non-collider lies outside `Z`.

As for d-separation (`Digraph.DConn`), a trail is recorded as a sequence of states
`(v, b) : V × Bool`, where `b = true` means that the trail arrived at `v` through an arrowhead
at `v`. The state graph `ADMG.mBall G Z` has the Bayes-ball edges of the directed part
(`Digraph.bayesBall`), and in addition an edge `(v, b) → (w, true)` for each bidirected edge
`v ↔ w` such that `v` lets a trail pass that leaves `v` through an arrowhead at `v`
(`Digraph.Passes Z v b false`).

* `ADMG.MConn G X Y Z`: some `x ∈ X` and `y ∈ Y`, both outside `Z`, are joined by an active
  trail given `Z`.

## The canonical DAG

* `ADMG.canonicalDAG G`: the DAG on `V ⊕ V × V` with a latent parent `Sum.inr (a, b)` of
  `Sum.inl a` and `Sum.inl b` for each bidirected edge `a ↔ b`.
* `ADMG.MSep G X Y Z`: d-separation of the observed vertices in the canonical DAG.

## Main results

* `ADMG.dConn_canonicalDAG_iff`, `ADMG.mSep_iff_not_mConn`: m-separation in the canonical DAG is
  the absence of an active trail in `G`.
* `ADMG.mConn_ofDigraph`, `ADMG.mSep_ofDigraph`: without bidirected edges, m-connection and
  m-separation are d-connection and d-separation of the directed graph.

## References

* T. S. Richardson (2003), *Markov properties for acyclic directed mixed graphs*.
* J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1.
-/

@[expose] public section

namespace CausalInference

open Relation

namespace ADMG

variable {V : Type*}

/-! ### The canonical DAG -/

/-- The canonical DAG of a directed mixed graph `G` on `V`, on the vertex type `V ⊕ V × V`: the
observed vertices `Sum.inl v` carry the directed edges of `G`, and for every bidirected edge
`a ↔ b` of `G` the latent vertex `Sum.inr (a, b)` is a common parent of `Sum.inl a` and
`Sum.inl b`. A latent `Sum.inr (a, b)` without a bidirected edge `a ↔ b` is isolated, and no
edge points into a latent vertex. -/
def canonicalDAG (G : ADMG V) : Digraph (V ⊕ V × V) where
  Adj s t := match s, t with
    | .inl u, .inl v => G.directed.Adj u v
    | .inr p, .inl v => G.bidirected.Adj p.1 p.2 ∧ (v = p.1 ∨ v = p.2)
    | _, .inr _ => False

variable {G : ADMG V}

@[simp] theorem canonicalDAG_adj_inl_inl {u v : V} :
    G.canonicalDAG.Adj (.inl u) (.inl v) ↔ G.directed.Adj u v := Iff.rfl

@[simp] theorem canonicalDAG_adj_inr_inl {p : V × V} {v : V} :
    G.canonicalDAG.Adj (.inr p) (.inl v) ↔ G.bidirected.Adj p.1 p.2 ∧ (v = p.1 ∨ v = p.2) :=
  Iff.rfl

@[simp] theorem not_canonicalDAG_adj_inr {s : V ⊕ V × V} {p : V × V} :
    ¬ G.canonicalDAG.Adj s (.inr p) := by
  cases s <;> exact id

/-- The canonical DAG of an acyclic directed mixed graph on a finite vertex type is acyclic. -/
theorem IsAcyclic.canonicalDAG [Finite V] (hG : G.IsAcyclic) : G.canonicalDAG.IsAcyclic := by
  have := Fintype.ofFinite V
  obtain ⟨f, hf⟩ := Digraph.IsAcyclic.exists_adj_lt hG
  refine Digraph.isAcyclic_of_adj_lt (Sum.elim (fun v => f v + 1) fun _ => 0) ?_
  rintro (u | p) (v | q) h
  · exact Nat.succ_lt_succ (hf h)
  · exact absurd h not_canonicalDAG_adj_inr
  · exact Nat.succ_pos _
  · exact absurd h not_canonicalDAG_adj_inr

/-- m-separation of `X` and `Y` given `Z` in a directed mixed graph, defined as d-separation of
the corresponding observed vertices in the canonical DAG `ADMG.canonicalDAG`, where every
bidirected edge is replaced by a latent common parent of its endpoints. It agrees with the trail
definition (`ADMG.mSep_iff_not_mConn`). -/
def MSep (G : ADMG V) (X Y Z : Set V) : Prop :=
  G.canonicalDAG.DSep (Sum.inl '' X) (Sum.inl '' Y) (Sum.inl '' Z)

/-- Directed paths of the canonical DAG out of an observed vertex stay among the observed
vertices and are directed paths of `G`. -/
theorem exists_of_reflTransGen_canonicalDAG {u : V} {t : V ⊕ V × V}
    (h : ReflTransGen G.canonicalDAG.Adj (.inl u) t) :
    ∃ v, t = .inl v ∧ ReflTransGen G.directed.Adj u v := by
  induction h with
  | refl => exact ⟨u, rfl, ReflTransGen.refl⟩
  | @tail t₁ t₂ _ h₁₂ ih =>
    obtain ⟨v, rfl, hv⟩ := ih
    cases t₂ with
    | inl w => exact ⟨w, rfl, hv.tail h₁₂⟩
    | inr p => exact absurd h₁₂ not_canonicalDAG_adj_inr

theorem inl_mem_ancestorsOf_canonicalDAG {Z : Set V} {v : V} :
    Sum.inl v ∈ G.canonicalDAG.ancestorsOf (Sum.inl '' Z) ↔ v ∈ G.directed.ancestorsOf Z := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
    obtain ⟨w, hw, hvw⟩ := exists_of_reflTransGen_canonicalDAG h
    obtain rfl := Sum.inl_injective hw
    exact ⟨z, hz, hvw⟩
  · rintro ⟨z, hz, h⟩
    refine ⟨.inl z, ⟨z, hz, rfl⟩, ?_⟩
    clear hz
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ h ih => exact ih.tail (canonicalDAG_adj_inl_inl.2 h)

theorem canonicalDAG_passes_inl {Z : Set V} {v : V} {b c : Bool} :
    G.canonicalDAG.Passes (Sum.inl '' Z) (.inl v) b c ↔ G.directed.Passes Z v b c := by
  unfold Digraph.Passes
  split_ifs
  · exact inl_mem_ancestorsOf_canonicalDAG
  · simp

/-! ### The trail definition -/

/-- The state graph of active trails of `G` given `Z`. A state `(v, b)` records a vertex `v`
reached by a trail, with `b = true` when the trail arrived at `v` through an arrowhead at `v`.
The edges are the Bayes-ball edges of the directed part, and an edge `(v, b) → (w, true)` for
every bidirected edge `v ↔ w` along which `v` passes the trail on: a bidirected edge leaves `v`
through an arrowhead at `v`, so `v` is then a collider if `b = true`. -/
def mBall (G : ADMG V) (Z : Set V) : Digraph (V × Bool) where
  Adj s t := (G.directed.bayesBall Z).Adj s t ∨
    (t.2 = true ∧ G.bidirected.Adj s.1 t.1 ∧ G.directed.Passes Z s.1 s.2 false)

/-- `G.MConn X Y Z`: `X` and `Y` are m-connected given `Z` in `G`. Some `x ∈ X` and `y ∈ Y`,
both outside `Z`, are joined by a trail of directed and bidirected edges that is active given
`Z`: every collider of the trail is in `G.ancestorsOf Z` and every other vertex of the trail is
outside `Z`. The trail is encoded as a path of the state graph `ADMG.mBall G Z` starting at
`(x, false)`. -/
def MConn (G : ADMG V) (X Y Z : Set V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, x ∉ Z ∧ y ∉ Z ∧ ∃ b, ReflTransGen (G.mBall Z).Adj (x, false) (y, b)

/-- Every active trail of `G` gives an active trail of the canonical DAG between the observed
copies of its endpoints: a bidirected step `v ↔ w` becomes `v ← (v, w) → w`. -/
theorem reflTransGen_canonicalDAG_of_mBall {Z : Set V} {s t : V × Bool}
    (h : ReflTransGen (G.mBall Z).Adj s t) :
    ReflTransGen (G.canonicalDAG.bayesBall (Sum.inl '' Z)).Adj (.inl s.1, s.2)
      (.inl t.1, t.2) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail t₁ t₂ _ h₁₂ ih =>
    obtain ⟨v, b⟩ := t₁
    obtain ⟨w, c⟩ := t₂
    rcases h₁₂ with ⟨hedge, hpass⟩ | ⟨rfl, hvw, hpass⟩
    · exact ih.tail ⟨by cases c <;> simpa using hedge, canonicalDAG_passes_inl.2 hpass⟩
    · refine (ih.tail (c := (.inr (v, w), false)) ⟨?_, canonicalDAG_passes_inl.2 hpass⟩).tail
        ⟨?_, ?_⟩
      · simpa using hvw
      · simpa using hvw
      · simp [Digraph.Passes]

/-- What an active trail of the canonical DAG out of `(Sum.inl x, false)` tells about the active
trails of `G` out of `(x, false)`. At an observed state `(v, c)`, either `(v, c)` is reached in
`G`, or `v ∉ Z` and `(v, false)` is reached (a state that lets every trail pass). At a latent
state `(Sum.inr p, c)`, `c = false` and the latent was entered from an endpoint `v` of the
bidirected edge `p` reached in `G` and passing the trail on through an arrowhead. -/
def CanonInv (G : ADMG V) (Z : Set V) (x : V) : (V ⊕ V × V) × Bool → Prop
  | (.inl v, c) => ReflTransGen (G.mBall Z).Adj (x, false) (v, c) ∨
      (v ∉ Z ∧ ReflTransGen (G.mBall Z).Adj (x, false) (v, false))
  | (.inr p, c) => c = false ∧ G.bidirected.Adj p.1 p.2 ∧ ∃ v b, (v = p.1 ∨ v = p.2) ∧
      ReflTransGen (G.mBall Z).Adj (x, false) (v, b) ∧ G.directed.Passes Z v b false

theorem canonInv_of_reflTransGen {Z : Set V} {x : V} {t : (V ⊕ V × V) × Bool}
    (h : ReflTransGen (G.canonicalDAG.bayesBall (Sum.inl '' Z)).Adj (.inl x, false) t) :
    G.CanonInv Z x t := by
  induction h with
  | refl => exact Or.inl ReflTransGen.refl
  | @tail t₁ t₂ _ h₁₂ ih =>
    obtain ⟨hedge, hpass⟩ := h₁₂
    obtain ⟨s₁ | p, c⟩ := t₁ <;> obtain ⟨s₂ | q, d⟩ := t₂
    · rw [canonicalDAG_passes_inl] at hpass
      have hedge' : (if d then G.directed.Adj s₁ s₂ else G.directed.Adj s₂ s₁) := by
        cases d <;> simpa using hedge
      rcases ih with ih | ⟨hvZ, ih⟩
      · exact Or.inl (ih.tail (Or.inl ⟨hedge', hpass⟩))
      · exact Or.inl (ih.tail (Or.inl ⟨hedge', by simpa [Digraph.Passes] using hvZ⟩))
    · rw [canonicalDAG_passes_inl] at hpass
      cases d
      · obtain ⟨hq, hv⟩ := by simpa using hedge
        rcases ih with ih | ⟨hvZ, ih⟩
        · exact ⟨rfl, hq, s₁, c, hv, ih, hpass⟩
        · exact ⟨rfl, hq, s₁, false, hv, ih, by simpa [Digraph.Passes] using hvZ⟩
      · simp at hedge
    · obtain ⟨rfl, hp, v, b, hv, hreach, hvpass⟩ := ih
      cases d
      · simp at hedge
      · obtain ⟨-, hw⟩ := by simpa using hedge
        by_cases hvw : v = s₂
        · subst hvw
          cases b
          · exact Or.inr ⟨by simpa [Digraph.Passes] using hvpass, hreach⟩
          · exact Or.inl hreach
        · have hadj : G.bidirected.Adj v s₂ := by
            rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
            · exact absurd rfl hvw
            · exact hp
            · exact hp.symm
            · exact absurd rfl hvw
          exact Or.inl (hreach.tail (Or.inr ⟨rfl, hadj, hvpass⟩))
    · cases d <;> simp at hedge

/-- d-connection of observed vertices in the canonical DAG is m-connection in `G`. -/
theorem dConn_canonicalDAG_iff {X Y Z : Set V} :
    G.canonicalDAG.DConn (Sum.inl '' X) (Sum.inl '' Y) (Sum.inl '' Z) ↔ G.MConn X Y Z := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxZ, hyZ, b, h⟩
    have hxZ' : x ∉ Z := fun h => hxZ ⟨x, h, rfl⟩
    have hyZ' : y ∉ Z := fun h => hyZ ⟨y, h, rfl⟩
    rcases canonInv_of_reflTransGen h with h' | ⟨-, h'⟩
    · exact ⟨x, hx, y, hy, hxZ', hyZ', b, h'⟩
    · exact ⟨x, hx, y, hy, hxZ', hyZ', false, h'⟩
  · rintro ⟨x, hx, y, hy, hxZ, hyZ, b, h⟩
    exact ⟨.inl x, ⟨x, hx, rfl⟩, .inl y, ⟨y, hy, rfl⟩, by simpa using hxZ, by simpa using hyZ,
      b, reflTransGen_canonicalDAG_of_mBall h⟩

/-- m-separation (d-separation in the canonical DAG) is the absence of an active trail. -/
theorem mSep_iff_not_mConn {X Y Z : Set V} : G.MSep X Y Z ↔ ¬ G.MConn X Y Z :=
  not_congr dConn_canonicalDAG_iff

/-! ### Graphs without bidirected edges -/

theorem mBall_ofDigraph_adj {D : Digraph V} {Z : Set V} {s t : V × Bool} :
    ((ofDigraph D).mBall Z).Adj s t ↔ (D.bayesBall Z).Adj s t := by
  simp [mBall, ofDigraph]

/-- Without bidirected edges, m-connection is d-connection of the directed graph. -/
theorem mConn_ofDigraph {D : Digraph V} {X Y Z : Set V} :
    (ofDigraph D).MConn X Y Z ↔ D.DConn X Y Z := by
  have hrel : ((ofDigraph D).mBall Z).Adj = (D.bayesBall Z).Adj := by
    ext s t; exact mBall_ofDigraph_adj
  simp only [MConn, Digraph.DConn, hrel]

/-- Without bidirected edges, m-separation is d-separation of the directed graph. -/
theorem mSep_ofDigraph {D : Digraph V} {X Y Z : Set V} :
    (ofDigraph D).MSep X Y Z ↔ D.DSep X Y Z := by
  rw [mSep_iff_not_mConn, mConn_ofDigraph]; rfl

end ADMG

end CausalInference
