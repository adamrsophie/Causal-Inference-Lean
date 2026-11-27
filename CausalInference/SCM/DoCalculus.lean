/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Effects
public import CausalInference.Graphical.GlobalMarkov

/-!
# The rules of do-calculus

Soundness of the three rules of do-calculus for a finite structural causal model
`M : SCM G α ε`. Latent variables need no separate treatment: a vertex in none of the query
sets is marginalized, so the statements cover semi-Markovian models.

All values are read off one configuration `v`: the intervention `do(X := x)` is
`M.intervene X v`, and `P(s | do(x))` for a set `S` is the marginal mass
`(M.intervene X v).dist.margAt S v`. Each rule is stated division-free, as an identity between
products of marginals (the way `FiniteDist.CondIndep` is stated), and in ratio form under the
positivity the ratio needs; no rule holds only because `x / 0 = 0`.

## Main results

* `SCM.rule1`, `SCM.rule1_div` (insertion or deletion of observations): if `Y` and `Z` are
  d-separated by `X ∪ W` in `G.deleteIncoming X`, then
  `P(y | do(x), z, w) = P(y | do(x), w)`. Proof: the interventional distribution factorizes
  according to `G.deleteIncoming X`, so the global Markov property applies.
* `SCM.rule2`, `SCM.rule2_div` (action and observation exchange): if `Y` and `Z` are
  d-separated by `X ∪ W` in `(G.deleteIncoming X).deleteOutgoing Z`, then
  `P(y | do(x), do(z), w) = P(y | do(x), z, w)`. Proof: the auxiliary model `SCM.rule2Model` on
  `(G.deleteIncoming X).deleteOutgoing Z` agrees with `do(X)` on events fixing `Z` and with
  `do(X ∪ Z)` on events not involving `Z`; the global Markov property applies to it.
* `SCM.rule3`, `SCM.rule3_div` (insertion or deletion of actions): if `Y` and `Z` are
  d-separated by `X ∪ W` in `G.deleteIncoming (X ∪ Z(W))`, where `Z(W)`
  (`Digraph.rule3Set`, computable form `Digraph.rule3SetFinset`) is the set of vertices of `Z`
  that are not ancestors of `W` in `G.deleteIncoming X`, then
  `P(y | do(x), do(z), w) = P(y | do(x), w)`. The division-free form needs no positivity; the
  ratio form needs only `P(w | do(x)) > 0` and `P(w | do(x, z)) > 0`. Proof: no vertex of
  `Y ∪ W` or of `Z \ Z(W)` descends from `Z(W)` (`Digraph.notMem_descendantsOf_rule3Set`), so
  the intervention on `Z(W)` does not change their law. The intervention on `B = Z \ Z(W)` is
  handled by the switch model `SCM.switchModel`: a fair binary root added to the graph
  (`Digraph.addRoot`) switches each mechanism of `B` between its own equation and the fixed
  value; the root is d-separated from `Y` (`Digraph.dSep_addRoot`), and the global Markov
  property of the switch model gives `SCM.margAt_intervene_mul_of_dSep`.

Rules 2 and 3 assume that `Z` is disjoint from `X` and `W`, and Rule 2 also from `Y`, as in
Pearl's statement for disjoint sets (in Rule 3 the disjointness of `Y` and `Z` follows from the
d-separation); Rule 1 needs no disjointness. Completeness of the calculus is not treated.
The back-door adjustment derived from these rules with the graphical back-door predicate is
`SCM.effect_eq_sum_of_backDoor` in `CausalInference.SCM.Adjustment`; examples, and a model
showing that the joint positivity hypothesis of `SCM.rule3_pos` is strictly stronger than the
positivity of the two denominators of `SCM.rule3_div`, are in
`CausalInference.SCM.DoCalculusRule3`.

Source: Pearl (2009), *Causality*, 2nd edition, section 3.4, Theorem 3.4.1, equations (3.31)
to (3.33); Pearl (1995), Causal diagrams for empirical research.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-! ### Conditioning on the intervened vertices is harmless -/

/-- Under `do(X := v)`, the vertices of `X` take the values of `v` at every noise value, so
adding coordinates of `X` to a marginal evaluated at `v` changes nothing. -/
theorem margAt_union_intervene {X X' : Finset V} (hX' : X' ⊆ X) (v : ∀ u, α u)
    (S : Finset V) :
    (M.intervene X v).dist.margAt (S ∪ X') v = (M.intervene X v).dist.margAt S v := by
  rw [margAt_dist, margAt_dist]
  refine FiniteDist.probOf_congr _ fun e => ?_
  simp only [mem_union, or_imp, forall_and]
  exact and_iff_left fun w hw => M.solve_intervene_of_mem e (hX' hw)

/-! ### Rule 1 -/

/-- The conditional independence behind Rule 1: if `Y` and `Z` are d-separated by `X ∪ W` in
`G.deleteIncoming X`, then `Y ⫫ Z | X ∪ W` under `do(X := v)`. -/
theorem condIndep_intervene_of_dSep {X Y Z W : Finset V} (v : ∀ u, α u)
    (hsep : (G.deleteIncoming ↑X).DSep ↑Y ↑Z ↑(X ∪ W)) :
    (M.intervene X v).dist.CondIndep Y Z (X ∪ W) :=
  (M.factorizes_intervene (X := X) (x := v)).condIndep_of_dSep (M.intervene X v).acyclic hsep

omit [Fintype V] in
/-- Reassociating a union so that a set `X` comes last. -/
theorem union_union_eq_union_union (S X W : Finset V) : S ∪ (X ∪ W) = S ∪ W ∪ X := by
  ext; simp only [mem_union]; tauto

/-- **Rule 1 of do-calculus** (insertion or deletion of observations; Pearl 2009,
Theorem 3.4.1, equation (3.31)), division-free form. If `Y` and `Z` are d-separated by `X ∪ W`
in `G.deleteIncoming X`, then under `do(X := v_X)`
`P(y, z, w) * P(w) = P(y, w) * P(z, w)`, all values read off `v`; that is,
`P(y | do(x), z, w) = P(y | do(x), w)`. No disjointness or positivity is needed. -/
theorem rule1 {X Y Z W : Finset V} (v : ∀ u, α u)
    (hsep : (G.deleteIncoming ↑X).DSep ↑Y ↑Z ↑(X ∪ W)) :
    (M.intervene X v).dist.margAt (Y ∪ Z ∪ W) v * (M.intervene X v).dist.margAt W v =
      (M.intervene X v).dist.margAt (Y ∪ W) v * (M.intervene X v).dist.margAt (Z ∪ W) v := by
  have h := (M.condIndep_intervene_of_dSep v hsep).margAt_mul v
  rw [union_union_eq_union_union, union_union_eq_union_union, union_union_eq_union_union,
    union_comm X W] at h
  simpa only [M.margAt_union_intervene subset_rfl] using h

/-- **Rule 1 of do-calculus**, ratio form: if `Y` and `Z` are d-separated by `X ∪ W` in
`G.deleteIncoming X` and `P(z, w | do(x)) > 0`, then
`P(y | do(x), z, w) = P(y | do(x), w)`. The positivity of `P(w | do(x))` follows. -/
theorem rule1_div {X Y Z W : Finset V} (v : ∀ u, α u)
    (hsep : (G.deleteIncoming ↑X).DSep ↑Y ↑Z ↑(X ∪ W))
    (hpos : 0 < (M.intervene X v).dist.margAt (Z ∪ W) v) :
    (M.intervene X v).dist.margAt (Y ∪ Z ∪ W) v / (M.intervene X v).dist.margAt (Z ∪ W) v =
      (M.intervene X v).dist.margAt (Y ∪ W) v / (M.intervene X v).dist.margAt W v := by
  have hW : 0 < (M.intervene X v).dist.margAt W v :=
    hpos.trans_le ((M.intervene X v).dist.margAt_anti subset_union_right v)
  rw [div_eq_div_iff hpos.ne' hW.ne']
  exact M.rule1 v hsep

/-! ### Rule 2 -/

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- A parent `p ∉ Z` of a vertex `u ∉ X` is a parent of `u` in
`(G.deleteIncoming X).deleteOutgoing Z`. -/
theorem mem_parentsFinset_deleteIncoming_deleteOutgoing {X Z : Finset V} {u : V} (hu : u ∉ X)
    (p : G.parentsFinset u) (hp : p.1 ∉ Z) :
    p.1 ∈ ((G.deleteIncoming ↑X).deleteOutgoing ↑Z).parentsFinset u :=
  Digraph.mem_parentsFinset.2 ⟨⟨Digraph.mem_parentsFinset.1 p.2, hu⟩, hp⟩

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- The auxiliary model of Rule 2, a model on `(G.deleteIncoming X).deleteOutgoing Z` with the
noise of `M`. The vertices of `X` are held at the values of `v`; every other vertex follows its
structural equation in `M`, except that the values of its parents in `Z` are replaced by the
constants `v`. So the vertices of `Z` keep their own mechanisms but no longer influence
anything. -/
def rule2Model (X Z : Finset V) (v : ∀ u, α u) :
    SCM ((G.deleteIncoming ↑X).deleteOutgoing ↑Z) α ε where
  acyclic := M.acyclic.deleteIncoming.deleteOutgoing
  f u z e := if hu : u ∈ X then v u else
    M.f u (fun p => if hp : p.1 ∈ Z then v p.1 else
      z ⟨p.1, mem_parentsFinset_deleteIncoming_deleteOutgoing hu p hp⟩) e
  noise := M.noise

section Rule2Model

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

variable {X Z : Finset V} {v : ∀ u, α u}

theorem rule2Model_f_of_mem {u : V} (hu : u ∈ X) (z) (e : ε u) :
    (M.rule2Model X Z v).f u z e = v u := by
  simp [rule2Model, hu]

theorem rule2Model_f_restrict_of_notMem {u : V} (hu : u ∉ X) (t : ∀ w, α w) (e : ε u) :
    (M.rule2Model X Z v).f u
        ((((G.deleteIncoming ↑X).deleteOutgoing ↑Z).parentsFinset u).restrict t) e =
      M.f u ((G.parentsFinset u).restrict (fun w => if w ∈ Z then v w else t w)) e := by
  simp only [rule2Model, hu, dite_false]
  congr 1

/-- The solution of the auxiliary model, overwritten by `v` on `Z`, is the solution of
`do(X ∪ Z := v)`. -/
theorem override_solve_rule2Model (e : ∀ u, ε u) :
    (fun w => if w ∈ Z then v w else (M.rule2Model X Z v).solve e w) =
      (M.intervene (X ∪ Z) v).solve e := by
  refine (M.intervene (X ∪ Z) v).eq_solve_of_isSolution
    (M.isSolution_intervene_iff.2 ⟨fun u hu => ?_, fun u hu => ?_⟩)
  · by_cases huZ : u ∈ Z
    · simp [huZ]
    · have huX : u ∈ X := (mem_union.1 hu).resolve_right huZ
      simp only [huZ, ite_false]
      rw [(M.rule2Model X Z v).solve_eq e u, M.rule2Model_f_of_mem huX]
  · have huX : u ∉ X := fun h => hu (mem_union_left _ h)
    have huZ : u ∉ Z := fun h => hu (mem_union_right _ h)
    simp only [huZ, ite_false]
    rw [(M.rule2Model X Z v).solve_eq e u, M.rule2Model_f_restrict_of_notMem huX]

/-- If the solution of the auxiliary model agrees with `v` on `Z`, it is the solution of
`do(X := v)`. -/
theorem solve_rule2Model_eq_of_agree {e : ∀ u, ε u}
    (h : ∀ w ∈ Z, (M.rule2Model X Z v).solve e w = v w) :
    (M.rule2Model X Z v).solve e = (M.intervene X v).solve e := by
  refine (M.intervene X v).eq_solve_of_isSolution
    (M.isSolution_intervene_iff.2 ⟨fun u hu => ?_, fun u hu => ?_⟩)
  · rw [(M.rule2Model X Z v).solve_eq e u, M.rule2Model_f_of_mem hu]
  · rw [(M.rule2Model X Z v).solve_eq e u, M.rule2Model_f_restrict_of_notMem hu]
    congr 2
    funext w
    split_ifs with hw
    · exact (h w hw).symm
    · rfl

/-- If the solution of `do(X := v)` agrees with `v` on `Z`, it is the solution of the auxiliary
model. -/
theorem solve_intervene_eq_of_agree {e : ∀ u, ε u}
    (h : ∀ w ∈ Z, (M.intervene X v).solve e w = v w) :
    (M.intervene X v).solve e = (M.rule2Model X Z v).solve e := by
  refine (M.rule2Model X Z v).eq_solve_of_isSolution fun u => ?_
  by_cases hu : u ∈ X
  · rw [M.rule2Model_f_of_mem hu, M.solve_intervene_of_mem e hu]
  · rw [M.rule2Model_f_restrict_of_notMem hu, M.solve_intervene_of_notMem e hu]
    congr 2
    funext w
    split_ifs with hw
    · exact h w hw
    · rfl

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- On a set containing `Z`, the auxiliary model and `do(X := v)` have the same marginal at
`v`. -/
theorem margAt_rule2Model_of_subset {T : Finset V} (hZT : Z ⊆ T) :
    (M.rule2Model X Z v).dist.margAt T v = (M.intervene X v).dist.margAt T v := by
  rw [margAt_dist, margAt_dist, noiseDist_intervene]
  refine FiniteDist.probOf_congr _ fun e => ⟨fun h => ?_, fun h => ?_⟩
  · rwa [← M.solve_rule2Model_eq_of_agree fun w hw => h w (hZT hw)]
  · rwa [M.solve_intervene_eq_of_agree fun w hw => h w (hZT hw)] at h

/-- On a set disjoint from `Z`, the auxiliary model and `do(X ∪ Z := v)` have the same
marginal at `v`. -/
theorem margAt_rule2Model_of_disjoint {T : Finset V} (hTZ : Disjoint T Z) :
    (M.rule2Model X Z v).dist.margAt T v = (M.intervene (X ∪ Z) v).dist.margAt T v := by
  rw [margAt_dist, margAt_dist, noiseDist_intervene]
  refine FiniteDist.probOf_congr _ fun e => forall₂_congr fun w hw => ?_
  rw [← M.override_solve_rule2Model e]
  simp [disjoint_left.1 hTZ hw]

end Rule2Model

/-- **Rule 2 of do-calculus** (action and observation exchange; Pearl 2009, Theorem 3.4.1,
equation (3.32)), division-free form. Let `Z` be disjoint from `X`, `Y` and `W`. If `Y` and `Z`
are d-separated by `X ∪ W` in `(G.deleteIncoming X).deleteOutgoing Z`, then
`P(y, w | do(x, z)) * P(z, w | do(x)) = P(y, z, w | do(x)) * P(w | do(x, z))`, all values read
off `v`; that is, `P(y | do(x), do(z), w) = P(y | do(x), z, w)`.

The proof compares `do(X)` and `do(X ∪ Z)` through an auxiliary model on
`(G.deleteIncoming X).deleteOutgoing Z` (`SCM.rule2Model`) in which the vertices of `Z` keep
their mechanisms but their children see the constants `v`. Its distribution agrees with
`do(X)` on events that fix `Z` at `v`, and with `do(X ∪ Z)` on events not involving `Z`; the
global Markov property applied to it gives the identity. -/
theorem rule2 {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hWZ : Disjoint W Z)
    (hsep : ((G.deleteIncoming ↑X).deleteOutgoing ↑Z).DSep ↑Y ↑Z ↑(X ∪ W)) :
    (M.intervene (X ∪ Z) v).dist.margAt (Y ∪ W) v * (M.intervene X v).dist.margAt (Z ∪ W) v =
      (M.intervene X v).dist.margAt (Y ∪ Z ∪ W) v *
        (M.intervene (X ∪ Z) v).dist.margAt W v := by
  have h := ((M.rule2Model X Z v).factorizes.condIndep_of_dSep (M.rule2Model X Z v).acyclic
    hsep).margAt_mul v
  have hXW : Disjoint (X ∪ W) Z := disjoint_union_left.2 ⟨hXZ, hWZ⟩
  rw [M.margAt_rule2Model_of_subset (subset_union_right.trans subset_union_left),
    M.margAt_rule2Model_of_subset subset_union_left,
    M.margAt_rule2Model_of_disjoint hXW,
    M.margAt_rule2Model_of_disjoint (disjoint_union_left.2 ⟨hYZ, hXW⟩),
    union_union_eq_union_union, union_union_eq_union_union, union_union_eq_union_union,
    union_comm X W, M.margAt_union_intervene subset_rfl, M.margAt_union_intervene subset_rfl,
    M.margAt_union_intervene subset_union_left,
    M.margAt_union_intervene subset_union_left] at h
  linear_combination -h

/-- Under the disjointness of `W` and `Z`, observing `z` under `do(x)` is at most as likely as
the event `w` under `do(x, z)`: `P(z, w | do(x)) ≤ P(w | do(x, z))`. -/
theorem margAt_intervene_le_margAt_intervene_union {X Z W : Finset V} (v : ∀ u, α u)
    (hWZ : Disjoint W Z) :
    (M.intervene X v).dist.margAt (Z ∪ W) v ≤ (M.intervene (X ∪ Z) v).dist.margAt W v := by
  rw [← M.margAt_rule2Model_of_subset (Z := Z) subset_union_left,
    ← M.margAt_rule2Model_of_disjoint (X := X) hWZ]
  exact FiniteDist.margAt_anti _ subset_union_right v

/-- **Rule 2 of do-calculus**, ratio form: under the hypotheses of `SCM.rule2` and
`P(z, w | do(x)) > 0`, `P(y | do(x), do(z), w) = P(y | do(x), z, w)`. The positivity of
`P(w | do(x, z))` follows from `SCM.margAt_intervene_le_margAt_intervene_union`. -/
theorem rule2_div {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hWZ : Disjoint W Z)
    (hsep : ((G.deleteIncoming ↑X).deleteOutgoing ↑Z).DSep ↑Y ↑Z ↑(X ∪ W))
    (hpos : 0 < (M.intervene X v).dist.margAt (Z ∪ W) v) :
    (M.intervene (X ∪ Z) v).dist.margAt (Y ∪ W) v / (M.intervene (X ∪ Z) v).dist.margAt W v =
      (M.intervene X v).dist.margAt (Y ∪ Z ∪ W) v /
        (M.intervene X v).dist.margAt (Z ∪ W) v := by
  have hW := hpos.trans_le (M.margAt_intervene_le_margAt_intervene_union v hWZ)
  rw [div_eq_div_iff hW.ne' hpos.ne']
  exact M.rule2 v hXZ hYZ hWZ hsep

end SCM

end CausalInference

/-! ### Rule 3: the graph side -/

namespace Digraph

open Relation Finset

/-- A directed path from a vertex of `S` contains a last vertex of `S`: the remaining segment is
a directed path that avoids the incoming edges of `S`. -/
theorem exists_last_reflTransGen_deleteIncoming {V : Type*} {G : Digraph V} {S : Set V} {s y : V}
    (hs : s ∈ S) (h : ReflTransGen G.Adj s y) :
    ∃ z ∈ S, ReflTransGen (G.deleteIncoming S).Adj z y := by
  induction h with
  | refl => exact ⟨s, hs, ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨z, hz, hzb⟩ := ih
    by_cases hc : c ∈ S
    · exact ⟨c, hc, ReflTransGen.refl⟩
    · exact ⟨z, hz, hzb.tail ⟨hbc, hc⟩⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The set `Z(W)` of Rule 3 of do-calculus: the vertices of `Z` that are not ancestors of any
vertex of `W` in `G.deleteIncoming X`. -/
noncomputable def rule3Set (G : Digraph V) (X Z W : Finset V) : Finset V :=
  Z.filter fun z => z ∉ (G.deleteIncoming ↑X).ancestorsOf ↑W

theorem mem_rule3Set {G : Digraph V} {X Z W : Finset V} {z : V} :
    z ∈ G.rule3Set X Z W ↔ z ∈ Z ∧ z ∉ (G.deleteIncoming ↑X).ancestorsOf ↑W := by
  classical
  unfold rule3Set
  exact mem_filter

theorem rule3Set_subset (G : Digraph V) (X Z W : Finset V) : G.rule3Set X Z W ⊆ Z :=
  fun _ hz => (mem_rule3Set.1 hz).1

/-- The set `Z(W)` of Rule 3 computed from the finite ancestral closure: `Z` minus the
ancestors of `W` in `G.deleteIncoming X`. Unlike `Digraph.rule3Set`, it can be evaluated (for
example by `decide`) when adjacency is decidable; `Digraph.rule3SetFinset_eq` shows that the two
agree. -/
def rule3SetFinset (G : Digraph V) [DecidableRel G.Adj] (X Z W : Finset V) : Finset V :=
  Z \ (G.deleteIncoming ↑X).ancestorsOfFinset W

theorem rule3SetFinset_eq (G : Digraph V) [DecidableRel G.Adj] (X Z W : Finset V) :
    G.rule3SetFinset X Z W = G.rule3Set X Z W := by
  ext z
  rw [rule3SetFinset, mem_sdiff, mem_rule3Set, ← mem_coe (s := ancestorsOfFinset _ W),
    coe_ancestorsOfFinset]

/-- No ancestor of `W` in `G.deleteIncoming X` is a descendant of `Z(W)` there. -/
theorem notMem_descendantsOf_rule3Set_of_mem_ancestorsOf {G : Digraph V} {X Z W : Finset V}
    {u : V} (hu : u ∈ (G.deleteIncoming ↑X).ancestorsOf ↑W) :
    u ∉ (G.deleteIncoming ↑X).descendantsOf ↑(G.rule3Set X Z W) := by
  rintro ⟨s, hs, hsu⟩
  obtain ⟨w, hw, huw⟩ := hu
  exact (mem_rule3Set.1 hs).2 ⟨w, hw, hsu.trans huw⟩

/-- **The graph lemma behind Rule 3.** Suppose `X` and `Z` are disjoint and `Y` and `Z` are
d-separated by `X ∪ W` in `G.deleteIncoming (X ∪ Z(W))`. Then no vertex of `Y` is a descendant
of `Z(W)` in `G.deleteIncoming X`: a directed path from `Z(W)` to `Y`, taken from its last
vertex in `Z(W)`, would be an active trail. -/
theorem notMem_descendantsOf_rule3Set {G : Digraph V} {X Y Z W : Finset V}
    (hXZ : Disjoint X Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W)) {y : V}
    (hy : y ∈ Y) :
    y ∉ (G.deleteIncoming ↑X).descendantsOf ↑(G.rule3Set X Z W) := by
  rintro ⟨s, hs, hsy⟩
  obtain ⟨z, hz, hzy⟩ := exists_last_reflTransGen_deleteIncoming hs hsy
  rw [deleteIncoming_deleteIncoming, ← coe_union] at hzy
  obtain ⟨hzZ, hzW⟩ := mem_rule3Set.1 hz
  have hzA : z ∉ (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).ancestorsOf ↑(X ∪ W) := by
    rintro ⟨t, ht, hzt⟩
    rcases mem_union.1 (mem_coe.1 ht) with htX | htW
    · rcases hzt.cases_tail with rfl | ⟨c, _, hct⟩
      · exact disjoint_left.1 hXZ htX hzZ
      · exact hct.2 (mem_coe.2 (mem_union_left _ htX))
    · exact hzW ⟨t, htW,
        reflTransGen_mono (deleteIncoming_anti (coe_subset.2 subset_union_left)) hzt⟩
  obtain ⟨c, hc⟩ := exists_reflTransGen_bayesBall_of_reflTransGen hzy hzA false
  refine hsep (DConn.symm ⟨z, hzZ, y, hy, fun h => hzA (subset_ancestorsOf _ h),
    fun h => hzA ⟨y, h, hzy⟩, c, hc⟩)

end Digraph

/-! ### The graph with an added root -/

namespace Digraph

open Relation Finset

variable {V : Type*}

/-- The graph `H` with one added root: on `Option V`, the vertex `none` is a new root with an
edge into `some b` for each `b ∈ B`, and the vertices `some u` carry the edges of `H`. -/
def addRoot (H : Digraph V) (B : Finset V) : Digraph (Option V) where
  Adj a b := match a, b with
    | none, some b => b ∈ B
    | some u, some w => H.Adj u w
    | _, _ => False

variable {H : Digraph V} {B : Finset V}

instance [DecidableEq V] [DecidableRel H.Adj] : DecidableRel (H.addRoot B).Adj := fun a b =>
  match a, b with
  | none, none => inferInstanceAs (Decidable False)
  | none, some b => inferInstanceAs (Decidable (b ∈ B))
  | some _, none => inferInstanceAs (Decidable False)
  | some u, some w => inferInstanceAs (Decidable (H.Adj u w))

@[simp] theorem addRoot_adj_none_some {b : V} : (H.addRoot B).Adj none (some b) ↔ b ∈ B :=
  Iff.rfl

@[simp] theorem addRoot_adj_some_some {u w : V} :
    (H.addRoot B).Adj (some u) (some w) ↔ H.Adj u w := Iff.rfl

@[simp] theorem not_addRoot_adj_none {a : Option V} : ¬ (H.addRoot B).Adj a none := by
  cases a <;> exact id

/-- Adding a root to an acyclic graph keeps it acyclic. -/
theorem IsAcyclic.addRoot [Finite V] (hH : H.IsAcyclic) (B : Finset V) :
    (H.addRoot B).IsAcyclic := by
  obtain ⟨f, hf⟩ := hH.exists_adj_lt
  refine isAcyclic_of_adj_lt (fun a => Option.elim a 0 fun u => f u + 1) ?_
  rintro (_ | a) (_ | b) h <;> simp_all [Digraph.addRoot]

/-- A directed path between two old vertices of the graph with an added root is a directed path
of `H`: the root has no incoming edge. -/
theorem reflTransGen_of_reflTransGen_addRoot {a c : Option V}
    (h : ReflTransGen (H.addRoot B).Adj a c) :
    ∀ u w, a = some u → c = some w → ReflTransGen H.Adj u w := by
  induction h using ReflTransGen.head_induction_on with
  | refl =>
    rintro u w rfl h
    cases h
    exact ReflTransGen.refl
  | @head a b hab _ ih =>
    rintro u w rfl rfl
    cases b with
    | none => exact absurd hab not_addRoot_adj_none
    | some b => exact ReflTransGen.head hab (ih b w rfl rfl)

theorem mem_ancestorsOf_of_some_mem_ancestorsOf_addRoot {C : Set V} {u : V}
    (h : some u ∈ (H.addRoot B).ancestorsOf (some '' C)) : u ∈ H.ancestorsOf C := by
  obtain ⟨_, ⟨c, hc, rfl⟩, huc⟩ := h
  exact ⟨c, hc, reflTransGen_of_reflTransGen_addRoot huc u c rfl rfl⟩

/-- A step of an active trail between two old vertices of the graph with an added root is a
step of an active trail in `H`, with the same flags. -/
theorem bayesBall_adj_of_bayesBall_addRoot {C : Set V} {u w : V} {a d : Bool}
    (h : ((H.addRoot B).bayesBall (some '' C)).Adj (some u, a) (some w, d)) :
    (H.bayesBall C).Adj (u, a) (w, d) := by
  obtain ⟨hadj, hpass⟩ := h
  refine ⟨by cases d <;> simpa using hadj, ?_⟩
  unfold Passes at hpass ⊢
  split_ifs at hpass ⊢
  · exact mem_ancestorsOf_of_some_mem_ancestorsOf_addRoot hpass
  · exact fun hu => hpass ⟨u, hu, rfl⟩

/-- An active trail that enters a vertex `w ∉ C` through an arrowhead can be restarted at `w`
with the arrival flag `false`. -/
theorem exists_reflTransGen_bayesBall_false {C : Set V} {w y : V} {c : Bool} (hw : w ∉ C)
    (h : ReflTransGen (H.bayesBall C).Adj (w, true) (y, c)) :
    ∃ c', ReflTransGen (H.bayesBall C).Adj (w, false) (y, c') := by
  rcases h.cases_head with h | ⟨⟨x, e⟩, hwx, hxy⟩
  · cases h
    exact ⟨false, ReflTransGen.refl⟩
  · refine ⟨c, ReflTransGen.head ?_ hxy⟩
    cases e
    · exact bayesBall_adj_false_false.2 ⟨(bayesBall_adj_true_false.1 hwx).1, hw⟩
    · exact bayesBall_adj_true.2 (bayesBall_adj_true.1 hwx)

/-- **The graph lemma of the added root.** If `B` is disjoint from `C` and `B` and `Y` are
d-separated by `C` in `H`, then the added root is d-separated from the copy of `Y` by the copy
of `C` in `H.addRoot B`: an active trail from the root starts with an edge into some `b ∈ B`,
and its remainder is an active trail from `b` in `H`. -/
theorem dSep_addRoot {C Y : Set V} (hBC : Disjoint (↑B : Set V) C) (hsep : H.DSep ↑B Y C) :
    (H.addRoot B).DSep {none} (some '' Y) (some '' C) := by
  rintro ⟨_, rfl, _, ⟨y, hy, rfl⟩, -, hyC, e, he⟩
  have key : ∀ s, ReflTransGen ((H.addRoot B).bayesBall (some '' C)).Adj s (some y, e) →
      (∃ b ∈ B, ∃ c', ReflTransGen (H.bayesBall C).Adj (b, false) (y, c')) ∨
        ∃ u, s.1 = some u ∧ ReflTransGen (H.bayesBall C).Adj (u, s.2) (y, e) := by
    intro s hs
    induction hs using ReflTransGen.head_induction_on with
    | refl => exact Or.inr ⟨y, rfl, ReflTransGen.refl⟩
    | @head s t hst _ ih =>
      rcases ih with ih | ⟨w, hw, hwy⟩
      · exact Or.inl ih
      obtain ⟨o, a⟩ := s
      obtain ⟨_, d⟩ := t
      simp only at hw hwy
      subst hw
      cases o with
      | some u =>
        exact Or.inr ⟨u, rfl, ReflTransGen.head (bayesBall_adj_of_bayesBall_addRoot hst) hwy⟩
      | none =>
        cases d
        · exact absurd hst.1 (by simp)
        · have hwB : w ∈ B := hst.1
          obtain ⟨c', hc'⟩ := exists_reflTransGen_bayesBall_false
            (Set.disjoint_left.1 hBC (mem_coe.2 hwB)) hwy
          exact Or.inl ⟨w, hwB, c', hc'⟩
  rcases key _ he with ⟨b, hb, c', hc'⟩ | ⟨u, hu, -⟩
  · exact hsep ⟨b, mem_coe.2 hb, y, hy, Set.disjoint_left.1 hBC (mem_coe.2 hb),
      fun h => hyC ⟨y, h, rfl⟩, c', hc'⟩
  · cases hu

end Digraph

namespace CausalInference

open Finset

namespace FiniteDist

/-- Under a product law on `Option ι`, an event on the coordinate `none` and an event on the other
coordinates are independent; the second has the probability given by the product of the
remaining laws. -/
theorem probOf_pi_option {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Option ι → Type*}
    [∀ o, Fintype (κ o)] (p : ∀ o, FiniteDist (κ o)) (P : κ none → Prop) [DecidablePred P]
    (E : (∀ i, κ (some i)) → Prop) [DecidablePred E] :
    (pi p).probOf (fun ω => P (ω none) ∧ E fun i => ω (some i)) =
      (p none).probOf P * (pi fun i => p (some i)).probOf E := by
  simp only [probOf, prob, sum_filter, pi_apply]
  rw [← (Equiv.piOptionEquivProd (β := κ)).symm.sum_comp, Fintype.sum_prod_type, sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun g _ => ?_
  simp only [Equiv.piOptionEquivProd, Equiv.coe_fn_symm_mk, Fintype.prod_option, ite_and]
  split_ifs <;> simp

end FiniteDist

namespace SCM

universe uα uε

variable {V : Type*}

/-! ### The switch model -/

/-- The value types of the switch model: a bit at the added root `none`, and `α u` at `some u`.
-/
abbrev switchVal (α : V → Type uα) : Option V → Type uα :=
  fun o => Option.elim o (ULift Bool) α

/-- The noise types of the switch model: a bit at the added root `none` (the fair coin of the
switch), and `ε u` at `some u`. -/
abbrev switchNoise (ε : V → Type uε) : Option V → Type uε :=
  fun o => Option.elim o (ULift Bool) ε

variable {α : V → Type uα} {ε : V → Type uε}

instance [∀ v, Fintype (α v)] : ∀ o, Fintype (switchVal α o)
  | none => inferInstanceAs (Fintype (ULift Bool))
  | some v => inferInstanceAs (Fintype (α v))

instance [∀ v, DecidableEq (α v)] : ∀ o, DecidableEq (switchVal α o)
  | none => inferInstanceAs (DecidableEq (ULift Bool))
  | some v => inferInstanceAs (DecidableEq (α v))

instance [∀ v, Fintype (ε v)] : ∀ o, Fintype (switchNoise ε o)
  | none => inferInstanceAs (Fintype (ULift Bool))
  | some v => inferInstanceAs (Fintype (ε v))

variable [Fintype V] [DecidableEq V] {H : Digraph V} [DecidableRel H.Adj] [∀ v, Fintype (ε v)]

theorem some_mem_parentsFinset_addRoot {B : Finset V} {u : V} (p : H.parentsFinset u) :
    some p.1 ∈ (H.addRoot B).parentsFinset (some u) :=
  Digraph.mem_parentsFinset.2 (Digraph.addRoot_adj_some_some.2 (Digraph.mem_parentsFinset.1 p.2))

theorem none_mem_parentsFinset_addRoot {B : Finset V} {u : V} (hu : u ∈ B) :
    none ∈ (H.addRoot B).parentsFinset (some u) :=
  Digraph.mem_parentsFinset.2 hu

/-- The structural functions of the switch model. The root copies its noise bit. A vertex
`u ∈ B` takes the value `v u` when the root is on and otherwise follows its equation in `N`
applied to the old parents; every other vertex follows its equation in `N`. -/
def switchF (N : SCM H α ε) (B : Finset V) (v : ∀ u, α u) :
    ∀ o, (∀ p : (H.addRoot B).parentsFinset o, switchVal α p) → switchNoise ε o →
      switchVal α o
  | none, _, e => ⟨e.down⟩
  | some u, z, e =>
    if hu : u ∈ B then
      (if (z ⟨none, none_mem_parentsFinset_addRoot hu⟩).down then v u else
        N.f u (fun p => z ⟨some p.1, some_mem_parentsFinset_addRoot p⟩) e)
    else N.f u (fun p => z ⟨some p.1, some_mem_parentsFinset_addRoot p⟩) e

/-- The noise laws of the switch model: a fair coin at the root, the laws of `N` elsewhere. -/
noncomputable def switchNoiseLaw (N : SCM H α ε) : ∀ o, FiniteDist (switchNoise ε o)
  | none => (FiniteDist.uniform : FiniteDist (ULift Bool))
  | some u => N.noise u

/-- The **switch model** of `N` for a set `B` and values `v`: a model on `H.addRoot B` whose
added root is a fair coin that switches the mechanisms of the vertices of `B` between their own
equations in `N` (root off) and the constants `v` (root on, the intervention `do(B := v)`). -/
noncomputable def switchModel (N : SCM H α ε) (B : Finset V) (v : ∀ u, α u) :
    SCM (H.addRoot B) (switchVal α) (switchNoise ε) where
  acyclic := N.acyclic.addRoot B
  f := switchF N B v
  noise := switchNoiseLaw N

/-- The noise of `N` read off a noise value of the switch model. -/
def switchProj (w : ∀ o, switchNoise ε o) : ∀ u, ε u := fun u => w (some u)

/-- The values of the old vertices in the switch model at a noise value: the solution of
`do(B := v)` in `N` if the root is on, and of `N` itself if it is off. -/
noncomputable def switchOld (N : SCM H α ε) (B : Finset V) (v : ∀ u, α u)
    (w : ∀ o, switchNoise ε o) : ∀ u, α u :=
  if (w none).down then (N.intervene B v).solve (switchProj w) else N.solve (switchProj w)

/-- The configuration of the switch model at a noise value: the root bit at the root, and
`SCM.switchOld` at the old vertices. -/
noncomputable def switchConfig (N : SCM H α ε) (B : Finset V) (v : ∀ u, α u)
    (w : ∀ o, switchNoise ε o) : ∀ o, switchVal α o
  | none => ⟨(w none).down⟩
  | some u => switchOld N B v w u

theorem switchModel_solve (N : SCM H α ε) (B : Finset V) (v : ∀ u, α u)
    (w : ∀ o, switchNoise ε o) : (N.switchModel B v).solve w = switchConfig N B v w := by
  refine ((N.switchModel B v).eq_solve_of_isSolution fun o => ?_).symm
  rcases o with _ | u
  · rfl
  change switchConfig N B v w (some u) = switchF N B v (some u) _ (w (some u))
  by_cases hw : (w none).down <;> by_cases hu : u ∈ B
  · simp [switchConfig, switchOld, switchF, hw, hu, N.solve_intervene_of_mem]
  · simp only [switchConfig, switchOld, switchF, hw, hu, ↓reduceIte, ↓reduceDIte,
      Finset.restrict]
    rw [N.solve_intervene_of_notMem _ hu]
    rfl
  · simp only [switchConfig, switchOld, switchF, hw, hu, ↓reduceIte, ↓reduceDIte,
      Bool.false_eq_true, Finset.restrict]
    rw [N.solve_eq]
    rfl
  · simp only [switchConfig, switchOld, switchF, hw, hu, ↓reduceIte, ↓reduceDIte,
      Bool.false_eq_true, Finset.restrict]
    rw [N.solve_eq]
    rfl

variable (N : SCM H α ε) (B : Finset V) (v : ∀ u, α u)

/-- The root bit of the switch model is a fair coin independent of the noise of `N`. -/
theorem probOf_noiseDist_switchModel (b : Bool) (E : (∀ u, ε u) → Prop) [DecidablePred E] :
    (N.switchModel B v).noiseDist.probOf (fun w => (w none).down = b ∧ E (switchProj w)) =
      1 / 2 * N.noiseDist.probOf E := by
  have hcoin : (switchNoiseLaw N none).probOf (fun a => a.down = b) = 1 / 2 := by
    change (FiniteDist.uniform : FiniteDist (ULift Bool)).probOf (fun a => a.down = b) = 1 / 2
    have hcard : (univ.filter fun a : ULift Bool => a.down = b).card = 1 :=
      card_eq_one.2 ⟨⟨b⟩, by ext a; simp [ULift.ext_iff]⟩
    simp only [FiniteDist.probOf, FiniteDist.prob, FiniteDist.uniform_apply, sum_const,
      nsmul_eq_mul]
    rw [hcard]
    simp
  have h := @FiniteDist.probOf_pi_option _ _ _ _ _ (switchNoiseLaw N) (fun a => a.down = b) _
    E ‹_›
  rw [hcoin] at h
  exact h

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

theorem probOf_switchConfig (b : Bool) (T : Finset V) :
    (N.switchModel B v).noiseDist.probOf
        (fun w => (w none).down = b ∧ ∀ u ∈ T, switchOld N B v w u = v u) =
      1 / 2 * (if b then (N.intervene B v).dist.margAt T v else N.dist.margAt T v) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [margAt_dist N, ← probOf_noiseDist_switchModel N B v false]
    refine FiniteDist.probOf_congr _ fun w => and_congr_right fun hw => ?_
    simp [switchOld, hw]
  · simp only [↓reduceIte]
    rw [margAt_dist (N.intervene B v), noiseDist_intervene,
      ← probOf_noiseDist_switchModel N B v true]
    refine FiniteDist.probOf_congr _ fun w => and_congr_right fun hw => ?_
    simp [switchOld, hw]

/-- The configuration of the switch model with root bit `b` and the values `v` elsewhere. -/
def switchCfg (v : ∀ u, α u) (b : Bool) : ∀ o, switchVal α o
  | none => ⟨b⟩
  | some u => v u

/-- The marginal of the switch model on the root and the copy of `T`, at root bit `b` and the
values `v`: half the marginal of `do(B := v)` (if `b = true`) or of `N` (if `b = false`). -/
theorem margAt_switchModel_insert (b : Bool) (T : Finset V) :
    (N.switchModel B v).dist.margAt (insert none (T.map .some)) (switchCfg v b) =
      1 / 2 * (if b then (N.intervene B v).dist.margAt T v else N.dist.margAt T v) := by
  rw [margAt_dist, ← probOf_switchConfig N B v b T]
  refine FiniteDist.probOf_congr _ fun w => ?_
  rw [switchModel_solve]
  simp [switchConfig, switchCfg, ULift.ext_iff]

/-- The marginal of the switch model on the copy of `T`, at the values `v`: the average of the
marginals of `do(B := v)` and of `N`. -/
theorem margAt_switchModel_map (b : Bool) (T : Finset V) :
    (N.switchModel B v).dist.margAt (T.map .some) (switchCfg v b) =
      1 / 2 * (N.intervene B v).dist.margAt T v + 1 / 2 * N.dist.margAt T v := by
  have h1 := probOf_switchConfig N B v true T
  have h0 := probOf_switchConfig N B v false T
  simp only [↓reduceIte, Bool.false_eq_true] at h1 h0
  rw [← h1, ← h0, margAt_dist, (N.switchModel B v).noiseDist.probOf_eq_sum_univ
    (fun w : ∀ o, switchNoise ε o => (w none).down), Fintype.sum_bool]
  congr 1 <;> refine FiniteDist.probOf_congr _ fun w => ?_ <;> rw [switchModel_solve] <;>
    simp [switchConfig, switchCfg, and_comm]

/-- **Exchange of an intervention through a fair switch.** If `B` is disjoint from `C` and `B`
and `Y` are d-separated by `C` in `H`, then for every model `N` on `H`
`P(y, c | do(b)) * P(c) = P(y, c) * P(c | do(b))`, all values read off `v`. No positivity is
needed. Proof: the switch model `N.switchModel B v` is a model on `H.addRoot B` in which the root
is d-separated from `Y` by `C` (`Digraph.dSep_addRoot`); its global Markov property gives the
identity, since conditioning on the root bit gives `do(B := v)` and `N`. -/
theorem margAt_intervene_mul_of_dSep {Y C : Finset V} (hBC : Disjoint B C)
    (hsep : H.DSep ↑B ↑Y ↑C) :
    (N.intervene B v).dist.margAt (Y ∪ C) v * N.dist.margAt C v =
      N.dist.margAt (Y ∪ C) v * (N.intervene B v).dist.margAt C v := by
  have hsep' : (H.addRoot B).DSep ↑({none} : Finset (Option V)) ↑(Y.map .some)
      ↑(C.map .some) := by
    rw [coe_singleton, coe_map, coe_map]
    exact Digraph.dSep_addRoot (disjoint_coe.2 hBC) hsep
  have h := ((N.switchModel B v).factorizes.condIndep_of_dSep (N.switchModel B v).acyclic
    hsep').margAt_mul (switchCfg v true)
  rw [show ({none} : Finset (Option V)) ∪ Y.map .some ∪ C.map .some =
      insert none ((Y ∪ C).map .some) by rw [map_union, union_assoc]; rfl,
    show ({none} : Finset (Option V)) ∪ C.map .some = insert none (C.map .some) from rfl,
    ← map_union, margAt_switchModel_insert, margAt_switchModel_insert, margAt_switchModel_map,
    margAt_switchModel_map] at h
  simp only [↓reduceIte] at h
  linear_combination 4 * h

end SCM

end CausalInference

namespace CausalInference

open Finset

/-! ### Rule 3 -/

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- Intervening on `Z(W)` in addition to `X` does not change the marginal at `v` of a set of
vertices that are not descendants of `Z(W)` in `G.deleteIncoming X`. -/
theorem margAt_intervene_union_rule3Set {X Z W S : Finset V} (v : ∀ u, α u)
    (hS : ∀ u ∈ S, u ∉ (G.deleteIncoming ↑X).descendantsOf ↑(G.rule3Set X Z W)) :
    (M.intervene (X ∪ G.rule3Set X Z W) v).dist.margAt S v =
      (M.intervene X v).dist.margAt S v := by
  rw [show (M.intervene (X ∪ G.rule3Set X Z W) v).dist =
      ((M.intervene X v).intervene (G.rule3Set X Z W) v).dist by
    rw [M.dist_intervene_intervene]
    simp only [ite_self]]
  exact (M.intervene X v).margAt_intervene_of_notMem_descendantsOf hS v

/-- Under the hypothesis of Rule 3, intervening on `Z(W)` in addition to `X` does not change the
marginals on subsets of `Y ∪ (Z \ Z(W)) ∪ W`. -/
theorem margAt_intervene_union_rule3Set_of_subset {X Y Z W S : Finset V} (v : ∀ u, α u)
    (hXZ : Disjoint X Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W))
    (hS : S ⊆ Y ∪ (Z \ G.rule3Set X Z W) ∪ W) :
    (M.intervene (X ∪ G.rule3Set X Z W) v).dist.margAt S v =
      (M.intervene X v).dist.margAt S v := by
  refine M.margAt_intervene_union_rule3Set v fun u hu => ?_
  rcases mem_union.1 (hS hu) with hu | hu
  · rcases mem_union.1 hu with hu | hu
    · exact Digraph.notMem_descendantsOf_rule3Set hXZ hsep hu
    · obtain ⟨huZ, hu2⟩ := mem_sdiff.1 hu
      refine Digraph.notMem_descendantsOf_rule3Set_of_mem_ancestorsOf ?_
      by_contra h
      exact hu2 (Digraph.mem_rule3Set.2 ⟨huZ, h⟩)
  · exact Digraph.notMem_descendantsOf_rule3Set_of_mem_ancestorsOf
      (Digraph.subset_ancestorsOf _ (mem_coe.2 hu))

theorem union_rule3Set_union_sdiff (G : Digraph V) (X Z W : Finset V) :
    X ∪ Z = X ∪ G.rule3Set X Z W ∪ (Z \ G.rule3Set X Z W) := by
  have h := G.rule3Set_subset X Z W
  ext u
  simp only [mem_union, mem_sdiff]
  constructor
  · rintro (hu | hu)
    · exact Or.inl (Or.inl hu)
    · by_cases h2 : u ∈ G.rule3Set X Z W
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨hu, h2⟩
  · rintro ((hu | hu) | hu)
    · exact Or.inl hu
    · exact Or.inr (h hu)
    · exact Or.inr hu.1

omit [DecidableRel G.Adj] in
/-- The d-separation of Rule 3 gives the d-separation needed by Rules 1 and 2 for the
intervention set `X ∪ Z(W)` and the observed set `Z \ Z(W)`. -/
theorem dSep_rule3_sdiff {X Y Z W : Finset V}
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W)) :
    (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑(Z \ G.rule3Set X Z W)
      ↑(X ∪ G.rule3Set X Z W ∪ W) := by
  have h := (hsep.mono_right (Y' := ↑(Z \ G.rule3Set X Z W) ∪ ↑(G.rule3Set X Z W))
    (by
      intro u hu
      rcases hu with hu | hu
      · exact mem_coe.2 (mem_sdiff.1 (mem_coe.1 hu)).1
      · exact mem_coe.2 (G.rule3Set_subset X Z W (mem_coe.1 hu)))).weak_union
  convert h using 1
  ext u
  simp only [coe_union, Set.mem_union, mem_coe]
  tauto

/-- Under the graphical premise of Rule 3 and `P(z', w | do(x)) > 0`, where `z'` are the values
on `Z \ Z(W)`, the denominator `P(w | do(x, z))` is positive. This joint positivity is a
sufficient condition for both denominators of `SCM.rule3_div`; it is not necessary
(`SCM.Rule3PositivityExample.premises_hold_joint_mass_zero`). -/
theorem rule3_pos {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W))
    (hpos : 0 < (M.intervene X v).dist.margAt ((Z \ G.rule3Set X Z W) ∪ W) v) :
    0 < (M.intervene (X ∪ Z) v).dist.margAt W v := by
  have h := M.margAt_intervene_le_margAt_intervene_union (X := X ∪ G.rule3Set X Z W)
    (Z := Z \ G.rule3Set X Z W) v (hWZ.mono_right sdiff_subset)
  rw [← union_rule3Set_union_sdiff, M.margAt_intervene_union_rule3Set_of_subset v hXZ hsep
    (union_subset (subset_union_right.trans subset_union_left) subset_union_right)] at h
  exact hpos.trans_le h

omit [Fintype V] [DecidableRel G.Adj] in
theorem rule3_aux_union (S X A W : Finset V) : S ∪ (X ∪ A ∪ W) = S ∪ W ∪ (X ∪ A) := by
  ext; simp only [mem_union]; tauto

/-- **Rule 3 of do-calculus** (insertion or deletion of actions; Pearl 2009, Theorem 3.4.1,
equation (3.33)), division-free form. Let `Z` be disjoint from `X` and `W`, and let
`Z(W) = Digraph.rule3Set G X Z W` be the vertices of `Z` that are not ancestors of `W` in
`G.deleteIncoming X`. If `Y` and `Z` are d-separated by `X ∪ W` in
`G.deleteIncoming (X ∪ Z(W))`, then
`P(y, w | do(x, z)) * P(w | do(x)) = P(y, w | do(x)) * P(w | do(x, z))`, all values read off
`v`; that is, `P(y | do(x), do(z), w) = P(y | do(x), w)`. No positivity is needed. The
disjointness of `Y` and `Z` is not assumed: it follows from the d-separation and the
disjointness of `Z` from `X ∪ W`.

Proof: write `A = Z(W)` and `B = Z \ A`. Under `do(X ∪ A)`, the d-separation of `Y` and `B` by
`X ∪ A ∪ W` (`SCM.dSep_rule3_sdiff`) gives, through the switch model
(`SCM.margAt_intervene_mul_of_dSep`), the identity between `do(X ∪ A)` and `do(X ∪ Z)`; the
intervention on `A` changes no marginal of `Y ∪ W`
(`SCM.margAt_intervene_union_rule3Set_of_subset`). -/
theorem rule3 {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W)) :
    (M.intervene (X ∪ Z) v).dist.margAt (Y ∪ W) v * (M.intervene X v).dist.margAt W v =
      (M.intervene X v).dist.margAt (Y ∪ W) v * (M.intervene (X ∪ Z) v).dist.margAt W v := by
  have hBC : Disjoint (Z \ G.rule3Set X Z W) (X ∪ G.rule3Set X Z W ∪ W) :=
    disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨(hXZ.mono_right sdiff_subset).symm,
      sdiff_disjoint⟩, (hWZ.mono_right sdiff_subset).symm⟩
  have h := (M.intervene (X ∪ G.rule3Set X Z W) v).margAt_intervene_mul_of_dSep
    (Z \ G.rule3Set X Z W) v hBC (dSep_rule3_sdiff hsep).symm
  have hd : ((M.intervene (X ∪ G.rule3Set X Z W) v).intervene (Z \ G.rule3Set X Z W) v).dist =
      (M.intervene (X ∪ Z) v).dist := by
    rw [M.dist_intervene_intervene]
    simp only [ite_self]
    rw [← union_rule3Set_union_sdiff G X Z W]
  have e := fun {S : Finset V} (hS : S ⊆ Y ∪ (Z \ G.rule3Set X Z W) ∪ W) =>
    M.margAt_intervene_union_rule3Set_of_subset v hXZ hsep hS
  have hXA : X ∪ G.rule3Set X Z W ⊆ X ∪ Z :=
    union_subset_union_right (G.rule3Set_subset X Z W)
  rw [hd, rule3_aux_union, union_comm (X ∪ G.rule3Set X Z W) W] at h
  rw [M.margAt_union_intervene hXA, M.margAt_union_intervene hXA,
    M.margAt_union_intervene subset_rfl, M.margAt_union_intervene subset_rfl,
    e (union_subset (subset_union_left.trans subset_union_left) subset_union_right),
    e subset_union_right] at h
  exact h

/-- **Rule 3 of do-calculus**, ratio form: under the hypotheses of `SCM.rule3`, if
`P(w | do(x)) > 0` and `P(w | do(x, z)) > 0`, then `P(y | do(x), do(z), w) = P(y | do(x), w)`.
-/
theorem rule3_div {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W))
    (hp : 0 < (M.intervene X v).dist.margAt W v)
    (hq : 0 < (M.intervene (X ∪ Z) v).dist.margAt W v) :
    (M.intervene (X ∪ Z) v).dist.margAt (Y ∪ W) v / (M.intervene (X ∪ Z) v).dist.margAt W v =
      (M.intervene X v).dist.margAt (Y ∪ W) v / (M.intervene X v).dist.margAt W v := by
  rw [div_eq_div_iff hq.ne' hp.ne']
  exact M.rule3 v hXZ hWZ hsep

end SCM

end CausalInference
