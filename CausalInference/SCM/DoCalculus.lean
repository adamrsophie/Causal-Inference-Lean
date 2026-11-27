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
  (`Digraph.rule3Set`) is the set of vertices of `Z` that are not ancestors of `W` in
  `G.deleteIncoming X`, then `P(y | do(x), do(z), w) = P(y | do(x), w)`. Proof: no vertex of
  `Y ∪ W` or of `Z \ Z(W)` descends from `Z(W)` (`Digraph.notMem_descendantsOf_rule3Set`), so
  the intervention on `Z(W)` does not change their law; Rules 1 and 2 for the intervention set
  `X ∪ Z(W)` handle `Z \ Z(W)`. This route needs `P(z', w | do(x)) > 0` for the values `z'` on
  `Z \ Z(W)`, also in the division-free form.

Rules 2 and 3 assume that `Z` is disjoint from `X`, `Y` and `W`, as in Pearl's statement for
disjoint sets; Rule 1 needs no disjointness. Completeness of the calculus is not treated.

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

/-- Under the hypotheses of Rule 3, `P(w | do(x, z)) > 0`. -/
theorem rule3_pos {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hWZ : Disjoint W Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W))
    (hpos : 0 < (M.intervene X v).dist.margAt ((Z \ G.rule3Set X Z W) ∪ W) v) :
    0 < (M.intervene (X ∪ Z) v).dist.margAt W v := by
  have h := M.margAt_intervene_le_margAt_intervene_union (X := X ∪ G.rule3Set X Z W)
    (Z := Z \ G.rule3Set X Z W) v (hWZ.mono_right sdiff_subset)
  rw [← union_rule3Set_union_sdiff, M.margAt_intervene_union_rule3Set_of_subset v hXZ hsep
    (union_subset (subset_union_right.trans subset_union_left) subset_union_right)] at h
  exact hpos.trans_le h

/-- **Rule 3 of do-calculus** (insertion or deletion of actions; Pearl 2009, Theorem 3.4.1,
equation (3.33)), division-free form. Let `Z` be disjoint from `X`, `Y` and `W`, and let
`Z(W) = Digraph.rule3Set G X Z W` be the vertices of `Z` that are not ancestors of `W` in
`G.deleteIncoming X`. If `Y` and `Z` are d-separated by `X ∪ W` in
`G.deleteIncoming (X ∪ Z(W))`, then
`P(y, w | do(x, z)) * P(w | do(x)) = P(y, w | do(x)) * P(w | do(x, z))`, all values read off
`v`; that is, `P(y | do(x), do(z), w) = P(y | do(x), w)`.

This version assumes `P(z', w | do(x)) > 0`, where `z'` are the values on `Z \ Z(W)`. The
textbook division-free statement has no positivity hypothesis; the hypothesis is used here to
cancel a common factor when Rule 3 is derived from Rules 1 and 2 applied to the intervention set
`X ∪ Z(W)`, after showing that `Y ∪ W` and `Z \ Z(W)` are not descendants of `Z(W)` in
`G.deleteIncoming X`. The ratio form `SCM.rule3_div` needs a positivity hypothesis anyway. -/
theorem rule3 {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hWZ : Disjoint W Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W))
    (hpos : 0 < (M.intervene X v).dist.margAt ((Z \ G.rule3Set X Z W) ∪ W) v) :
    (M.intervene (X ∪ Z) v).dist.margAt (Y ∪ W) v * (M.intervene X v).dist.margAt W v =
      (M.intervene X v).dist.margAt (Y ∪ W) v * (M.intervene (X ∪ Z) v).dist.margAt W v := by
  have hsep1 := dSep_rule3_sdiff hsep
  have hX'Z₁ : Disjoint (X ∪ G.rule3Set X Z W) (Z \ G.rule3Set X Z W) :=
    disjoint_union_left.2 ⟨hXZ.mono_right sdiff_subset, disjoint_sdiff⟩
  have r2 := M.rule2 v hX'Z₁ (hYZ.mono_right sdiff_subset) (hWZ.mono_right sdiff_subset)
    (hsep1.deleteOutgoing (W := ↑(Z \ G.rule3Set X Z W)))
  have r1 := M.rule1 v hsep1
  rw [← union_rule3Set_union_sdiff] at r2
  have e := fun {S : Finset V} (hS : S ⊆ Y ∪ (Z \ G.rule3Set X Z W) ∪ W) =>
    M.margAt_intervene_union_rule3Set_of_subset v hXZ hsep hS
  rw [e (union_subset (subset_union_right.trans subset_union_left) subset_union_right)] at r2 r1
  rw [e (union_subset (subset_union_left.trans subset_union_left) subset_union_right),
    e subset_union_right] at r1
  refine mul_right_cancel₀ hpos.ne' ?_
  linear_combination (M.intervene X v).dist.margAt W v * r2 +
    (M.intervene (X ∪ Z) v).dist.margAt W v * r1

/-- **Rule 3 of do-calculus**, ratio form: under the hypotheses of `SCM.rule3`,
`P(y | do(x), do(z), w) = P(y | do(x), w)`. Both denominators are positive. -/
theorem rule3_div {X Y Z W : Finset V} (v : ∀ u, α u) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hWZ : Disjoint W Z)
    (hsep : (G.deleteIncoming ↑(X ∪ G.rule3Set X Z W)).DSep ↑Y ↑Z ↑(X ∪ W))
    (hpos : 0 < (M.intervene X v).dist.margAt ((Z \ G.rule3Set X Z W) ∪ W) v) :
    (M.intervene (X ∪ Z) v).dist.margAt (Y ∪ W) v / (M.intervene (X ∪ Z) v).dist.margAt W v =
      (M.intervene X v).dist.margAt (Y ∪ W) v / (M.intervene X v).dist.margAt W v := by
  have hq := M.rule3_pos v hXZ hWZ hsep hpos
  have hp : 0 < (M.intervene X v).dist.margAt W v :=
    hpos.trans_le ((M.intervene X v).dist.margAt_anti subset_union_right v)
  rw [div_eq_div_iff hq.ne' hp.ne']
  exact M.rule3 v hXZ hYZ hWZ hsep hpos

end SCM

end CausalInference
