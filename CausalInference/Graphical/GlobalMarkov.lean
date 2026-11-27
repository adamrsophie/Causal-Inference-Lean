/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.LocalMarkov
public import CausalInference.Graphical.DSeparationDecide

/-!
# The global Markov property

Soundness of d-separation: a finite distribution that factorizes according to an acyclic graph
satisfies every conditional independence read off the graph by d-separation. Consequently
factorization, the local Markov property and the global Markov property are equivalent.

## Main definitions

* `Digraph.GlobalMarkov G p`: for all finsets `X`, `Y`, `Z` of vertices, `G.DSep X Y Z` implies
  `p.CondIndep X Y Z`.

## Main results

* `Digraph.DSep.reach_family`: the graph lemma behind the proof. On the ancestral closure of
  `X ∪ Y ∪ Z`, the set of vertices reached by the Bayes-ball search from `X` given `Z` never
  splits the family `{v} ∪ parents v` of a vertex; `Digraph.DSep.dConn_family` is the
  d-connection form, for family members outside `Z`.
* `Digraph.Factorizes.condIndep_of_dSep`: **d-separation implies conditional independence**, for
  arbitrary finsets and without any positivity assumption.
* `Digraph.factorizes_tfae`, `Digraph.factorizes_iff_globalMarkov`,
  `Digraph.localMarkov_iff_globalMarkov`: factorization, local and global Markov properties are
  equivalent for an acyclic graph.
* `CausalInference.GraphExamples.chain_condIndep`, `fork_condIndep`, `collider_condIndep`: the
  three-vertex patterns.
* `CausalInference.GraphExamples.exists_factorizes_condIndep_not_dSep`: the converse fails for a
  fixed distribution. The exclusive or of two fair bits factorizes along the collider
  `0 → 2 ← 1`, and `0` is independent of `2` although they are adjacent.

## Proof

Let `A` be the ancestral closure of `X ∪ Y ∪ Z` (with `X`, `Y` disjoint from `Z`). Its marginal is
the product of the kernels of the vertices of `A` (`MarkovKernels.margAt_of_ancestral`). Let `S`
be the vertices of `A \ Z` reached from `X` by an active trail given `Z`, and `T` the rest of
`A \ Z`; then `X ⊆ S` and, by d-separation, `Y ⊆ T`. By `DSep.reach_family` each kernel factor
depends only on the coordinates in `S ∪ Z` or only on those in `T ∪ Z`, so the factorization
criterion gives `S ⫫ T | Z`, hence `X ⫫ Y | Z`. This is the moral graph argument of Lauritzen
(1996) with the moral graph replaced by Bayes-ball reachability.

## References

* T. Verma and J. Pearl (1988), *Causal networks: semantics and expressiveness*.
* S. L. Lauritzen, A. P. Dawid, B. N. Larsen, H.-G. Leimer (1990), *Independence properties of
  directed Markov fields*.
* S. L. Lauritzen (1996), *Graphical Models*, chapter 3.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, sections 1.2
  and 2.4.
-/

@[expose] public section

namespace Digraph

open Relation

/-! ### The graph side: reachability is closed under families -/

section Graph

variable {V : Type*} {G : Digraph V} {X Y Z : Set V}

/-- A directed path `v → ⋯ → t` whose first vertex is not an ancestor of `Z`, read backwards from
`t`, is an active trail given `Z` that always moves against the edges (arrival flag `false`). -/
theorem reflTransGen_bayesBall_of_reflTransGen_rev {v t : V} (h : ReflTransGen G.Adj v t)
    (hv : v ∉ G.ancestorsOf Z) : ReflTransGen (G.bayesBall Z).Adj (t, false) (v, false) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | @head v v₁ hvv₁ _ ih =>
    have hv₁ : v₁ ∉ G.ancestorsOf Z := fun h => hv (mem_ancestorsOf_of_adj hvv₁ h)
    exact (ih hv₁).tail
      (bayesBall_adj_false_false.2 ⟨hvv₁, fun h => hv₁ (subset_ancestorsOf Z h)⟩)

/-- **Families are not split by d-separation.** Suppose `X` is disjoint from `Z`, `X` and `Y` are
d-separated by `Z`, the vertex `v` lies in the ancestral closure of `X ∪ Y ∪ Z`, and `u` and `w`
are members of the family `{v} ∪ parents v` with `u ∉ Z`. If the Bayes-ball search from `X`
given `Z` arrives at `u` (in some arrival state), then it also arrives at `w`. The conclusion is
reachability of a Bayes-ball state, not d-connection: `w` may lie in `Z`, and then it is not the
endpoint of an active trail. `Digraph.DSep.dConn_family` is the d-connection form for `w ∉ Z`. -/
theorem DSep.reach_family (hsep : G.DSep X Y Z) (hXZ : ∀ x ∈ X, x ∉ Z) {v u w : V}
    (hvA : v ∈ G.ancestorsOf (X ∪ Y ∪ Z)) (hu : u = v ∨ G.Adj u v) (hw : w = v ∨ G.Adj w v)
    (huZ : u ∉ Z) {x : V} (hx : x ∈ X) {b : Bool}
    (hxu : ReflTransGen (G.bayesBall Z).Adj (x, false) (u, b)) :
    ∃ x ∈ X, ∃ c, ReflTransGen (G.bayesBall Z).Adj (x, false) (w, c) := by
  have hreach : ∃ d, ReflTransGen (G.bayesBall Z).Adj (x, false) (v, d) ∧
      (d = false → v ∉ Z) := by
    rcases hu with rfl | huv
    · exact ⟨b, hxu, fun _ => huZ⟩
    · exact ⟨true, hxu.tail (bayesBall_adj_true.2 ⟨huv, huZ⟩), fun h => absurd h (by simp)⟩
  obtain ⟨d, hxv, hd⟩ := hreach
  rcases hw with rfl | hwv
  · exact ⟨x, hx, d, hxv⟩
  by_cases hvZ : v ∈ G.ancestorsOf Z
  · refine ⟨x, hx, false, hxv.tail ?_⟩
    cases d
    · exact bayesBall_adj_false_false.2 ⟨hwv, hd rfl⟩
    · exact bayesBall_adj_true_false.2 ⟨hwv, hvZ⟩
  · obtain ⟨s, hs, hvs⟩ := hvA
    rcases hs with (hsX | hsY) | hsZ
    · exact ⟨s, hsX, false, (reflTransGen_bayesBall_of_reflTransGen_rev hvs hvZ).tail
        (bayesBall_adj_false_false.2 ⟨hwv, fun h => hvZ (subset_ancestorsOf Z h)⟩)⟩
    · exfalso
      obtain ⟨c, hc⟩ := exists_reflTransGen_bayesBall_of_reflTransGen hvs hvZ d
      exact hsep ⟨x, hx, s, hsY, hXZ x hx, fun h => hvZ ⟨s, h, hvs⟩, c, hxv.trans hc⟩
    · exact absurd ⟨s, hsZ, hvs⟩ hvZ

/-- The d-connection form of `Digraph.DSep.reach_family`: under the same hypotheses, if moreover
`w ∉ Z`, then `X` and `{w}` are d-connected given `Z`. -/
theorem DSep.dConn_family (hsep : G.DSep X Y Z) (hXZ : ∀ x ∈ X, x ∉ Z) {v u w : V}
    (hvA : v ∈ G.ancestorsOf (X ∪ Y ∪ Z)) (hu : u = v ∨ G.Adj u v) (hw : w = v ∨ G.Adj w v)
    (huZ : u ∉ Z) (hwZ : w ∉ Z) {x : V} (hx : x ∈ X) {b : Bool}
    (hxu : ReflTransGen (G.bayesBall Z).Adj (x, false) (u, b)) : G.DConn X {w} Z := by
  obtain ⟨x', hx', c, h⟩ := hsep.reach_family hXZ hvA hu hw huZ hx hxu
  exact ⟨x', hx', w, Set.mem_singleton w, hXZ x' hx', hwZ, c, h⟩

end Graph

/-! ### Soundness of d-separation -/

section Soundness

open CausalInference Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] {G : Digraph V} [DecidableRel G.Adj]

/-- **d-separation implies conditional independence**, for sets disjoint from the conditioning
set. Let `A` be the ancestral closure of `X ∪ Y ∪ Z`, let `S` be the vertices of `A \ Z` reached
from `X` by an active trail given `Z`, and `T = (A \ Z) \ S`. By `DSep.reach_family`, the family
of each vertex of `A` meets at most one of `S` and `T`, so the product of the kernels over `A`
(the marginal on `A`) splits into a factor depending on `S ∪ Z` and one depending on `T ∪ Z`. -/
theorem MarkovKernels.condIndep_of_dSep_of_disjoint (k : G.MarkovKernels α) (hG : G.IsAcyclic)
    {p : FiniteDist (∀ v, α v)} (hp : ∀ x, p x = ∏ v, k.factor v x) {X Y Z : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hsep : G.DSep ↑X ↑Y ↑Z) :
    p.CondIndep X Y Z := by
  classical
  set A : Finset V := univ.filter (fun v => v ∈ G.ancestorsOf (↑X ∪ ↑Y ∪ ↑Z : Set V))
  have hmemA : ∀ v, v ∈ A ↔ v ∈ G.ancestorsOf (↑X ∪ ↑Y ∪ ↑Z : Set V) := fun v => by simp [A]
  have hA : ∀ v ∈ A, ∀ u, G.Adj u v → u ∈ A := fun v hv u huv =>
    (hmemA u).2 (mem_ancestorsOf_of_adj huv ((hmemA v).1 hv))
  have hfamA : ∀ v ∈ A, ∀ u, (u = v ∨ G.Adj u v) → u ∈ A := by
    rintro v hv u (rfl | huv)
    · exact hv
    · exact hA v hv u huv
  have hXZ' : ∀ x ∈ (↑X : Set V), x ∉ (↑Z : Set V) := fun x hx hxZ =>
    disjoint_left.1 hXZ (mem_coe.1 hx) (mem_coe.1 hxZ)
  set S : Finset V := A.filter (fun u => u ∉ Z ∧
    ∃ x ∈ X, ∃ b, ReflTransGen (G.bayesBall ↑Z).Adj (x, false) (u, b))
  set T : Finset V := (A \ Z) \ S
  have hXS : X ⊆ S := fun x hx => mem_filter.2 ⟨(hmemA x).2 (subset_ancestorsOf _
    (Or.inl (Or.inl (mem_coe.2 hx)))), disjoint_left.1 hXZ hx, x, hx, false, ReflTransGen.refl⟩
  have hYT : Y ⊆ T := by
    intro y hy
    have hyZ : y ∉ Z := disjoint_left.1 hYZ hy
    refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨(hmemA y).2 (subset_ancestorsOf _
      (Or.inl (Or.inr (mem_coe.2 hy)))), hyZ⟩, fun hyS => ?_⟩
    obtain ⟨-, -, x, hx, b, hxy⟩ := mem_filter.1 hyS
    exact hsep ⟨x, hx, y, hy, disjoint_left.1 hXZ hx, hyZ, b, hxy⟩
  have hST : Disjoint S T := disjoint_left.2 fun u huS huT => (mem_sdiff.1 huT).2 huS
  have hSZ : Disjoint S Z := disjoint_left.2 fun u huS => (mem_filter.1 huS).2.1
  have hTZ : Disjoint T Z := disjoint_left.2 fun u huT => (mem_sdiff.1 (mem_sdiff.1 huT).1).2
  have hAeq : S ∪ T ∪ Z = A := by
    ext u
    by_cases huS : u ∈ S
    · simp [huS, (mem_filter.1 huS).1]
    · by_cases huZ : u ∈ Z
      · simp [huZ, (hmemA u).2 (subset_ancestorsOf _ (Or.inr (mem_coe.2 huZ)))]
      · simp [T, huS, huZ]
  -- the closure property of `S` along families
  have hclos : ∀ v ∈ A, ∀ u w, (u = v ∨ G.Adj u v) → (w = v ∨ G.Adj w v) → u ∈ S → w ∉ Z →
      w ∈ S := by
    intro v hv u w hu hw huS hwZ
    obtain ⟨-, huZ, x, hx, b, hxu⟩ := mem_filter.1 huS
    obtain ⟨x', hx', c, hx'w⟩ := hsep.reach_family hXZ' ((hmemA v).1 hv) hu hw
      (fun h => huZ (mem_coe.1 h)) (mem_coe.2 hx) hxu
    exact mem_filter.2 ⟨hfamA v hv w hw, hwZ, x', hx', c, hx'w⟩
  set P : V → Prop := fun v => ∀ u, (u = v ∨ G.Adj u v) → u ∈ S ∪ Z
  refine ((FiniteDist.condIndep_of_margAt_eq_mul (by simp [disjoint_iff_inter_eq_empty.1 hST])
    (fun x => ∏ v ∈ A.filter P, k.factor v x)
    (fun x => ∏ v ∈ A.filter (fun v => ¬ P v), k.factor v x) ?_ ?_ ?_).mono_left hXS).mono_right
    hYT
  · intro x x' hxx'
    refine prod_congr rfl fun v hv => k.factor_congr fun u hu => hxx' u ?_
    exact (mem_filter.1 hv).2 u hu
  · intro x x' hxx'
    refine prod_congr rfl fun v hv => k.factor_congr fun w hw => hxx' w ?_
    obtain ⟨hvA, hnP⟩ := mem_filter.1 hv
    simp only [P, not_forall] at hnP
    obtain ⟨u, hu, huSZ⟩ := hnP
    rw [mem_union] at huSZ ⊢
    push Not at huSZ
    by_cases hwZ : w ∈ Z
    · exact Or.inr hwZ
    · refine Or.inl (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hfamA v hvA w hw, hwZ⟩, fun hwS => ?_⟩)
      exact huSZ.1 (hclos v hvA w u hw hu hwS huSZ.2)
  · intro x
    rw [hAeq, k.margAt_of_ancestral hG hp hA, MarkovKernels.prodOn,
      prod_filter_mul_prod_filter_not]

/-- **Soundness of d-separation** (the directed global Markov property). If `p` factorizes
according to an acyclic graph `G` and `X` and `Y` are d-separated by `Z` in `G`, then the
coordinates in `X` and those in `Y` are conditionally independent given those in `Z`. The sets are
arbitrary finsets: coordinates in `Z` are irrelevant on both sides (`Digraph.dSep_diff_iff`,
`FiniteDist.condIndep_sdiff_iff`). No positivity is assumed. -/
theorem Factorizes.condIndep_of_dSep (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)}
    (h : G.Factorizes p) {X Y Z : Finset V} (hsep : G.DSep ↑X ↑Y ↑Z) : p.CondIndep X Y Z := by
  obtain ⟨k, hk⟩ := h
  rw [← FiniteDist.condIndep_sdiff_iff]
  rw [← dSep_diff_iff, ← coe_sdiff, ← coe_sdiff] at hsep
  exact k.condIndep_of_dSep_of_disjoint hG hk sdiff_disjoint sdiff_disjoint hsep

variable (G) in
/-- The directed global Markov property of `p` with respect to `G`: whenever `X` and `Y` are
d-separated by `Z` in `G`, the coordinates in `X` and `Y` are conditionally independent given
those in `Z`. -/
def GlobalMarkov (p : FiniteDist (∀ v, α v)) : Prop :=
  ∀ X Y Z : Finset V, G.DSep ↑X ↑Y ↑Z → p.CondIndep X Y Z

/-- Factorization implies the global Markov property. -/
theorem Factorizes.globalMarkov (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)}
    (h : G.Factorizes p) : G.GlobalMarkov p :=
  fun _ _ _ hsep => h.condIndep_of_dSep hG hsep

/-- The global Markov property implies the local one: the local statements are the instances
given by `Digraph.IsAcyclic.dSep_nondescendants_parents`. -/
theorem GlobalMarkov.localMarkov (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)}
    (h : G.GlobalMarkov p) : G.LocalMarkov p := by
  intro v
  refine h _ _ _ ?_
  rw [coe_singleton, coe_parentsFinset]
  refine DSep.mono_right ?_ (hG.dSep_nondescendants_parents v)
  intro u hu hdesc
  obtain ⟨hND, -⟩ := mem_sdiff.1 (mem_coe.1 hu)
  obtain ⟨huv, hanc⟩ := mem_nondescendantsFinset.1 hND
  obtain ⟨s, hs, hsu⟩ := hdesc
  rw [Set.mem_singleton_iff] at hs
  subst hs
  rcases hsu.cases_head with rfl | ⟨c, hsc, hcu⟩
  · exact huv rfl
  · exact hanc (TransGen.head' hsc hcu)

/-- **Factorization, the local and the global Markov property are equivalent** for a finite
distribution and an acyclic graph (Lauritzen 1996, Theorem 3.27, in the finite discrete case). -/
theorem factorizes_tfae (hG : G.IsAcyclic) (p : FiniteDist (∀ v, α v)) :
    List.TFAE [G.Factorizes p, G.LocalMarkov p, G.GlobalMarkov p] := by
  tfae_have 1 → 3 := Factorizes.globalMarkov hG
  tfae_have 3 → 2 := GlobalMarkov.localMarkov hG
  tfae_have 2 → 1 := LocalMarkov.factorizes hG
  tfae_finish

/-- For an acyclic graph, factorization is equivalent to the global Markov property. -/
theorem factorizes_iff_globalMarkov (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)} :
    G.Factorizes p ↔ G.GlobalMarkov p :=
  (factorizes_tfae hG p).out 1 3

/-- For an acyclic graph, the local and the global Markov properties are equivalent. -/
theorem localMarkov_iff_globalMarkov (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)} :
    G.LocalMarkov p ↔ G.GlobalMarkov p :=
  (factorizes_tfae hG p).out 2 3

end Soundness

end Digraph

/-! ### Three-vertex patterns -/

namespace CausalInference.GraphExamples

open Digraph Finset

variable {α : Fin 3 → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  {p : FiniteDist (∀ v, α v)}

/-- In a distribution factorizing along the chain `0 → 1 → 2`, the ends are conditionally
independent given the middle vertex. -/
theorem chain_condIndep (h : chain.Factorizes p) : p.CondIndep {0} {2} {1} :=
  h.condIndep_of_dSep (by decide) (by simp only [coe_singleton]; decide)

/-- In a distribution factorizing along the fork `1 ← 0 → 2`, the two effects are conditionally
independent given the common cause. -/
theorem fork_condIndep (h : fork.Factorizes p) : p.CondIndep {1} {2} {0} :=
  h.condIndep_of_dSep (by decide) (by simp only [coe_singleton]; decide)

/-- In a distribution factorizing along the collider `0 → 2 ← 1`, the two causes are
marginally independent. -/
theorem collider_condIndep (h : collider.Factorizes p) : p.CondIndep {0} {1} ∅ :=
  h.condIndep_of_dSep (by decide) (by simp only [coe_singleton, coe_empty]; decide)

/-! ### An unfaithful distribution: the exclusive or -/

/-- A parent of the collider vertex `2` in `0 → 2 ← 1`. -/
def colliderParent (i : Fin 3) (hi : i ≠ 2) (v : Fin 3) (hv : v = 2) :
    collider.parentsFinset v :=
  ⟨i, mem_parentsFinset.2 ⟨hi, hv⟩⟩

/-- Kernels for the collider `0 → 2 ← 1` over `Bool`: vertices `0` and `1` are fair bits and
vertex `2` is their exclusive or. -/
noncomputable def xorKernels : collider.MarkovKernels (fun _ : Fin 3 => Bool) where
  kernel v z a := if h : v = 2 then
      (if a = xor (z (colliderParent 0 (by decide) v h)) (z (colliderParent 1 (by decide) v h))
        then 1 else 0)
    else 1 / 2
  nonneg v z a := by split_ifs <;> norm_num
  sum_eq_one v z := by
    by_cases h : v = 2
    · simp [h]
    · simp only [h, dite_false, Fintype.sum_bool]
      norm_num

/-- The exclusive-or distribution: two fair bits and their exclusive or. -/
noncomputable def xorDist : FiniteDist (Fin 3 → Bool) := xorKernels.jointDist (by decide)

/-- The exclusive-or distribution factorizes according to the collider `0 → 2 ← 1`. -/
theorem xorDist_factorizes : collider.Factorizes xorDist :=
  xorKernels.factorizes_jointDist _

theorem xorKernels_factor_of_ne {v : Fin 3} (hv : v ≠ 2) (y : Fin 3 → Bool) :
    xorKernels.factor v y = 1 / 2 := by
  simp [MarkovKernels.factor, xorKernels, hv]

theorem xorKernels_factor_two (y : Fin 3 → Bool) :
    xorKernels.factor 2 y = if y 2 = xor (y 0) (y 1) then 1 else 0 := by
  simp only [MarkovKernels.factor, xorKernels, colliderParent, Finset.restrict, dite_true]
  exact if_congr Iff.rfl rfl rfl

theorem xorDist_apply (y : Fin 3 → Bool) :
    xorDist y = if y 2 = xor (y 0) (y 1) then 1 / 4 else 0 := by
  change ∏ v, xorKernels.factor v y = _
  rw [Fin.prod_univ_three, xorKernels_factor_of_ne (by decide),
    xorKernels_factor_of_ne (by decide), xorKernels_factor_two]
  split_ifs <;> norm_num

/-- In the exclusive-or distribution, the cause `0` and the effect `2` are independent, although
they are adjacent in the graph. -/
theorem xorDist_condIndep : xorDist.CondIndep {0} {2} ∅ := by
  refine FiniteDist.condIndep_of_margAt_eq_mul (by decide)
    (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun x => ?_
  rw [xorDist.margAt_eq_sum_margAt (subset_univ _),
    show (univ \ ({0} ∪ {2} ∪ ∅) : Finset (Fin 3)) = {1} by decide,
    FiniteDist.sum_agreeOn_compl_singleton, Fintype.sum_bool]
  simp only [FiniteDist.margAt_univ, xorDist_apply, Function.update_self,
    Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)]
  cases x 0 <;> cases x 2 <;> norm_num

/-- The effect `2` and the cause `0` are adjacent, hence d-connected given `∅`. -/
theorem collider_not_dSep_zero_two : ¬ collider.DSep ↑({0} : Finset (Fin 3))
    ↑({2} : Finset (Fin 3)) ↑(∅ : Finset (Fin 3)) := by
  simp only [coe_singleton, coe_empty]
  decide

/-- **The converse of soundness fails.** There is a distribution factorizing according to an
acyclic graph with a conditional independence that is not a d-separation: the exclusive-or
distribution over the collider `0 → 2 ← 1` (an unfaithful distribution; Pearl 2009, section 2.4).
So for a fixed distribution, conditional independence does not imply d-separation. -/
theorem exists_factorizes_condIndep_not_dSep :
    ∃ (p : FiniteDist (Fin 3 → Bool)) (X Y Z : Finset (Fin 3)), collider.Factorizes p ∧
      p.CondIndep X Y Z ∧ ¬ collider.DSep ↑X ↑Y ↑Z :=
  ⟨xorDist, {0}, {2}, ∅, xorDist_factorizes, xorDist_condIndep, collider_not_dSep_zero_two⟩

end CausalInference.GraphExamples
