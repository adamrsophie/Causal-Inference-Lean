/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Criteria.BackDoor
public import CausalInference.Graphical.Criteria.Moralization
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The sequential back-door criterion (graph side)

A plan sets the control variables `x 0, …, x (n - 1)` in this order; the outcome is `y`.
Covariates must be chosen among a finite set `C` of observed vertices, which is an explicit
parameter: without it, latent vertices could be conditioned on and the claims of
nonexistence in Pearl's examples would change.

## Main definitions

* `Digraph.stepGraph G x k`: the graph `G` with the edges out of `x k` and the edges into the
  later controls `x j`, `j > k`, removed; Pearl writes it with a bar under `X_k` and bars over
  `X_{k+1}, …, X_n`.
* `Digraph.SeqBackDoorStep G x y Zs k`: the d-separation test (4.5) of step `k`: `y` and `x k`
  are d-separated in `G.stepGraph x k` by the earlier controls together with `Zs 0, …, Zs k`.
* `Digraph.Admissible G C x y Zs`: the raw step tests of Definition 4.4.2: for every `k`,
  `Zs k` consists of observed covariates (members of `C`) that are nondescendants of every
  control `x j` with `j ≥ k` (condition (4.4)), and the test (4.5) holds.
* `Digraph.GIdentifiable G C x y`: some sequence passes the raw step tests.
* `Digraph.PlanRoles G C x y`: the standing assumptions of a control problem (section 4.4.2):
  the controls are listed in an order compatible with `G` (hence distinct), the controls, the
  covariates, and the outcome are disjoint, and the outcome is a descendant of the last control.
* `Digraph.AdmissiblePlan`, `Digraph.GIdentifiablePlan`: Pearl's admissible sequence and
  G-identifiability (Definition 4.4.2, Corollary 4.4.3): the raw tests within `PlanRoles`.
  Pearl's control problems are also acyclic; acyclicity is a hypothesis of the theorems that
  need it.
* `Digraph.wSet G C x y k`: the explicit covariate set `W_k` of Theorem 4.4.6: the members of
  `C` that are nondescendants of the controls `x j`, `j ≥ k`, and ancestors of `y` or `x k` in
  `G.stepGraph x k`.

## Main results

* `Digraph.admissible_wSet`: if the sets `W_k` pass the tests (4.5), they form an admissible
  sequence, so the plan is G-identifiable. This is the "if" direction of Theorem 4.4.6.
* `Digraph.seqBackDoorStep_wSet_of_admissible`, `Digraph.gIdentifiable_iff_wSet`,
  `Digraph.gIdentifiablePlan_iff_wSet`: the "only if" direction of Theorem 4.4.6 (whose proof
  Pearl defers to Pearl and Robins 1995): in an acyclic graph with the controls listed in an
  order compatible with the graph and outside the covariates, if some sequence passes the step
  tests then the sets `W_k` pass them. `Digraph.decidableGIdentifiablePlan`: the resulting
  decision procedure for G-identifiability of a plan in an acyclic graph.
* Decidability of each step test and of admissibility, and the examples of Figures 4.4, 4.6,
  4.7 and 4.8 checked by `decide`.
* Countermodels showing that the raw tests accept plans outside Pearl's setting: controls listed
  against the order of `G` (`controlsAgainstOrder`, `reversedChain`) and a repeated control
  (`repeatedControl`).

## Proof of the converse of Theorem 4.4.6

The argument is step by step; no induction over the steps is needed. Fix a step `k` and write
`H` for its graph. By the moral-graph criterion (`Digraph.dSep_iff_moralSep`), the test of step
`k` with the conditioning set `Z` of an admissible sequence is a separation in the moral graph
of the ancestral set of `{y, x k} ∪ Z` in `H`. Replacing `Z` by the conditioning set `Z'` built
from the sets `W_j` keeps the separation (`Digraph.MoralSep.of_subset`) as long as the new
ancestral set is contained in the old one and every vertex of `Z` in the new ancestral set lies
in `Z'`. Both hold: a set `W_j` with `j < k` consists of ancestors of `y` or of `x j` in `H`
(`Digraph.reflTransGen_of_mem_wSet_of_lt`), and a covariate that is an ancestor in `H` of `y`
or of `x k` is in `W_k`, while one that is an ancestor of an earlier control `x i` is in `W_i`
(`Digraph.mem_wSet_of_reflTransGen`, which uses acyclicity and the order of the controls).

## Notes on the source

The printed formula (4.5) is garbled in the extract; the reading used here,
`(Y ⫫ X_k | X_1, …, X_{k-1}, Z_1, …, Z_k)` in `G` with the arrows out of `X_k` and into
`X_{k+1}, …, X_n` deleted, is re-derived from the two tests that the text spells out for
Figure 4.4. The graphs of Figures 4.4, 4.7 and 4.8 follow the printed drawings. Figure 4.4
contains the edge `X₁ → U₂`. The text describes Figure 4.8 as Figure 4.4 without `X₁ → X₂` and
`X₁ → Z`; the printed drawing of Figure 4.8 also lacks `X₁ → U₂`, and the graph here follows
the drawing. For Figure 4.6 the example is a graph with the properties the text states.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 4.4:
  Theorem 4.4.1, Definition 4.4.2, Corollary 4.4.3, Theorem 4.4.6 and Figures 4.4 to 4.8.
* J. Pearl and J. M. Robins (1995), *Probabilistic evaluation of sequential plans from causal
  models with hidden variables*.
-/

@[expose] public section

namespace Digraph

variable {V : Type*} {n : ℕ}

/-- The controls `x j` with `j ≥ k`. -/
def controlsFrom (x : Fin n → V) (k : Fin n) : Set V := {v | ∃ j, k ≤ j ∧ x j = v}

/-- The controls `x j` with `j > k`. -/
def controlsAfter (x : Fin n → V) (k : Fin n) : Set V := {v | ∃ j, k < j ∧ x j = v}

/-- The graph of step `k` of the sequential back-door test: the edges out of `x k` and the edges
into the later controls `x j`, `j > k`, are removed. -/
def stepGraph (G : Digraph V) (x : Fin n → V) (k : Fin n) : Digraph V :=
  (G.deleteOutgoing {x k}).deleteIncoming (controlsAfter x k)

/-- The conditioning set of step `k`: the earlier controls `x j`, `j < k`, and the covariates of
`Zs j` for `j ≤ k`. -/
def stepCond (x : Fin n → V) (Zs : Fin n → Finset V) (k : Fin n) : Set V :=
  {v | (∃ j, j < k ∧ x j = v) ∨ ∃ j, j ≤ k ∧ v ∈ Zs j}

/-- The d-separation test (4.5) of step `k` (Pearl 2009, Theorem 4.4.1): `y` and `x k` are
d-separated by the earlier controls and `Zs 0, …, Zs k` in `G.stepGraph x k`. -/
def SeqBackDoorStep (G : Digraph V) (x : Fin n → V) (y : V) (Zs : Fin n → Finset V)
    (k : Fin n) : Prop :=
  (G.stepGraph x k).DSep {y} {x k} (stepCond x Zs k)

/-- The raw step tests of an admissible sequence (Definition 4.4.2) relative to the observed
covariates `C`: for every step `k`, `Zs k` consists of members of `C` that are nondescendants
of every control `x j` with `j ≥ k` (condition (4.4)), and the step test (4.5) holds. This is
Pearl's notion only within the standing assumptions `PlanRoles` (see `AdmissiblePlan`); without
them it accepts controls listed against the order of `G` (the example `controlsAgainstOrder`). -/
def Admissible (G : Digraph V) (C : Finset V) (x : Fin n → V) (y : V)
    (Zs : Fin n → Finset V) : Prop :=
  ∀ k, (∀ v ∈ Zs k, v ∈ C ∧ v ∉ G.descendantsOf (controlsFrom x k)) ∧
    G.SeqBackDoorStep x y Zs k

/-- Some sequence of covariate sets passes the raw step tests `Admissible`. This is Pearl's
G-identifiability (Definition 4.4.2 and Corollary 4.4.3) only within the standing assumptions
`PlanRoles` (see `GIdentifiablePlan`). -/
def GIdentifiable (G : Digraph V) (C : Finset V) (x : Fin n → V) (y : V) : Prop :=
  ∃ Zs, G.Admissible C x y Zs

/-- The controls are listed in an order compatible with `G`: no control is a descendant of a
later one (Pearl's standing assumption in section 4.4.2). -/
def ControlsOrdered (G : Digraph V) (x : Fin n → V) : Prop :=
  ∀ i j, i < j → x i ∉ G.descendantsOf {x j}

/-- Controls listed in an order compatible with `G` are distinct, since descendants are
inclusive. -/
theorem ControlsOrdered.injective {G : Digraph V} {x : Fin n → V} (h : G.ControlsOrdered x) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h i j hlt ⟨x j, rfl, by rw [hij]⟩
  · exact h j i hlt ⟨x i, rfl, by rw [hij]⟩

/-- The standing assumptions of a control problem (Pearl 2009, section 4.4.2) for the controls
`x`, the observed covariates `C`, and the outcome `y`: the controls are listed in an order
compatible with `G` (which makes them distinct, `ControlsOrdered.injective`), no control is the
outcome or a covariate, the outcome is not a covariate, and the outcome is a descendant of the
last control. Pearl also assumes `G` acyclic; that is a separate hypothesis. -/
def PlanRoles (G : Digraph V) (C : Finset V) (x : Fin n → V) (y : V) : Prop :=
  G.ControlsOrdered x ∧ (∀ k, x k ≠ y) ∧ (∀ k, x k ∉ C) ∧ y ∉ C ∧
    ∀ k : Fin n, (k : ℕ) + 1 = n → y ∈ G.descendantsOf {x k}

/-- Pearl's admissible sequence (Definition 4.4.2): the raw step tests within the standing
assumptions of a control problem. -/
def AdmissiblePlan (G : Digraph V) (C : Finset V) (x : Fin n → V) (y : V)
    (Zs : Fin n → Finset V) : Prop :=
  G.PlanRoles C x y ∧ G.Admissible C x y Zs

/-- Pearl's G-identifiability (Definition 4.4.2 and Corollary 4.4.3): the plan satisfies the
standing assumptions and some sequence of covariate sets passes the raw step tests. -/
def GIdentifiablePlan (G : Digraph V) (C : Finset V) (x : Fin n → V) (y : V) : Prop :=
  G.PlanRoles C x y ∧ G.GIdentifiable C x y

/-! ### Path lemmas for the converse of Theorem 4.4.6 -/

open Relation in
/-- Transfer of separation in the ancestral moral graph: if `Z` separates `X` from `Y`, then so
does `Z'`, provided the ancestral closure of `X ∪ Y ∪ Z'` is contained in that of `X ∪ Y ∪ Z`
and every member of `Z` in the former closure belongs to `Z'`. -/
theorem MoralSep.of_subset {G : Digraph V} {X Y Z Z' : Set V} (h : G.MoralSep X Y Z)
    (hA : G.ancestorsOf (X ∪ Y ∪ Z') ⊆ G.ancestorsOf (X ∪ Y ∪ Z))
    (hZ : ∀ v ∈ G.ancestorsOf (X ∪ Y ∪ Z'), v ∈ Z → v ∈ Z') : G.MoralSep X Y Z' := by
  intro a ha b hb haZ hpath
  have hle : G.restrict (G.ancestorsOf (X ∪ Y ∪ Z')) ≤
      G.restrict (G.ancestorsOf (X ∪ Y ∪ Z)) := restrict_mono hA
  have haA : a ∈ G.ancestorsOf (X ∪ Y ∪ Z') := subset_ancestorsOf _ (Or.inl (Or.inl ha))
  refine h a ha b hb (fun h' => haZ (hZ a haA h'))
    (ReflTransGen.mono (fun u w huw => ?_) _ _ hpath)
  obtain ⟨huw, huZ, hwZ⟩ := huw
  rw [moralGraph_adj] at huw
  obtain ⟨hne, h1⟩ := huw
  have hmem : u ∈ G.ancestorsOf (X ∪ Y ∪ Z') ∧ w ∈ G.ancestorsOf (X ∪ Y ∪ Z') := by
    rcases h1 with (h1 | ⟨c, h1, h2⟩) | (h1 | ⟨c, h1, h2⟩)
    · exact ⟨h1.2.1, h1.2.2⟩
    · exact ⟨h1.2.1, h2.2.1⟩
    · exact ⟨h1.2.2, h1.2.1⟩
    · exact ⟨h2.2.1, h1.2.1⟩
  refine ⟨?_, fun h' => huZ (hZ u hmem.1 h'), fun h' => hwZ (hZ w hmem.2 h')⟩
  rw [moralGraph_adj]
  refine ⟨hne, ?_⟩
  rcases h1 with (h1 | ⟨c, h1, h2⟩) | (h1 | ⟨c, h1, h2⟩)
  · exact Or.inl (Or.inl (hle h1))
  · exact Or.inl (Or.inr ⟨c, hle h1, hle h2⟩)
  · exact Or.inr (Or.inl (hle h1))
  · exact Or.inr (Or.inr ⟨c, hle h1, hle h2⟩)

section Converse

open Relation

variable {G : Digraph V} {x : Fin n → V}

/-- The graph of a step is a subgraph of `G`. -/
theorem stepGraph_le (k : Fin n) : G.stepGraph x k ≤ G :=
  fun _ _ h => h.1.1

/-- Later steps have fewer controls from them on. -/
theorem controlsFrom_anti {j k : Fin n} (h : j ≤ k) : controlsFrom x k ⊆ controlsFrom x j :=
  fun _ ⟨m, hm, e⟩ => ⟨m, h.trans hm, e⟩

/-- A directed path of the graph of step `j` that starts outside the controls after `j` is a
directed path of the graph of every later step `k`. -/
theorem ReflTransGen.stepGraph_of_lt {j k : Fin n} (hjk : j < k) {a t : V}
    (h : ReflTransGen (G.stepGraph x j).Adj a t) (ha : a ∉ controlsAfter x j) :
    ReflTransGen (G.stepGraph x k).Adj a t := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hab _ ih =>
    refine .head ⟨⟨hab.1.1, fun hax => ha ⟨k, hjk, (Set.mem_singleton_iff.1 hax).symm⟩⟩,
      fun hb => hab.2 ?_⟩ (ih hab.2)
    obtain ⟨m, hm, e⟩ := hb
    exact ⟨m, hjk.trans hm, e⟩

/-- In an acyclic graph with the controls listed in an order compatible with it, a directed
path of `G` that ends at the control `x i` is a directed path of the graph of step `i`. -/
theorem reflTransGen_stepGraph_of_reflTransGen (hG : G.IsAcyclic) (hord : G.ControlsOrdered x)
    {i : Fin n} {a : V} (h : ReflTransGen G.Adj a (x i)) :
    ReflTransGen (G.stepGraph x i).Adj a (x i) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hab hb ih =>
    refine .head ⟨⟨hab, fun hax => ?_⟩, fun hbc => ?_⟩ ih
    · rw [Set.mem_singleton_iff] at hax
      subst hax
      exact hG _ (TransGen.head' hab hb)
    · obtain ⟨m, hm, rfl⟩ := hbc
      exact hord i m hm ⟨x m, rfl, hb⟩

/-- In an acyclic graph with ordered controls, a vertex other than the controls that is an
ancestor of the control `x i` is not a descendant of any control `x m` with `m ≥ i`. -/
theorem notMem_descendantsOf_controlsFrom (hG : G.IsAcyclic) (hord : G.ControlsOrdered x)
    {i : Fin n} {v : V} (hv : ReflTransGen G.Adj v (x i)) (hvx : ∀ m, x m ≠ v) :
    v ∉ G.descendantsOf (controlsFrom x i) := by
  rintro ⟨s, ⟨m, hm, rfl⟩, hs⟩
  rcases hm.lt_or_eq with hlt | rfl
  · exact hord i m hlt ⟨x m, rfl, hs.trans hv⟩
  · rcases reflTransGen_iff_eq_or_transGen.1 hs with h | h
    · exact hvx _ h.symm
    · exact hG _ (h.trans_left hv)

end Converse

section Decidable

instance decidableMemControlsFrom [DecidableEq V] (x : Fin n → V) (k : Fin n) :
    DecidablePred (· ∈ controlsFrom x k) :=
  fun v => inferInstanceAs (Decidable (∃ j, k ≤ j ∧ x j = v))

instance decidableMemControlsAfter [DecidableEq V] (x : Fin n → V) (k : Fin n) :
    DecidablePred (· ∈ controlsAfter x k) :=
  fun v => inferInstanceAs (Decidable (∃ j, k < j ∧ x j = v))

instance decidableMemStepCond [DecidableEq V] (x : Fin n → V) (Zs : Fin n → Finset V)
    (k : Fin n) : DecidablePred (· ∈ stepCond x Zs k) :=
  fun v => inferInstanceAs (Decidable ((∃ j, j < k ∧ x j = v) ∨ ∃ j, j ≤ k ∧ v ∈ Zs j))

variable (G : Digraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance decidableRelStepGraph (x : Fin n → V) (k : Fin n) :
    DecidableRel (G.stepGraph x k).Adj :=
  inferInstanceAs (DecidableRel ((G.deleteOutgoing {x k}).deleteIncoming _).Adj)

instance decidableSeqBackDoorStep (x : Fin n → V) (y : V) (Zs : Fin n → Finset V)
    (k : Fin n) : Decidable (G.SeqBackDoorStep x y Zs k) :=
  inferInstanceAs (Decidable ((G.stepGraph x k).DSep {y} {x k} (stepCond x Zs k)))

instance decidableAdmissible (C : Finset V) (x : Fin n → V) (y : V) (Zs : Fin n → Finset V) :
    Decidable (G.Admissible C x y Zs) := by
  unfold Admissible
  infer_instance

instance decidableControlsOrdered (x : Fin n → V) : Decidable (G.ControlsOrdered x) := by
  unfold ControlsOrdered
  infer_instance

instance decidablePlanRoles (C : Finset V) (x : Fin n → V) (y : V) :
    Decidable (G.PlanRoles C x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance decidableAdmissiblePlan (C : Finset V) (x : Fin n → V) (y : V)
    (Zs : Fin n → Finset V) : Decidable (G.AdmissiblePlan C x y Zs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The covariate set `W_k` of Theorem 4.4.6: the members of `C` that are nondescendants of the
controls `x j`, `j ≥ k`, and that have `y` or `x k` as a descendant in `G.stepGraph x k`. -/
def wSet (C : Finset V) (x : Fin n → V) (y : V) (k : Fin n) : Finset V :=
  C.filter fun v => v ∉ G.descendantsOf (controlsFrom x k) ∧
    v ∈ (G.stepGraph x k).ancestorsOf {y, x k}


variable {G}

/-- The "if" direction of Theorem 4.4.6 (Pearl 2009): if the explicit sets `W_k` pass the
tests (4.5), they form an admissible sequence, so the plan is G-identifiable. -/
theorem admissible_wSet {C : Finset V} {x : Fin n → V} {y : V}
    (h : ∀ k, G.SeqBackDoorStep x y (G.wSet C x y) k) : G.Admissible C x y (G.wSet C x y) :=
  fun k => ⟨fun v hv => by
    simp only [wSet, Finset.mem_filter] at hv
    exact ⟨hv.1, hv.2.1⟩, h k⟩

theorem gIdentifiable_of_wSet {C : Finset V} {x : Fin n → V} {y : V}
    (h : ∀ k, G.SeqBackDoorStep x y (G.wSet C x y) k) : G.GIdentifiable C x y :=
  ⟨_, admissible_wSet h⟩

section Converse

open Relation

variable {C : Finset V} {x : Fin n → V} {y : V}

/-- A covariate that is an ancestor in `G` of the control `x i` belongs to `W_i`, in an acyclic
graph with ordered controls that are not covariates. -/
theorem mem_wSet_of_reflTransGen (hG : G.IsAcyclic) (hord : G.ControlsOrdered x)
    (hC : ∀ k, x k ∉ C) {i : Fin n} {v : V} (hvC : v ∈ C) (hv : ReflTransGen G.Adj v (x i)) :
    v ∈ G.wSet C x y i := by
  simp only [wSet, Finset.mem_filter]
  refine ⟨hvC, notMem_descendantsOf_controlsFrom hG hord hv fun m h => hC m (h ▸ hvC), ?_⟩
  exact ⟨x i, Or.inr rfl, reflTransGen_stepGraph_of_reflTransGen hG hord hv⟩

/-- A member of `W_j` is an ancestor of `y` or of `x j` in the graph of every later step. -/
theorem reflTransGen_of_mem_wSet_of_lt (hC : ∀ k, x k ∉ C) {j k : Fin n} (hjk : j < k) {v : V}
    (hv : v ∈ G.wSet C x y j) :
    ReflTransGen (G.stepGraph x k).Adj v y ∨ ReflTransGen (G.stepGraph x k).Adj v (x j) := by
  simp only [wSet, Finset.mem_filter] at hv
  obtain ⟨hvC, -, s, hs, hvs⟩ := hv
  have hva : v ∉ controlsAfter x j := fun ⟨m, _, hm⟩ => hC m (hm ▸ hvC)
  have h' := ReflTransGen.stepGraph_of_lt hjk hvs hva
  rcases hs with rfl | hs
  · exact Or.inl h'
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact Or.inr h'

/-- **The "only if" direction of Theorem 4.4.6** (Pearl 2009): in an acyclic graph with the
controls listed in an order compatible with the graph and outside the covariates, if some
sequence of covariate sets passes the step tests, then the explicit sets `W_k` pass the test
of every step. -/
theorem seqBackDoorStep_wSet_of_admissible (hG : G.IsAcyclic) (hord : G.ControlsOrdered x)
    (hC : ∀ k, x k ∉ C) {Zs : Fin n → Finset V} (h : G.Admissible C x y Zs) (k : Fin n) :
    G.SeqBackDoorStep x y (G.wSet C x y) k := by
  have hsep : (G.stepGraph x k).DSep {y} {x k} (stepCond x Zs k) := (h k).2
  unfold SeqBackDoorStep
  rw [dSep_iff_moralSep] at hsep ⊢
  have key : ∀ v ∈ (G.stepGraph x k).ancestorsOf ({y} ∪ {x k} ∪ stepCond x (G.wSet C x y) k),
      v ∈ (G.stepGraph x k).ancestorsOf {y, x k} ∨
        ∃ i < k, ReflTransGen (G.stepGraph x k).Adj v (x i) := by
    rintro v ⟨s, hs, hvs⟩
    rcases hs with (hs | hs) | ⟨i, hi, rfl⟩ | ⟨i, hi, hsW⟩
    · exact Or.inl ⟨s, Or.inl hs, hvs⟩
    · exact Or.inl ⟨s, Or.inr hs, hvs⟩
    · exact Or.inr ⟨i, hi, hvs⟩
    · rcases hi.lt_or_eq with hlt | rfl
      · rcases reflTransGen_of_mem_wSet_of_lt hC hlt hsW with h' | h'
        · exact Or.inl ⟨y, Or.inl rfl, hvs.trans h'⟩
        · exact Or.inr ⟨i, hlt, hvs.trans h'⟩
      · simp only [wSet, Finset.mem_filter] at hsW
        obtain ⟨-, -, t, ht, hst⟩ := hsW
        exact Or.inl ⟨t, ht, hvs.trans hst⟩
  refine MoralSep.of_subset hsep (fun v hv => ?_) fun v hv hvZ => ?_
  · rcases key v hv with ⟨t, ht, hvt⟩ | ⟨i, hi, hvi⟩
    · rcases ht with rfl | ht
      · exact ⟨t, Or.inl (Or.inl rfl), hvt⟩
      · exact ⟨t, Or.inl (Or.inr ht), hvt⟩
    · exact ⟨x i, Or.inr (Or.inl ⟨i, hi, rfl⟩), hvi⟩
  · rcases hvZ with ⟨i, hi, rfl⟩ | ⟨j, hj, hvZs⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · obtain ⟨hvC, hvd⟩ := (h j).1 v hvZs
      right
      rcases key v hv with hvt | ⟨i, hi, hvi⟩
      · refine ⟨k, le_rfl, ?_⟩
        simp only [wSet, Finset.mem_filter]
        exact ⟨hvC, fun hd => hvd (descendantsOf_mono (controlsFrom_anti hj) hd), hvt⟩
      · exact ⟨i, hi.le, mem_wSet_of_reflTransGen hG hord hC hvC
          (reflTransGen_mono (stepGraph_le k) hvi)⟩

/-- **Theorem 4.4.6** (Pearl 2009), the graphical equivalence: in an acyclic graph with the
controls listed in an order compatible with the graph and outside the covariates, the plan is
G-identifiable (some sequence passes the step tests) if and only if the sets `W_k` pass the
test of every step. -/
theorem gIdentifiable_iff_wSet (hG : G.IsAcyclic) (hord : G.ControlsOrdered x)
    (hC : ∀ k, x k ∉ C) :
    G.GIdentifiable C x y ↔ ∀ k, G.SeqBackDoorStep x y (G.wSet C x y) k :=
  ⟨fun ⟨_, h⟩ => seqBackDoorStep_wSet_of_admissible hG hord hC h, gIdentifiable_of_wSet⟩

/-- Theorem 4.4.6 within the standing assumptions of a control problem: in an acyclic graph a
plan is G-identifiable in Pearl's sense exactly when it satisfies `PlanRoles` and the sets
`W_k` pass the test of every step. -/
theorem gIdentifiablePlan_iff_wSet (hG : G.IsAcyclic) :
    G.GIdentifiablePlan C x y ↔
      G.PlanRoles C x y ∧ ∀ k, G.SeqBackDoorStep x y (G.wSet C x y) k :=
  ⟨fun ⟨hr, hi⟩ => ⟨hr, (gIdentifiable_iff_wSet hG hr.1 hr.2.2.1).1 hi⟩,
    fun ⟨hr, hs⟩ => ⟨hr, gIdentifiable_of_wSet hs⟩⟩

/-- The decision procedure for G-identifiability of a plan in an acyclic graph (Pearl 2009,
Theorem 4.4.6): check the standing assumptions and the step tests with the sets `W_k`. -/
def decidableGIdentifiablePlan (hG : G.IsAcyclic) : Decidable (G.GIdentifiablePlan C x y) :=
  decidable_of_iff _ (gIdentifiablePlan_iff_wSet hG).symm

end Converse

end Decidable

/-- For a single control, admissibility of `Zs` is the back-door criterion for the pair
`(x 0, y)` with covariates `Zs 0` drawn from `C`. -/
theorem admissible_one_iff {G : Digraph V} {C : Finset V} {x : Fin 1 → V} {y : V}
    {Zs : Fin 1 → Finset V} :
    G.Admissible C x y Zs ↔ (∀ v ∈ Zs 0, v ∈ C) ∧ G.BackDoor {x 0} {y} (Zs 0) := by
  have hfrom : controlsFrom x 0 = {x 0} := by
    ext v
    simp only [controlsFrom, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨j, _, hj⟩ => by rw [Fin.fin_one_eq_zero j] at hj; exact hj.symm,
      fun h => ⟨0, le_rfl, h.symm⟩⟩
  have hafter : controlsAfter x 0 = ∅ := by
    ext v
    simp only [controlsAfter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
      not_and]
    intro j hj
    exact absurd hj (by rw [Fin.fin_one_eq_zero j]; exact lt_irrefl 0)
  have hcond : stepCond x Zs 0 = (Zs 0 : Set V) := by
    ext v
    simp only [stepCond, Set.mem_ofPred_eq, Finset.mem_coe]
    constructor
    · rintro (⟨j, hj, -⟩ | ⟨j, -, hv⟩)
      · exact absurd hj (by rw [Fin.fin_one_eq_zero j]; exact lt_irrefl 0)
      · rwa [Fin.fin_one_eq_zero j] at hv
    · exact fun hv => Or.inr ⟨0, le_rfl, hv⟩
  constructor
  · intro h
    obtain ⟨hZ, hstep⟩ := h 0
    refine ⟨fun v hv => (hZ v hv).1, fun v hv => by rw [← hfrom]; exact (hZ v hv).2, ?_⟩
    unfold SeqBackDoorStep stepGraph at hstep
    rw [hafter, deleteIncoming_empty, hcond] at hstep
    exact hstep.symm
  · rintro ⟨hC, hZ, hsep⟩ k
    rw [Fin.fin_one_eq_zero k]
    refine ⟨fun v hv => ⟨hC v hv, by rw [hfrom]; exact hZ v hv⟩, ?_⟩
    unfold SeqBackDoorStep stepGraph
    rw [hafter, deleteIncoming_empty, hcond]
    exact hsep.symm

end Digraph

namespace CausalInference.SequentialBackDoorExamples

open Criteria Digraph

/-- Pearl (2009), Figure 4.4 as printed: `U₁ = 0`, `U₂ = 1`, `X₁ = 2`, `Z = 3`, `X₂ = 4`,
`Y = 5`, with edges `U₁ → X₁`, `U₁ → Z`, `X₁ → U₂`, `U₂ → Z`, `U₂ → Y`, `X₁ → Z`, `X₁ → X₂`,
`X₁ → Y`, `Z → X₂`, `X₂ → Y`. The latent `U₁`, `U₂` are not observed; the only observed
covariate is `Z`. -/
abbrev pearlFig44 : Digraph (Fin 6) :=
  ofEdges [(0, 2), (0, 3), (2, 1), (1, 3), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

example : pearlFig44.IsAcyclic := by decide +kernel
example : pearlFig44.ControlsOrdered ![2, 4] := by decide +kernel
-- The two tests of the text for `Z₁ = Z₂ = ∅`: the first holds, the second fails.
example : pearlFig44.SeqBackDoorStep ![2, 4] 5 ![∅, ∅] 0 := by decide +kernel
example : ¬ pearlFig44.SeqBackDoorStep ![2, 4] 5 ![∅, ∅] 1 := by decide +kernel
-- The sequence `Z₁ = ∅`, `Z₂ = {Z}` is admissible; `Z₁ = {Z}` violates (4.4).
example : pearlFig44.Admissible {3} ![2, 4] 5 ![∅, {3}] := by decide +kernel
example : ¬ pearlFig44.Admissible {3} ![2, 4] 5 ![∅, ∅] := by decide +kernel
example : ¬ pearlFig44.Admissible {3} ![2, 4] 5 ![{3}, {3}] := by decide +kernel
-- Theorem 4.4.6: `W₁ = ∅` and `W₂ = {Z}`, and they pass the tests.
example : pearlFig44.wSet {3} ![2, 4] 5 0 = ∅ := by decide +kernel
example : pearlFig44.wSet {3} ![2, 4] 5 1 = {3} := by decide +kernel
example : pearlFig44.GIdentifiable {3} ![2, 4] 5 :=
  gIdentifiable_of_wSet (by decide +kernel)
example : pearlFig44.AdmissiblePlan {3} ![2, 4] 5 ![∅, {3}] := by decide +kernel

/-- Figure 4.8 as printed: Figure 4.4 without the edges `X₁ → X₂`, `X₁ → Z` (the two the text
names) and `X₁ → U₂` (absent from the drawing), so the controls can be listed in either
order. -/
abbrev pearlFig48 : Digraph (Fin 6) :=
  ofEdges [(0, 2), (0, 3), (1, 3), (1, 5), (2, 5), (3, 4), (4, 5)]

example : pearlFig48.ControlsOrdered ![2, 4] := by decide +kernel
example : pearlFig48.ControlsOrdered ![4, 2] := by decide +kernel
-- For the order `(X₁, X₂)` the sequence `(∅, {Z})` is still admissible.
example : pearlFig48.Admissible {3} ![2, 4] 5 ![∅, {3}] := by decide +kernel

/-- For the order `(X₂, X₁)` no admissible sequence exists in Figure 4.8. -/
theorem pearlFig48_not_gIdentifiable : ¬ pearlFig48.GIdentifiable {3} ![4, 2] 5 := by
  rintro ⟨Zs, h⟩
  have key : ∀ A ∈ ({3} : Finset (Fin 6)).powerset, ∀ B ∈ ({3} : Finset (Fin 6)).powerset,
      ¬ pearlFig48.Admissible {3} ![4, 2] 5 ![A, B] := by decide +kernel
  have hZs : Zs = ![Zs 0, Zs 1] := by
    ext k : 1
    fin_cases k <;> rfl
  have hsub : ∀ k, Zs k ⊆ {3} := fun k v hv => Finset.mem_singleton.2
    (Finset.mem_singleton.1 ((h k).1 v hv).1)
  rw [hZs] at h
  exact key _ (Finset.mem_powerset.2 (hsub 0)) _ (Finset.mem_powerset.2 (hsub 1)) h

/-- The same conclusion by the decision procedure of Theorem 4.4.6: for the order `(X₂, X₁)` the
sets `W_k` fail a step test, so no admissible sequence exists. -/
example : ¬ pearlFig48.GIdentifiable {3} ![4, 2] 5 := by
  rw [gIdentifiable_iff_wSet (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- A graph with the properties stated for Pearl's Figure 4.6: `X₁ = 0`, `W = 1`, `X₂ = 2`,
`Y = 3`, latent `U₁ = 4`, `U₂ = 5`, with edges `X₁ → X₂`, `X₂ → Y`, `U₁ → W`, `U₂ → W`,
`U₁ → X₂`, `U₂ → Y`; the observed covariate is `W`. -/
abbrev fig46Like : Digraph (Fin 6) :=
  ofEdges [(0, 2), (2, 3), (4, 1), (5, 1), (4, 2), (5, 3)]

-- `Z₁ = W` passes the first test, but then no `Z₂` (necessarily `∅` or `{W}`) passes the
-- second; the choice `Z₁ = Z₂ = ∅` is admissible.
example : fig46Like.SeqBackDoorStep ![0, 2] 3 ![{1}, ∅] 0 := by decide +kernel
example : ∀ B ∈ ({1} : Finset (Fin 6)).powerset,
    ¬ fig46Like.SeqBackDoorStep ![0, 2] 3 ![{1}, B] 1 := by decide +kernel
example : fig46Like.Admissible {1} ![0, 2] 3 ![∅, ∅] := by decide +kernel

/-- Pearl (2009), Figure 4.7 as printed: `X₁ = 0`, `X₂ = 1`, `Y = 2`, `Z₁ = 3`, `Z₁' = 4`, and
the latent `U = 5`, with edges `U → Z₁`, `Z₁ → X₁`, `U → X₂`, `U → Z₁'`, `Z₁' → Y`,
`X₁ → X₂`, `X₂ → Y`. The observed covariates are `Z₁` and `Z₁'`. -/
abbrev pearlFig47 : Digraph (Fin 6) :=
  ofEdges [(5, 3), (3, 0), (5, 1), (5, 4), (4, 2), (0, 1), (1, 2)]

example : pearlFig47.IsAcyclic := by decide +kernel
-- The caption: `{Z₁}` and `{Z₁'}` both pass the first test and are minimal, since `∅` fails.
example : pearlFig47.SeqBackDoorStep ![0, 1] 2 ![{3}, ∅] 0 := by decide +kernel
example : pearlFig47.SeqBackDoorStep ![0, 1] 2 ![{4}, ∅] 0 := by decide +kernel
example : ¬ pearlFig47.SeqBackDoorStep ![0, 1] 2 ![∅, ∅] 0 := by decide +kernel
-- Starting with `{Z₁}`, the path `X₂ ← U → Z₁' → Y` forces `Z₁'` into the second set; starting
-- with `{Z₁'}`, the empty second set suffices.
example : ¬ pearlFig47.Admissible {3, 4} ![0, 1] 2 ![{3}, ∅] := by decide +kernel
example : pearlFig47.AdmissiblePlan {3, 4} ![0, 1] 2 ![{3}, {4}] := by decide +kernel
example : pearlFig47.AdmissiblePlan {3, 4} ![0, 1] 2 ![{4}, ∅] := by decide +kernel

/-! ### The raw step tests outside Pearl's setting -/

/-- Controls listed against the order of `G`: `L → B`, `L → Y`, `B → A`, `A → Y`, with `L = 0`,
`B = 1`, `A = 2`, `Y = 3`, the observed covariate `L`, and the controls listed as `(A, B)`. The
sequence `(∅, {L})` passes the raw step tests, although `A` is a descendant of the later
control `B`. For this listing the plan formula of Theorem 4.4.1 would be
`∑_l P(y | a, b, l) P(l | a)`, which is not the effect of the plan; `PlanRoles` excludes the
listing. -/
theorem controlsAgainstOrder :
    (ofEdges (n := 4) [(0, 1), (0, 3), (1, 2), (2, 3)]).Admissible {0} ![2, 1] 3 ![∅, {0}] ∧
      ¬ (ofEdges (n := 4) [(0, 1), (0, 3), (1, 2), (2, 3)]).ControlsOrdered ![2, 1] :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Controls listed against the order of `G` with no covariates: `b → a → y`, with `a = 0`,
`b = 1`, `y = 2`, and the controls listed as `(a, b)`. The empty sequence passes the raw step
tests. -/
theorem reversedChain :
    (ofEdges (n := 3) [(1, 0), (0, 2)]).Admissible ∅ ![0, 1] 2 ![∅, ∅] ∧
      ¬ (ofEdges (n := 3) [(1, 0), (0, 2)]).ControlsOrdered ![0, 1] :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A repeated control: for `x → y` (`x = 0`, `y = 1`), the controls `(x, x)` with empty
covariate sets pass the raw step tests; the second test conditions on its own treatment. The
listing is not ordered, since a control is a descendant of itself. -/
theorem repeatedControl :
    (ofEdges (n := 2) [(0, 1)]).Admissible ∅ ![0, 0] 1 ![∅, ∅] ∧
      ¬ (ofEdges (n := 2) [(0, 1)]).ControlsOrdered ![0, 0] :=
  ⟨by decide +kernel, by decide +kernel⟩

end CausalInference.SequentialBackDoorExamples
