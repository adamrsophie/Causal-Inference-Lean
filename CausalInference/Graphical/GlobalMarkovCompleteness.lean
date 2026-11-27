/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.GlobalMarkov

/-!
# Completeness of d-separation: the single-edge case

The second half of Pearl (2009), Theorem 1.2.4 (Geiger and Pearl): if `X` and `Y` are
d-connected given `Z` in an acyclic graph `G`, some distribution factorizing according to `G`
violates `X ⫫ Y | Z`. This file proves only the special case in which the d-connecting trail is a
single edge.

## Main definitions

* `Digraph.copyKernels huv`: for an edge `u → v`, binary kernels under which `v` copies `u` and
  every other vertex is an independent fair bit.

## Main results

* `Digraph.exists_factorizes_not_condIndep_of_adj`: if `u → v` is an edge and neither `u` nor `v`
  is in `Z`, there is a distribution over binary variables that factorizes according to `G` and
  in which `{u} ⫫ {v} | Z` fails.

The general weak completeness theorem (an arbitrary active trail, possibly through colliders
that are opened by descendants in `Z`) is not proved here.

## References

* D. Geiger and J. Pearl (1990), *On the logic of causal models*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 1.2.3.
-/

@[expose] public section

namespace Digraph

open CausalInference Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]

/-- Binary kernels for an edge `u → v`: the vertex `v` copies the value of its parent `u`, and
every other vertex is a fair bit that ignores its parents. -/
noncomputable def copyKernels {u v : V} (huv : G.Adj u v) :
    G.MarkovKernels (fun _ : V => Bool) where
  kernel w z a := if h : w = v then
      (if a = z ⟨u, mem_parentsFinset.2 (h ▸ huv)⟩ then 1 else 0)
    else 1 / 2
  nonneg w z a := by split_ifs <;> norm_num
  sum_eq_one w z := by
    by_cases h : w = v
    · simp [h]
    · simp only [h, dite_false, Fintype.sum_bool]
      norm_num

theorem copyKernels_factor_of_ne {u v w : V} (huv : G.Adj u v) (hw : w ≠ v) (y : V → Bool) :
    (copyKernels huv).factor w y = 1 / 2 := by
  simp [MarkovKernels.factor, copyKernels, hw]

theorem copyKernels_factor_self {u v : V} (huv : G.Adj u v) (y : V → Bool) :
    (copyKernels huv).factor v y = if y v = y u then 1 else 0 := by
  simp only [MarkovKernels.factor, copyKernels, dite_true, Finset.restrict]
  exact if_congr Iff.rfl rfl rfl

/-- **Completeness of d-separation for a single edge.** If `u → v` is an edge of an acyclic graph
and neither `u` nor `v` is in `Z` (so `{u}` and `{v}` are d-connected given `Z`,
`Digraph.dConn_of_adj`), then some distribution over binary variables factorizes according to
`G` and violates `{u} ⫫ {v} | Z`: the one in which `v` copies `u` and all other vertices are
independent fair bits. -/
theorem exists_factorizes_not_condIndep_of_adj (hG : G.IsAcyclic) {u v : V} (huv : G.Adj u v)
    {Z : Finset V} (hu : u ∉ Z) (hv : v ∉ Z) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {u} {v} Z := by
  set k := copyKernels huv
  refine ⟨k.jointDist hG, k.factorizes_jointDist hG, fun h => ?_⟩
  set p := k.jointDist hG
  have hpos : ∀ y : V → Bool, y v = y u → 0 < p y := by
    intro y hy
    refine prod_pos fun w _ => ?_
    by_cases hw : w = v
    · subst hw
      rw [copyKernels_factor_self, ite_eq_left_iff.2 (fun h => absurd hy h)]
      norm_num
    · rw [copyKernels_factor_of_ne huv hw]
      norm_num
  have hzero : ∀ y : V → Bool, y v ≠ y u → p y = 0 := by
    intro y hy
    refine prod_eq_zero (mem_univ v) ?_
    rw [copyKernels_factor_self, ite_eq_right_iff.2 (fun h => absurd h hy)]
  let y₁ : V → Bool := fun _ => true
  let y₂ : V → Bool := fun w => decide (w ∈ Z)
  have hy₂ : Z.restrict y₂ = Z.restrict y₁ := by
    funext w
    simp [Finset.restrict, y₂, y₁, w.2]
  have key := h (({u} : Finset V).restrict y₁) (({v} : Finset V).restrict y₂) (Z.restrict y₁)
  have h0 : p.probOf (fun y => ({u} : Finset V).restrict y = ({u} : Finset V).restrict y₁ ∧
      ({v} : Finset V).restrict y = ({v} : Finset V).restrict y₂ ∧
      Z.restrict y = Z.restrict y₁) = 0 := by
    unfold FiniteDist.probOf FiniteDist.prob
    refine sum_eq_zero fun y hy => hzero y ?_
    obtain ⟨h1, h2, -⟩ := (mem_filter.1 hy).2
    have e1 := congrFun h1 ⟨u, mem_singleton_self u⟩
    have e2 := congrFun h2 ⟨v, mem_singleton_self v⟩
    simp only [Finset.restrict, y₁, y₂, hv, decide_false] at e1 e2
    rw [e1, e2]
    decide
  have hXc : 0 < p.probOf (fun y => ({u} : Finset V).restrict y = ({u} : Finset V).restrict y₁ ∧
      Z.restrict y = Z.restrict y₁) :=
    (hpos y₁ rfl).trans_le (p.le_probOf y₁ ⟨rfl, rfl⟩)
  have hYc : 0 < p.probOf (fun y => ({v} : Finset V).restrict y = ({v} : Finset V).restrict y₂ ∧
      Z.restrict y = Z.restrict y₁) :=
    (hpos y₂ (by simp [y₂, hu, hv])).trans_le (p.le_probOf y₂ ⟨rfl, hy₂⟩)
  rw [h0, zero_mul] at key
  exact (mul_pos hXc hYc).ne key

end Digraph
