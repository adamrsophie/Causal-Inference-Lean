/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Factorization

/-!
# The local directed Markov property

## Main definitions

* `Digraph.nondescendantsFinset G v`: the vertices other than `v` that are not descendants of
  `v`.
* `Digraph.LocalMarkov G p`: every vertex is conditionally independent of its nondescendants
  (other than its parents) given its parents.
* `Digraph.condKernels G p`: the conditional distributions of each vertex given its parents
  under `p`, with the uniform distribution on parent configurations of probability zero.

## Main results

* `Digraph.MarkovKernels.localMarkov`, `Digraph.Factorizes.localMarkov`: a distribution that
  factorizes according to an acyclic graph satisfies the local Markov property.
* A concrete noisy chain `0 → 1 → 2` over `Bool` (`CausalInference.GraphExamples.chainDist`),
  with its factorization, the conditional independence `{2} ⫫ {0} | {1}` and the dependence of
  `0` and `1`, the latter checked by computation.

* `Digraph.LocalMarkov.factorizes`: conversely, for an acyclic graph a distribution with the
  local Markov property factorizes, with the kernels `condKernels G p`; hence
  `Digraph.factorizes_iff_localMarkov`.

Sources: Lauritzen (1996), Graphical Models, chapter 3; Pearl (1988); Pearl (2009), Causality,
section 1.2.
-/

@[expose] public section

namespace Digraph

open CausalInference Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] {G : Digraph V} [DecidableRel G.Adj]

variable (G) in
/-- The nondescendants of `v`: the vertices other than `v` that are not reached from `v` by a
directed path. -/
def nondescendantsFinset (v : V) : Finset V := (insert v (G.descendantsFinset v))ᶜ

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
@[simp] theorem mem_nondescendantsFinset {u v : V} :
    u ∈ G.nondescendantsFinset v ↔ u ≠ v ∧ ¬ G.IsAncestor v u := by
  simp [nondescendantsFinset]

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- In an acyclic graph the parents of `v` are nondescendants of `v`. -/
theorem IsAcyclic.parentsFinset_subset_nondescendantsFinset (hG : G.IsAcyclic) (v : V) :
    G.parentsFinset v ⊆ G.nondescendantsFinset v := by
  intro u hu
  have huv := mem_parentsFinset.1 hu
  exact mem_nondescendantsFinset.2 ⟨hG.ne_of_adj huv, fun h => hG v (h.tail huv)⟩

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- The nondescendants of `v` are closed under taking parents. -/
theorem mem_nondescendantsFinset_of_adj {u v w : V} (hw : w ∈ G.nondescendantsFinset v)
    (huw : G.Adj u w) : u ∈ G.nondescendantsFinset v := by
  rw [mem_nondescendantsFinset] at hw ⊢
  refine ⟨?_, fun h => hw.2 (h.tail huw)⟩
  rintro rfl
  exact hw.2 (isAncestor_of_adj huw)

variable (G) in
/-- The local directed Markov property of `p` with respect to `G`: every vertex is
conditionally independent of its nondescendants other than its parents, given its parents. -/
def LocalMarkov (p : FiniteDist (∀ v, α v)) : Prop :=
  ∀ v, p.CondIndep {v} (G.nondescendantsFinset v \ G.parentsFinset v) (G.parentsFinset v)

/-- **Factorization implies the local Markov property.** If `p` is the product of the Markov
kernels `k` of an acyclic graph `G`, then every vertex is conditionally independent of its
nondescendants given its parents. -/
theorem MarkovKernels.localMarkov (k : G.MarkovKernels α) (hG : G.IsAcyclic)
    {p : FiniteDist (∀ v, α v)} (hp : ∀ x, p x = ∏ v, k.factor v x) : G.LocalMarkov p := by
  intro v
  set ND := G.nondescendantsFinset v
  set pa := G.parentsFinset v
  have hpa : pa ⊆ ND := hG.parentsFinset_subset_nondescendantsFinset v
  have hvND : v ∉ ND := fun h => (mem_nondescendantsFinset.1 h).1 rfl
  have hvpa : v ∉ pa := fun h => hG.irrefl v (mem_parentsFinset.1 h)
  have hND : ∀ w ∈ ND, ∀ u, G.Adj u w → u ∈ ND := fun w hw u huw =>
    mem_nondescendantsFinset_of_adj hw huw
  have hND' : ∀ w ∈ insert v ND, ∀ u, G.Adj u w → u ∈ insert v ND := by
    intro w hw u huw
    rcases mem_insert.1 hw with rfl | hw
    · exact mem_insert_of_mem (hpa (mem_parentsFinset.2 huw))
    · exact mem_insert_of_mem (hND w hw u huw)
  have h : ∀ y, p.margAt (insert v ND) y = k.factor v y * p.margAt ND y := fun y => by
    rw [k.margAt_of_ancestral hG hp hND', k.margAt_of_ancestral hG hp hND,
      MarkovKernels.prodOn, prod_insert hvND]
    rfl
  have hlift := p.margAt_insert_of_margAt_insert hpa hvND (k.factor v)
    (fun y y' hyy => k.factor_congr fun u hu => hyy u (by
      rcases hu with rfl | hu
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_parentsFinset.2 hu))) h
  rw [FiniteDist.condIndep_iff_margAt_mul
    (disjoint_singleton_left.2 fun h => hvND (mem_sdiff.1 h).1)
    (disjoint_singleton_left.2 hvpa) sdiff_disjoint]
  intro x
  rw [union_assoc, sdiff_union_of_subset hpa, ← insert_eq, ← insert_eq, h x, hlift x]
  ring

/-- **Factorization implies the local Markov property**, for a distribution that factorizes
according to an acyclic graph. -/
theorem Factorizes.localMarkov (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)}
    (h : G.Factorizes p) : G.LocalMarkov p :=
  let ⟨k, hk⟩ := h
  k.localMarkov hG hk

/-! ### Local Markov implies factorization -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] in
/-- A set closed under taking parents is closed under taking ancestors. -/
theorem mem_of_reflTransGen_of_closed {A : Finset V} (hA : ∀ w ∈ A, ∀ u, G.Adj u w → u ∈ A)
    {c w : V} (hcw : Relation.ReflTransGen G.Adj c w) (hw : w ∈ A) : c ∈ A := by
  induction hcw using Relation.ReflTransGen.head_induction_on with
  | refl => exact hw
  | head hcd _ ih => exact hA _ ih _ hcd

variable (G) in
/-- The conditional distribution of each vertex given its parents under `p`, as Markov kernels:
`P(x_v = a, x_pa = z) / P(x_pa = z)` when `P(x_pa = z) > 0`, and the uniform distribution on
`α v` for parent configurations of probability zero (a convention that does not affect the
factorization, since those configurations carry no mass). -/
noncomputable def condKernels (p : FiniteDist (∀ v, α v)) : G.MarkovKernels α where
  kernel v z a :=
    if p.probOf (fun y => (G.parentsFinset v).restrict y = z) = 0 then 1 / Fintype.card (α v)
    else p.probOf (fun y => y v = a ∧ (G.parentsFinset v).restrict y = z) /
      p.probOf (fun y => (G.parentsFinset v).restrict y = z)
  nonneg v z a := by
    split_ifs
    · positivity
    · exact div_nonneg (p.probOf_nonneg) (p.probOf_nonneg)
  sum_eq_one v z := by
    obtain ⟨x₀⟩ := p.nonempty
    have : Nonempty (α v) := ⟨x₀ v⟩
    split_ifs with hz
    · simp
    · rw [← sum_div, div_eq_one_iff_eq hz,
        p.probOf_eq_sum_univ (P := fun y => (G.parentsFinset v).restrict y = z) (fun y => y v)]
      exact sum_congr rfl fun a _ => p.probOf_congr fun y => and_comm

/-- The factor of `v` for `condKernels` at `x`, in terms of marginal masses. -/
theorem condKernels_factor (p : FiniteDist (∀ v, α v)) (v : V) (x : ∀ v, α v) :
    (condKernels G p).factor v x =
      if p.margAt (G.parentsFinset v) x = 0 then (1 / Fintype.card (α v) : ℝ)
      else p.margAt (insert v (G.parentsFinset v)) x / p.margAt (G.parentsFinset v) x := by
  have h1 : p.probOf (fun y => (G.parentsFinset v).restrict y =
      (G.parentsFinset v).restrict x) = p.margAt (G.parentsFinset v) x :=
    FiniteDist.probOf_restrict_eq_margAt₁ x
  have h2 : p.probOf (fun y => y v = x v ∧ (G.parentsFinset v).restrict y =
      (G.parentsFinset v).restrict x) = p.margAt (insert v (G.parentsFinset v)) x := by
    rw [FiniteDist.margAt_eq_probOf]
    refine p.probOf_congr fun y => ?_
    simp [FiniteDist.restrict_eq_restrict_iff]
  simp only [MarkovKernels.factor, condKernels, h1, h2]

/-- **Local Markov implies factorization**, on ancestral sets: if `p` satisfies the local Markov
property for an acyclic `G`, then on every set `A` closed under taking parents the marginal of
`p` is the product of the conditional kernels `condKernels G p` of the vertices of `A`. -/
theorem LocalMarkov.margAt_eq_prodOn (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)}
    (hL : G.LocalMarkov p) {A : Finset V} (hA : ∀ w ∈ A, ∀ u, G.Adj u w → u ∈ A)
    (x : ∀ v, α v) : p.margAt A x = (condKernels G p).prodOn A x := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨s, hsA, hsmax⟩ := A.exists_max_image f hne
    have hsink : ∀ v ∈ A, ¬ G.Adj s v := fun v hv hsv => (hf hsv).not_ge (hsmax v hv)
    set A' := A.erase s
    set pa := G.parentsFinset s
    have hA' : ∀ w ∈ A', ∀ u, G.Adj u w → u ∈ A' := fun w hw u huw =>
      mem_erase.2 ⟨fun hus => hsink w (mem_of_mem_erase hw) (by rw [← hus]; exact huw),
        hA w (mem_of_mem_erase hw) u huw⟩
    have hpa : pa ⊆ A' := fun u hu =>
      mem_erase.2 ⟨fun hus => hG.irrefl s (by have := mem_parentsFinset.1 hu; rwa [hus] at this),
        hA s hsA u (mem_parentsFinset.1 hu)⟩
    have hA'ND : A' ⊆ G.nondescendantsFinset s := by
      intro w hw
      refine mem_nondescendantsFinset.2 ⟨ne_of_mem_erase hw, fun hsw => ?_⟩
      obtain ⟨c, hsc, hcw⟩ := Relation.TransGen.head'_iff.1 hsw
      exact hsink c (mem_of_reflTransGen_of_closed hA hcw (mem_of_mem_erase hw)) hsc
    have hci := ((hL s).mono_right (sdiff_subset_sdiff hA'ND subset_rfl)).margAt_mul x
    rw [union_assoc, sdiff_union_of_subset hpa, ← insert_eq, ← insert_eq, insert_erase hsA]
      at hci
    have hstep : p.margAt A x = (condKernels G p).factor s x * p.margAt A' x := by
      rw [condKernels_factor]
      split_ifs with h0
      · have hA0 : p.margAt A x = 0 := le_antisymm
          ((p.margAt_anti (hpa.trans (erase_subset s A)) x).trans_eq h0) (p.margAt_nonneg _ _)
        have hA'0 : p.margAt A' x = 0 :=
          le_antisymm ((p.margAt_anti hpa x).trans_eq h0) (p.margAt_nonneg _ _)
        rw [hA0, hA'0, mul_zero]
      · rw [div_mul_eq_mul_div, eq_div_iff h0, hci]
    rw [hstep, ih A' (erase_ssubset hsA) hA', MarkovKernels.prodOn, MarkovKernels.prodOn,
      ← mul_prod_erase A _ hsA]

/-- **Local Markov implies factorization**: for an acyclic graph, a distribution satisfying the
local Markov property is the product of its conditional kernels `condKernels G p`. -/
theorem LocalMarkov.factorizes (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)}
    (hL : G.LocalMarkov p) : G.Factorizes p :=
  ⟨condKernels G p, fun x => by
    rw [← FiniteDist.margAt_univ p x, hL.margAt_eq_prodOn hG (fun _ _ u _ => mem_univ u) x]
    rfl⟩

/-- For an acyclic graph, factorization and the local Markov property are equivalent. -/
theorem factorizes_iff_localMarkov (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)} :
    G.Factorizes p ↔ G.LocalMarkov p :=
  ⟨Factorizes.localMarkov hG, LocalMarkov.factorizes hG⟩

end Digraph

/-! ### A noisy chain over `Bool` -/

namespace CausalInference.GraphExamples

open Digraph Finset

/-- The predecessor of a nonzero vertex of the chain `0 → 1 → 2`, as a parent. -/
def chainParent (v : Fin 3) (h : v ≠ 0) : chain.parentsFinset v :=
  ⟨⟨v.val - 1, by omega⟩, mem_parentsFinset.2 (by
    have : v.val ≠ 0 := fun h' => h (Fin.ext h')
    change v.val - 1 + 1 = v.val
    omega)⟩

/-- Kernels for the chain `0 → 1 → 2` over `Bool`: vertex `0` is a fair bit, and each later bit
copies its parent with probability `3 / 4`. -/
noncomputable def chainKernels : chain.MarkovKernels (fun _ : Fin 3 => Bool) where
  kernel v z a := if h : v = 0 then 1 / 2 else if a = z (chainParent v h) then 3 / 4 else 1 / 4
  nonneg v z a := by split_ifs <;> norm_num
  sum_eq_one v z := by
    by_cases h : v = 0
    · simp [h]
    · simp only [h, dite_false, Fintype.sum_bool]
      cases z (chainParent v h) <;> norm_num

theorem chainKernels_factor_zero (y : Fin 3 → Bool) : chainKernels.factor 0 y = 1 / 2 := by
  simp [MarkovKernels.factor, chainKernels]

theorem chainKernels_factor_one (y : Fin 3 → Bool) :
    chainKernels.factor 1 y = if y 1 = y 0 then 3 / 4 else 1 / 4 := by
  simp [MarkovKernels.factor, chainKernels, chainParent, Finset.restrict]

/-- The joint distribution of the noisy chain: the product of its kernels. -/
noncomputable def chainDist : FiniteDist (Fin 3 → Bool) := chainKernels.jointDist (by decide)

/-- The noisy chain factorizes according to the chain graph. -/
theorem chainDist_factorizes : chain.Factorizes chainDist :=
  chainKernels.factorizes_jointDist _

/-- In the noisy chain, `2 ⫫ 0 | 1`: an instance of the local Markov property. -/
theorem chainDist_condIndep : chainDist.CondIndep {2} {0} {1} := by
  have h := chainDist_factorizes.localMarkov (by decide) 2
  rwa [show chain.nondescendantsFinset 2 \ chain.parentsFinset 2 = {0} by decide,
    show chain.parentsFinset 2 = {1} by decide] at h

/-- In the noisy chain, `0` and `1` are dependent: `P(X₀ = X₁ = true) = 3 / 8` while
`P(X₀ = true) * P(X₁ = true) = 1 / 4`. -/
theorem chainDist_not_condIndep : ¬ chainDist.CondIndep {0} {1} ∅ := by
  intro h
  have key := h.margAt_mul (fun _ => true)
  have hp : ∀ x, chainDist x = ∏ v, chainKernels.factor v x := fun _ => rfl
  have hG : chain.IsAcyclic := by decide
  have h01 : ∀ y, chainDist.margAt {0, 1} y =
      chainKernels.factor 0 y * chainKernels.factor 1 y := fun y => by
    rw [chainKernels.margAt_of_ancestral hG hp (A := {0, 1}) (by decide) y,
      MarkovKernels.prodOn, prod_pair (by decide)]
  have h0 : chainDist.margAt {0} (fun _ => true) = 1 / 2 := by
    rw [chainKernels.margAt_of_ancestral hG hp (by decide), MarkovKernels.prodOn,
      prod_singleton, chainKernels_factor_zero]
  have h1 : chainDist.margAt {1} (fun _ => true) = 1 / 2 := by
    rw [chainDist.margAt_eq_sum_margAt (show ({1} : Finset (Fin 3)) ⊆ {0, 1} by decide),
      show ({0, 1} \ {1} : Finset (Fin 3)) = {0} by decide,
      FiniteDist.sum_agreeOn_compl_singleton]
    simp only [h01, chainKernels_factor_zero, chainKernels_factor_one, Fintype.sum_bool]
    norm_num
  rw [show ({0} ∪ {1} ∪ ∅ : Finset (Fin 3)) = {0, 1} by decide,
    show ({0} ∪ ∅ : Finset (Fin 3)) = {0} by decide,
    show ({1} ∪ ∅ : Finset (Fin 3)) = {1} by decide, h01, h0, h1, FiniteDist.margAt_empty,
    chainKernels_factor_zero, chainKernels_factor_one] at key
  norm_num at key

end CausalInference.GraphExamples
