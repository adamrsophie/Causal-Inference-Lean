/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.MarkovEquivalenceCharacterization

/-!
# Faithfulness

A finite distribution `p` is *faithful* to a directed graph `G` when every conditional
independence of `p` is a d-separation of `G`. Pearl (2009, *Causality*, 2nd edition,
Definition 2.4.1) calls this condition *stability*; Spirtes, Glymour and Scheines (1993) call it
faithfulness. Together with the global Markov property (every d-separation is a conditional
independence), faithfulness makes the conditional independences of `p` exactly the
d-separations of `G`, so `p` determines the Markov equivalence class of `G`, hence its skeleton
and v-structures.

## Main definitions

* `CausalInference.FiniteDist.IsFaithful p G`: `p.CondIndep X Y Z → G.DSep X Y Z` for all
  finsets of vertices.
* `CausalInference.FiniteDist.ofWeights`: the distribution with masses proportional to natural
  number weights; used for the concrete faithful laws.

## Main results

* `CausalInference.FiniteDist.isFaithful_iff_forall_singleton`: faithfulness reduces to single
  vertices outside the conditioning set.
* `CausalInference.FiniteDist.IsFaithful.condIndep_iff_dSep`: for a Markov and faithful law,
  conditional independence is d-separation.
* `CausalInference.FiniteDist.IsFaithful.markovEquivalent`: two graphs to which the same law is
  Markov and faithful are Markov equivalent; `IsFaithful.skeleton_eq` and
  `IsFaithful.isVStructure_iff`: such a law determines the skeleton and the v-structures.
* `CausalInference.FiniteDist.IsFaithful.skeleton_adj_iff`,
  `CausalInference.FiniteDist.IsFaithful.collider_iff`: adjacency and colliders read off the
  conditional independences of a Markov and faithful law.
* `CausalInference.GraphExamples.not_isFaithful_xorDist`: the exclusive-or law over the collider
  is Markov but not faithful.
* `CausalInference.GraphExamples.chainLaw_isFaithful`,
  `CausalInference.GraphExamples.colliderLaw_isFaithful`: explicit strictly positive laws over
  binary variables that are Markov and faithful to the chain `0 → 1 → 2` and to the collider
  `0 → 2 ← 1`.

The existence of a faithful law for every acyclic graph (Meek 1995; Spirtes, Glymour and Scheines
1993) is proved in `CausalInference.Discovery.FaithfulExistence`.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, sections 2.4 and
  2.5.
* P. Spirtes, C. Glymour and R. Scheines (1993), *Causation, Prediction, and Search*.
-/

@[expose] public section

namespace CausalInference.FiniteDist

open Digraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- A finite distribution `p` on configurations is faithful to `G` when every conditional
independence of `p` is a d-separation of `G`: `p.CondIndep X Y Z → G.DSep X Y Z`. -/
def IsFaithful (p : FiniteDist (∀ v, α v)) (G : Digraph V) : Prop :=
  ∀ X Y Z : Finset V, p.CondIndep X Y Z → G.DSep ↑X ↑Y ↑Z

variable {p : FiniteDist (∀ v, α v)} {G H : Digraph V}

/-- Faithfulness for single vertices: it suffices that `{x} ⫫ {y} | Z` implies d-separation of
`x` and `y` by `Z` when neither `x` nor `y` lies in `Z`. -/
theorem isFaithful_iff_forall_singleton :
    p.IsFaithful G ↔ ∀ (x y : V) (Z : Finset V), x ∉ Z → y ∉ Z →
      p.CondIndep {x} {y} Z → G.DSep {x} {y} ↑Z := by
  refine ⟨fun h x y Z _ _ hci => by simpa using h _ _ _ hci, fun h X Y Z hci => ?_⟩
  rw [dSep_iff_forall_singleton]
  intro x hx y hy
  by_cases hxZ : x ∈ Z
  · exact dSep_of_subset_left (Set.singleton_subset_iff.2 (mem_coe.2 hxZ))
  by_cases hyZ : y ∈ Z
  · exact dSep_of_subset_right (Set.singleton_subset_iff.2 (mem_coe.2 hyZ))
  exact h x y Z hxZ hyZ ((hci.mono_left (singleton_subset_iff.2 (mem_coe.1 hx))).mono_right
    (singleton_subset_iff.2 (mem_coe.1 hy)))

/-- For a law that is Markov and faithful to `G`, conditional independence is d-separation. -/
theorem IsFaithful.condIndep_iff_dSep (hM : G.GlobalMarkov p)
    (hF : p.IsFaithful G) {X Y Z : Finset V} : p.CondIndep X Y Z ↔ G.DSep ↑X ↑Y ↑Z :=
  ⟨hF X Y Z, hM X Y Z⟩

/-- **A Markov and faithful law determines the Markov equivalence class.** If the same law is
Markov and faithful to `G` and to `H`, then `G` and `H` have the same d-separation relation. -/
theorem IsFaithful.markovEquivalent
    (hMG : G.GlobalMarkov p) (hFG : p.IsFaithful G) (hMH : H.GlobalMarkov p)
    (hFH : p.IsFaithful H) : MarkovEquivalent G H := by
  intro X Y Z
  classical
  obtain ⟨X, rfl⟩ : ∃ X' : Finset V, (X' : Set V) = X := ⟨X.toFinset, Set.coe_toFinset X⟩
  obtain ⟨Y, rfl⟩ : ∃ Y' : Finset V, (Y' : Set V) = Y := ⟨Y.toFinset, Set.coe_toFinset Y⟩
  obtain ⟨Z, rfl⟩ : ∃ Z' : Finset V, (Z' : Set V) = Z := ⟨Z.toFinset, Set.coe_toFinset Z⟩
  rw [← hFG.condIndep_iff_dSep hMG, hFH.condIndep_iff_dSep hMH]

/-- A law that is Markov and faithful to two acyclic graphs forces the same skeleton. -/
theorem IsFaithful.skeleton_eq (hG : G.IsAcyclic)
    (hH : H.IsAcyclic) (hMG : G.GlobalMarkov p) (hFG : p.IsFaithful G)
    (hMH : H.GlobalMarkov p) (hFH : p.IsFaithful H) : G.skeleton = H.skeleton :=
  (hFG.markovEquivalent hMG hMH hFH).skeleton_eq hG hH

/-- A law that is Markov and faithful to two acyclic graphs forces the same v-structures. -/
theorem IsFaithful.isVStructure_iff
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) (hMG : G.GlobalMarkov p) (hFG : p.IsFaithful G)
    (hMH : H.GlobalMarkov p) (hFH : p.IsFaithful H) {a c b : V} :
    G.IsVStructure a c b ↔ H.IsVStructure a c b :=
  (hFG.markovEquivalent hMG hMH hFH).isVStructure_iff hG hH

/-- For a law that is Markov and faithful to an acyclic graph `G`, two vertices are adjacent in
the skeleton of `G` if and only if they are distinct and dependent given every set containing
neither of them. -/
theorem IsFaithful.skeleton_adj_iff (hG : G.IsAcyclic)
    (hM : G.GlobalMarkov p) (hF : p.IsFaithful G) {u v : V} :
    G.skeleton.Adj u v ↔ u ≠ v ∧ ∀ Z : Finset V, u ∉ Z → v ∉ Z → ¬ p.CondIndep {u} {v} Z := by
  classical
  rw [hG.skeleton_adj_iff]
  refine and_congr_right fun _ => ⟨fun h Z hu hv hci => ?_, fun h Z hu hv hsep => ?_⟩
  · exact h Z hu hv (by simpa using hF _ _ _ hci)
  · obtain ⟨Z, rfl⟩ : ∃ Z' : Finset V, (Z' : Set V) = Z := ⟨Z.toFinset, Set.coe_toFinset Z⟩
    exact h Z hu hv (hM _ _ _ (by simpa using hsep))

/-- For a law that is Markov and faithful to an acyclic graph `G`, the middle vertex of an
unshielded triple `a, c, b` is a collider if and only if `a` and `b` are independent given some
set that contains neither `a`, `b` nor `c`. -/
theorem IsFaithful.collider_iff (hG : G.IsAcyclic) (hM : G.GlobalMarkov p)
    (hF : p.IsFaithful G) {a c b : V} (hs : G.IsUnshielded a c b) :
    (G.Adj a c ∧ G.Adj b c) ↔
      ∃ Z : Finset V, a ∉ Z ∧ b ∉ Z ∧ p.CondIndep {a} {b} Z ∧ c ∉ Z := by
  classical
  rw [hG.collider_iff_exists_dSep hs]
  constructor
  · rintro ⟨Z, ha, hb, hsep, hc⟩
    obtain ⟨Z, rfl⟩ : ∃ Z' : Finset V, (Z' : Set V) = Z := ⟨Z.toFinset, Set.coe_toFinset Z⟩
    exact ⟨Z, ha, hb, hM _ _ _ (by simpa using hsep), hc⟩
  · rintro ⟨Z, ha, hb, hci, hc⟩
    exact ⟨Z, ha, hb, by simpa using hF _ _ _ hci, hc⟩

/-! ### Laws from natural weights -/

section Weights

variable {Ω : Type*} [Fintype Ω]

/-- The distribution with masses `w ω / ∑ ω', w ω'` for natural weights `w` with positive
total. -/
noncomputable def ofWeights (w : Ω → ℕ) (hw : ∑ ω, w ω ≠ 0) : FiniteDist Ω where
  mass ω := (w ω : ℝ) / (∑ ω', w ω' : ℕ)
  nonneg _ := by positivity
  sum_eq_one := by
    rw [← sum_div]
    push_cast
    exact div_self (by exact_mod_cast hw)

theorem ofWeights_apply (w : Ω → ℕ) (hw : ∑ ω, w ω ≠ 0) (ω : Ω) :
    ofWeights w hw ω = (w ω : ℝ) / (∑ ω', w ω' : ℕ) := rfl

theorem ofWeights_pos (w : Ω → ℕ) (hw : ∑ ω, w ω ≠ 0) (hpos : ∀ ω, 0 < w ω) (ω : Ω) :
    0 < ofWeights w hw ω := by
  rw [ofWeights_apply]
  have := hpos ω
  have : (0 : ℝ) < (∑ ω', w ω' : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hw
  positivity

end Weights

/-- Marginal masses of a weighted law are sums of weights over the agreeing configurations. -/
theorem margAt_ofWeights (w : (∀ v, α v) → ℕ) (hw : ∑ ω, w ω ≠ 0) (S : Finset V)
    (x : ∀ v, α v) : (ofWeights w hw).margAt S x =
      ((∑ y ∈ agreeOn S x, w y : ℕ) : ℝ) / (∑ ω, w ω : ℕ) := by
  rw [margAt, prob, Nat.cast_sum, sum_div]
  rfl

/-- **A dependence check in natural numbers.** If the cylinder identity of `X ⫫ Y | Z` fails for
the weight sums at some configuration, the weighted law violates `X ⫫ Y | Z`. -/
theorem not_condIndep_ofWeights (w : (∀ v, α v) → ℕ) (hw : ∑ ω, w ω ≠ 0) {X Y Z : Finset V}
    (x : ∀ v, α v)
    (hne : (∑ y ∈ agreeOn (X ∪ Y ∪ Z) x, w y) * (∑ y ∈ agreeOn Z x, w y) ≠
      (∑ y ∈ agreeOn (X ∪ Z) x, w y) * (∑ y ∈ agreeOn (Y ∪ Z) x, w y)) :
    ¬ (ofWeights w hw).CondIndep X Y Z := by
  intro h
  have key := h.margAt_mul x
  simp only [margAt_ofWeights] at key
  have hN : ((∑ ω, w ω : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hw
  field_simp at key
  exact hne (by exact_mod_cast key)

/-! ### Strictly positive laws over binary variables -/

/-- In a strictly positive law over binary variables, no vertex outside `Z` is independent of
itself given `Z`. -/
theorem not_condIndep_self_of_pos {p : FiniteDist (V → Bool)} (hp : ∀ ω, 0 < p ω) {x : V}
    {Z : Finset V} (hx : x ∉ Z) : ¬ p.CondIndep {x} {x} Z := by
  intro h
  set c : V → Bool := fun _ => true
  have key := h.margAt_mul c
  rw [union_self] at key
  set B : Finset V := {x} ∪ Z
  have hsum : p.margAt Z c = p.margAt B c + p.margAt B (Function.update c x false) := by
    have hBZ : B \ Z = {x} := by
      ext v
      simp only [B, mem_sdiff, mem_union, mem_singleton]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact h
        · exact absurd h h'
      · rintro rfl
        exact ⟨Or.inl rfl, hx⟩
    rw [p.margAt_eq_sum_margAt (subset_union_right : Z ⊆ B), hBZ,
      FiniteDist.sum_agreeOn_compl_singleton, Fintype.sum_bool]
    have : Function.update c x true = c := Function.update_eq_self x c
    rw [this]
  have hpos : 0 < p.margAt B c :=
    lt_of_lt_of_le (hp c) (p.le_probOf c fun _ _ => rfl)
  have hpos' : 0 < p.margAt B (Function.update c x false) :=
    lt_of_lt_of_le (hp _) (p.le_probOf _ fun _ _ => rfl)
  rw [hsum] at key
  nlinarith

end CausalInference.FiniteDist

/-! ### The exclusive-or law and two faithful laws -/

namespace CausalInference.GraphExamples

open Digraph Finset FiniteDist

/-- **The exclusive-or law is not faithful.** It factorizes according to the collider
`0 → 2 ← 1`, so it is Markov to it, but `0` and `2` are independent although they are adjacent.
-/
theorem not_isFaithful_xorDist : ¬ xorDist.IsFaithful collider := fun h =>
  collider_not_dSep_zero_two (h _ _ _ xorDist_condIndep)

/-- The exclusive-or law is Markov to the collider. -/
theorem xorDist_globalMarkov : collider.GlobalMarkov xorDist :=
  xorDist_factorizes.globalMarkov (by decide)

/-! #### The chain -/

/-- Weights of a noisy copy chain on `0 → 1 → 2`: `0` is a fair bit and each later bit copies
its parent with probability `3 / 4`. The total weight is `32`. -/
def chainWeight (y : Fin 3 → Bool) : ℕ :=
  (if y 1 = y 0 then 3 else 1) * (if y 2 = y 1 then 3 else 1)

theorem chainWeight_sum : ∑ y, chainWeight y = 32 := by decide

/-- The noisy copy law on the chain `0 → 1 → 2`. -/
noncomputable def chainLaw : FiniteDist (Fin 3 → Bool) :=
  ofWeights chainWeight (by rw [chainWeight_sum]; decide)

/-- Kernel weights of the noisy copy law, out of `4`. -/
def chainKernelWeight (v : Fin 3) (c : Fin 3 → Bool) : ℕ :=
  if v = 0 then 2 else if v = 1 then (if c 1 = c 0 then 3 else 1)
  else (if c 2 = c 1 then 3 else 1)

/-- The factors of the noisy copy law. -/
noncomputable def chainFactor (v : Fin 3) (c : Fin 3 → Bool) : ℝ :=
  (chainKernelWeight v c : ℝ) / 4

theorem chainFactor_nonneg (v : Fin 3) (c : Fin 3 → Bool) : 0 ≤ chainFactor v c := by
  unfold chainFactor
  positivity

theorem chainKernelWeight_update : ∀ (v : Fin 3) (c : Fin 3 → Bool),
    chainKernelWeight v (Function.update c v true) +
      chainKernelWeight v (Function.update c v false) = 4 := by
  decide

theorem chainFactor_sum (v : Fin 3) (c : Fin 3 → Bool) :
    ∑ b : Bool, chainFactor v (Function.update c v b) = 1 := by
  rw [Fintype.sum_bool]
  simp only [chainFactor]
  rw [← add_div, ← Nat.cast_add, chainKernelWeight_update]
  norm_num

theorem chainFactor_congr (v : Fin 3) (c c' : Fin 3 → Bool)
    (h : ∀ u, u = v ∨ chain.Adj u v → c u = c' u) : chainFactor v c = chainFactor v c' := by
  fin_cases v
  · rfl
  · have h1 : c 1 = c' 1 := h 1 (Or.inl rfl)
    have h0 : c 0 = c' 0 := h 0 (Or.inr (by decide))
    simp [chainFactor, chainKernelWeight, h0, h1]
  · have h2 : c 2 = c' 2 := h 2 (Or.inl rfl)
    have h1 : c 1 = c' 1 := h 1 (Or.inr (by decide))
    simp [chainFactor, chainKernelWeight, h1, h2]

theorem chainWeight_eq : ∀ y : Fin 3 → Bool,
    2 * chainWeight y = chainKernelWeight 0 y * chainKernelWeight 1 y * chainKernelWeight 2 y := by
  decide

/-- The noisy copy law factorizes according to the chain. -/
theorem chainLaw_factorizes : chain.Factorizes chainLaw := by
  refine ⟨MarkovKernels.ofFactor chain chainFactor chainFactor_nonneg chainFactor_sum,
    fun y => ?_⟩
  simp only [MarkovKernels.factor_ofFactor chain chainFactor chainFactor_nonneg chainFactor_sum
    chainFactor_congr, Fin.prod_univ_three]
  change ofWeights chainWeight _ y = _
  rw [ofWeights_apply, chainWeight_sum]
  have h : ((2 * chainWeight y : ℕ) : ℝ) = ((chainKernelWeight 0 y * chainKernelWeight 1 y *
      chainKernelWeight 2 y : ℕ) : ℝ) := by rw [chainWeight_eq]
  push_cast at h
  simp only [chainFactor]
  linear_combination h / 64

theorem chainLaw_pos (y : Fin 3 → Bool) : 0 < chainLaw y :=
  ofWeights_pos _ _ (by decide) y

/-- The noisy copy law is Markov to the chain. -/
theorem chainLaw_globalMarkov : chain.GlobalMarkov chainLaw :=
  chainLaw_factorizes.globalMarkov (by decide)

/-- Every d-connection of two distinct vertices of the chain is witnessed by a failure of the
cylinder identity for the chain weights. -/
theorem chain_dependence_witness : ∀ x y : Fin 3, ∀ Z : Finset (Fin 3), x ∉ Z → y ∉ Z →
    x ≠ y → ¬ chain.DSep {x} {y} ↑Z → ∃ c : Fin 3 → Bool,
      (∑ y ∈ agreeOn ({x} ∪ {y} ∪ Z) c, chainWeight y) * (∑ y ∈ agreeOn Z c, chainWeight y) ≠
        (∑ y ∈ agreeOn ({x} ∪ Z) c, chainWeight y) *
          (∑ y ∈ agreeOn ({y} ∪ Z) c, chainWeight y) := by
  decide

/-- **A faithful law for the chain.** The noisy copy law is faithful to `0 → 1 → 2`. -/
theorem chainLaw_isFaithful : chainLaw.IsFaithful chain := by
  refine isFaithful_iff_forall_singleton.2 fun x y Z hx hy hci => ?_
  by_contra hd
  by_cases hxy : x = y
  · subst hxy
    exact not_condIndep_self_of_pos chainLaw_pos hx hci
  · obtain ⟨c, hc⟩ := chain_dependence_witness x y Z hx hy hxy hd
    exact not_condIndep_ofWeights _ _ c hc hci

/-! #### The collider -/

/-- Weights of a noisy collider on `0 → 2 ← 1`: `0` and `1` are fair bits and `2` is true with
probability `(1 + y 0 + y 1) / 4`. The total weight is `16`. -/
def colliderWeight (y : Fin 3 → Bool) : ℕ :=
  if y 2 then 1 + (y 0).toNat + (y 1).toNat else 3 - (y 0).toNat - (y 1).toNat

theorem colliderWeight_sum : ∑ y, colliderWeight y = 16 := by decide

/-- The noisy collider law. -/
noncomputable def colliderLaw : FiniteDist (Fin 3 → Bool) :=
  ofWeights colliderWeight (by rw [colliderWeight_sum]; decide)

/-- The factors of the noisy collider law. -/
noncomputable def colliderFactor (v : Fin 3) (c : Fin 3 → Bool) : ℝ :=
  if v = 2 then (colliderWeight c : ℝ) / 4 else 1 / 2

theorem colliderFactor_nonneg (v : Fin 3) (c : Fin 3 → Bool) : 0 ≤ colliderFactor v c := by
  unfold colliderFactor
  split_ifs <;> positivity

theorem colliderWeight_update (c : Fin 3 → Bool) :
    colliderWeight (Function.update c 2 true) + colliderWeight (Function.update c 2 false) = 4 :=
  by revert c; decide

theorem colliderFactor_sum (v : Fin 3) (c : Fin 3 → Bool) :
    ∑ b : Bool, colliderFactor v (Function.update c v b) = 1 := by
  rw [Fintype.sum_bool]
  by_cases hv : v = 2
  · subst hv
    simp only [colliderFactor, ↓reduceIte]
    rw [← add_div, ← Nat.cast_add, colliderWeight_update]
    norm_num
  · simp only [colliderFactor, hv, ↓reduceIte]
    norm_num

theorem colliderFactor_congr (v : Fin 3) (c c' : Fin 3 → Bool)
    (h : ∀ u, u = v ∨ collider.Adj u v → c u = c' u) :
    colliderFactor v c = colliderFactor v c' := by
  fin_cases v
  · rfl
  · rfl
  · have h2 : c 2 = c' 2 := h 2 (Or.inl rfl)
    have h0 : c 0 = c' 0 := h 0 (Or.inr (by decide))
    have h1 : c 1 = c' 1 := h 1 (Or.inr (by decide))
    simp [colliderFactor, colliderWeight, h0, h1, h2]

/-- The noisy collider law factorizes according to the collider. -/
theorem colliderLaw_factorizes : collider.Factorizes colliderLaw := by
  refine ⟨MarkovKernels.ofFactor collider colliderFactor colliderFactor_nonneg colliderFactor_sum,
    fun y => ?_⟩
  simp only [MarkovKernels.factor_ofFactor collider colliderFactor colliderFactor_nonneg
    colliderFactor_sum colliderFactor_congr, Fin.prod_univ_three]
  change ofWeights colliderWeight _ y = _
  rw [ofWeights_apply, colliderWeight_sum]
  simp only [colliderFactor, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    ↓reduceIte]
  push_cast
  ring

theorem colliderLaw_pos (y : Fin 3 → Bool) : 0 < colliderLaw y :=
  ofWeights_pos _ _ (by decide) y

/-- The noisy collider law is Markov to the collider. -/
theorem colliderLaw_globalMarkov : collider.GlobalMarkov colliderLaw :=
  colliderLaw_factorizes.globalMarkov (by decide)

/-- Every d-connection of two distinct vertices of the collider is witnessed by a failure of the
cylinder identity for the collider weights. -/
theorem collider_dependence_witness : ∀ x y : Fin 3, ∀ Z : Finset (Fin 3), x ∉ Z → y ∉ Z →
    x ≠ y → ¬ collider.DSep {x} {y} ↑Z → ∃ c : Fin 3 → Bool,
      (∑ y ∈ agreeOn ({x} ∪ {y} ∪ Z) c, colliderWeight y) *
          (∑ y ∈ agreeOn Z c, colliderWeight y) ≠
        (∑ y ∈ agreeOn ({x} ∪ Z) c, colliderWeight y) *
          (∑ y ∈ agreeOn ({y} ∪ Z) c, colliderWeight y) := by
  decide

/-- **A faithful law for the collider.** The noisy collider law is faithful to `0 → 2 ← 1`. -/
theorem colliderLaw_isFaithful : colliderLaw.IsFaithful collider := by
  refine isFaithful_iff_forall_singleton.2 fun x y Z hx hy hci => ?_
  by_contra hd
  by_cases hxy : x = y
  · subst hxy
    exact not_condIndep_self_of_pos colliderLaw_pos hx hci
  · obtain ⟨c, hc⟩ := collider_dependence_witness x y Z hx hy hxy hd
    exact not_condIndep_ofWeights _ _ c hc hci

end CausalInference.GraphExamples
