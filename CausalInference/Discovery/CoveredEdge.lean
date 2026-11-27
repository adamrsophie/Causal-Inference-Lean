/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.MarkovEquivalence
public import CausalInference.Graphical.GlobalMarkovCompleteness

/-!
# Covered edge reversal

An edge `x → y` of a directed graph is *covered* when the parents of `y` are exactly `x` and the
parents of `x`. Reversing a covered edge of an acyclic graph gives an acyclic graph with the same
skeleton, the same v-structures, and the same d-separation relation (Chickering 1995).

The d-separation statement is proved through distributions. A distribution over binary variables
that factorizes according to `G` also factorizes according to the reversed graph: the two
kernels of `x` and `y` are replaced by the marginal kernel of `y` given the common parents and
the conditional kernel of `x` given `y` and the common parents (Bayes' rule, with an arbitrary
kernel where the conditioning event has mass zero). Since d-separation is the conditional
independence shared by all such distributions
(`Digraph.dSep_iff_forall_factorizes_condIndep'`), the d-separation relations agree.

## Main definitions

* `Digraph.IsCovered G x y`: `x → y` is an edge and `G.Adj u y ↔ u = x ∨ G.Adj u x`.
* `Digraph.reverseEdge G x y`: `G` with the edge `x → y` replaced by `y → x`.
* `Digraph.MarkovKernels.ofFactor`: Markov kernels over binary variables built from factors on
  full configurations.

## Main results

* `Digraph.IsCovered.isAcyclic_reverseEdge`, `Digraph.IsCovered.reverseEdge`,
  `Digraph.reverseEdge_reverseEdge`, `Digraph.skeleton_reverseEdge`,
  `Digraph.IsCovered.isVStructure_reverseEdge_iff`: the graph facts.
* `Digraph.IsCovered.factorizes_reverseEdge`: factorization transfers to the reversed graph.
* `Digraph.IsCovered.dSep_reverseEdge_iff`, `Digraph.IsCovered.markovEquivalent_reverseEdge`:
  **reversing a covered edge preserves d-separation**.

## References

* D. M. Chickering (1995), *A transformational characterization of equivalent Bayesian network
  structures*.
-/

@[expose] public section

namespace Digraph

open CausalInference Finset

variable {V : Type*}

/-- The edge `x → y` of `G` is covered: it is an edge, and the parents of `y` are `x` together
with the parents of `x`. -/
def IsCovered (G : Digraph V) (x y : V) : Prop :=
  G.Adj x y ∧ ∀ u, G.Adj u y ↔ u = x ∨ G.Adj u x

/-- The graph `G` with the edge `x → y` replaced by the edge `y → x`. -/
def reverseEdge (G : Digraph V) (x y : V) : Digraph V where
  Adj u v := (G.Adj u v ∧ ¬ (u = x ∧ v = y)) ∨ (u = y ∧ v = x)

variable {G : Digraph V} {x y u v a b c : V}

@[simp] theorem reverseEdge_adj :
    (G.reverseEdge x y).Adj u v ↔ (G.Adj u v ∧ ¬ (u = x ∧ v = y)) ∨ (u = y ∧ v = x) :=
  Iff.rfl

/-! ### Graph facts -/

theorem IsCovered.ne (hG : G.IsAcyclic) (hc : G.IsCovered x y) : x ≠ y :=
  hG.ne_of_adj hc.1

theorem IsCovered.not_adj_symm (hG : G.IsAcyclic) (hc : G.IsCovered x y) : ¬ G.Adj y x :=
  hG.asymm hc.1

/-- A parent of `x` is a parent of `y`. -/
theorem IsCovered.adj_of_adj (hc : G.IsCovered x y) (h : G.Adj u x) : G.Adj u y :=
  (hc.2 u).2 (Or.inr h)

/-- A parent of `y` other than `x` is a parent of `x`. -/
theorem IsCovered.adj_of_adj_of_ne (hc : G.IsCovered x y) (h : G.Adj u y) (hu : u ≠ x) :
    G.Adj u x :=
  ((hc.2 u).1 h).resolve_left hu

/-- Reversing the reversed edge restores the graph. -/
theorem reverseEdge_reverseEdge (hxy : G.Adj x y) (hyx : ¬ G.Adj y x) :
    (G.reverseEdge x y).reverseEdge y x = G := by
  have hne : x ≠ y := fun h => hyx (h ▸ h ▸ hxy)
  ext u v
  simp only [reverseEdge_adj]
  by_cases h1 : u = x ∧ v = y
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hxy, hne]
  · by_cases h2 : u = y ∧ v = x
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hyx, hne]
    · simp [h1, h2]

/-- After the reversal, the edge `y → x` is covered. -/
theorem IsCovered.reverseEdge (hG : G.IsAcyclic) (hc : G.IsCovered x y) :
    (G.reverseEdge x y).IsCovered y x := by
  have hxy := hc.ne hG
  refine ⟨Or.inr ⟨rfl, rfl⟩, fun u => ?_⟩
  rw [reverseEdge_adj, reverseEdge_adj]
  constructor
  · rintro (⟨h, -⟩ | ⟨rfl, -⟩)
    · by_cases hu : u = x
      · exact absurd (hu ▸ h) (hG.irrefl x)
      · exact Or.inr (Or.inl ⟨hc.adj_of_adj h, fun h' => hu h'.1⟩)
    · exact Or.inl rfl
  · rintro (rfl | ⟨h, hn⟩ | ⟨rfl, h⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨hc.adj_of_adj_of_ne h fun hu => hn ⟨hu, rfl⟩, fun h' => hxy h'.2⟩
    · exact absurd h.symm hxy

/-- Reversing a covered edge of an acyclic graph gives an acyclic graph. With a topological order
`f` of `G`, the labels `2 f v + 1` for `v ≠ y` and `2 f x` for `y` increase along the edges of the
reversed graph. -/
theorem IsCovered.isAcyclic_reverseEdge (hG : G.IsAcyclic) (hc : G.IsCovered x y) [Finite V] :
    (G.reverseEdge x y).IsAcyclic := by
  classical
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  have hxy := hc.ne hG
  let g : V → ℕ := fun v => if v = y then 2 * f x else 2 * f v + 1
  refine isAcyclic_of_adj_lt g fun u v huv => ?_
  rcases huv with ⟨h, hn⟩ | ⟨rfl, rfl⟩
  · by_cases hv : v = y
    · subst hv
      have hu : u ≠ x := fun hu => hn ⟨hu, rfl⟩
      have hux := hf (hc.adj_of_adj_of_ne h hu)
      have huy : u ≠ v := hG.ne_of_adj h
      simp only [g, huy, ↓reduceIte]
      omega
    · by_cases hu : u = y
      · subst hu
        have h1 := hf hc.1
        have h2 := hf h
        simp only [g, hv, ↓reduceIte]
        omega
      · have h1 := hf h
        simp only [g, hu, hv, ↓reduceIte]
        omega
  · simp only [g, hxy, ↓reduceIte]
    omega

/-- Reversing an edge does not change the skeleton. -/
theorem skeleton_reverseEdge (hxy : G.Adj x y) : (G.reverseEdge x y).skeleton = G.skeleton := by
  ext u v
  simp only [skeleton_adj, reverseEdge_adj]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ((⟨h, -⟩ | ⟨rfl, rfl⟩) | (⟨h, -⟩ | ⟨rfl, rfl⟩))
    · exact Or.inl h
    · exact Or.inr hxy
    · exact Or.inr h
    · exact Or.inl hxy
  · rintro (h | h)
    · by_cases h1 : u = x ∧ v = y
      · obtain ⟨rfl, rfl⟩ := h1
        exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inl ⟨h, h1⟩)
    · by_cases h1 : v = x ∧ u = y
      · obtain ⟨rfl, rfl⟩ := h1
        exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨h, h1⟩)

/-- Every v-structure of `G` is a v-structure after reversing a covered edge. -/
theorem IsCovered.isVStructure_reverseEdge (hc : G.IsCovered x y)
    (h : G.IsVStructure a c b) : (G.reverseEdge x y).IsVStructure a c b := by
  obtain ⟨hac, hbc, hab, hnab, hnba⟩ := h
  refine ⟨Or.inl ⟨hac, ?_⟩, Or.inl ⟨hbc, ?_⟩, hab, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    exact hnba (hc.adj_of_adj_of_ne hbc hab.symm)
  · rintro ⟨rfl, rfl⟩
    exact hnab (hc.adj_of_adj_of_ne hac hab)
  · rintro (⟨h, -⟩ | ⟨rfl, rfl⟩)
    · exact hnab h
    · exact hnba hc.1
  · rintro (⟨h, -⟩ | ⟨rfl, rfl⟩)
    · exact hnba h
    · exact hnab hc.1

/-- Reversing a covered edge of an acyclic graph preserves the v-structures. -/
theorem IsCovered.isVStructure_reverseEdge_iff (hG : G.IsAcyclic) (hc : G.IsCovered x y) :
    (G.reverseEdge x y).IsVStructure a c b ↔ G.IsVStructure a c b := by
  refine ⟨fun h => ?_, hc.isVStructure_reverseEdge⟩
  have h' := (hc.reverseEdge hG).isVStructure_reverseEdge h
  rwa [reverseEdge_reverseEdge hc.1 (hc.not_adj_symm hG)] at h'

/-! ### Markov kernels from factors -/

namespace MarkovKernels

variable [Fintype V] [DecidableEq V]

/-- Extend a configuration of the parents of `v` to a full configuration over binary variables,
with the value `false` off the parents. -/
def extendParents (H : Digraph V) [DecidableRel H.Adj] (v : V)
    (z : ∀ _ : H.parentsFinset v, Bool) : V → Bool :=
  fun w => if h : w ∈ H.parentsFinset v then z ⟨w, h⟩ else false

/-- Markov kernels over binary variables from factors `F v` on full configurations: the kernel of
`v` at a parent configuration `z` and value `a` is `F v` at the configuration that agrees with `z`
on the parents, has value `a` at `v`, and is `false` elsewhere. The factors must be nonnegative
and sum to one over the values of `v`. -/
def ofFactor (H : Digraph V) [DecidableRel H.Adj] (F : V → (V → Bool) → ℝ)
    (hnn : ∀ v x, 0 ≤ F v x) (hsum : ∀ v x, ∑ b : Bool, F v (Function.update x v b) = 1) :
    H.MarkovKernels (fun _ => Bool) where
  kernel v z a := F v (Function.update (extendParents H v z) v a)
  nonneg _ _ _ := hnn _ _
  sum_eq_one v _ := hsum v _

/-- If each factor `F v` depends only on `v` and its parents in `H`, the factors of the kernels
`ofFactor` are the given factors. -/
theorem factor_ofFactor (H : Digraph V) [DecidableRel H.Adj] (F : V → (V → Bool) → ℝ)
    (hnn : ∀ v x, 0 ≤ F v x) (hsum : ∀ v x, ∑ b : Bool, F v (Function.update x v b) = 1)
    (hdep : ∀ v x x', (∀ u, u = v ∨ H.Adj u v → x u = x' u) → F v x = F v x')
    (v : V) (x : V → Bool) : (ofFactor H F hnn hsum).factor v x = F v x := by
  change F v (Function.update (extendParents H v _) v (x v)) = F v x
  refine hdep v _ _ fun u hu => ?_
  by_cases huv : u = v
  · subst huv
    simp
  · have hu' : H.Adj u v := hu.resolve_left huv
    simp [Function.update_of_ne huv, extendParents, mem_parentsFinset.2 hu', Finset.restrict]

end MarkovKernels

/-! ### Factorization after a covered edge reversal -/

section Factorization

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (k : G.MarkovKernels (fun _ => Bool))

/-- The marginal factor of `y` after summing out `x`:
`∑ a, kernel_x(a | pa x) * kernel_y(y | a, pa x)`. -/
noncomputable def coveredFy (x y : V) (c : V → Bool) : ℝ :=
  ∑ a : Bool, k.factor x (Function.update c x a) * k.factor y (Function.update c x a)

/-- The conditional factor of `x` given `y` and the parents of `x`, by Bayes' rule; where the
conditioning mass vanishes it is the old factor of `x`. -/
noncomputable def coveredFx (x y : V) (c : V → Bool) : ℝ :=
  if 0 < coveredFy k x y c then k.factor x c * k.factor y c / coveredFy k x y c
  else k.factor x c

/-- The factors of the reversed graph. -/
noncomputable def coveredF (x y : V) (v : V) : (V → Bool) → ℝ :=
  if v = x then coveredFx k x y else if v = y then coveredFy k x y else k.factor v

theorem coveredFy_nonneg (c : V → Bool) : 0 ≤ coveredFy k x y c :=
  sum_nonneg fun _ _ => mul_nonneg (k.factor_nonneg _ _) (k.factor_nonneg _ _)

theorem coveredFx_nonneg (c : V → Bool) : 0 ≤ coveredFx k x y c := by
  unfold coveredFx
  split_ifs with h
  · exact div_nonneg (mul_nonneg (k.factor_nonneg _ _) (k.factor_nonneg _ _)) h.le
  · exact k.factor_nonneg _ _

variable {k}

/-- The marginal factor of `y` depends only on `y` and the parents of `x`. -/
theorem IsCovered.coveredFy_congr (hc : G.IsCovered x y) (hG : G.IsAcyclic) {c c' : V → Bool}
    (h : ∀ u, u = y ∨ (G.Adj u y ∧ u ≠ x) → c u = c' u) :
    coveredFy k x y c = coveredFy k x y c' := by
  have hxy := hc.ne hG
  refine sum_congr rfl fun a _ => ?_
  congr 1
  · refine k.factor_congr fun u hu => ?_
    by_cases hux : u = x
    · subst hux
      simp
    · rw [Function.update_of_ne hux, Function.update_of_ne hux]
      exact h u (Or.inr ⟨hc.adj_of_adj (hu.resolve_left hux), hux⟩)
  · refine k.factor_congr fun u hu => ?_
    by_cases hux : u = x
    · subst hux
      simp
    · rw [Function.update_of_ne hux, Function.update_of_ne hux]
      rcases hu with rfl | hu
      · exact h u (Or.inl rfl)
      · exact h u (Or.inr ⟨hu, hux⟩)

/-- The marginal factor of `y` does not depend on the value of `x`. -/
theorem IsCovered.coveredFy_update (hc : G.IsCovered x y) (hG : G.IsAcyclic) (c : V → Bool)
    (a : Bool) : coveredFy k x y (Function.update c x a) = coveredFy k x y c := by
  have hxy := hc.ne hG
  refine hc.coveredFy_congr hG fun u hu => Function.update_of_ne ?_ _ _
  rintro rfl
  rcases hu with h | ⟨-, h⟩
  · exact hxy h
  · exact h rfl

/-- The new factors of `x` and `y` multiply to the old ones. -/
theorem coveredFx_mul_coveredFy (c : V → Bool) :
    coveredFx k x y c * coveredFy k x y c = k.factor x c * k.factor y c := by
  unfold coveredFx
  split_ifs with h
  · field_simp
  · have h0 : coveredFy k x y c = 0 := le_antisymm (not_lt.1 h) (coveredFy_nonneg k c)
    have hle : k.factor x c * k.factor y c ≤ coveredFy k x y c := by
      have := single_le_sum (f := fun a : Bool =>
        k.factor x (Function.update c x a) * k.factor y (Function.update c x a))
        (fun a _ => mul_nonneg (k.factor_nonneg _ _) (k.factor_nonneg _ _)) (mem_univ (c x))
      simp only [Function.update_eq_self] at this
      exact this
    have hp : k.factor x c * k.factor y c = 0 :=
      le_antisymm (h0 ▸ hle) (mul_nonneg (k.factor_nonneg _ _) (k.factor_nonneg _ _))
    rw [h0, hp, mul_zero]

/-- The marginal factor of `y` sums to one over the values of `y`. -/
theorem IsCovered.sum_coveredFy (hc : G.IsCovered x y) (hG : G.IsAcyclic) (c : V → Bool) :
    ∑ b : Bool, coveredFy k x y (Function.update c y b) = 1 := by
  have hxy := hc.ne hG
  unfold coveredFy
  have hupd : ∀ a b : Bool, Function.update (Function.update c y b) x a =
      Function.update (Function.update c x a) y b := fun a b =>
    Function.update_comm hxy.symm b a c
  simp_rw [hupd]
  rw [sum_comm]
  simp_rw [k.factor_update_of_not_adj hxy.symm (hc.not_adj_symm hG), ← mul_sum,
    k.sum_factor_update_eq_one (hG.irrefl y), mul_one]
  exact k.sum_factor_update_eq_one (hG.irrefl x) c

/-- The conditional factor of `x` sums to one over the values of `x`. -/
theorem IsCovered.sum_coveredFx (hc : G.IsCovered x y) (hG : G.IsAcyclic) (c : V → Bool) :
    ∑ a : Bool, coveredFx k x y (Function.update c x a) = 1 := by
  unfold coveredFx
  simp_rw [hc.coveredFy_update hG]
  by_cases hpos : 0 < coveredFy k x y c
  · simp only [hpos, ↓reduceIte]
    rw [← sum_div]
    exact div_self hpos.ne'
  · simp only [hpos, ↓reduceIte]
    exact k.sum_factor_update_eq_one (hG.irrefl x) c

theorem coveredF_nonneg (v : V) (c : V → Bool) : 0 ≤ coveredF k x y v c := by
  unfold coveredF
  split_ifs
  · exact coveredFx_nonneg k c
  · exact coveredFy_nonneg k c
  · exact k.factor_nonneg _ _

theorem IsCovered.sum_coveredF (hc : G.IsCovered x y) (hG : G.IsAcyclic) (v : V)
    (c : V → Bool) : ∑ b : Bool, coveredF k x y v (Function.update c v b) = 1 := by
  unfold coveredF
  split_ifs with h1 h2
  · subst h1
    exact hc.sum_coveredFx hG c
  · subst h2
    exact hc.sum_coveredFy hG c
  · exact k.sum_factor_update_eq_one (hG.irrefl v) c

/-- The factors of the reversed graph depend only on each vertex and its parents in the reversed
graph. -/
theorem IsCovered.coveredF_congr (hc : G.IsCovered x y) (hG : G.IsAcyclic) (v : V)
    {c c' : V → Bool} (h : ∀ u, u = v ∨ (G.reverseEdge x y).Adj u v → c u = c' u) :
    coveredF k x y v c = coveredF k x y v c' := by
  have hxy := hc.ne hG
  unfold coveredF
  split_ifs with h1 h2
  · subst h1
    have hx : ∀ u, u = v ∨ G.Adj u v → c u = c' u := fun u hu => h u (by
      rcases hu with rfl | hu
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hu, fun h' => hxy h'.2⟩))
    have hy : c y = c' y := h y (Or.inr (Or.inr ⟨rfl, rfl⟩))
    have hfx : k.factor v c = k.factor v c' := k.factor_congr hx
    have hfy : k.factor y c = k.factor y c' := k.factor_congr fun u hu => by
      rcases hu with rfl | hu
      · exact hy
      · rcases (hc.2 u).1 hu with rfl | hu
        · exact hx _ (Or.inl rfl)
        · exact hx u (Or.inr hu)
    have hFy : coveredFy k v y c = coveredFy k v y c' := hc.coveredFy_congr hG fun u hu => by
      rcases hu with rfl | ⟨hu, hux⟩
      · exact hy
      · exact hx u (Or.inr (hc.adj_of_adj_of_ne hu hux))
    unfold coveredFx
    rw [hfx, hfy, hFy]
  · subst h2
    exact hc.coveredFy_congr hG fun u hu => by
      rcases hu with rfl | ⟨hu, hux⟩
      · exact h _ (Or.inl rfl)
      · exact h u (Or.inr (Or.inl ⟨hu, fun h' => hux h'.1⟩))
  · refine k.factor_congr fun u hu => h u ?_
    rcases hu with rfl | hu
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hu, fun h' => h2 h'.2⟩)

/-- The product of the new factors is the product of the old ones. -/
theorem IsCovered.prod_coveredF (hc : G.IsCovered x y) (hG : G.IsAcyclic) (c : V → Bool) :
    ∏ v, coveredF k x y v c = ∏ v, k.factor v c := by
  have hxy := hc.ne hG
  have hy : y ∈ (univ : Finset V).erase x := mem_erase.2 ⟨hxy.symm, mem_univ y⟩
  have split : ∀ g : V → ℝ, ∏ v, g v = g x * (g y * ∏ v ∈ (univ.erase x).erase y, g v) := by
    intro g
    rw [mul_prod_erase _ _ hy, mul_prod_erase _ _ (mem_univ x)]
  rw [split, split (fun v => k.factor v c), ← mul_assoc, ← mul_assoc]
  congr 1
  · simp only [coveredF, ↓reduceIte, hxy.symm]
    exact coveredFx_mul_coveredFy c
  · refine prod_congr rfl fun v hv => ?_
    obtain ⟨hvy, hv'⟩ := mem_erase.1 hv
    obtain ⟨hvx, -⟩ := mem_erase.1 hv'
    simp [coveredF, hvx, hvy]

end Factorization

/-- **Factorization survives a covered edge reversal.** If a distribution over binary variables
factorizes according to an acyclic graph `G` and `x → y` is covered, it factorizes according to
the graph with `x → y` reversed. -/
theorem IsCovered.factorizes_reverseEdge [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableRel (G.reverseEdge x y).Adj] (hc : G.IsCovered x y) (hG : G.IsAcyclic)
    {p : FiniteDist (V → Bool)} (hp : G.Factorizes p) : (G.reverseEdge x y).Factorizes p := by
  obtain ⟨k, hk⟩ := hp
  refine ⟨MarkovKernels.ofFactor _ (coveredF k x y) (coveredF_nonneg (k := k))
    (hc.sum_coveredF hG), fun c => ?_⟩
  rw [hk c, ← hc.prod_coveredF hG c]
  refine prod_congr rfl fun v _ => ?_
  rw [MarkovKernels.factor_ofFactor]
  exact fun v c c' h => hc.coveredF_congr hG v h

/-- Factorization does not depend on the decidability instance of the adjacency relation. -/
theorem factorizes_of_eq [Fintype V] [DecidableEq V] {G H : Digraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hGH : G = H) {p : FiniteDist (V → Bool)} (hp : G.Factorizes p) :
    H.Factorizes p := by
  subst hGH
  convert hp

/-- **Reversing a covered edge preserves d-separation.** For an acyclic graph `G` on a finite
vertex type with a covered edge `x → y`, the graph with `x → y` reversed has the same
d-separation relation (Chickering 1995). -/
theorem IsCovered.dSep_reverseEdge_iff [Finite V] (hc : G.IsCovered x y) (hG : G.IsAcyclic)
    {X Y Z : Set V} : (G.reverseEdge x y).DSep X Y Z ↔ G.DSep X Y Z := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨X, rfl⟩ : ∃ X' : Finset V, (X' : Set V) = X := ⟨X.toFinset, Set.coe_toFinset X⟩
  obtain ⟨Y, rfl⟩ : ∃ Y' : Finset V, (Y' : Set V) = Y := ⟨Y.toFinset, Set.coe_toFinset Y⟩
  obtain ⟨Z, rfl⟩ : ∃ Z' : Finset V, (Z' : Set V) = Z := ⟨Z.toFinset, Set.coe_toFinset Z⟩
  have hG' := hc.isAcyclic_reverseEdge hG
  rw [dSep_iff_forall_factorizes_condIndep' hG', dSep_iff_forall_factorizes_condIndep' hG]
  refine ⟨fun h p hp => h p (hc.factorizes_reverseEdge hG hp), fun h p hp => h p ?_⟩
  exact factorizes_of_eq (reverseEdge_reverseEdge hc.1 (hc.not_adj_symm hG))
    ((hc.reverseEdge hG).factorizes_reverseEdge hG' hp)

/-- Reversing a covered edge of a finite acyclic graph gives a Markov equivalent graph. -/
theorem IsCovered.markovEquivalent_reverseEdge [Finite V] (hc : G.IsCovered x y)
    (hG : G.IsAcyclic) : MarkovEquivalent G (G.reverseEdge x y) :=
  fun _ _ _ => (hc.dSep_reverseEdge_iff hG).symm

end Digraph
