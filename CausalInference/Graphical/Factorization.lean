/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.FiniteCondIndep
public import CausalInference.Graphical.Mutilation

/-!
# Markov factorization along a directed graph

Finite variables indexed by the vertices of a `Digraph V`, with a Markov kernel for each vertex
given its parents, and distributions that factorize as the product of these kernels.

## Main definitions

* `Digraph.MarkovKernels G α`: for each vertex `v`, a conditional mass function
  `kernel v : (∀ u : G.parentsFinset v, α u) → α v → ℝ`, nonnegative and summing to one over
  `α v` for every configuration of the parents.
* `Digraph.MarkovKernels.factor k v x`: the factor of `v` at the full configuration `x`, and
  `Digraph.MarkovKernels.prodOn k S x`: the product of the factors of the vertices in `S`.
* `Digraph.MarkovKernels.jointDist k hG`: for acyclic `G`, the product of the kernels as a
  finite distribution.
* `Digraph.Factorizes G p`: `p x = ∏ v, kernel v (x restricted to the parents of v) (x v)` for
  some family of kernels.

## Main results

* `Digraph.MarkovKernels.sum_update_prodOn`: summing out a sink. If `s ∈ S` has no child in `S`,
  summing the product over `S` over the values of `x s` gives the product over `S.erase s`.
* `Digraph.MarkovKernels.sum_agreeOn_prodOn`: the iterated version for an acyclic graph. If `T`
  is closed under children inside `S ⊇ T`, summing the product over `S` over the coordinates in
  `T` gives the product over `S \ T`.
* `Digraph.MarkovKernels.sum_prodOn_univ`: for acyclic `G`, the product of the kernels sums to
  one.
* `Digraph.MarkovKernels.margAt_of_ancestral`: the marginal of a factorizing distribution on an
  ancestral set `A` is the product of the kernels of the vertices of `A`.
* `Digraph.MarkovKernels.margAt_insert_parents`: the kernel of `v` is the conditional
  distribution of `x v` given its parents, in product form
  `p(x_v, x_pa) = kernel v x_pa x_v * p(x_pa)`.

Sources: Lauritzen (1996), Graphical Models, chapter 3; Pearl (1988); Pearl (2009), Causality,
section 1.2.
-/

@[expose] public section

namespace CausalInference

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

namespace FiniteDist

/-- Lifting a product decomposition of a marginal to smaller sets. Suppose `A ⊆ B`, `v ∉ B`, and
`p(x_{B ∪ {v}}) = f x * p(x_B)` for all `x`, where `f` depends only on the coordinates in
`A ∪ {v}`. Then `p(x_{A ∪ {v}}) = f x * p(x_A)`. -/
theorem margAt_insert_of_margAt_insert (p : FiniteDist (∀ v, α v)) {A B : Finset V} {v : V}
    (hAB : A ⊆ B) (hvB : v ∉ B) (f : (∀ v, α v) → ℝ)
    (hf : ∀ y y', (∀ u ∈ insert v A, y u = y' u) → f y = f y')
    (h : ∀ y, p.margAt (insert v B) y = f y * p.margAt B y) (x : ∀ v, α v) :
    p.margAt (insert v A) x = f x * p.margAt A x := by
  have hset : insert v B \ insert v A = B \ A := by
    ext u
    simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h3 => h2 (Or.inr h3)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, fun h3 => h3.elim (fun h4 => hvB (h4 ▸ h1)) h2⟩
  rw [margAt_eq_sum_margAt p (insert_subset_insert v hAB) x, margAt_eq_sum_margAt p hAB x,
    hset, mul_sum]
  refine sum_congr rfl fun y hy => ?_
  rw [h y, hf y x fun u hu => (mem_agreeOn.1 hy) u ?_]
  simp only [mem_compl, mem_sdiff, not_and, not_not]
  intro huB
  rcases mem_insert.1 hu with rfl | huA
  · exact absurd huB hvB
  · exact huA

/-- Splitting off one coordinate `s ∈ T` from a sum over the configurations that agree with `x`
outside `T`. -/
theorem sum_agreeOn_compl_eq_sum_update {M : Type*} [AddCommMonoid M] (F : (∀ v, α v) → M)
    {T : Finset V} {s : V} (hs : s ∈ T) (x : ∀ v, α v) :
    ∑ y ∈ FiniteDist.agreeOn Tᶜ x, F y =
      ∑ y ∈ FiniteDist.agreeOn (T.erase s)ᶜ x, ∑ a : α s, F (Function.update y s a) := by
  rw [← sum_fiberwise_of_maps_to (s := FiniteDist.agreeOn Tᶜ x)
    (t := FiniteDist.agreeOn (T.erase s)ᶜ x) (g := fun y => Function.update y s (x s)) ?_]
  · refine sum_congr rfl fun y' hy' => ?_
    rw [← FiniteDist.sum_agreeOn_compl_singleton F s y']
    refine sum_congr ?_ fun _ _ => rfl
    simp only [FiniteDist.mem_agreeOn, mem_compl, mem_erase, not_and] at hy' ⊢
    ext y
    simp only [mem_filter, FiniteDist.mem_agreeOn, mem_compl, mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩ v hv
      simp [Function.update_of_ne hv]
    · intro hy
      refine ⟨fun v hv => ?_, funext fun v => ?_⟩
      · have hvs : v ≠ s := fun h => hv (h ▸ hs)
        rw [hy v hvs, hy' v fun _ => hv]
      · by_cases hvs : v = s
        · subst hvs
          simp only [Function.update_self]
          exact (hy' v fun h => absurd rfl h).symm
        · simp [Function.update_of_ne hvs, hy v hvs]
  · intro y hy
    simp only [FiniteDist.mem_agreeOn, mem_compl, mem_erase, not_and] at hy ⊢
    intro v hv
    by_cases hvs : v = s
    · subst hvs
      simp
    · rw [Function.update_of_ne hvs]
      exact hy v fun h => hv hvs h

end FiniteDist

end CausalInference

namespace Digraph

open CausalInference Finset

variable {V : Type*} [Fintype V] {α : V → Type*} [∀ v, Fintype (α v)]

/-- Markov kernels for the vertices of `G`: for each vertex `v` and each configuration of its
parents, a probability mass function on the values of `v`. -/
structure MarkovKernels (G : Digraph V) [DecidableRel G.Adj] (α : V → Type*)
    [∀ v, Fintype (α v)] where
  /-- The conditional mass of the value `a` of `v` given the parent configuration `z`. -/
  kernel : ∀ v, (∀ u : G.parentsFinset v, α u) → α v → ℝ
  /-- Conditional masses are nonnegative. -/
  nonneg : ∀ v z a, 0 ≤ kernel v z a
  /-- Conditional masses sum to one for every parent configuration. -/
  sum_eq_one : ∀ v z, ∑ a, kernel v z a = 1

namespace MarkovKernels

variable {G : Digraph V} [DecidableRel G.Adj] (k : G.MarkovKernels α)

/-- The factor of `v` at the full configuration `x`: the kernel of `v` evaluated at the parent
configuration of `x` and the value `x v`. -/
def factor (v : V) (x : ∀ v, α v) : ℝ :=
  k.kernel v ((G.parentsFinset v).restrict x) (x v)

/-- The product of the factors of the vertices in `S` at the configuration `x`. -/
def prodOn (S : Finset V) (x : ∀ v, α v) : ℝ := ∏ v ∈ S, k.factor v x

theorem factor_nonneg (v : V) (x : ∀ v, α v) : 0 ≤ k.factor v x := k.nonneg _ _ _

theorem prodOn_nonneg (S : Finset V) (x : ∀ v, α v) : 0 ≤ k.prodOn S x :=
  prod_nonneg fun v _ => k.factor_nonneg v x

@[simp] theorem prodOn_empty (x : ∀ v, α v) : k.prodOn ∅ x = 1 := prod_empty

/-- The factor of `v` depends only on the coordinates of `v` and of its parents. -/
theorem factor_congr {v : V} {x y : ∀ v, α v} (h : ∀ u, u = v ∨ G.Adj u v → x u = y u) :
    k.factor v x = k.factor v y := by
  unfold factor
  rw [h v (Or.inl rfl)]
  congr 1
  funext u
  exact h u (Or.inr (mem_parentsFinset.1 u.2))

/-- Changing the value of a vertex `s` that is neither `v` nor a parent of `v` does not change the
factor of `v`. -/
theorem factor_update_of_not_adj [DecidableEq V] {s v : V} (hsv : s ≠ v) (hadj : ¬ G.Adj s v)
    (x : ∀ v, α v) (a : α s) : k.factor v (Function.update x s a) = k.factor v x := by
  refine k.factor_congr fun u hu => ?_
  have : u ≠ s := by
    rintro rfl
    rcases hu with h | h
    · exact hsv h
    · exact hadj h
  simp [Function.update_of_ne this]

/-- Summing the factor of a vertex without a self-loop over its own values gives one. -/
theorem sum_factor_update [DecidableEq V] {s : V} (hs : ¬ G.Adj s s) (x : ∀ v, α v) :
    ∑ a : α s, k.factor s (Function.update x s a) = ∑ a : α s, k.kernel s
      ((G.parentsFinset s).restrict x) a := by
  refine sum_congr rfl fun a _ => ?_
  unfold factor
  simp only [Function.update_self]
  congr 1
  funext u
  have : u.1 ≠ s := fun h => hs (by have := mem_parentsFinset.1 u.2; rwa [h] at this)
  simp [Finset.restrict, Function.update_of_ne this]

/-- **Summing out a sink.** If `s ∈ S` has no child in `S` (in particular no self-loop), then
summing the product of the factors over `S` over the values of `x s` gives the product over
`S.erase s`. -/
theorem sum_update_prodOn [DecidableEq V] {S : Finset V} {s : V} (hs : s ∈ S)
    (hsink : ∀ v ∈ S, ¬ G.Adj s v) (x : ∀ v, α v) :
    ∑ a : α s, k.prodOn S (Function.update x s a) = k.prodOn (S.erase s) x := by
  unfold prodOn
  have hrest : ∀ a : α s, ∏ v ∈ S.erase s, k.factor v (Function.update x s a) =
      ∏ v ∈ S.erase s, k.factor v x := fun a =>
    prod_congr rfl fun v hv => k.factor_update_of_not_adj (ne_of_mem_erase hv).symm
      (hsink v (mem_of_mem_erase hv)) x a
  simp_rw [← mul_prod_erase S _ hs, hrest, ← sum_mul, k.sum_factor_update (hsink s hs) x,
    k.sum_eq_one, one_mul]

/-- **Summing out a child-closed set of vertices.** For an acyclic graph, if `T ⊆ S` and every
child inside `S` of a vertex of `T` lies in `T`, then summing the product of the factors over
`S` over the coordinates in `T` (with the other coordinates fixed to those of `x`) gives the
product over `S \ T`. -/
theorem sum_agreeOn_prodOn [DecidableEq V] [∀ v, DecidableEq (α v)] (hG : G.IsAcyclic)
    {S T : Finset V} (hTS : T ⊆ S)
    (hT : ∀ u ∈ T, ∀ v ∈ S, G.Adj u v → v ∈ T) (x : ∀ v, α v) :
    ∑ y ∈ FiniteDist.agreeOn Tᶜ x, k.prodOn S y = k.prodOn (S \ T) x := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  induction T using Finset.strongInduction generalizing S with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hne
    · have : FiniteDist.agreeOn (∅ : Finset V)ᶜ x = {x} := by
        ext y
        simp [funext_iff]
      rw [this, sum_singleton, sdiff_empty]
    · obtain ⟨s, hsT, hsmax⟩ := T.exists_max_image f hne
      have hsink : ∀ v ∈ S, ¬ G.Adj s v := fun v hv hsv =>
        (hf hsv).not_ge (hsmax v (hT s hsT v hv hsv))
      rw [FiniteDist.sum_agreeOn_compl_eq_sum_update _ hsT x]
      simp_rw [k.sum_update_prodOn (hTS hsT) hsink]
      rw [ih (T.erase s) (erase_ssubset hsT) (erase_subset_erase s hTS) ?_]
      · congr 1
        ext v
        simp only [mem_sdiff, mem_erase]
        constructor
        · rintro ⟨⟨hvs, hv⟩, hvT⟩
          exact ⟨hv, fun h => hvT ⟨hvs, h⟩⟩
        · rintro ⟨hv, hvT⟩
          refine ⟨⟨fun hvs => hvT (hvs ▸ hsT), hv⟩, fun h => hvT h.2⟩
      · intro u hu v hv huv
        exact mem_erase.2 ⟨(ne_of_mem_erase hv), hT u (mem_of_mem_erase hu) v
          (mem_of_mem_erase hv) huv⟩

include k in
/-- For an acyclic graph with Markov kernels, every value type is nonempty: by induction along
a topological order, a vertex whose parents have values has a parent configuration, and the
kernel there sums to one, so the vertex has a value. -/
theorem nonempty_value (hG : G.IsAcyclic) (v : V) : Nonempty (α v) := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  suffices ∀ n, ∀ v, f v = n → Nonempty (α v) from this _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    have z : ∀ u : G.parentsFinset v, α u := fun u =>
      Classical.choice (ih (f u) (hv ▸ hf (mem_parentsFinset.1 u.2)) u rfl)
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := k.sum_eq_one v z
    simp at this

include k in
/-- For an acyclic graph with Markov kernels, there is a configuration. -/
theorem nonempty_config (hG : G.IsAcyclic) : Nonempty (∀ v, α v) :=
  ⟨fun v => Classical.choice (k.nonempty_value hG v)⟩

/-- **Normalization.** For an acyclic graph, the product of any family of Markov kernels sums to
one over all configurations. -/
theorem sum_prodOn_univ [DecidableEq V] (hG : G.IsAcyclic) :
    ∑ x, k.prodOn univ x = 1 := by
  classical
  obtain ⟨x₀⟩ := k.nonempty_config hG
  have h := k.sum_agreeOn_prodOn hG (S := univ) (T := univ) subset_rfl
    (fun _ _ v _ _ => mem_univ v) x₀
  have hu : FiniteDist.agreeOn (univ : Finset V)ᶜ x₀ = univ := by
    ext y
    simp
  rwa [sdiff_self, bot_eq_empty, prodOn_empty, hu] at h

/-- For an acyclic graph, the product of a family of Markov kernels as a finite distribution on
configurations. -/
noncomputable def jointDist [DecidableEq V] [∀ v, DecidableEq (α v)] (hG : G.IsAcyclic) :
    FiniteDist (∀ v, α v) where
  mass := k.prodOn univ
  nonneg := k.prodOn_nonneg univ
  sum_eq_one := k.sum_prodOn_univ hG

@[simp] theorem jointDist_apply [DecidableEq V] [∀ v, DecidableEq (α v)] (hG : G.IsAcyclic)
    (x : ∀ v, α v) : k.jointDist hG x = ∏ v, k.factor v x := rfl

/-- **Marginal on an ancestral set.** If `p` is the product of the kernels of an acyclic graph
and `A` is closed under taking parents, then the marginal mass of `p` on `A` at `x` is the
product of the factors of the vertices of `A`. -/
theorem margAt_of_ancestral [DecidableEq V] [∀ v, DecidableEq (α v)] (hG : G.IsAcyclic)
    {p : FiniteDist (∀ v, α v)} (hp : ∀ x, p x = ∏ v, k.factor v x) {A : Finset V}
    (hA : ∀ v ∈ A, ∀ u, G.Adj u v → u ∈ A) (x : ∀ v, α v) :
    p.margAt A x = k.prodOn A x := by
  have h := k.sum_agreeOn_prodOn hG (S := univ) (T := Aᶜ) (subset_univ _)
    (fun u hu v _ huv => mem_compl.2 fun hv => (mem_compl.1 hu) (hA v hv u huv)) x
  rw [compl_compl, sdiff_compl, univ_inter] at h
  rw [← h, FiniteDist.margAt, FiniteDist.prob]
  exact sum_congr rfl fun y _ => hp y

omit [Fintype V] [DecidableRel G.Adj] in
/-- A finset whose ancestral closure (in the sense of `Digraph.ancestorsOf`) is itself is
closed under taking parents. -/
theorem _root_.Digraph.mem_of_adj_of_ancestorsOf_eq {A : Finset V}
    (hA : G.ancestorsOf (A : Set V) = A) {u v : V} (hv : v ∈ A) (huv : G.Adj u v) : u ∈ A := by
  have : u ∈ G.ancestorsOf (A : Set V) := mem_ancestorsOf_of_adj huv (subset_ancestorsOf _ hv)
  rwa [hA] at this

/-- The marginal on an ancestral set `A` (with `G.ancestorsOf A = A`) of a distribution that
factorizes according to an acyclic `G` is the product of the kernels of the vertices of `A`. -/
theorem margAt_of_ancestorsOf_eq [DecidableEq V] [∀ v, DecidableEq (α v)] (hG : G.IsAcyclic)
    {p : FiniteDist (∀ v, α v)} (hp : ∀ x, p x = ∏ v, k.factor v x) {A : Finset V}
    (hA : G.ancestorsOf (A : Set V) = A) (x : ∀ v, α v) :
    p.margAt A x = ∏ v ∈ A, k.factor v x :=
  k.margAt_of_ancestral hG hp (fun _ hv _ huv => mem_of_adj_of_ancestorsOf_eq hA hv huv) x

/-- **The kernel is the conditional distribution given the parents**, in product form:
`p(x_v, x_pa(v)) = kernel v x_pa(v) x_v * p(x_pa(v))`. -/
theorem margAt_insert_parents [DecidableEq V] [∀ v, DecidableEq (α v)] (hG : G.IsAcyclic)
    {p : FiniteDist (∀ v, α v)} (hp : ∀ x, p x = ∏ v, k.factor v x) (v : V)
    (x : ∀ v, α v) :
    p.margAt (insert v (G.parentsFinset v)) x =
      k.kernel v ((G.parentsFinset v).restrict x) (x v) * p.margAt (G.parentsFinset v) x := by
  set A := G.ancestorsFinset v
  have hA : ∀ w ∈ A, ∀ u, G.Adj u w → u ∈ A := fun w hw u huw =>
    mem_ancestorsFinset.2 (IsAncestor.head huw (mem_ancestorsFinset.1 hw))
  have hvA : v ∉ A := fun h => hG.not_isAncestor_self v (mem_ancestorsFinset.1 h)
  have hpaA : G.parentsFinset v ⊆ A := fun u hu =>
    mem_ancestorsFinset.2 (isAncestor_of_adj (mem_parentsFinset.1 hu))
  have hA' : ∀ w ∈ insert v A, ∀ u, G.Adj u w → u ∈ insert v A := by
    intro w hw u huw
    rcases mem_insert.1 hw with rfl | hw
    · exact mem_insert_of_mem (hpaA (mem_parentsFinset.2 huw))
    · exact mem_insert_of_mem (hA w hw u huw)
  have h : ∀ y, p.margAt (insert v A) y = k.factor v y * p.margAt A y := fun y => by
    rw [k.margAt_of_ancestral hG hp hA', k.margAt_of_ancestral hG hp hA, prodOn,
      prod_insert hvA]
    rfl
  exact p.margAt_insert_of_margAt_insert hpaA hvA (k.factor v)
    (fun y y' hyy => k.factor_congr fun u hu => hyy u (by
      rcases hu with rfl | hu
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_parentsFinset.2 hu))) h x

end MarkovKernels

/-- A distribution `p` on configurations factorizes according to `G` when there are Markov
kernels with `p x = ∏ v, kernel v (x restricted to the parents of v) (x v)` for all `x`. -/
def Factorizes [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (p : FiniteDist (∀ v, α v)) : Prop :=
  ∃ k : G.MarkovKernels α, ∀ x, p x = ∏ v, k.factor v x

/-- The product of the kernels of an acyclic graph factorizes according to the graph. -/
theorem MarkovKernels.factorizes_jointDist [DecidableEq V] [∀ v, DecidableEq (α v)]
    {G : Digraph V} [DecidableRel G.Adj] (k : G.MarkovKernels α) (hG : G.IsAcyclic) :
    G.Factorizes (k.jointDist hG) :=
  ⟨k, fun _ => rfl⟩

end Digraph
