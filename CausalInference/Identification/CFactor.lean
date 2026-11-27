/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.AgreeOnSums
public import CausalInference.SCM.Effects
public import CausalInference.Graphical.LatentProjection

/-!
# C-factors of a structural causal model with latent variables

A finite Markovian structural causal model `M : SCM G α ε` on a directed acyclic graph `G` with a
finset `O` of observed vertices; every other vertex is latent. No restriction is put on the
latent vertices: they may have parents and children of any kind. The causal structure seen from
the observed vertices is the latent projection `latentProjection G (↑O)ᶜ`, an acyclic directed
mixed graph whose edges join observed vertices (see `CausalInference.Graphical.LatentProjection`).

The **c-factor** of a set `S ⊆ O` (Tian and Pearl 2002) is the law of `S` when every other
observed vertex is set by intervention:
`Q[S](w) = P(S = w_S | do(O \ S := w_{O \ S}))`, a function of the observed values `w`.

## Main definitions

* `SCM.cFactor M O S w`: the c-factor `Q[S]` at the configuration `w`, defined as the causal
  effect `M.effect (O \ S) w S w`.
* `latentReach G O S`: the latent vertices from which a directed path with latent interior
  reaches a vertex of `S`.

## Main results

* `SCM.cFactor_eq_sum`: `Q[S](w) = ∑_l ∏_{v ∈ S ∪ L} P(v | pa v)`, the sum running over the
  values of the latent vertices `L = Oᶜ` (the truncated factorization, marginalized).
* `SCM.cFactor_eq_sum_latentReach`: only the latent vertices that reach `S` matter.
* `SCM.cFactor_self`, `SCM.cFactor_empty`: `Q[O]` is the observed law, `Q[∅] = 1`.
* `SCM.cFactor_union` (**c-component factorization**, the binary step): if no bidirected edge
  of the latent projection joins the disjoint sets `S₁` and `S₂`, then
  `Q[S₁ ∪ S₂] = Q[S₁] Q[S₂]`.
* `SCM.sum_cFactor_of_closed` (**ancestral marginalization**): if `S ⊆ T ⊆ O` and no directed
  edge of the latent projection enters `S` from `T \ S`, then summing `Q[T]` over the values of
  `T \ S` gives `Q[S]`.
* `SCM.effect_eq_sum_cFactor`: `P(y | do(x)) = ∑_{(O \ X) \ Y} Q[O \ X]`.
* `SCM.cFactor_pos`: a strictly positive observed law makes every c-factor strictly positive.

Sources: Tian and Pearl (2002), *A general identification condition for causal effects*; Tian
(2002), PhD thesis; Pearl (2009), *Causality*, 2nd edition, sections 3.5 and 3.6.
-/

@[expose] public section

namespace CausalInference

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The latent vertices (those outside `O`) from which a directed path of `G` with latent
interior reaches a vertex of `S`. -/
noncomputable def latentReach (G : Digraph V) (O S : Finset V) : Finset V := by
  classical
  exact Oᶜ.filter fun l => ∃ s ∈ S, LatentPath G (↑O)ᶜ l s

/-- Membership in `latentReach`: a latent vertex with a latent-interior path into `S`. -/
theorem mem_latentReach {G : Digraph V} {O S : Finset V} {l : V} :
    l ∈ latentReach G O S ↔ l ∉ O ∧ ∃ s ∈ S, LatentPath G (↑O)ᶜ l s := by
  classical
  unfold latentReach
  simp only [mem_filter, mem_compl]

/-- The vertices of `latentReach` are latent. -/
theorem latentReach_subset_compl {G : Digraph V} {O S : Finset V} :
    latentReach G O S ⊆ Oᶜ :=
  fun _ h => mem_compl.2 (mem_latentReach.1 h).1

/-- `latentReach` of a union is the union of the `latentReach` sets. -/
theorem latentReach_union {G : Digraph V} {O S₁ S₂ : Finset V} :
    latentReach G O (S₁ ∪ S₂) = latentReach G O S₁ ∪ latentReach G O S₂ := by
  ext l
  simp only [mem_union, mem_latentReach]
  constructor
  · rintro ⟨hl, s, hs, hp⟩
    rcases hs with hs | hs
    · exact Or.inl ⟨hl, s, hs, hp⟩
    · exact Or.inr ⟨hl, s, hs, hp⟩
  · rintro (⟨hl, s, hs, hp⟩ | ⟨hl, s, hs, hp⟩)
    · exact ⟨hl, s, Or.inl hs, hp⟩
    · exact ⟨hl, s, Or.inr hs, hp⟩

/-- The configurations that agree with `w` on `O` are those that agree with `w` outside `Oᶜ`. -/
theorem FiniteDist.agreeOn_eq_compl_compl {α : V → Type*} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] (O : Finset V) (w : ∀ v, α v) :
    FiniteDist.agreeOn O w = FiniteDist.agreeOn Oᶜᶜ w := by
  rw [compl_compl]

omit [DecidableEq V] in
/-- The product of the factors of the vertices of `R` does not depend on the coordinates of `B`
when neither the vertices of `R` nor their parents lie in `B`. -/
theorem _root_.Digraph.MarkovKernels.dependsOn_prodOn {G : Digraph V} [DecidableRel G.Adj]
    {α : V → Type*} [∀ v, Fintype (α v)] (k : G.MarkovKernels α) {R B : Finset V}
    (h : ∀ v ∈ R, v ∉ B ∧ ∀ u, G.Adj u v → u ∉ B) :
    DependsOn (k.prodOn R) (↑B)ᶜ := by
  intro x y hxy
  refine prod_congr rfl fun v hv => k.factor_congr fun u hu => hxy u ?_
  simp only [Set.mem_compl_iff, mem_coe]
  rcases hu with rfl | hu
  · exact (h u hv).1
  · exact (h v hv).2 u hu

namespace SCM

variable {G : Digraph V} [DecidableRel G.Adj] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- The **c-factor** `Q[S]` of a set `S` of observed vertices (Tian and Pearl 2002): the
probability that `S` takes the values of `w` when every other observed vertex, those of
`O \ S`, is set by intervention to its value in `w`. It is a function of the observed values
`w`; the coordinates of `w` outside `O` are not used (`SCM.cFactor_congr`). -/
noncomputable def cFactor (O S : Finset V) (w : ∀ v, α v) : ℝ := M.effect (O \ S) w S w

/-- **The c-factor as a sum over the latent values**: for `S ⊆ O`,
`Q[S](w) = ∑ ∏_{v ∈ S ∪ Oᶜ} P(v | pa v)`, the sum running over the configurations that agree
with `w` on `O`. This is the truncated factorization of `do(O \ S)` with the latent
coordinates summed out. -/
theorem cFactor_eq_sum {O S : Finset V} (hS : S ⊆ O) (w : ∀ v, α v) :
    M.cFactor O S w = ∑ d ∈ FiniteDist.agreeOn O w, M.kernels.prodOn (S ∪ Oᶜ) d := by
  unfold cFactor effect FiniteDist.margAt FiniteDist.prob
  simp_rw [M.dist_intervene]
  rw [← sum_filter]
  have hset : (O \ S)ᶜ = S ∪ Oᶜ := by
    ext v
    simp only [mem_compl, mem_sdiff, mem_union, not_and, not_not]
    constructor
    · intro h
      by_cases hv : v ∈ O
      · exact Or.inl (h hv)
      · exact Or.inr hv
    · rintro (h | h) hv
      · exact h
      · exact absurd hv h
  rw [hset]
  refine sum_congr ?_ fun _ _ => rfl
  ext d
  simp only [mem_filter, FiniteDist.mem_agreeOn, mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩ v hv
    by_cases hvS : v ∈ S
    · exact h1 v hvS
    · exact h2 v ⟨hv, hvS⟩
  · intro h
    exact ⟨fun v hv => h v (hS hv), fun v hv => h v hv.1⟩

/-- The c-factor depends only on the observed coordinates of `w`. -/
theorem cFactor_congr {O S : Finset V} (hS : S ⊆ O) {w w' : ∀ v, α v}
    (h : ∀ v ∈ O, w v = w' v) : M.cFactor O S w = M.cFactor O S w' := by
  rw [M.cFactor_eq_sum hS, M.cFactor_eq_sum hS, FiniteDist.agreeOn_congr h]

/-- C-factors are nonnegative. -/
theorem cFactor_nonneg (O S : Finset V) (w : ∀ v, α v) : 0 ≤ M.cFactor O S w :=
  FiniteDist.margAt_nonneg _ _ _

/-- The c-factor of the observed set is the observed law. -/
theorem cFactor_self (O : Finset V) (w : ∀ v, α v) : M.cFactor O O w = M.dist.margAt O w := by
  unfold cFactor effect
  rw [sdiff_self, bot_eq_empty, dist_intervene_empty]

/-- The c-factor of the empty set is one. -/
@[simp] theorem cFactor_empty (O : Finset V) (w : ∀ v, α v) : M.cFactor O ∅ w = 1 := by
  unfold cFactor effect
  exact FiniteDist.margAt_empty _ _

/-- **Only the latent vertices that reach `S` matter**: for `S ⊆ O`, `Q[S](w)` is the sum over
the values of the latent vertices of `latentReach G O S` of the product of the factors of `S`
and of these latent vertices. The other latent vertices sum out: none of them is a parent of a
vertex of `S` or of a latent vertex that reaches `S`. -/
theorem cFactor_eq_sum_latentReach {O S : Finset V} (hS : S ⊆ O) (w : ∀ v, α v) :
    M.cFactor O S w = ∑ d ∈ FiniteDist.agreeOn (latentReach G O S)ᶜ w,
      M.kernels.prodOn (S ∪ latentReach G O S) d := by
  set LS := latentReach G O S with hLS
  have hsub : LS ⊆ Oᶜ := latentReach_subset_compl
  rw [M.cFactor_eq_sum hS, FiniteDist.agreeOn_eq_compl_compl,
    show FiniteDist.agreeOn Oᶜᶜ w = FiniteDist.agreeOn ((Oᶜ \ LS) ∪ LS)ᶜ w by
      rw [sdiff_union_of_subset hsub],
    FiniteDist.sum_agreeOn_union disjoint_sdiff_self_left]
  refine sum_congr rfl fun d' _ => ?_
  rw [M.kernels.sum_agreeOn_prodOn M.acyclic (S := S ∪ Oᶜ) (T := Oᶜ \ LS)
    (sdiff_subset.trans subset_union_right) ?_ d']
  · congr 1
    ext v
    simp only [mem_sdiff, mem_union, mem_compl, not_and, not_not]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (h2 h1)
    · rintro (h | h)
      · exact ⟨Or.inl h, fun h' => absurd (hS h) h'⟩
      · exact ⟨Or.inr (mem_compl.1 (hsub h)), fun _ => h⟩
  · intro u hu v hv huv
    rw [mem_sdiff] at hu
    have hu' : u ∉ O := mem_compl.1 hu.1
    rcases mem_union.1 hv with hv | hv
    · exact absurd (mem_latentReach.2 ⟨hu', v, hv, latentPath_of_adj huv⟩) hu.2
    · refine mem_sdiff.2 ⟨hv, fun hvL => hu.2 ?_⟩
      obtain ⟨hvO, s, hs, hp⟩ := mem_latentReach.1 hvL
      exact mem_latentReach.2 ⟨hu', s, hs, LatentPath.head huv (by simpa using hvO) hp⟩

/-- **C-component factorization**, the binary step (Tian and Pearl 2002): if `S₁` and `S₂` are
disjoint sets of observed vertices and no bidirected edge of the latent projection joins a
vertex of `S₁` to a vertex of `S₂`, then `Q[S₁ ∪ S₂] = Q[S₁] Q[S₂]`. The latent vertices that
reach `S₁` and those that reach `S₂` form disjoint sets, so the sum over the latent values
splits. -/
theorem cFactor_union {O S₁ S₂ : Finset V} (hS₁ : S₁ ⊆ O) (hS₂ : S₂ ⊆ O) (hd : Disjoint S₁ S₂)
    (hbi : ∀ u ∈ S₁, ∀ v ∈ S₂, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (w : ∀ v, α v) : M.cFactor O (S₁ ∪ S₂) w = M.cFactor O S₁ w * M.cFactor O S₂ w := by
  set L₁ := latentReach G O S₁
  set L₂ := latentReach G O S₂
  have hL : Disjoint L₁ L₂ := by
    refine disjoint_left.2 fun l h1 h2 => ?_
    obtain ⟨hl, u, hu, hpu⟩ := mem_latentReach.1 h1
    obtain ⟨-, v, hv, hpv⟩ := mem_latentReach.1 h2
    refine hbi u hu v hv (latentProjection_bidirected_adj.2 ⟨fun h => ?_, ?_, ?_, l, ?_, hpu, hpv⟩)
    · exact disjoint_left.1 hd hu (h ▸ hv)
    · simpa using hS₁ hu
    · simpa using hS₂ hv
    · simpa using hl
  have hpar : ∀ {S L L' : Finset V}, S ⊆ O → L = latentReach G O S → Disjoint L L' →
      L' ⊆ Oᶜ → ∀ v ∈ S ∪ L, v ∉ L' ∧ ∀ u, G.Adj u v → u ∉ L' := by
    intro S L L' hS hLdef hLL' hL'O v hv
    have hu_notin : ∀ u, G.Adj u v → u ∈ Oᶜ → u ∈ L := by
      intro u huv huO
      rw [hLdef]
      rcases mem_union.1 hv with hv | hv
      · exact mem_latentReach.2 ⟨mem_compl.1 huO, v, hv, latentPath_of_adj huv⟩
      · rw [hLdef] at hv
        obtain ⟨hvO, s, hs, hp⟩ := mem_latentReach.1 hv
        exact mem_latentReach.2 ⟨mem_compl.1 huO, s, hs,
          LatentPath.head huv (by simpa using hvO) hp⟩
    refine ⟨fun hv' => ?_, fun u huv hu => disjoint_left.1 hLL' (hu_notin u huv (hL'O hu)) hu⟩
    rcases mem_union.1 hv with hv | hv
    · exact mem_compl.1 (hL'O hv') (hS hv)
    · exact disjoint_left.1 hLL' hv hv'
  rw [M.cFactor_eq_sum_latentReach (union_subset hS₁ hS₂), latentReach_union,
    M.cFactor_eq_sum_latentReach hS₁, M.cFactor_eq_sum_latentReach hS₂,
    ← FiniteDist.sum_agreeOn_union_mul hL
      (M.kernels.dependsOn_prodOn (hpar hS₁ rfl hL latentReach_subset_compl))
      (M.kernels.dependsOn_prodOn (hpar hS₂ rfl hL.symm latentReach_subset_compl))]
  refine sum_congr rfl fun d _ => ?_
  have hdisj : Disjoint (S₁ ∪ L₁) (S₂ ∪ L₂) := by
    refine disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨hd, ?_⟩,
      disjoint_union_right.2 ⟨?_, hL⟩⟩
    · exact disjoint_left.2 fun v hv hv' =>
        mem_compl.1 (latentReach_subset_compl hv') (hS₁ hv)
    · exact disjoint_left.2 fun v hv hv' =>
        mem_compl.1 (latentReach_subset_compl hv) (hS₂ hv')
  have hset : S₁ ∪ S₂ ∪ (L₁ ∪ L₂) = (S₁ ∪ L₁) ∪ (S₂ ∪ L₂) := by
    ext v
    simp only [mem_union]
    tauto
  unfold Digraph.MarkovKernels.prodOn
  rw [hset, prod_union hdisj]

/-- **Ancestral marginalization** (Tian and Pearl 2002): if `S ⊆ T ⊆ O` and no directed edge of
the latent projection goes from a vertex of `T \ S` into `S`, then summing `Q[T]` over the
values of `T \ S` gives `Q[S]`:
`∑_{t \ s} Q[T] = Q[S]`. -/
theorem sum_cFactor_of_closed {O S T : Finset V} (hST : S ⊆ T) (hT : T ⊆ O)
    (hcl : ∀ u ∈ T, ∀ v ∈ S, (latentProjection G (↑O)ᶜ).directed.Adj u v → u ∈ S)
    (w : ∀ v, α v) :
    ∑ c ∈ FiniteDist.agreeOn (T \ S)ᶜ w, M.cFactor O T c = M.cFactor O S w := by
  classical
  -- the latent vertices below `T \ S`
  set L' := Oᶜ.filter fun l => ∃ t ∈ T \ S, LatentPath G (↑O)ᶜ t l with hL'
  set R := Oᶜ \ L' with hR
  have hL'O : L' ⊆ Oᶜ := filter_subset _ _
  have hobs : ∀ {v}, v ∈ O → v ∉ ((↑O)ᶜ : Set V) := fun hv h => h (mem_coe.2 hv)
  -- a latent-interior path from `T \ S` never ends in `S`
  have hnoS : ∀ t ∈ T \ S, ∀ v ∈ S, ¬ LatentPath G (↑O)ᶜ t v := by
    intro t ht v hv hp
    have := hcl t (mem_sdiff.1 ht).1 v hv
      (latentProjection_directed_adj.2 ⟨hobs (hT (mem_sdiff.1 ht).1), hobs (hT (hST hv)), hp⟩)
    exact (mem_sdiff.1 ht).2 this
  have hstep : ∀ u v, (u ∈ T \ S ∨ u ∈ L') → G.Adj u v → v ∉ O →
      v ∈ L' := by
    intro u v hu huv hv
    refine mem_filter.2 ⟨mem_compl.2 hv, ?_⟩
    rcases hu with hu | hu
    · exact ⟨u, hu, latentPath_of_adj huv⟩
    · obtain ⟨huO, t, ht, hp⟩ := mem_filter.1 hu
      exact ⟨t, ht, hp.trans (by simpa using mem_compl.1 huO) (latentPath_of_adj huv)⟩
  have hpathS : ∀ u v, (u ∈ T \ S ∨ u ∈ L') → G.Adj u v → v ∉ S := by
    intro u v hu huv hv
    rcases hu with hu | hu
    · exact hnoS u hu v hv (latentPath_of_adj huv)
    · obtain ⟨huO, t, ht, hp⟩ := mem_filter.1 hu
      exact hnoS t ht v hv (hp.trans (by simpa using mem_compl.1 huO) (latentPath_of_adj huv))
  -- left side: sum out `(T \ S) ∪ L'` from the product over `T ∪ Oᶜ`
  have hdisj1 : Disjoint Oᶜ (T \ S) :=
    disjoint_left.2 fun v hv hv' => mem_compl.1 hv (hT (mem_sdiff.1 hv').1)
  simp_rw [M.cFactor_eq_sum hT, FiniteDist.agreeOn_eq_compl_compl O]
  rw [← FiniteDist.sum_agreeOn_union hdisj1]
  have hset1 : Oᶜ ∪ (T \ S) = ((T \ S) ∪ L') ∪ R := by
    ext v
    simp only [hR, mem_union, mem_sdiff]
    constructor
    · rintro (h | h)
      · by_cases hv : v ∈ L'
        · exact Or.inl (Or.inr hv)
        · exact Or.inr ⟨h, hv⟩
      · exact Or.inl (Or.inl h)
    · rintro ((h | h) | h)
      · exact Or.inr h
      · exact Or.inl (hL'O h)
      · exact Or.inl h.1
  have hdisj2 : Disjoint ((T \ S) ∪ L') R := by
    refine disjoint_union_left.2 ⟨disjoint_left.2 fun v hv hv' => ?_, disjoint_sdiff⟩
    exact mem_compl.1 (mem_sdiff.1 hv').1 (hT (mem_sdiff.1 hv).1)
  rw [hset1, FiniteDist.sum_agreeOn_union hdisj2]
  -- right side: sum out `L'` from the product over `S ∪ Oᶜ`
  rw [M.cFactor_eq_sum (hST.trans hT), FiniteDist.agreeOn_eq_compl_compl O,
    show Oᶜ = L' ∪ R from (union_sdiff_of_subset hL'O).symm,
    FiniteDist.sum_agreeOn_union disjoint_sdiff]
  have hK1 : (T \ S) ∪ L' ⊆ T ∪ (L' ∪ R) := by
    intro v hv
    rcases mem_union.1 hv with hv | hv
    · exact mem_union_left _ (mem_sdiff.1 hv).1
    · exact mem_union_right _ (mem_union_left _ hv)
  have hK2 : ∀ u ∈ (T \ S) ∪ L', ∀ v ∈ T ∪ (L' ∪ R), G.Adj u v → v ∈ (T \ S) ∪ L' := by
    intro u hu v hv huv
    have hu' : u ∈ T \ S ∨ u ∈ L' := mem_union.1 hu
    rcases mem_union.1 hv with hv | hv
    · by_cases hvS : v ∈ S
      · exact absurd hvS (hpathS u v hu' huv)
      · exact mem_union_left _ (mem_sdiff.2 ⟨hv, hvS⟩)
    · rcases mem_union.1 hv with hv | hv
      · exact mem_union_right _ hv
      · exact mem_union_right _ (hstep u v hu' huv (mem_compl.1 (mem_sdiff.1 hv).1))
  have hL1 : L' ⊆ S ∪ (L' ∪ R) := subset_union_left.trans subset_union_right
  have hL2 : ∀ u ∈ L', ∀ v ∈ S ∪ (L' ∪ R), G.Adj u v → v ∈ L' := by
    intro u hu v hv huv
    rcases mem_union.1 hv with hv | hv
    · exact absurd hv (hpathS u v (Or.inr hu) huv)
    · rcases mem_union.1 hv with hv | hv
      · exact hv
      · exact hstep u v (Or.inr hu) huv (mem_compl.1 (mem_sdiff.1 hv).1)
  refine sum_congr rfl fun d' _ => ?_
  rw [M.kernels.sum_agreeOn_prodOn M.acyclic hK1 hK2 d',
    M.kernels.sum_agreeOn_prodOn M.acyclic hL1 hL2 d']
  congr 1
  have hRT : ∀ v ∈ R, v ∉ T := fun v hv hvT => mem_compl.1 (mem_sdiff.1 hv).1 (hT hvT)
  have hRL : ∀ v ∈ R, v ∉ L' := fun v hv => (mem_sdiff.1 hv).2
  ext v
  have h1 := hRT v
  have h2 := hRL v
  have h3 : v ∈ S → v ∈ T := fun h => hST h
  simp only [mem_sdiff, mem_union]
  tauto

/-- **The causal effect from the c-factor of the non-intervened observed vertices**: for
`X ⊆ O` and `Y ⊆ O \ X`, `P(y | do(x)) = ∑_{(O \ X) \ Y} Q[O \ X]`, the sum running over the
values of the observed vertices that are neither intervened on nor in `Y`. -/
theorem effect_eq_sum_cFactor {O X Y : Finset V} (hX : X ⊆ O) (hY : Y ⊆ O \ X)
    (w : ∀ v, α v) :
    M.effect X w Y w = ∑ c ∈ FiniteDist.agreeOn ((O \ X) \ Y)ᶜ w, M.cFactor O (O \ X) c := by
  unfold cFactor
  simp_rw [Finset.sdiff_sdiff_eq_self hX]
  rw [effect, FiniteDist.margAt_eq_sum_margAt _ hY w]
  refine sum_congr rfl fun c hc => ?_
  rw [effect, M.dist_intervene_congr fun u hu => ?_]
  refine ((FiniteDist.mem_agreeOn.1 hc) u ?_).symm
  simp only [mem_compl, mem_sdiff, not_and, not_not]
  intro h
  exact absurd hu h.2

/-- **Positivity of the c-factors**: if the observed law is strictly positive, so is every
c-factor `Q[S]`, `S ⊆ O`. A configuration of positive observed mass has a latent completion
at which every factor is positive, and that term is part of the sum defining `Q[S]`. -/
theorem cFactor_pos {O S : Finset V} (hS : S ⊆ O) (hpos : ∀ w, 0 < M.dist.margAt O w)
    (w : ∀ v, α v) : 0 < M.cFactor O S w := by
  have h := hpos w
  rw [← M.cFactor_self, M.cFactor_eq_sum subset_rfl] at h
  obtain ⟨d, hd, hdp⟩ : ∃ d ∈ FiniteDist.agreeOn O w,
      0 < M.kernels.prodOn (O ∪ Oᶜ) d := by
    by_contra hc
    push Not at hc
    exact absurd h (not_lt.2 (sum_nonpos hc))
  have hsub : S ∪ Oᶜ ⊆ O ∪ Oᶜ := union_subset_union hS subset_rfl
  have hsplit := prod_sdiff (f := fun v => M.kernels.factor v d) hsub
  have hpart : 0 < M.kernels.prodOn (S ∪ Oᶜ) d := by
    refine lt_of_le_of_ne (M.kernels.prodOn_nonneg _ d) fun h0 => ?_
    unfold Digraph.MarkovKernels.prodOn at hdp h0
    rw [← hsplit, ← h0, mul_zero] at hdp
    exact lt_irrefl 0 hdp
  rw [M.cFactor_eq_sum hS]
  exact hpart.trans_le (single_le_sum (fun d _ => M.kernels.prodOn_nonneg _ d) hd)

end SCM

end CausalInference
