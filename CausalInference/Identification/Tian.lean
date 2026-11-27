/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.CFactor
public import CausalInference.SCM.Adjustment

/-!
# Tian's c-component results

For a finite structural causal model with observed set `O` and latent projection
`latentProjection G (↑O)ᶜ`, the results of Tian and Pearl (2002) on c-factors:

* the c-factor of a union of districts is the product of their c-factors, and in particular the
  observed law is the product of the c-factors of the districts of the latent projection;
* the c-factor of a set `S` that is closed under bidirected edges inside a set `A` is computed
  from `Q[A]` as a product of conditionals along an order of `A`:
  `Q[S] = ∏_{v ∈ S} Q[A^{≤v}] / Q[A^{<v}]`, where `A^{≤v}` and `A^{<v}` are the vertices of `A`
  up to `v` and before `v`; when the order is topological, `Q[A^{≤v}]` and `Q[A^{<v}]` are
  marginals of `Q[A]` (ancestral marginalization), so `Q[S]` is a functional of `Q[A]`.

Every statement is given in a division-free form; the divided forms assume that the divisors
are nonzero (or strictly positive).

## Main results

* `prod_filter_le_eq_mul_prod_filter_lt`: the telescoping identity behind Tian's formula.
* `SCM.cFactor_biUnion`, `SCM.cFactor_eq_prod_districtsOn`: **c-component factorization**,
  `Q[D] = ∏_j Q[D_j]` over the districts `D_j` of the latent projection restricted to `D`.
* `SCM.margAt_eq_prod_districtsOn`: the observed law is the product of the c-factors of the
  districts of the latent projection.
* `SCM.cFactor_mul_prod_pre`: Tian's formula, division-free:
  `Q[S] ∏_{v ∈ S} Q[A^{<v}] = ∏_{v ∈ S} Q[A^{≤v}]` for any order of `A` injective on `A`.
* `SCM.cFactor_eq_prod_div`: the divided form.
* `SCM.cFactor_mul_prod_sum`, `SCM.cFactor_eq_prod_sum_div`: with a topological order, the same
  with `Q[A^{≤v}]` and `Q[A^{<v}]` written as sums of `Q[A]`: the decomposition used in the
  recursion of the identification algorithm.
* `SCM.cFactor_mul_prod_margAt`, `SCM.cFactor_eq_prod_margAt_div`: the case `A = O`, the
  c-factor of every district of the latent projection is the product of the conditionals
  `P(v | o^{<v})` of the observed law along a topological order.
* `SCM.identifiableFrom_cFactor`: hence every such c-factor is identifiable from the observed law
  within the class of models with a strictly positive observed law.

Sources: Tian and Pearl (2002), *A general identification condition for causal effects*; Tian
(2002), PhD thesis.
-/

@[expose] public section

namespace CausalInference

open Finset

/-- **Telescoping along an order.** For a function `f` on finsets with `f ∅ = 1` and an order
`ord` injective on `S`, the product over `v ∈ S` of `f` at the vertices of `S` up to `v` is
`f S` times the product of `f` at the vertices of `S` before `v`. -/
theorem prod_filter_le_eq_mul_prod_filter_lt {ι : Type*} (f : Finset ι → ℝ)
    (hf : f ∅ = 1) (ord : ι → ℕ) (S : Finset ι) (hinj : Set.InjOn ord ↑S) :
    ∏ v ∈ S, f (S.filter fun u => ord u ≤ ord v) =
      f S * ∏ v ∈ S, f (S.filter fun u => ord u < ord v) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [hf]
    obtain ⟨s, hs, hmax⟩ := S.exists_max_image ord hne
    have hlt : ∀ v ∈ S.erase s, ord v < ord s := by
      intro v hv
      refine lt_of_le_of_ne (hmax v (mem_of_mem_erase hv)) fun h => ?_
      exact ne_of_mem_erase hv (hinj (mem_of_mem_erase hv) hs h)
    have key : ∀ v ∈ S.erase s, ∀ (r : ℕ → ℕ → Prop) [DecidableRel r],
        (∀ n : ℕ, r n (ord v) → n ≤ ord v) →
        S.filter (fun u => r (ord u) (ord v)) =
          (S.erase s).filter fun u => r (ord u) (ord v) := by
      intro v hv r _ hr
      ext u
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨hu, hr'⟩
        refine ⟨⟨fun hus => ?_, hu⟩, hr'⟩
        subst hus
        exact absurd (hr _ hr') (not_le.2 (hlt v hv))
      · rintro ⟨⟨-, hu⟩, hr'⟩
        exact ⟨hu, hr'⟩
    have hle_s : S.filter (fun u => ord u ≤ ord s) = S := filter_true_of_mem fun u hu => hmax u hu
    have hlt_s : S.filter (fun u => ord u < ord s) = S.erase s := by
      ext u
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨hu, hlt'⟩
        exact ⟨fun h => by subst h; exact lt_irrefl _ hlt', hu⟩
      · rintro ⟨hne', hu⟩
        exact ⟨hu, hlt u (mem_erase.2 ⟨hne', hu⟩)⟩
    rw [← mul_prod_erase S _ hs, ← mul_prod_erase S _ hs, hle_s, hlt_s,
      prod_congr rfl fun v hv => congrArg f (key v hv (· ≤ ·) fun _ h => h),
      prod_congr rfl fun v hv => congrArg f (key v hv (· < ·) fun _ h => h.le),
      ih _ (erase_ssubset hs) (hinj.mono (coe_subset.2 (erase_subset s S)))]

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-! ### Factorization over districts -/

/-- **C-component factorization** for a family of sets: if the members of `𝒮` are pairwise
disjoint sets of observed vertices and no bidirected edge of the latent projection joins two
different members, then the c-factor of their union is the product of their c-factors. -/
theorem cFactor_biUnion {O : Finset V} (𝒮 : Finset (Finset V)) (hsub : ∀ s ∈ 𝒮, s ⊆ O)
    (hdisj : ∀ s ∈ 𝒮, ∀ t ∈ 𝒮, s ≠ t → Disjoint s t)
    (hbi : ∀ s ∈ 𝒮, ∀ t ∈ 𝒮, s ≠ t → ∀ u ∈ s, ∀ v ∈ t,
      ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (w : ∀ v, α v) : M.cFactor O (𝒮.biUnion id) w = ∏ s ∈ 𝒮, M.cFactor O s w := by
  induction 𝒮 using Finset.induction_on with
  | empty => simp
  | insert s 𝒮 hs ih =>
    have hne : ∀ t ∈ 𝒮, s ≠ t := fun t ht h => hs (h ▸ ht)
    rw [biUnion_insert, prod_insert hs, id, M.cFactor_union (hsub s (mem_insert_self s 𝒮))
      (biUnion_subset.2 fun t ht => hsub t (mem_insert_of_mem ht) : 𝒮.biUnion id ⊆ O) ?_ ?_,
      ih (fun t ht => hsub t (mem_insert_of_mem ht))
        (fun t ht t' ht' => hdisj t (mem_insert_of_mem ht) t' (mem_insert_of_mem ht'))
        (fun t ht t' ht' => hbi t (mem_insert_of_mem ht) t' (mem_insert_of_mem ht'))]
    · exact (disjoint_biUnion_right _ _ _).2 fun t ht =>
        hdisj s (mem_insert_self s 𝒮) t (mem_insert_of_mem ht) (hne t ht)
    · intro u hu v hv
      obtain ⟨t, ht, hvt⟩ := mem_biUnion.1 hv
      exact hbi s (mem_insert_self s 𝒮) t (mem_insert_of_mem ht) (hne t ht) u hu v hvt

/-- The districts of a mixed graph restricted to `D` cover `D`, are pairwise disjoint, and are
joined by no bidirected edge. -/
theorem _root_.CausalInference.ADMG.districtsOn_facts (H : ADMG V)
    [DecidableRel H.bidirected.Adj] (D : Finset V) :
    (H.districtsOn D).biUnion id = D ∧
      (∀ s ∈ H.districtsOn D, ∀ t ∈ H.districtsOn D, s ≠ t → Disjoint s t) ∧
      ∀ s ∈ H.districtsOn D, ∀ t ∈ H.districtsOn D, s ≠ t → ∀ u ∈ s, ∀ v ∈ t,
        ¬ H.bidirected.Adj u v := by
  have hmem : ∀ s ∈ H.districtsOn D, ∀ u ∈ s,
      s = (H.restrict ↑D).districtFinset u := by
    intro s hs u hu
    have hu' : u ∈ D := ADMG.subset_of_mem_districtsOn hs hu
    obtain ⟨d, -, hd⟩ := ADMG.existsUnique_mem_districtsOn (G := H) hu'
    exact (hd s ⟨hs, hu⟩).trans (hd _ ⟨ADMG.mem_districtsOn.2 ⟨u, hu', rfl⟩,
      ADMG.mem_districtFinset.2 (ADMG.mem_district_self u)⟩).symm
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [mem_biUnion, id]
    constructor
    · rintro ⟨s, hs, hv⟩
      exact ADMG.subset_of_mem_districtsOn hs hv
    · intro hv
      obtain ⟨d, ⟨hd, hvd⟩, -⟩ := ADMG.existsUnique_mem_districtsOn (G := H) hv
      exact ⟨d, hd, hvd⟩
  · intro s hs t ht hst
    refine disjoint_left.2 fun v hvs hvt => hst ?_
    rw [hmem s hs v hvs, hmem t ht v hvt]
  · intro s hs t ht hst u hu v hv huv
    refine hst ?_
    have hu' : u ∈ D := ADMG.subset_of_mem_districtsOn hs hu
    have hv' : v ∈ D := ADMG.subset_of_mem_districtsOn ht hv
    have hreach : v ∈ (H.restrict ↑D).districtFinset u :=
      ADMG.mem_districtFinset.2 (SimpleGraph.Adj.reachable ⟨huv, hu', hv'⟩)
    have hvs : v ∈ s := by
      rw [hmem s hs u hu]
      exact hreach
    rw [hmem s hs v hvs, hmem t ht v hv]

/-- **C-component factorization** (Tian and Pearl 2002): for a set `D ⊆ O` and a mixed graph `H`
that contains every bidirected edge of the latent projection, the c-factor of `D` is the product
of the c-factors of the districts of `H` restricted to `D`. -/
theorem cFactor_eq_prod_districtsOn {O : Finset V} (H : ADMG V) [DecidableRel H.bidirected.Adj]
    (hH : ∀ u v, (latentProjection G (↑O)ᶜ).bidirected.Adj u v → H.bidirected.Adj u v)
    {D : Finset V} (hD : D ⊆ O) (w : ∀ v, α v) :
    M.cFactor O D w = ∏ d ∈ H.districtsOn D, M.cFactor O d w := by
  obtain ⟨hU, hdisj, hbi⟩ := H.districtsOn_facts D
  conv_lhs => rw [← hU]
  exact M.cFactor_biUnion _ (fun s hs => (ADMG.subset_of_mem_districtsOn hs).trans hD) hdisj
    (fun s hs t ht hst u hu v hv h => hbi s hs t ht hst u hu v hv (hH u v h)) w

/-- **The observed law is the product of the c-factors of the districts** of the latent
projection (Tian and Pearl 2002), for any mixed graph `H` containing the bidirected edges of the
latent projection. -/
theorem margAt_eq_prod_districtsOn {O : Finset V} (H : ADMG V) [DecidableRel H.bidirected.Adj]
    (hH : ∀ u v, (latentProjection G (↑O)ᶜ).bidirected.Adj u v → H.bidirected.Adj u v)
    (w : ∀ v, α v) :
    M.dist.margAt O w = ∏ d ∈ H.districtsOn O, M.cFactor O d w := by
  rw [← M.cFactor_self, M.cFactor_eq_prod_districtsOn H hH subset_rfl]

/-! ### Tian's formula -/

/-- **Tian's formula, division-free** (Tian and Pearl 2002). Let `S ⊆ A ⊆ O` with no bidirected
edge of the latent projection between `S` and `A \ S`, and let `ord` be injective on `A` (any
order). Writing `A^{<v}` and `A^{≤v}` for the vertices of `A` before `v` and up to `v`,
`Q[S] ∏_{v ∈ S} Q[A^{<v}] = ∏_{v ∈ S} Q[A^{≤v}]`. -/
theorem cFactor_mul_prod_pre {O A S : Finset V} (ord : V → ℕ) (hA : A ⊆ O) (hS : S ⊆ A)
    (hcl : ∀ u ∈ S, ∀ v ∈ A \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑A) (w : ∀ v, α v) :
    M.cFactor O S w * ∏ v ∈ S, M.cFactor O (A.filter fun u => ord u < ord v) w =
      ∏ v ∈ S, M.cFactor O (A.filter fun u => ord u ≤ ord v) w := by
  -- split a subset of `A` into its parts in `S` and outside `S`
  have hsplit : ∀ B ⊆ A, M.cFactor O B w =
      M.cFactor O (B.filter (· ∈ S)) w * M.cFactor O (B.filter (· ∉ S)) w := by
    intro B hB
    conv_lhs => rw [← filter_union_filter_not_eq (· ∈ S) B]
    refine M.cFactor_union ((filter_subset _ _).trans (hB.trans hA))
      ((filter_subset _ _).trans (hB.trans hA)) (disjoint_filter_filter_not _ _ _) ?_ w
    intro u hu v hv
    exact hcl u (mem_filter.1 hu).2 v
      (mem_sdiff.2 ⟨hB (mem_filter.1 hv).1, (mem_filter.1 hv).2⟩)
  have hS_le : ∀ v, (A.filter fun u => ord u ≤ ord v).filter (· ∈ S) =
      S.filter fun u => ord u ≤ ord v := by
    intro v
    ext u
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨-, h⟩, hu⟩
      exact ⟨hu, h⟩
    · rintro ⟨hu, h⟩
      exact ⟨⟨hS hu, h⟩, hu⟩
  have hS_lt : ∀ v, (A.filter fun u => ord u < ord v).filter (· ∈ S) =
      S.filter fun u => ord u < ord v := by
    intro v
    ext u
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨-, h⟩, hu⟩
      exact ⟨hu, h⟩
    · rintro ⟨hu, h⟩
      exact ⟨⟨hS hu, h⟩, hu⟩
  have hR : ∀ v ∈ S, (A.filter fun u => ord u ≤ ord v).filter (· ∉ S) =
      (A.filter fun u => ord u < ord v).filter (· ∉ S) := by
    intro v hv
    ext u
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hu, h⟩, huS⟩
      refine ⟨⟨hu, lt_of_le_of_ne h fun h' => huS ?_⟩, huS⟩
      rwa [hinj hu (hS hv) h']
    · rintro ⟨⟨hu, h⟩, huS⟩
      exact ⟨⟨hu, h.le⟩, huS⟩
  rw [prod_congr rfl fun v _ => hsplit _ (filter_subset _ A),
    prod_congr rfl fun v _ => hsplit (A.filter fun u => ord u ≤ ord v) (filter_subset _ A),
    prod_mul_distrib, prod_mul_distrib]
  simp_rw [hS_le, hS_lt]
  rw [prod_congr rfl fun v hv => congrArg (fun B => M.cFactor O B w) (hR v hv),
    prod_filter_le_eq_mul_prod_filter_lt (fun B => M.cFactor O B w)
    (M.cFactor_empty O w) ord S (hinj.mono (coe_subset.2 hS))]
  ring

/-- **Tian's formula**, divided form: under the hypotheses of `SCM.cFactor_mul_prod_pre` and
`Q[A^{<v}] ≠ 0` for every `v ∈ S`, `Q[S] = ∏_{v ∈ S} Q[A^{≤v}] / Q[A^{<v}]`. -/
theorem cFactor_eq_prod_div {O A S : Finset V} (ord : V → ℕ) (hA : A ⊆ O) (hS : S ⊆ A)
    (hcl : ∀ u ∈ S, ∀ v ∈ A \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑A) (w : ∀ v, α v)
    (hne : ∀ v ∈ S, M.cFactor O (A.filter fun u => ord u < ord v) w ≠ 0) :
    M.cFactor O S w = ∏ v ∈ S, M.cFactor O (A.filter fun u => ord u ≤ ord v) w /
      M.cFactor O (A.filter fun u => ord u < ord v) w := by
  rw [prod_div_distrib, eq_div_iff (prod_ne_zero_iff.2 hne),
    M.cFactor_mul_prod_pre ord hA hS hcl hinj w]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The vertices of `A` up to `v`, and those before `v`, along a topological order of the latent
projection, are closed under the parents (in the projection) that lie in `A`. -/
theorem filter_closed {O A : Finset V} (ord : V → ℕ)
    (hord : ∀ u v, (latentProjection G (↑O)ᶜ).directed.Adj u v → ord u < ord v) (v : V)
    (r : ℕ → ℕ → Prop) [DecidableRel r] (hr : ∀ a b c, a < b → r b c → r a c) :
    ∀ u ∈ A, ∀ x ∈ A.filter (fun u => r (ord u) (ord v)),
      (latentProjection G (↑O)ᶜ).directed.Adj u x → u ∈ A.filter (fun u => r (ord u) (ord v)) :=
  fun u hu x hx hux => mem_filter.2 ⟨hu, hr _ _ _ (hord u x hux) (mem_filter.1 hx).2⟩

/-- **Tian's formula from `Q[A]`, division-free**: with a topological order `ord` of the latent
projection, injective on `A`, the c-factors of the prefixes of `A` are sums of `Q[A]`
(ancestral marginalization), so for `S ⊆ A ⊆ O` closed under bidirected edges inside `A`,
`Q[S] ∏_{v ∈ S} (∑_{A \ A^{<v}} Q[A]) = ∏_{v ∈ S} (∑_{A \ A^{≤v}} Q[A])`. -/
theorem cFactor_mul_prod_sum {O A S : Finset V} (ord : V → ℕ) (hA : A ⊆ O) (hS : S ⊆ A)
    (hcl : ∀ u ∈ S, ∀ v ∈ A \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑A)
    (hord : ∀ u v, (latentProjection G (↑O)ᶜ).directed.Adj u v → ord u < ord v)
    (w : ∀ v, α v) :
    M.cFactor O S w * ∏ v ∈ S, (∑ c ∈ FiniteDist.agreeOn (A \ A.filter fun u => ord u < ord v)ᶜ w,
        M.cFactor O A c) =
      ∏ v ∈ S, ∑ c ∈ FiniteDist.agreeOn (A \ A.filter fun u => ord u ≤ ord v)ᶜ w,
        M.cFactor O A c := by
  simp_rw [M.sum_cFactor_of_closed (filter_subset _ A) hA
    (filter_closed ord hord _ (· < ·) fun _ _ _ => lt_trans),
    M.sum_cFactor_of_closed (filter_subset _ A) hA
    (filter_closed ord hord _ (· ≤ ·) fun _ _ _ h h' => (h.trans_le h').le)]
  exact M.cFactor_mul_prod_pre ord hA hS hcl hinj w

/-- **Tian's formula from `Q[A]`**, divided form (Tian and Pearl 2002): under the hypotheses of
`SCM.cFactor_mul_prod_sum` and the positivity `Q[A^{<v}](w) ≠ 0` for every `v ∈ S`,
`Q[S] = ∏_{v ∈ S} (∑_{A \ A^{≤v}} Q[A]) / (∑_{A \ A^{<v}} Q[A])`. -/
theorem cFactor_eq_prod_sum_div {O A S : Finset V} (ord : V → ℕ) (hA : A ⊆ O) (hS : S ⊆ A)
    (hcl : ∀ u ∈ S, ∀ v ∈ A \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑A)
    (hord : ∀ u v, (latentProjection G (↑O)ᶜ).directed.Adj u v → ord u < ord v)
    (w : ∀ v, α v)
    (hne : ∀ v ∈ S, M.cFactor O (A.filter fun u => ord u < ord v) w ≠ 0) :
    M.cFactor O S w = ∏ v ∈ S,
      (∑ c ∈ FiniteDist.agreeOn (A \ A.filter fun u => ord u ≤ ord v)ᶜ w, M.cFactor O A c) /
        ∑ c ∈ FiniteDist.agreeOn (A \ A.filter fun u => ord u < ord v)ᶜ w, M.cFactor O A c := by
  simp_rw [M.sum_cFactor_of_closed (filter_subset _ A) hA
    (filter_closed ord hord _ (· < ·) fun _ _ _ => lt_trans),
    M.sum_cFactor_of_closed (filter_subset _ A) hA
    (filter_closed ord hord _ (· ≤ ·) fun _ _ _ h h' => (h.trans_le h').le)]
  exact M.cFactor_eq_prod_div ord hA hS hcl hinj w hne

/-! ### The c-factors of the districts from the observed law -/

/-- For `U ⊆ O` closed under the parents (in the latent projection) that are observed, the
c-factor of `U` is the marginal law of `U`. -/
theorem cFactor_eq_margAt_of_closed {O U : Finset V} (hU : U ⊆ O)
    (hcl : ∀ u ∈ O, ∀ v ∈ U, (latentProjection G (↑O)ᶜ).directed.Adj u v → u ∈ U)
    (w : ∀ v, α v) : M.cFactor O U w = M.dist.margAt U w := by
  rw [← M.sum_cFactor_of_closed hU subset_rfl hcl w]
  simp_rw [M.cFactor_self]
  rw [FiniteDist.sum_agreeOn_margAt _ sdiff_subset, Finset.sdiff_sdiff_eq_self hU]

/-- **The c-factor of a district from the observed law, division-free** (Tian and Pearl 2002):
for `S ⊆ O` with no bidirected edge of the latent projection between `S` and `O \ S` (for
instance a district of the latent projection) and a topological order `ord` of the latent
projection injective on `O`,
`Q[S] ∏_{v ∈ S} P(o^{<v}) = ∏_{v ∈ S} P(o^{≤v})`, where `o^{<v}` and `o^{≤v}` are the observed
vertices before `v` and up to `v`. -/
theorem cFactor_mul_prod_margAt {O S : Finset V} (ord : V → ℕ) (hS : S ⊆ O)
    (hcl : ∀ u ∈ S, ∀ v ∈ O \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑O)
    (hord : ∀ u v, (latentProjection G (↑O)ᶜ).directed.Adj u v → ord u < ord v)
    (w : ∀ v, α v) :
    M.cFactor O S w * ∏ v ∈ S, M.dist.margAt (O.filter fun u => ord u < ord v) w =
      ∏ v ∈ S, M.dist.margAt (O.filter fun u => ord u ≤ ord v) w := by
  simp_rw [← M.cFactor_eq_margAt_of_closed (filter_subset _ O)
    (filter_closed ord hord _ (· < ·) fun _ _ _ => lt_trans),
    ← M.cFactor_eq_margAt_of_closed (filter_subset _ O)
    (filter_closed ord hord _ (· ≤ ·) fun _ _ _ h h' => (h.trans_le h').le)]
  exact M.cFactor_mul_prod_pre ord subset_rfl hS hcl hinj w

/-- **The c-factor of a district from the observed law** (Tian and Pearl 2002), divided form:
under the hypotheses of `SCM.cFactor_mul_prod_margAt` and a strictly positive observed law at
`w`, `Q[S] = ∏_{v ∈ S} P(v | o^{<v})`, written as `P(o^{≤v}) / P(o^{<v})`. -/
theorem cFactor_eq_prod_margAt_div {O S : Finset V} (ord : V → ℕ) (hS : S ⊆ O)
    (hcl : ∀ u ∈ S, ∀ v ∈ O \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑O)
    (hord : ∀ u v, (latentProjection G (↑O)ᶜ).directed.Adj u v → ord u < ord v)
    (w : ∀ v, α v) (hpos : 0 < M.dist.margAt O w) :
    M.cFactor O S w = ∏ v ∈ S, M.dist.margAt (O.filter fun u => ord u ≤ ord v) w /
      M.dist.margAt (O.filter fun u => ord u < ord v) w := by
  have hne : ∀ v ∈ S, M.dist.margAt (O.filter fun u => ord u < ord v) w ≠ 0 := fun v _ =>
    (hpos.trans_le (M.dist.margAt_anti (filter_subset _ O) w)).ne'
  rw [prod_div_distrib, eq_div_iff (prod_ne_zero_iff.2 hne),
    M.cFactor_mul_prod_margAt ord hS hcl hinj hord w]

end SCM

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- **The c-factor of a district is identified** (Tian and Pearl 2002): for `S ⊆ O` with no
bidirected edge of the latent projection between `S` and `O \ S`, and a topological order of the
latent projection injective on `O`, the c-factor `Q[S](w)` is identifiable from the observed law
within the class of models on `G` whose observed law is strictly positive. -/
theorem identifiableFrom_cFactor {O S : Finset V} (ord : V → ℕ) (hS : S ⊆ O)
    (hcl : ∀ u ∈ S, ∀ v ∈ O \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑O)
    (hord : ∀ u v, (latentProjection G (↑O)ᶜ).directed.Adj u v → ord u < ord v)
    (w : ∀ v, α v) :
    IdentifiableFrom {m : Model G α | ∀ w, 0 < m.scm.dist.margAt O w} O
      (fun m => m.scm.cFactor O S w) := by
  intro m hm m' hm' hobs
  simp only
  rw [m.scm.cFactor_eq_prod_margAt_div ord hS hcl hinj hord w (hm w),
    m'.scm.cFactor_eq_prod_margAt_div ord hS hcl hinj hord w (hm' w)]
  refine prod_congr rfl fun v _ => ?_
  rw [FiniteDist.margAt_eq_of_marginal_eq hobs (filter_subset _ O) w,
    FiniteDist.margAt_eq_of_marginal_eq hobs (filter_subset _ O) w]

end SCM

end CausalInference
