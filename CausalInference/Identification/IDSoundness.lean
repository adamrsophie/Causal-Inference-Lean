/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDAlgorithm

/-!
# Soundness of the identification algorithm

Let `M : SCM G α ε` be a finite structural causal model on a directed acyclic graph `G`, with a
finset `O` of observed vertices (all other vertices latent, with no restriction on where they
sit in `G`), whose latent projection `latentProjection G (↑O)ᶜ` is the mixed graph `H`. Let
`ord` be a topological order of `H` that is injective on `O`, and assume the observed law is
strictly positive. If the identification algorithm `idAlg H ord O X Y` returns an expression
`e`, then for every configuration `w`,
`P(Y = w_Y | do(X := w_X)) = e.eval P w`,
where `P` is the joint law of the model; the right side depends on `P` only through its marginal
on `O`. Hence the effect is identifiable from the observed law within the class of models on
`G` with a strictly positive observed law.

## Main results

* `SCM.eval_tianExpr`: Tian's formula evaluates to the c-factor.
* `SCM.eval_identify`: soundness of the recursive step: from an expression for `Q[T]`, the
  returned expression evaluates to `Q[C]`.
* `SCM.effect_eq_eval_of_idAlg`: **soundness of the identification algorithm**.
* `SCM.identifiableFrom_of_idAlg`: the effect is identifiable (`SCM.IdentifiableFrom`) whenever
  the algorithm succeeds.

Sources: Tian (2002), PhD thesis; Tian and Pearl (2002), *A general identification condition for
causal effects*; Shpitser and Pearl (2006), *Identification of joint interventional
distributions in recursive semi-Markovian causal models*.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- **Tian's formula evaluates to the c-factor**: if `q` evaluates to `Q[A]` and `S ⊆ A ⊆ O`
is closed under bidirected edges inside `A`, then `tianExpr ord A S q` evaluates to `Q[S]`,
for a topological order `ord` of the latent projection injective on `A` and a strictly positive
observed law. -/
theorem eval_tianExpr {O A S : Finset V} (ord : V → ℕ) {q : IdExpr V}
    (hq : ∀ c, q.eval M.dist c = M.cFactor O A c) (hA : A ⊆ O) (hS : S ⊆ A)
    (hcl : ∀ u ∈ S, ∀ v ∈ A \ S, ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v)
    (hinj : Set.InjOn ord ↑A)
    (hord : ∀ u v, (latentProjection G (↑O)ᶜ).directed.Adj u v → ord u < ord v)
    (hpos : ∀ w, 0 < M.dist.margAt O w) (w : ∀ v, α v) :
    (tianExpr ord A S q).eval M.dist w = M.cFactor O S w := by
  rw [M.cFactor_eq_prod_sum_div ord hA hS hcl hinj hord w
    fun v _ => (M.cFactor_pos ((filter_subset _ A).trans hA) hpos w).ne']
  simp only [tianExpr, IdExpr.eval_prodV, IdExpr.eval_div, IdExpr.eval_sum, hq]

variable {H : ADMG V} [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]

/-- **Soundness of the recursive step** of the identification algorithm: if `C ⊆ T ⊆ O`, `q`
evaluates to `Q[T]`, and `identify H ord C T q` returns `e`, then `e` evaluates to `Q[C]`. The
model's latent projection is `H`, `ord` is a topological order of `H` injective on `O`, and the
observed law is strictly positive. The proof is by strong induction on `T`: the base case is
ancestral marginalization (`SCM.sum_cFactor_of_closed`); the recursive case computes `Q[A]` by
ancestral marginalization and `Q[T']` by Tian's formula (`SCM.eval_tianExpr`). -/
theorem eval_identify {O : Finset V} (hH : latentProjection G (↑O)ᶜ = H) (ord : V → ℕ)
    (hinj : Set.InjOn ord ↑O) (hord : ∀ u v, H.directed.Adj u v → ord u < ord v)
    (hpos : ∀ w, 0 < M.dist.margAt O w) :
    ∀ (T C : Finset V) (q e : IdExpr V), C ⊆ T → T ⊆ O →
      (∀ c, q.eval M.dist c = M.cFactor O T c) → identify H ord C T q = some e →
      ∀ c, e.eval M.dist c = M.cFactor O C c := by
  have hdir : ∀ {u v}, (latentProjection G (↑O)ᶜ).directed.Adj u v → H.directed.Adj u v :=
    fun h => hH ▸ h
  have hbid : ∀ {u v}, (latentProjection G (↑O)ᶜ).bidirected.Adj u v → H.bidirected.Adj u v :=
    fun h => hH ▸ h
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro C q e hCT hTO hq he c
    rw [identify] at he
    split_ifs at he with h₁ h₂
    · cases he
      simp only [IdExpr.eval_sum, hq]
      refine M.sum_cFactor_of_closed hCT hTO (fun u hu v hv huv => ?_) c
      have := ancIn_closed hu (h₁.symm ▸ hv) (hdir huv)
      rwa [h₁] at this
    · have hAT : ancIn H T C ⊆ T := ancIn_subset T C
      have hAO := hAT.trans hTO
      have hCA : C ⊆ ancIn H T C := subset_ancIn hCT
      have hqA : ∀ c, (IdExpr.sum (T \ ancIn H T C) q).eval M.dist c =
          M.cFactor O (ancIn H T C) c := fun c => by
        simp only [IdExpr.eval_sum, hq]
        exact M.sum_cFactor_of_closed hAT hTO
          (fun u hu v hv huv => ancIn_closed hu hv (hdir huv)) c
      have hT'A := closeIn_subset (H := H) (ancIn H T C) C
      have hcl : ∀ u ∈ closeIn H (ancIn H T C) C, ∀ v ∈ ancIn H T C \ closeIn H (ancIn H T C) C,
          ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v := fun u hu v hv huv =>
        (mem_sdiff.1 hv).2 (closeIn_closed hu (mem_sdiff.1 hv).1 (hbid huv))
      exact ih _ (hT'A.trans_ssubset h₂) C _ e (subset_closeIn hCA) (hT'A.trans hAO)
        (M.eval_tianExpr ord hqA hAO hT'A hcl (hinj.mono (coe_subset.2 hAO))
          (fun u v h => hord u v (hdir h)) hpos) he c

/-- **Soundness of the identification algorithm** (Tian 2002; Tian and Pearl 2002; Shpitser
and Pearl 2006). Let `M` be a structural causal model on `G` whose latent projection onto the
observed set `O` is `H`, let `ord` be a topological order of `H` injective on `O`, and let the
observed law be strictly positive. If `idAlg H ord O X Y` returns `e`, then at every
configuration `w`, `P(Y = w_Y | do(X := w_X)) = e.eval P w`, with `P = M.dist`. -/
theorem effect_eq_eval_of_idAlg {O X Y : Finset V} (hH : latentProjection G (↑O)ᶜ = H)
    (ord : V → ℕ) (hinj : Set.InjOn ord ↑O) (hord : ∀ u v, H.directed.Adj u v → ord u < ord v)
    (hpos : ∀ w, 0 < M.dist.margAt O w) {e : IdExpr V} (he : idAlg H ord O X Y = some e)
    (w : ∀ v, α v) : M.effect X w Y w = e.eval M.dist w := by
  have hdir : ∀ {u v}, (latentProjection G (↑O)ᶜ).directed.Adj u v → H.directed.Adj u v :=
    fun h => hH ▸ h
  have hbid : ∀ {u v}, (latentProjection G (↑O)ᶜ).bidirected.Adj u v → H.bidirected.Adj u v :=
    fun h => hH ▸ h
  have hident := M.eval_identify hH ord hinj hord hpos
  rw [idAlg] at he
  split_ifs at he with h₁ h₂
  cases he
  obtain ⟨hX, hY⟩ := h₁
  set D := ancIn H (O \ X) Y with hDdef
  have hDsub : D ⊆ O \ X := ancIn_subset _ _
  have hYD : Y ⊆ D := subset_ancIn hY
  have hDO : D ⊆ O := hDsub.trans sdiff_subset
  have hpart : ∀ d ∈ H.districtsOn D, ∀ c,
      ((idPart H ord O d).getD (.marg ∅)).eval M.dist c = M.cFactor O d c := by
    intro d hd c
    obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 (h₂ d hd)
    rw [he', Option.getD_some]
    have hdO : d ⊆ O := (ADMG.subset_of_mem_districtsOn hd).trans hDO
    have hcl : ∀ u ∈ closeIn H O d, ∀ v ∈ O \ closeIn H O d,
        ¬ (latentProjection G (↑O)ᶜ).bidirected.Adj u v := fun u hu v hv huv =>
      (mem_sdiff.1 hv).2 (closeIn_closed hu (mem_sdiff.1 hv).1 (hbid huv))
    refine hident _ d _ e' (subset_closeIn hdO) (closeIn_subset _ _) (fun c' => ?_) he' c
    exact M.eval_tianExpr ord (fun c => by simp [M.cFactor_self]) subset_rfl
      (closeIn_subset _ _) hcl hinj (fun u v h => hord u v (hdir h)) hpos c'
  simp only [IdExpr.eval_sum, IdExpr.eval_prodSets]
  rw [M.effect_eq_sum_cFactor hX hY]
  have hset : (O \ X) \ Y = ((O \ X) \ D) ∪ (D \ Y) := by
    ext v
    have h1 := @hYD v
    have h2 := @hDsub v
    simp only [mem_sdiff, mem_union] at h1 h2 ⊢
    tauto
  have hdisj : Disjoint ((O \ X) \ D) (D \ Y) :=
    disjoint_left.2 fun v hv hv' => (mem_sdiff.1 hv).2 (mem_sdiff.1 hv').1
  rw [hset, FiniteDist.sum_agreeOn_union hdisj]
  refine sum_congr rfl fun c _ => ?_
  rw [M.sum_cFactor_of_closed hDsub sdiff_subset
      (fun u hu v hv huv => ancIn_closed hu hv (hdir huv)) c,
    M.cFactor_eq_prod_districtsOn H (fun _ _ h => hbid h) hDO c]
  exact prod_congr rfl fun d hd => (hpart d hd c).symm

end SCM

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  {H : ADMG V} [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]

/-- **Identifiability from a successful run of the identification algorithm.** Let `G` be a
directed acyclic graph whose latent projection onto the observed set `O` is `H`, and `ord` a
topological order of `H` injective on `O`. If `idAlg H ord O X Y` returns an expression, then
for every configuration `w` the effect `P(Y = w_Y | do(X := w_X))` is identifiable from the
observed law within the class of models on `G` whose observed law is strictly positive. -/
theorem identifiableFrom_of_idAlg {O X Y : Finset V} (hH : latentProjection G (↑O)ᶜ = H)
    (ord : V → ℕ) (hinj : Set.InjOn ord ↑O) (hord : ∀ u v, H.directed.Adj u v → ord u < ord v)
    {e : IdExpr V} (he : idAlg H ord O X Y = some e) (w : ∀ v, α v) :
    IdentifiableFrom {m : Model G α | ∀ w, 0 < m.scm.dist.margAt O w} O
      (fun m => m.scm.effect X w Y w) := by
  intro m hm m' hm' hobs
  simp only
  rw [m.scm.effect_eq_eval_of_idAlg hH ord hinj hord hm he w,
    m'.scm.effect_eq_eval_of_idAlg hH ord hinj hord hm' he w,
    IdExpr.eval_eq_of_marginal_eq hobs e (idAlg_margWithin H ord he)]

end SCM

end CausalInference
