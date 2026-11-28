/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessModels

/-!
# Non-identifiability of the c-factor of a failing district

Let `G` be an acyclic directed mixed graph on `V`, and let `T` be a failure witness of a
bidirected connected set `d` (`IsIdFailure G d T`: `d ⊂ T`, `T` bidirected connected, every
vertex of `T` an ancestor of `d` inside `T`). On the canonical DAG of `G`, with every vertex of
`G` observed and Boolean values, the c-factor `Q[d]` (Tian and Pearl 2002) is not identifiable
from the observed law within the class of models whose observed law is strictly positive
(`IDCompleteness.not_identifiableFrom_cFactor`): for every value of the vertices outside `d`
there is a value of `d` at which two models of the class with the same observed law give
different values of `Q[d]`.

The two models are those of `IDCompleteness.Setup.model` with no routing. Under the
intervention on every observed vertex outside `d`, the parity of the values of `d` is a fair
bit in model one (a latent bit of a bidirected edge between `d` and `T \ d` flips it), and a
biased bit in model two (it is a function of the intervened values plus the sum of the noise
bits of `d`). This is the hedge argument of Shpitser and Pearl (2006) and of Huang and Valtorta
(2006), with every vertex observed.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

variable {V : Type} [Fintype V] [DecidableEq V] {G : ADMG V} [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj] [DecidableRel G.bidirected.Adj] in
/-- A path from a vertex with a property to a vertex without it has a step leaving the
property. -/
theorem exists_step_of_reflTransGen {α : Type*} {r : α → α → Prop} {P : α → Prop} {x y : α}
    (h : Relation.ReflTransGen r x y) (hx : P x) (hy : ¬ P y) :
    ∃ a b, r a b ∧ P a ∧ ¬ P b := by
  induction h with
  | refl => exact absurd hx hy
  | tail _ hbc ih =>
    rename_i b c _
    by_cases hb : P b
    · exact ⟨b, c, hbc, hb, hy⟩
    · exact ih hb

omit [DecidableRel G.bidirected.Adj] in
/-- A bidirected edge of `G` between `d` and `T \ d`, for a failure witness `T` of `d`. -/
theorem exists_cross {d T : Finset V} (hf : IsIdFailure G d T) (hne : d.Nonempty) :
    ∃ a ∈ d, ∃ b ∈ T \ d, G.bidirected.Adj a b := by
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨s, hsT, hsd⟩ := exists_of_ssubset hf.ssubset
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
    (hf.connected c₀ (hf.ssubset.subset hc₀) s hsT)
  obtain ⟨a, b, hab, ha, hb⟩ := exists_step_of_reflTransGen (P := (· ∈ d)) hr hc₀ hsd
  exact ⟨a, ha, b, mem_sdiff.2 ⟨mem_coe.1 hab.2.2, hb⟩, hab.1⟩

namespace Setup

/-- The construction without routing, for a failure witness `T` of a bidirected connected
set `d`. -/
noncomputable def ofFailure {d T : Finset V} (hf : IsIdFailure G d T) (hd : BiConnected G d) :
    Setup G where
  d := d
  T := T
  fail := hf
  conn := hd
  ch := Classical.choose (exists_forestChild hf.ancestral)
  ch_mem s hs := (Classical.choose_spec (exists_forestChild hf.ancestral) s hs).1
  ch_adj s hs := (Classical.choose_spec (exists_forestChild hf.ancestral) s hs).2
  rt _ := ∅
  rt_adj _ _ h := absurd h (notMem_empty _)
  rt_R _ _ := rfl

variable (S : Setup G) (hG : G.IsAcyclic)

/-- The observed vertices outside `d`. -/
abbrev outD : Finset (V ⊕ V × V) := ADMG.canonicalObs \ S.d.map .inl

omit [DecidableRel G.bidirected.Adj] in
theorem inr_notMem_outD (p : V × V) : (.inr p : V ⊕ V × V) ∉ S.outD := by
  simp

omit [DecidableRel G.bidirected.Adj] in
theorem inl_notMem_outD {c : V} (hc : c ∈ S.d) : (.inl c : V ⊕ V × V) ∉ S.outD := by
  simp [hc]

omit [DecidableRel G.bidirected.Adj] in
theorem inl_mem_outD {s : V} (hs : s ∉ S.d) : (.inl s : V ⊕ V × V) ∈ S.outD := by
  simp [hs]

/-- Under the intervention on the observed vertices outside `d`, a vertex that is not
intervened follows its mechanism. -/
theorem solve_outD (i : Bool) (x ν : V ⊕ V × V → Bool) {j : V ⊕ V × V} (hj : j ∉ S.outD) :
    ((S.scm hG i).intervene S.outD x).solve ν j =
      S.mech i j (((S.scm hG i).intervene S.outD x).solve ν) (ν j) :=
  ((solve_intervene_boolSCM_iff (S.readsParents i) S.outD x).1 rfl).2 j hj

theorem lat_solve_outD (i : Bool) (x ν : V ⊕ V × V → Bool) :
    lat (((S.scm hG i).intervene S.outD x).solve ν) = lat ν := by
  funext p
  exact S.solve_outD hG i x ν (S.inr_notMem_outD p)

/-- **The parity of `d` in model one** under the intervention on the observed vertices
outside `d`, without routing. -/
theorem parity_false (hrt : ∀ v, S.rt v = ∅) (x ν : V ⊕ V × V → Bool) :
    ∑ c ∈ S.d, ((S.scm hG false).intervene S.outD x).solve ν (.inl c) =
      ∑ c ∈ S.d, (bnd G S.T (lat ν) c + ν (.inl c)) := by
  refine sum_congr rfl fun c hc => ?_
  rw [S.solve_outD hG false x ν (S.inl_notMem_outD hc), S.mech_d_false hc, S.lat_solve_outD,
    hrt, sum_empty, add_zero]

/-- **The parity of `d` in model two** under the intervention on the observed vertices
outside `d`, without routing: the intervened values of the forest parents plus the noise bits
of `d`. -/
theorem parity_true (hrt : ∀ v, S.rt v = ∅) (x ν : V ⊕ V × V → Bool) :
    ∑ c ∈ S.d, ((S.scm hG true).intervene S.outD x).solve ν (.inl c) =
      ∑ c ∈ S.d, ∑ s ∈ S.fp c, x (.inl s) + ∑ c ∈ S.d, ν (.inl c) := by
  have h : ∀ c ∈ S.d, ((S.scm hG true).intervene S.outD x).solve ν (.inl c) =
      ∑ s ∈ S.fp c, x (.inl s) + bnd G S.d (lat ν) c + ν (.inl c) := by
    intro c hc
    rw [S.solve_outD hG true x ν (S.inl_notMem_outD hc), S.mech_d_true hc, S.lat_solve_outD,
      hrt, sum_empty, add_zero]
    congr 2
    refine sum_congr rfl fun s hs => ?_
    exact SCM.solve_intervene_of_mem _ ν
      (S.inl_mem_outD (mem_sdiff.1 (S.fp_subset c hs)).2)
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, sum_bnd_self, add_zero]

/-- **Model one gives `d` a fair parity** under the intervention on the observed vertices
outside `d`, without routing. -/
theorem probOf_parity_false (hrt : ∀ v, S.rt v = ∅) (x : V ⊕ V × V → Bool) (b : Bool) :
    (FiniteDist.pi S.noise).probOf (fun ν =>
      ∑ c ∈ S.d, ((S.scm hG false).intervene S.outD x).solve ν (.inl c) = b) = 1 / 2 := by
  obtain ⟨a, ha, a', ha', hadj⟩ := exists_cross S.fail S.d_nonempty
  have hq : (a, a') ∈ bedges G S.T :=
    mem_bedges.2 ⟨hadj, S.fail.ssubset.subset ha, (mem_sdiff.1 ha').1⟩
  let e : V ⊕ V × V → Bool := Sum.elim 0 (single (a, a'))
  let φ : (V ⊕ V × V → Bool) → V ⊕ V × V → Bool := fun ν => ν + e
  have hφφ : ∀ ν, φ (φ ν) = ν := fun ν => by
    funext j
    simp only [φ, Pi.add_apply, add_assoc, bool_add_self, add_zero]
  have hcross : ∑ c ∈ S.d, bnd G S.T (single (a, a')) c = 1 := by
    simp only [bnd_single hq]
    have ha'd := (mem_sdiff.1 ha').2
    rw [sum_add_distrib, sum_ite_eq, sum_ite_eq]
    simp only [ha, ha'd, ↓reduceIte, add_zero]
  have hpar : ∀ ν, ∑ c ∈ S.d, (bnd G S.T (lat (φ ν)) c + (φ ν) (.inl c)) =
      ∑ c ∈ S.d, (bnd G S.T (lat ν) c + ν (.inl c)) + 1 := by
    intro ν
    have hl : lat (φ ν) = lat ν + single (a, a') := rfl
    simp only [hl, bnd_add, φ, Pi.add_apply, e, Sum.elim_inl, Pi.zero_apply, add_zero]
    rw [← hcross, ← sum_add_distrib]
    exact sum_congr rfl fun c _ => by ring
  simp_rw [S.parity_false hG hrt x]
  unfold FiniteDist.probOf
  refine IDCompletenessBow.prob_eq_of_involution _ _ φ hφφ (fun ν => ?_) (q' := 1 / 2)
    (by norm_num) fun ν _ => ?_
  · simp only [mem_filter, mem_univ, true_and, hpar]
    cases ∑ c ∈ S.d, (bnd G S.T (lat ν) c + ν (.inl c)) <;> cases b <;> decide
  · rw [FiniteDist.pi_add_eq _ _ _ fun j hj => ?_]
    rcases j with v | p
    · exact absurd hj (by simp [e])
    · rfl

/-- **Model two gives `d` a biased parity** under the intervention on the observed vertices
outside `d`, without routing. -/
theorem probOf_parity_true_ne (hrt : ∀ v, S.rt v = ∅) (x : V ⊕ V × V → Bool) (b : Bool) :
    (FiniteDist.pi S.noise).probOf (fun ν =>
      ∑ c ∈ S.d, ((S.scm hG true).intervene S.outD x).solve ν (.inl c) = b) ≠ 1 / 2 := by
  set κ := ∑ c ∈ S.d, ∑ s ∈ S.fp c, x (.inl s)
  have h : ∀ ν : V ⊕ V × V → Bool,
      (∑ c ∈ S.d, ((S.scm hG true).intervene S.outD x).solve ν (.inl c) = b) ↔
        ∑ j ∈ S.d.map .inl, ν j = b + κ := by
    intro ν
    have hs : ∑ j ∈ S.d.map .inl, ν j = ∑ c ∈ S.d, ν (.inl c) := sum_map _ _ _
    rw [S.parity_true hG hrt x ν, hs]
    constructor
    · rintro rfl
      rw [add_comm κ, add_assoc, bool_add_self, add_zero]
    · intro h
      rw [h, add_comm b, ← add_assoc, bool_add_self, zero_add]
  rw [FiniteDist.probOf_congr _ h]
  refine probOf_parity_ne_half _ _ (fun j hj => ?_) _
  obtain ⟨c, hc, rfl⟩ := mem_map.1 hj
  have : c ∉ S.T \ S.d := fun h' => (mem_sdiff.1 h').2 hc
  simp [noise, this]

end Setup

/-- **The c-factor of a failing set is not identifiable.** Let `G` be an acyclic directed mixed
graph and `T` a failure witness of a bidirected connected set `d` (`IsIdFailure G d T`). On the
canonical DAG of `G`, with every vertex of `G` observed, for every configuration `x` there is a
configuration `w` agreeing with `x` outside the copy of `d` at which the c-factor `Q[d](w)` is
not identifiable from the observed law within the class of Boolean models whose observed law
is strictly positive. The hypothesis that `d` is bidirected connected holds for the districts
of `idAlg_eq_none_iff`. -/
theorem not_identifiableFrom_cFactor (hG : G.IsAcyclic) {d T : Finset V}
    (hf : IsIdFailure G d T) (hd : BiConnected G d) (x : V ⊕ V × V → Bool) :
    ∃ w : V ⊕ V × V → Bool, (∀ j ∉ d.map .inl, w j = x j) ∧
      ¬ SCM.IdentifiableFrom
        {m : SCM.Model G.canonicalDAG (fun _ => Bool) |
          ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
        (fun m => m.scm.cFactor ADMG.canonicalObs (d.map .inl) w) := by
  classical
  set S := Setup.ofFailure hf hd
  have hrt : ∀ v, S.rt v = ∅ := fun _ => rfl
  by_contra hcon
  push Not at hcon
  -- the intervened laws agree on the copy of `d`
  have hmarg : ∀ c : V ⊕ V × V → Bool,
      ((S.scm hG false).intervene S.outD x).dist.margAt (d.map .inl) c =
        ((S.scm hG true).intervene S.outD x).dist.margAt (d.map .inl) c := by
    intro c
    let wc : V ⊕ V × V → Bool := fun j => if j ∈ d.map .inl then c j else x j
    have hwc : ∀ j ∉ d.map .inl, wc j = x j := fun j hj => by simp only [wc, hj, ↓reduceIte]
    have hid := hcon wc hwc (S.model hG false) (S.margAt_pos hG false)
      (S.model hG true) (S.margAt_pos hG true) (S.marginal_eq hG)
    change (S.scm hG false).cFactor _ _ wc = (S.scm hG true).cFactor _ _ wc at hid
    have hX : ∀ i, ((S.scm hG i).intervene S.outD wc).dist =
        ((S.scm hG i).intervene S.outD x).dist := fun i =>
      (S.scm hG i).dist_intervene_congr fun j hj => hwc j (mem_sdiff.1 hj).2
    have hY : ∀ i, ((S.scm hG i).intervene S.outD x).dist.margAt (d.map .inl) wc =
        ((S.scm hG i).intervene S.outD x).dist.margAt (d.map .inl) c := fun i =>
      FiniteDist.margAt_congr _ _ fun j hj => by simp only [wc, hj, ↓reduceIte]
    change ((S.scm hG false).intervene S.outD wc).dist.margAt (d.map .inl) wc =
      ((S.scm hG true).intervene S.outD wc).dist.margAt (d.map .inl) wc at hid
    rw [hX, hX, hY, hY] at hid
    exact hid
  have hm := marginal_eq_of_margAt_eq hmarg
  have hp := FiniteDist.probOf_eq_of_marginal_eq hm
    (fun τ => ∑ c ∈ d, τ (.inl c) = true) fun τ τ' h => by
      rw [sum_congr rfl fun c hc => h (.inl c) (mem_map_of_mem _ hc)]
  rw [SCM.probOf_dist, SCM.probOf_dist, SCM.noiseDist_intervene, SCM.noiseDist_intervene,
    S.noiseDist_scm, S.noiseDist_scm] at hp
  exact S.probOf_parity_true_ne hG hrt x true (hp ▸ S.probOf_parity_false hG hrt x true)

end IDCompleteness

end CausalInference
