/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessBoundary

/-!
# The two models of the completeness proof

Fix an acyclic directed mixed graph `G` on `V`, a failure witness `T` of a bidirected connected
set `d` (`IsIdFailure G d T`), and write `R = T \ d`. Every vertex `s ∈ R` has a child `ch s` in
`T` (the first step of a directed path inside `T` from `s` to `d`). A routing relation `rt`
(the vertices `w ∈ rt v` are parents of `v`, and no vertex of `R` receives a routed input) is
a parameter; it is empty for the c-factor.

On the canonical DAG of `G`, with Boolean values, two models (`IDCompleteness.Setup.model`,
`i = false` for model one, `i = true` for model two) are defined by exclusive or mechanisms.
Latent vertices are fair bits. A vertex `s ∈ R` is the boundary of the latent bits of the
bidirected edges inside `T` at `s` plus the values of its forest parents (no noise). A vertex
`c ∈ d` is, in model one, the boundary of the latent bits inside `T` at `c`, and in model two,
the values of its forest parents plus the boundary of the latent bits inside `d` at `c`; in both
models plus its routed inputs and a noise bit that is true with probability `1/4`. Every other
vertex is its routed inputs plus such a noise bit.

## Main results

* `IDCompleteness.Setup.marginal_eq` (**equal observed laws**): the two models have the same
  law of the observed vertices. The proof is a shear: an involution of the noise, changing
  only fair latent bits inside `d`, that carries the solution of model one to that of model
  two on the observed vertices (`IDCompleteness.Setup.solve_shear`).
* `IDCompleteness.Setup.margAt_pos` (**positivity**): the observed law of each model is
  strictly positive.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

variable {V : Type} [Fintype V] [DecidableEq V] {G : ADMG V} [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj]

omit [DecidableRel G.bidirected.Adj] in
/-- Every vertex of `T` outside `d` has a child in `T`, when every vertex of `T` is an ancestor
of `d` inside `T`. -/
theorem exists_forestChild {d T : Finset V} (h : ancIn G T d = T) :
    ∃ ch : V → V, ∀ s ∈ T \ d, ch s ∈ T ∧ G.directed.Adj s (ch s) := by
  have key : ∀ s ∈ T \ d, ∃ c, c ∈ T ∧ G.directed.Adj s c := by
    intro s hs
    obtain ⟨hsT, hsd⟩ := mem_sdiff.1 hs
    rw [← h] at hsT
    obtain ⟨hs', -⟩ := mem_inter.1 hsT
    obtain ⟨c₀, hc₀, hp⟩ := ADMG.mem_ancestorsOfFinset.1 hs'
    rcases hp.cases_head with rfl | ⟨c, hsc, -⟩
    · exact absurd hc₀ hsd
    · exact ⟨c, mem_coe.1 hsc.2.2, hsc.1⟩
  choose! ch hch using key
  exact ⟨ch, hch⟩

/-- The data of the construction: a failure witness `T` of a bidirected connected set `d`, a
forest child `ch` on `R = T \ d`, and a routing relation `rt` whose inputs are parents and
never enter `R`. -/
structure Setup (G : ADMG V) [DecidableRel G.directed.Adj] where
  /-- The inner set. -/
  d : Finset V
  /-- The failure witness. -/
  T : Finset V
  /-- `T` is a failure witness of `d`. -/
  fail : IsIdFailure G d T
  /-- `d` is bidirected connected. -/
  conn : BiConnected G d
  /-- The forest child. -/
  ch : V → V
  /-- The forest child lies in `T`. -/
  ch_mem : ∀ s ∈ T \ d, ch s ∈ T
  /-- The forest child is a child. -/
  ch_adj : ∀ s ∈ T \ d, G.directed.Adj s (ch s)
  /-- The routed inputs of each vertex. -/
  rt : V → Finset V
  /-- Routed inputs are parents. -/
  rt_adj : ∀ v, ∀ w ∈ rt v, G.directed.Adj w v
  /-- No vertex of `T \ d` receives a routed input. -/
  rt_R : ∀ v ∈ T \ d, rt v = ∅

namespace Setup

variable (S : Setup G)

/-- The latent part of a configuration of the canonical DAG. -/
def lat (σ : V ⊕ V × V → Bool) : V × V → Bool := fun p => σ (.inr p)

/-- The forest parents of `v`: the vertices of `T \ d` whose forest child is `v`. -/
def fp (v : V) : Finset V := (S.T \ S.d).filter fun s => S.ch s = v

omit [DecidableRel G.bidirected.Adj] in
/-- The forest parents lie in `T \ d`. -/
theorem fp_subset (v : V) : S.fp v ⊆ S.T \ S.d := filter_subset _ _

/-- The mechanism of the observed vertex `v` without its noise bit, in model `i`. -/
def base (i : Bool) (v : V) (σ : V ⊕ V × V → Bool) : Bool :=
  if v ∈ S.T \ S.d then bnd G S.T (lat σ) v + ∑ s ∈ S.fp v, σ (.inl s)
  else if v ∈ S.d then
    (if i then ∑ s ∈ S.fp v, σ (.inl s) + bnd G S.d (lat σ) v else bnd G S.T (lat σ) v) +
      ∑ w ∈ S.rt v, σ (.inl w)
  else ∑ w ∈ S.rt v, σ (.inl w)

/-- The mechanisms of model `i`: a latent vertex is its noise bit; a vertex of `T \ d` ignores
its noise bit; every other observed vertex adds its noise bit. -/
def mech (i : Bool) : V ⊕ V × V → (V ⊕ V × V → Bool) → Bool → Bool
  | .inr _, _, e => e
  | .inl v, σ, e => if v ∈ S.T \ S.d then S.base i v σ else S.base i v σ + e

/-- The noise laws: fair bits at the latent vertices and at `T \ d`, bits true with
probability `1/4` elsewhere. -/
noncomputable def noise : V ⊕ V × V → FiniteDist Bool
  | .inr _ => FiniteDist.uniform
  | .inl v => if v ∈ S.T \ S.d then FiniteDist.uniform else quarterBit

/-- The mechanism of a latent vertex. -/
theorem mech_inr (i : Bool) (p : V × V) (σ : V ⊕ V × V → Bool) (e : Bool) :
    S.mech i (.inr p) σ e = e := rfl

/-- The mechanism of a vertex of `T \ d`. -/
theorem mech_R (i : Bool) {v : V} (hv : v ∈ S.T \ S.d) (σ : V ⊕ V × V → Bool) (e : Bool) :
    S.mech i (.inl v) σ e = bnd G S.T (lat σ) v + ∑ s ∈ S.fp v, σ (.inl s) := by
  simp [mech, base, hv]

/-- The mechanism of a vertex of `d` in model one. -/
theorem mech_d_false {v : V} (hv : v ∈ S.d) (σ : V ⊕ V × V → Bool) (e : Bool) :
    S.mech false (.inl v) σ e = bnd G S.T (lat σ) v + ∑ w ∈ S.rt v, σ (.inl w) + e := by
  have : v ∉ S.T \ S.d := fun h => (mem_sdiff.1 h).2 hv
  simp [mech, base, hv, this]

/-- The mechanism of a vertex of `d` in model two. -/
theorem mech_d_true {v : V} (hv : v ∈ S.d) (σ : V ⊕ V × V → Bool) (e : Bool) :
    S.mech true (.inl v) σ e = ∑ s ∈ S.fp v, σ (.inl s) + bnd G S.d (lat σ) v +
      ∑ w ∈ S.rt v, σ (.inl w) + e := by
  have : v ∉ S.T \ S.d := fun h => (mem_sdiff.1 h).2 hv
  simp [mech, base, hv, this]

/-- The mechanism of a vertex outside `T`. -/
theorem mech_out (i : Bool) {v : V} (hv : v ∉ S.T) (σ : V ⊕ V × V → Bool) (e : Bool) :
    S.mech i (.inl v) σ e = ∑ w ∈ S.rt v, σ (.inl w) + e := by
  have h1 : v ∉ S.T \ S.d := fun h => hv (mem_sdiff.1 h).1
  have h2 : v ∉ S.d := fun h => hv (S.fail.ssubset.subset h)
  simp [mech, base, h1, h2]

omit [DecidableRel G.bidirected.Adj] in
/-- Every noise value has positive mass. -/
theorem noise_pos (j : V ⊕ V × V) (b : Bool) : 0 < S.noise j b := by
  rcases j with v | _
  · simp only [noise]
    split_ifs
    · simp
    · exact quarterBit_pos b
  · simp [noise]

omit [DecidableRel G.directed.Adj] in
/-- A boundary relative to any set, of the latent part, reads only parents. -/
theorem bnd_lat_congr (A : Finset V) {v : V} {σ σ' : V ⊕ V × V → Bool}
    (h : ∀ u, G.canonicalDAG.Adj u (.inl v) → σ u = σ' u) :
    bnd G A (lat σ) v = bnd G A (lat σ') v :=
  bnd_congr_at fun _ hp hpv => h _ (ADMG.canonicalDAG_adj_inr_inl.2
    ⟨(mem_bedges.1 hp).1, hpv.imp Eq.symm Eq.symm⟩)

omit [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj] in
/-- A sum of observed values over a set of parents reads only parents. -/
theorem sum_inl_congr {s : Finset V} {v : V} (hs : ∀ w ∈ s, G.directed.Adj w v)
    {σ σ' : V ⊕ V × V → Bool} (h : ∀ u, G.canonicalDAG.Adj u (.inl v) → σ u = σ' u) :
    ∑ w ∈ s, σ (.inl w) = ∑ w ∈ s, σ' (.inl w) :=
  sum_congr rfl fun w hw => h _ (ADMG.canonicalDAG_adj_inl_inl.2 (hs w hw))

omit [DecidableRel G.bidirected.Adj] in
/-- The forest parents are parents. -/
theorem fp_adj {v : V} : ∀ s ∈ S.fp v, G.directed.Adj s v := by
  intro s hs
  obtain ⟨hs', hv⟩ := mem_filter.1 hs
  rw [← hv]
  exact S.ch_adj s hs'

/-- The mechanisms read only parents. -/
theorem readsParents (i : Bool) : ReadsParents G.canonicalDAG (S.mech i) := by
  intro j σ σ' e h
  rcases j with v | p
  · have hb : S.base i v σ = S.base i v σ' := by
      unfold base
      rw [bnd_lat_congr S.T h, bnd_lat_congr S.d h, sum_inl_congr S.fp_adj h,
        sum_inl_congr (S.rt_adj v) h]
    simp only [mech, hb]
  · rfl

/-- Model `i` as a Boolean structural causal model on the canonical DAG. -/
noncomputable def scm (hG : G.IsAcyclic) (i : Bool) :
    SCM G.canonicalDAG (fun _ => Bool) (fun _ => Bool) :=
  boolSCM G.canonicalDAG hG.canonicalDAG (S.mech i) S.noise

/-- Model `i`, bundled with its noise types. -/
noncomputable def model (hG : G.IsAcyclic) (i : Bool) : SCM.Model G.canonicalDAG (fun _ => Bool) :=
  ⟨fun _ => Bool, S.scm hG i⟩

variable (hG : G.IsAcyclic)

/-- The noise law of model `i` does not depend on `i`. -/
theorem noiseDist_scm (i : Bool) : (S.scm hG i).noiseDist = FiniteDist.pi S.noise := rfl

/-! ### Solutions -/

/-- The solution of model `i` follows the mechanisms. -/
theorem solve_apply (i : Bool) (ν : V ⊕ V × V → Bool) (j : V ⊕ V × V) :
    (S.scm hG i).solve ν j = S.mech i j ((S.scm hG i).solve ν) (ν j) :=
  solve_boolSCM_apply (S.readsParents i) ν j

/-- Latent vertices are their noise bits. -/
theorem lat_solve (i : Bool) (ν : V ⊕ V × V → Bool) : lat ((S.scm hG i).solve ν) = lat ν := by
  funext p
  exact S.solve_apply hG i ν (.inr p)

/-- The vertices of `T \ d` in model `i`. -/
theorem solve_R (i : Bool) (ν : V ⊕ V × V → Bool) {s : V} (hs : s ∈ S.T \ S.d) :
    (S.scm hG i).solve ν (.inl s) = bnd G S.T (lat ν) s +
      ∑ s' ∈ S.fp s, (S.scm hG i).solve ν (.inl s') := by
  rw [S.solve_apply hG i ν (.inl s)]
  simp only [mech, hs, ite_true, base, lat_solve]

omit [DecidableRel G.bidirected.Adj] in
/-- The forest parents of the vertices of `T` partition `T \ d`. -/
theorem sum_fp (g : V → Bool) : ∑ v ∈ S.T, ∑ s ∈ S.fp v, g s = ∑ s ∈ S.T \ S.d, g s :=
  sum_fiberwise_of_maps_to (fun s hs => S.ch_mem s hs) g

/-- The boundary relative to `T` sums to the same value over `T \ d` and over `d`. -/
theorem sum_R_bnd (u : V × V → Bool) :
    ∑ s ∈ S.T \ S.d, bnd G S.T u s = ∑ c ∈ S.d, bnd G S.T u c := by
  have h := sum_bnd_self (G := G) S.T u
  rw [← sum_sdiff S.fail.ssubset.subset] at h
  calc _ = ∑ s ∈ S.T \ S.d, bnd G S.T u s +
        (∑ s ∈ S.T \ S.d, bnd G S.T u s + ∑ c ∈ S.d, bnd G S.T u c) := by rw [h, add_zero]
    _ = _ := by rw [← add_assoc, bool_add_self, zero_add]

/-- **The forest parents of `d` carry the boundary of `T \ d`.** If a configuration satisfies the
equations of the vertices of `T \ d`, the values of the forest parents of the vertices of `d`
sum to the boundary of the latent bits over `T \ d`. -/
theorem sum_d_fp {t : V ⊕ V × V → Bool}
    (ht : ∀ s ∈ S.T \ S.d, t (.inl s) = bnd G S.T (lat t) s + ∑ s' ∈ S.fp s, t (.inl s')) :
    ∑ c ∈ S.d, ∑ s ∈ S.fp c, t (.inl s) = ∑ s ∈ S.T \ S.d, bnd G S.T (lat t) s := by
  have h1 := S.sum_fp fun s => t (.inl s)
  rw [← sum_sdiff S.fail.ssubset.subset] at h1
  have h2 : ∑ s ∈ S.T \ S.d, t (.inl s) = ∑ s ∈ S.T \ S.d, bnd G S.T (lat t) s +
      ∑ s ∈ S.T \ S.d, ∑ s' ∈ S.fp s, t (.inl s') := by
    rw [← sum_add_distrib]
    exact sum_congr rfl ht
  rw [h2] at h1
  set A := ∑ s ∈ S.T \ S.d, ∑ s' ∈ S.fp s, t (.inl s')
  set B := ∑ c ∈ S.d, ∑ s ∈ S.fp c, t (.inl s)
  set C := ∑ s ∈ S.T \ S.d, bnd G S.T (lat t) s
  calc B = (A + B) + A := by rw [add_comm A B, add_assoc, bool_add_self, add_zero]
    _ = (C + A) + A := by rw [h1]
    _ = C := by rw [add_assoc, bool_add_self, add_zero]

/-! ### The shear -/

/-- The correction at `c ∈ d` that turns the equation of model one into that of model two. -/
noncomputable def gam (ν : V ⊕ V × V → Bool) (c : V) : Bool :=
  bnd G S.T (lat ν) c + bnd G S.d (lat ν) c + ∑ s ∈ S.fp c, (S.scm hG false).solve ν (.inl s)

/-- **The correction sums to zero over `d`.** -/
theorem sum_gam (ν : V ⊕ V × V → Bool) : ∑ c ∈ S.d, S.gam hG ν c = 0 := by
  unfold gam
  rw [sum_add_distrib, sum_add_distrib, sum_bnd_self]
  have ht := S.sum_d_fp (t := (S.scm hG false).solve ν) fun s hs => by
    rw [S.lat_solve]
    exact S.solve_R hG false ν hs
  rw [ht, S.lat_solve, S.sum_R_bnd, add_zero, bool_add_self]

/-- A latent vector inside `d` whose boundary relative to `d` is a given vector of sum zero. -/
noncomputable def psi (g : V → Bool) : V × V → Bool :=
  if h : ∑ c ∈ S.d, g c = 0 then Classical.choose (exists_bnd_eq S.conn g h) else 0

theorem bnd_psi {g : V → Bool} (h : ∑ c ∈ S.d, g c = 0) :
    ∀ c ∈ S.d, bnd G S.d (S.psi g) c = g c := by
  unfold psi
  rw [dite_eq_left h]
  exact Classical.choose_spec (exists_bnd_eq S.conn g h)

/-- A latent vector restricted to the pairs inside `d`, as a noise vector. -/
def lift (m : V × V → Bool) : V ⊕ V × V → Bool :=
  Sum.elim 0 fun p => if p ∈ bedges G S.d then m p else 0

/-- The shear of the noise. -/
noncomputable def shear (ν : V ⊕ V × V → Bool) : V ⊕ V × V → Bool :=
  ν + S.lift (S.psi (S.gam hG ν))

theorem lat_add_lift (σ : V ⊕ V × V → Bool) (m : V × V → Bool) :
    lat (σ + S.lift m) = lat σ + fun p => if p ∈ bedges G S.d then m p else 0 := rfl

/-- Adding a lifted vector changes the boundary relative to `T` at `v` by the boundary relative
to `d`. -/
theorem bnd_T_add_lift (σ : V ⊕ V × V → Bool) (m : V × V → Bool) (v : V) :
    bnd G S.T (lat (σ + S.lift m)) v = bnd G S.T (lat σ) v + bnd G S.d m v := by
  rw [lat_add_lift, bnd_add, bnd_mask S.fail.ssubset.subset]

theorem bnd_d_add_lift (σ : V ⊕ V × V → Bool) (m : V × V → Bool) (v : V) :
    bnd G S.d (lat (σ + S.lift m)) v = bnd G S.d (lat σ) v + bnd G S.d m v := by
  rw [lat_add_lift, bnd_add, bnd_mask subset_rfl]

/-- A lifted vector vanishes on the observed vertices. -/
@[simp] theorem lift_inl (m : V × V → Bool) (v : V) : S.lift m (.inl v) = 0 := rfl

/-- Adding a lifted vector to the noise does not change the vertices of `T \ d` in model
`i`. -/
theorem solve_add_lift_R (i : Bool) (ν : V ⊕ V × V → Bool) (m : V × V → Bool) {s : V}
    (hs : s ∈ S.T \ S.d) :
    (S.scm hG i).solve (ν + S.lift m) (.inl s) = (S.scm hG i).solve ν (.inl s) := by
  let A : Set (V ⊕ V × V) := {j | (∃ s ∈ S.T \ S.d, j = .inl s) ∨ ∃ p ∉ bedges G S.d, j = .inr p}
  refine solve_boolSCM_eq_on (S.readsParents i) A ?_ ?_ _ (.inl ⟨s, hs, rfl⟩)
  · rintro j (⟨s, hs, rfl⟩ | ⟨p, -, rfl⟩) σ σ' e h
    · have hb : S.base i s σ = S.base i s σ' := by
        simp only [base, hs, ite_true]
        congr 1
        · refine bnd_congr_at fun p hp hps => h _ (.inr ⟨p, fun hpd => ?_, rfl⟩)
            (ADMG.canonicalDAG_adj_inr_inl.2 ⟨(mem_bedges.1 hp).1, hps.imp Eq.symm Eq.symm⟩)
          obtain ⟨-, h1, h2⟩ := mem_bedges.1 hpd
          rcases hps with rfl | rfl
          · exact (mem_sdiff.1 hs).2 h1
          · exact (mem_sdiff.1 hs).2 h2
        · exact sum_congr rfl fun s' hs' => h _ (.inl ⟨s', S.fp_subset s hs', rfl⟩)
            (ADMG.canonicalDAG_adj_inl_inl.2 (S.fp_adj s' hs'))
      simp only [mech, hs, ite_true, hb]
    · rfl
  · rintro j (⟨s, -, rfl⟩ | ⟨p, hp, rfl⟩)
    · simp
    · simp [lift, hp]

/-- The correction is invariant under the shear. -/
theorem gam_shear (ν : V ⊕ V × V → Bool) : S.gam hG (S.shear hG ν) = S.gam hG ν := by
  funext c
  unfold gam shear
  rw [S.bnd_T_add_lift, S.bnd_d_add_lift]
  have : ∑ s ∈ S.fp c, (S.scm hG false).solve (ν + S.lift (S.psi (S.gam hG ν))) (.inl s) =
      ∑ s ∈ S.fp c, (S.scm hG false).solve ν (.inl s) :=
    sum_congr rfl fun s hs => S.solve_add_lift_R hG false ν _ (S.fp_subset c hs)
  rw [this]
  calc _ = bnd G S.T (lat ν) c + bnd G S.d (lat ν) c +
        (bnd G S.d (S.psi (S.gam hG ν)) c + bnd G S.d (S.psi (S.gam hG ν)) c) +
        ∑ s ∈ S.fp c, (S.scm hG false).solve ν (.inl s) := by ring
    _ = _ := by rw [bool_add_self, add_zero]

/-- **The shear is an involution.** -/
theorem shear_shear (ν : V ⊕ V × V → Bool) : S.shear hG (S.shear hG ν) = ν := by
  rw [shear, S.gam_shear, shear, add_assoc]
  funext j
  simp only [Pi.add_apply, bool_add_self, add_zero]

/-- **The shear preserves the noise law**: it changes only fair latent bits. -/
theorem pi_shear (ν : V ⊕ V × V → Bool) :
    FiniteDist.pi S.noise (S.shear hG ν) = FiniteDist.pi S.noise ν := by
  refine FiniteDist.pi_add_eq _ _ _ fun j hj => ?_
  rcases j with v | p
  · exact absurd hj (by simp)
  · rfl

/-- **The shear carries model one to model two**: the solution of model two at the sheared
noise is the solution of model one with the latent bits inside `d` sheared. -/
theorem solve_shear (ν : V ⊕ V × V → Bool) :
    (S.scm hG true).solve (S.shear hG ν) =
      (S.scm hG false).solve ν + S.lift (S.psi (S.gam hG ν)) := by
  set t := (S.scm hG false).solve ν
  set m := S.psi (S.gam hG ν)
  have ht : ∀ j, t j = S.mech false j t (ν j) := S.solve_apply hG false ν
  refine (solve_boolSCM_iff (S.readsParents true)).2 fun j => ?_
  rcases j with v | p
  · have htv := ht (.inl v)
    simp only [Pi.add_apply, lift_inl, add_zero, shear]
    by_cases hR : v ∈ S.T \ S.d
    · rw [S.mech_R true hR, S.bnd_T_add_lift, bnd_eq_zero_of_notMem (mem_sdiff.1 hR).2, add_zero,
        S.mech_R false hR] at *
      simpa using htv
    by_cases hd : v ∈ S.d
    · rw [S.mech_d_true hd, S.bnd_d_add_lift, S.bnd_psi (S.sum_gam hG ν) v hd]
      rw [S.mech_d_false hd] at htv
      simp only [Pi.add_apply, lift_inl, add_zero]
      rw [htv]
      unfold gam
      rw [S.lat_solve]
      calc _ = bnd G S.T (lat ν) v + ∑ w ∈ S.rt v, t (.inl w) + ν (.inl v) +
            ((∑ s ∈ S.fp v, t (.inl s) + ∑ s ∈ S.fp v, t (.inl s)) +
            (bnd G S.d (lat ν) v + bnd G S.d (lat ν) v)) := by
            rw [bool_add_self, bool_add_self, add_zero, add_zero]
        _ = _ := by ring
    · have hT : v ∉ S.T := fun h => hR (mem_sdiff.2 ⟨h, hd⟩)
      rw [S.mech_out true hT]
      rw [S.mech_out false hT] at htv
      simpa using htv
  · simp only [Pi.add_apply, shear, mech]
    exact congrArg (· + S.lift m (.inr p)) (ht (.inr p))

/-- The shear is a bijection of the noise values. -/
theorem shear_bijective : Function.Bijective (S.shear hG) :=
  Function.Involutive.bijective (S.shear_shear hG)

/-- **Equal observed laws.** Models one and two have the same law of the observed
vertices. -/
theorem marginal_eq : (S.scm hG false).dist.marginal ADMG.canonicalObs =
    (S.scm hG true).dist.marginal ADMG.canonicalObs := by
  unfold FiniteDist.marginal SCM.dist
  rw [FiniteDist.map_map, FiniteDist.map_map, S.noiseDist_scm, S.noiseDist_scm]
  conv_rhs => rw [← FiniteDist.map_comp_eq_of_bijective _ (S.shear_bijective hG) (S.pi_shear hG)]
  congr 1
  funext ν
  simp only [Function.comp, S.solve_shear]
  funext ⟨j, hj⟩
  obtain ⟨v, -, rfl⟩ := mem_map.1 hj
  simp [Finset.restrict]

/-! ### Positivity -/

omit [DecidableRel G.bidirected.Adj] in
/-- The inner set of a failure witness is nonempty. -/
theorem d_nonempty : S.d.Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro h
  obtain ⟨t, ht, -⟩ := exists_of_ssubset S.fail.ssubset
  rw [← S.fail.ancestral] at ht
  obtain ⟨c, hc, -⟩ := ADMG.mem_ancestorsOfFinset.1 (mem_inter.1 ht).1
  rw [h] at hc
  exact notMem_empty c hc

/-- **Positivity.** The observed law of model one is strictly positive. -/
theorem margAt_pos_false (w : V ⊕ V × V → Bool) :
    0 < (S.scm hG false).dist.margAt ADMG.canonicalObs w := by
  classical
  obtain ⟨c₀, hc₀⟩ := S.d_nonempty
  let r : V → Bool := fun s => w (.inl s) + ∑ s' ∈ S.fp s, w (.inl s')
  let b : V → Bool := fun v =>
    if v ∈ S.T \ S.d then r v else if v = c₀ then ∑ s ∈ S.T \ S.d, r s else 0
  have hb : ∑ v ∈ S.T, b v = 0 := by
    have h1 : ∑ v ∈ S.T \ S.d, b v = ∑ s ∈ S.T \ S.d, r s :=
      sum_congr rfl fun v hv => by simp only [b, hv, ↓reduceIte]
    have h2 : ∑ v ∈ S.d, b v = ∑ s ∈ S.T \ S.d, r s := by
      rw [sum_eq_single c₀]
      · have : c₀ ∉ S.T \ S.d := fun h => (mem_sdiff.1 h).2 hc₀
        simp only [b, this, ↓reduceIte]
      · intro v hv hne
        have : v ∉ S.T \ S.d := fun h => (mem_sdiff.1 h).2 hv
        simp only [b, this, hne, ↓reduceIte]
      · exact fun h => absurd hc₀ h
    rw [← sum_sdiff S.fail.ssubset.subset, h1, h2, bool_add_self]
  obtain ⟨u, hu⟩ := exists_bnd_eq S.fail.connected b hb
  let σ : V ⊕ V × V → Bool := Sum.elim (fun v => w (.inl v)) u
  let ν : V ⊕ V × V → Bool := Sum.elim
    (fun v => if v ∈ S.T \ S.d then false else σ (.inl v) + S.base false v σ) u
  have hsol : (S.scm hG false).solve ν = σ := by
    refine (solve_boolSCM_iff (S.readsParents false)).2 fun j => ?_
    rcases j with v | p
    · by_cases hR : v ∈ S.T \ S.d
      · simp only [mech, hR, ite_true, base]
        change w (.inl v) = bnd G S.T u v + ∑ s ∈ S.fp v, w (.inl s)
        rw [hu v (mem_sdiff.1 hR).1]
        simp only [b, hR, ite_true, r]
        rw [add_assoc, bool_add_self, add_zero]
      · simp only [mech, hR, ite_false, ν, Sum.elim_inl]
        rw [add_comm (σ (.inl v)), ← add_assoc, bool_add_self, zero_add]
    · rfl
  have hpos : 0 < FiniteDist.pi S.noise ν :=
    prod_pos fun j _ => S.noise_pos j (ν j)
  rw [SCM.margAt_dist, S.noiseDist_scm]
  refine hpos.trans_le (FiniteDist.le_probOf _ ν ?_)
  intro j hj
  obtain ⟨v, -, rfl⟩ := mem_map.1 hj
  rw [hsol]
  rfl

/-- **Positivity of both models.** -/
theorem margAt_pos (i : Bool) (w : V ⊕ V × V → Bool) :
    0 < (S.scm hG i).dist.margAt ADMG.canonicalObs w := by
  cases i
  · exact S.margAt_pos_false hG w
  · rw [← FiniteDist.marginal_restrict, ← S.marginal_eq hG, FiniteDist.marginal_restrict]
    exact S.margAt_pos_false hG w

end Setup

end IDCompleteness

end CausalInference
