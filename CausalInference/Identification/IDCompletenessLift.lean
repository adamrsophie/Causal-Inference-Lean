/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessCFactor

/-!
# Non-identifiability of an effect from a routed hedge

Let `G` be an acyclic directed mixed graph on `V`, `X` and `Y` disjoint sets of vertices, and
`D` the ancestors of `Y` inside `V \ X`. A **routed pair** (`IDCompleteness.RoutedPair G X Y`)
is a bidirected connected set `C ⊆ D` with a failure witness `T` (`IsIdFailure G C T`) that
meets `X`, such that every vertex of `C` reaches `Y \ R` by a directed path inside `D \ R`,
where `R = T \ C`. This is a hedge of Shpitser and Pearl (2006) for the effect of `X` on `Y`,
together with directed paths from its inner set to `Y` that avoid the rest of the hedge.

For a routed pair, the effect `P(Y = y | do(X := x))` on the canonical DAG of `G`, with every
vertex of `G` observed, is not identifiable from the observed law within the class of Boolean
models whose observed law is strictly positive (`IDCompleteness.not_identifiableFrom_effect`).
The two models are those of `IDCompleteness.Setup.model`, with the routing that sends each
vertex of `Q` (the vertices of `D \ R` that reach `Y \ R` inside `D \ R`) and each vertex
`s ∈ T \ C` outside `X` with forest child in `C` one step toward `Y`. Under `do(X := x)`, the
parity of the values of a set `Yo ⊆ Y` telescopes along the routing: it is a fair bit in model
one (a latent bit of a bidirected edge leaving `C ∪ S1`, a set of vertices of `T` outside `X`,
flips it) and a biased bit in model two.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

variable {V : Type} [Fintype V] [DecidableEq V] {G : ADMG V} [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj]

open Classical in
/-- The vertices of `D \ R` from which a directed path inside `D \ R` reaches `Y \ R`. -/
noncomputable def routeSet (G : ADMG V) [DecidableRel G.directed.Adj] (D R Y : Finset V) :
    Finset V :=
  (D \ R).filter fun v => ∃ y ∈ Y \ R, Relation.ReflTransGen (G.restrict ↑(D \ R)).directed.Adj v y

omit [DecidableRel G.bidirected.Adj] in
theorem mem_routeSet {D R Y : Finset V} {v : V} :
    v ∈ routeSet G D R Y ↔ v ∈ D \ R ∧
      ∃ y ∈ Y \ R, Relation.ReflTransGen (G.restrict ↑(D \ R)).directed.Adj v y := by
  unfold routeSet
  rw [mem_filter]

/-- A **routed pair** for the effect of `X` on `Y`: a bidirected connected set `C` of ancestors
of `Y` outside `X`, a failure witness `T` of `C` meeting `X`, and directed paths from every
vertex of `C` to `Y \ (T \ C)` inside `D \ (T \ C)`, where `D` is the set of ancestors of `Y`
inside `V \ X`. -/
structure RoutedPair (G : ADMG V) [DecidableRel G.directed.Adj] (X Y : Finset V) where
  /-- The inner set. -/
  C : Finset V
  /-- The failure witness. -/
  T : Finset V
  /-- The inner set consists of ancestors of `Y` outside `X`. -/
  sub : C ⊆ ancIn G (univ \ X) Y
  /-- The inner set is bidirected connected. -/
  conn : BiConnected G C
  /-- `T` is a failure witness of `C`. -/
  fail : IsIdFailure G C T
  /-- `T` meets `X`. -/
  meets : (T ∩ X).Nonempty
  /-- The routing property. -/
  route : ∀ c ∈ C, c ∈ routeSet G (ancIn G (univ \ X) Y) (T \ C) Y

namespace RoutedPair

variable {X Y : Finset V} (P : RoutedPair G X Y)

/-- The forest child. -/
noncomputable def ch : V → V := Classical.choose (exists_forestChild P.fail.ancestral)

omit [DecidableRel G.bidirected.Adj] in
theorem ch_spec : ∀ s ∈ P.T \ P.C, P.ch s ∈ P.T ∧ G.directed.Adj s (P.ch s) :=
  Classical.choose_spec (exists_forestChild P.fail.ancestral)

/-- The routed vertices of `D \ R`. -/
noncomputable def Q : Finset V := routeSet G (ancIn G (univ \ X) Y) (P.T \ P.C) Y

open Classical in
/-- The vertices of `T \ C` outside `X` whose forest child lies in `C`. -/
noncomputable def R1 : Finset V := (P.T \ P.C).filter fun s => s ∉ X ∧ P.ch s ∈ P.C

/-- The routed set. -/
noncomputable def Z : Finset V := P.Q ∪ P.R1

/-- The target of the parity, a subset of `Y`. -/
noncomputable def Yo : Finset V := (Y \ (P.T \ P.C)) ∪ (Y ∩ P.R1)

omit [DecidableRel G.bidirected.Adj] in
theorem Q_sub {v : V} (hv : v ∈ P.Q) : v ∈ ancIn G (univ \ X) Y \ (P.T \ P.C) :=
  (mem_routeSet.1 hv).1

omit [DecidableRel G.bidirected.Adj] in
theorem notMem_X_of_mem_D {v : V} (hv : v ∈ ancIn G (univ \ X) Y) : v ∉ X :=
  (mem_sdiff.1 (ancIn_subset _ _ hv)).2

omit [DecidableRel G.bidirected.Adj] in
theorem mem_R1 {s : V} : s ∈ P.R1 ↔ s ∈ P.T \ P.C ∧ s ∉ X ∧ P.ch s ∈ P.C := by
  unfold R1
  rw [mem_filter]

omit [DecidableRel G.bidirected.Adj] in
theorem C_sub_Q : P.C ⊆ P.Q := fun c hc => P.route c hc

omit [DecidableRel G.bidirected.Adj] in
/-- Every vertex of the routed set outside the target has a successor in `Q`. -/
theorem exists_next : ∀ w ∈ P.Z \ P.Yo, ∃ v ∈ P.Q, G.directed.Adj w v := by
  intro w hw
  obtain ⟨hwZ, hwY⟩ := mem_sdiff.1 hw
  rcases mem_union.1 hwZ with hQ | hR
  · obtain ⟨hwD, y, hy, hp⟩ := mem_routeSet.1 hQ
    rcases hp.cases_head with rfl | ⟨v, hwv, hvy⟩
    · exact absurd (mem_union_left _ hy) hwY
    · exact ⟨v, mem_routeSet.2 ⟨mem_coe.1 hwv.2.2, y, hy, hvy⟩, hwv.1⟩
  · obtain ⟨hs, -, hc⟩ := P.mem_R1.1 hR
    exact ⟨P.ch w, P.C_sub_Q hc, (P.ch_spec w hs).2⟩

/-- The routing successor. -/
noncomputable def f (w : V) : V :=
  if h : w ∈ P.Z \ P.Yo then Classical.choose (P.exists_next w h) else w

omit [DecidableRel G.bidirected.Adj] in
theorem f_spec {w : V} (hw : w ∈ P.Z \ P.Yo) : P.f w ∈ P.Q ∧ G.directed.Adj w (P.f w) := by
  unfold f
  rw [dite_eq_left hw]
  exact Classical.choose_spec (P.exists_next w hw)

open Classical in
/-- The routed inputs of `v`. -/
noncomputable def rt (v : V) : Finset V := (P.Z \ P.Yo).filter fun w => P.f w = v

omit [DecidableRel G.bidirected.Adj] in
theorem mem_rt {v w : V} : w ∈ P.rt v ↔ w ∈ P.Z \ P.Yo ∧ P.f w = v := by
  unfold rt
  rw [mem_filter]

/-- The construction of `IDCompleteness.Setup` for the routed pair. -/
noncomputable def setup : Setup G where
  d := P.C
  T := P.T
  fail := P.fail
  conn := P.conn
  ch := P.ch
  ch_mem s hs := (P.ch_spec s hs).1
  ch_adj s hs := (P.ch_spec s hs).2
  rt := P.rt
  rt_adj v w hw := by
    obtain ⟨hw', hv⟩ := P.mem_rt.1 hw
    rw [← hv]
    exact (P.f_spec hw').2
  rt_R v hv := by
    refine eq_empty_of_forall_notMem fun w hw => ?_
    obtain ⟨hw', hv'⟩ := P.mem_rt.1 hw
    exact (mem_sdiff.1 (P.Q_sub (P.f_spec hw').1)).2 (hv' ▸ hv)

/-! ### Telescoping along the routing -/

omit [DecidableRel G.bidirected.Adj] in
/-- The target lies in the routed set when `X` and `Y` are disjoint. -/
theorem Yo_sub_Z (hXY : Disjoint X Y) : P.Yo ⊆ P.Z := by
  intro y hy
  rcases mem_union.1 hy with h | h
  · obtain ⟨hyY, hyR⟩ := mem_sdiff.1 h
    have hyD : y ∈ ancIn G (univ \ X) Y :=
      subset_ancIn (fun v hv => mem_sdiff.2 ⟨mem_univ v, disjoint_right.1 hXY hv⟩) hyY
    exact mem_union_left _ (mem_routeSet.2 ⟨mem_sdiff.2 ⟨hyD, hyR⟩, y, h, .refl⟩)
  · exact mem_union_right _ (mem_inter.1 h).2

omit [DecidableRel G.bidirected.Adj] in
/-- **Telescoping.** For any configuration, the values of the target sum to the sum over the
routed set of each value plus its routed inputs. -/
theorem sum_Yo (hXY : Disjoint X Y) (τ : V ⊕ V × V → Bool) :
    ∑ y ∈ P.Yo, τ (.inl y) = ∑ v ∈ P.Z, (τ (.inl v) + ∑ w ∈ P.rt v, τ (.inl w)) := by
  classical
  have h1 : ∑ v ∈ P.Z, ∑ w ∈ P.rt v, τ (.inl w) = ∑ w ∈ P.Z \ P.Yo, τ (.inl w) := by
    have := sum_fiberwise_of_maps_to (s := P.Z \ P.Yo) (t := P.Z) (g := P.f)
      (fun w hw => mem_union_left _ (P.f_spec hw).1) (fun w => τ (.inl w))
    rw [← this]
    refine sum_congr rfl fun v _ => sum_congr ?_ fun _ _ => rfl
    ext w
    rw [P.mem_rt, mem_filter]
  rw [sum_add_distrib, h1, ← sum_sdiff (P.Yo_sub_Z hXY), add_comm (∑ w ∈ P.Z \ P.Yo, _),
    add_assoc, bool_add_self, add_zero]

/-! ### The forest parents of a set -/

omit [DecidableRel G.bidirected.Adj] in
/-- Summing over the forest parents of the vertices of `B` is summing over the vertices of
`T \ C` whose forest child lies in `B`. -/
theorem sum_fp_eq (B : Finset V) (g : V → Bool) :
    ∑ v ∈ B, ∑ s ∈ P.setup.fp v, g s = ∑ s ∈ (P.T \ P.C).filter (fun s => P.ch s ∈ B), g s := by
  change ∑ v ∈ B, ∑ s ∈ (P.T \ P.C).filter (fun s => P.ch s = v), g s = _
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_ite_eq]

open Classical in
/-- The vertices of `T \ C` outside `X` whose forest path reaches `C` without meeting `X`. -/
noncomputable def S1 : Finset V :=
  (P.T \ P.C).filter fun s => ∃ k, P.ch^[k + 1] s ∈ P.C ∧
    ∀ j ≤ k, P.ch^[j] s ∈ P.T \ P.C ∧ P.ch^[j] s ∉ X

omit [DecidableRel G.bidirected.Adj] in
open Classical in
theorem mem_S1 {s : V} : s ∈ P.S1 ↔ s ∈ P.T \ P.C ∧ ∃ k, P.ch^[k + 1] s ∈ P.C ∧
    ∀ j ≤ k, P.ch^[j] s ∈ P.T \ P.C ∧ P.ch^[j] s ∉ X := by
  unfold S1
  rw [mem_filter]

omit [DecidableRel G.bidirected.Adj] in
theorem S1_sub {s : V} (hs : s ∈ P.S1) : s ∈ P.T \ P.C ∧ s ∉ X := by
  obtain ⟨-, k, -, hk⟩ := P.mem_S1.1 hs
  exact hk 0 (Nat.zero_le k)

omit [DecidableRel G.bidirected.Adj] in
theorem S1_ch {s : V} (hs : s ∈ P.S1) : P.ch s ∈ P.S1 ∨ P.ch s ∈ P.C := by
  obtain ⟨-, k, hk1, hk⟩ := P.mem_S1.1 hs
  rcases k with _ | k
  · exact .inr hk1
  · refine .inl (P.mem_S1.2 ⟨(hk 1 (by omega)).1, k, ?_, fun j hj => ?_⟩)
    · rwa [← Function.iterate_succ_apply]
    · rw [← Function.iterate_succ_apply]
      exact hk (j + 1) (by omega)

omit [DecidableRel G.bidirected.Adj] in
theorem mem_S1_of {s : V} (hs : s ∈ P.T \ P.C) (hsX : s ∉ X)
    (hc : P.ch s ∈ P.S1 ∨ P.ch s ∈ P.C) : s ∈ P.S1 := by
  rcases hc with hc | hc
  · obtain ⟨-, k, hk1, hk⟩ := P.mem_S1.1 hc
    refine P.mem_S1.2 ⟨hs, k + 1, ?_, fun j hj => ?_⟩
    · rwa [Function.iterate_succ_apply]
    · rcases j with _ | j
      · exact ⟨hs, hsX⟩
      · rw [Function.iterate_succ_apply]
        exact hk j (by omega)
  · refine P.mem_S1.2 ⟨hs, 0, hc, fun j hj => ?_⟩
    rw [Nat.le_zero.1 hj]
    exact ⟨hs, hsX⟩

omit [DecidableRel G.bidirected.Adj] in
theorem R1_sub_S1 : P.R1 ⊆ P.S1 := fun s hs => by
  obtain ⟨h1, h2, h3⟩ := P.mem_R1.1 hs
  exact P.mem_S1_of h1 h2 (.inr h3)

/-! ### The intervened models -/

variable (hG : G.IsAcyclic)

/-- Under `do(X := x)`, a vertex that is not intervened follows its mechanism. -/
theorem solve_X (i : Bool) (x ν : V ⊕ V × V → Bool) {j : V ⊕ V × V}
    (hj : j ∉ X.map .inl) :
    ((P.setup.scm hG i).intervene (X.map .inl) x).solve ν j =
      P.setup.mech i j (((P.setup.scm hG i).intervene (X.map .inl) x).solve ν) (ν j) :=
  ((solve_intervene_boolSCM_iff (P.setup.readsParents i) _ x).1 rfl).2 j hj

omit [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj] in
theorem inl_notMem {v : V} (hv : v ∉ X) : (.inl v : V ⊕ V × V) ∉ X.map .inl := by
  simp [hv]

theorem lat_solve_X (i : Bool) (x ν : V ⊕ V × V → Bool) :
    Setup.lat (((P.setup.scm hG i).intervene (X.map .inl) x).solve ν) = Setup.lat ν := by
  funext p
  exact P.solve_X hG i x ν (by simp)

/-- The values of the vertices of `S1` under `do(X := x)` follow the equations of `T \ C`, and
the vertices of `R1` sum to the boundary over `S1` plus intervened values. -/
theorem sum_R1 (i : Bool) (x ν : V ⊕ V × V → Bool) :
    ∑ s ∈ P.R1, ((P.setup.scm hG i).intervene (X.map .inl) x).solve ν (.inl s) =
      ∑ s ∈ P.S1, bnd G P.T (Setup.lat ν) s +
        ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.S1), x (.inl s) := by
  classical
  set τ := ((P.setup.scm hG i).intervene (X.map .inl) x).solve ν
  have heq : ∀ s ∈ P.S1, τ (.inl s) = bnd G P.T (Setup.lat ν) s +
      ∑ s' ∈ P.setup.fp s, τ (.inl s') := by
    intro s hs
    obtain ⟨hR, hX⟩ := P.S1_sub hs
    have h := P.solve_X hG i x ν (inl_notMem hX)
    rw [P.setup.mech_R i hR, P.lat_solve_X] at h
    exact h
  have hA : ∑ s ∈ P.S1, τ (.inl s) = ∑ s ∈ P.S1, bnd G P.T (Setup.lat ν) s +
      ∑ s ∈ (P.T \ P.C).filter (fun s => P.ch s ∈ P.S1), τ (.inl s) := by
    rw [← P.sum_fp_eq, ← sum_add_distrib]
    exact sum_congr rfl heq
  have hB : ∑ s ∈ (P.T \ P.C).filter (fun s => P.ch s ∈ P.S1), τ (.inl s) =
      ∑ s ∈ P.S1.filter (fun s => P.ch s ∈ P.S1), τ (.inl s) +
        ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.S1), x (.inl s) := by
    rw [← sum_filter_add_sum_filter_not _ (fun s => s ∈ X)]
    rw [add_comm]
    congr 1
    · refine sum_congr ?_ fun _ _ => rfl
      ext s
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hs, hc⟩, hX⟩
        exact ⟨P.mem_S1_of hs hX (.inl hc), hc⟩
      · rintro ⟨hs, hc⟩
        exact ⟨⟨(P.S1_sub hs).1, hc⟩, (P.S1_sub hs).2⟩
    · rw [filter_filter]
      refine sum_congr (by ext s; simp only [mem_filter]; tauto) fun s hs => ?_
      exact SCM.solve_intervene_of_mem _ ν (mem_map_of_mem _ (mem_filter.1 hs).2.1)
  have hC : ∑ s ∈ P.S1, τ (.inl s) = ∑ s ∈ P.S1.filter (fun s => P.ch s ∈ P.S1), τ (.inl s) +
      ∑ s ∈ P.R1, τ (.inl s) := by
    rw [← sum_filter_add_sum_filter_not P.S1 (fun s => P.ch s ∈ P.S1)]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext s
    rw [mem_filter]
    constructor
    · rintro ⟨hs, hc⟩
      have := (P.S1_sub hs)
      exact P.mem_R1.2 ⟨this.1, this.2, (P.S1_ch hs).resolve_left hc⟩
    · intro hs
      obtain ⟨h1, -, h3⟩ := P.mem_R1.1 hs
      exact ⟨P.R1_sub_S1 hs, fun h => (mem_sdiff.1 (P.S1_sub h).1).2 h3⟩
  set a := ∑ s ∈ P.S1.filter (fun s => P.ch s ∈ P.S1), τ (.inl s)
  set b := ∑ s ∈ P.R1, τ (.inl s)
  set c := ∑ s ∈ P.S1, bnd G P.T (Setup.lat ν) s
  set e := ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.S1), x (.inl s)
  have h : a + b = c + (a + e) := by rw [← hC, hA, hB]
  calc b = (a + b) + a := by rw [add_comm a b, add_assoc, bool_add_self, add_zero]
    _ = c + e + (a + a) := by rw [h]; ring
    _ = c + e := by rw [bool_add_self, add_zero]

omit [DecidableRel G.bidirected.Adj] in
theorem Q_notMem_X {v : V} (hv : v ∈ P.Q) : v ∉ X :=
  notMem_X_of_mem_D (mem_sdiff.1 (P.Q_sub hv)).1

omit [DecidableRel G.bidirected.Adj] in
theorem disjoint_Q_R1 : Disjoint P.Q P.R1 :=
  disjoint_left.2 fun _ hQ hR => (mem_sdiff.1 (P.Q_sub hQ)).2 (P.mem_R1.1 hR).1

/-- A vertex of `Q` outside `C`, plus its routed inputs, is its noise bit. -/
theorem own_out (i : Bool) (x ν : V ⊕ V × V → Bool) {v : V} (hQ : v ∈ P.Q) (hC : v ∉ P.C) :
    ((P.setup.scm hG i).intervene (X.map .inl) x).solve ν (.inl v) +
      ∑ w ∈ P.rt v, ((P.setup.scm hG i).intervene (X.map .inl) x).solve ν (.inl w) =
        ν (.inl v) := by
  have hT : v ∉ P.T := fun h => (mem_sdiff.1 (P.Q_sub hQ)).2 (mem_sdiff.2 ⟨h, hC⟩)
  have h := P.solve_X hG i x ν (inl_notMem (P.Q_notMem_X hQ))
  rw [P.setup.mech_out i hT] at h
  rw [h]
  change ∑ w ∈ P.rt v, _ + ν (.inl v) + ∑ w ∈ P.rt v, _ = _
  rw [add_comm, ← add_assoc, bool_add_self, zero_add]

/-- A vertex of `C` in model one, plus its routed inputs. -/
theorem own_C_false (x ν : V ⊕ V × V → Bool) {c : V} (hc : c ∈ P.C) :
    ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν (.inl c) +
      ∑ w ∈ P.rt c, ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν (.inl w) =
        bnd G P.T (Setup.lat ν) c + ν (.inl c) := by
  have h := P.solve_X hG false x ν (inl_notMem (notMem_X_of_mem_D (P.sub hc)))
  rw [P.setup.mech_d_false hc, P.lat_solve_X] at h
  rw [h]
  change bnd G P.T (Setup.lat ν) c + ∑ w ∈ P.rt c, _ + ν (.inl c) + ∑ w ∈ P.rt c, _ = _
  calc _ = bnd G P.T (Setup.lat ν) c + ν (.inl c) +
        ((∑ w ∈ P.rt c, ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν (.inl w)) +
        ∑ w ∈ P.rt c, ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν (.inl w)) := by
        ring
    _ = _ := by rw [bool_add_self, add_zero]

/-- A vertex of `C` in model two, plus its routed inputs. -/
theorem own_C_true (x ν : V ⊕ V × V → Bool) {c : V} (hc : c ∈ P.C) :
    ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl c) +
      ∑ w ∈ P.rt c, ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl w) =
        ∑ s ∈ P.setup.fp c, ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl s) +
          bnd G P.C (Setup.lat ν) c + ν (.inl c) := by
  have h := P.solve_X hG true x ν (inl_notMem (notMem_X_of_mem_D (P.sub hc)))
  rw [P.setup.mech_d_true hc, P.lat_solve_X] at h
  rw [h]
  change _ + bnd G P.C (Setup.lat ν) c + ∑ w ∈ P.rt c, _ + ν (.inl c) + ∑ w ∈ P.rt c, _ = _
  set r := ∑ w ∈ P.rt c, ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl w)
  calc _ = ∑ s ∈ P.setup.fp c, ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl s) +
        bnd G P.C (Setup.lat ν) c + ν (.inl c) + (r + r) := by ring
    _ = _ := by rw [bool_add_self, add_zero]

omit [DecidableRel G.bidirected.Adj] in
/-- The vertices of `R1` receive no routed input. -/
theorem rt_R1 {s : V} (hs : s ∈ P.R1) : P.rt s = ∅ := P.setup.rt_R s (P.mem_R1.1 hs).1

omit [DecidableRel G.bidirected.Adj] in
/-- The telescoped parity, split into `Q \ C`, `C` and `R1`. -/
theorem sum_Yo_split (hXY : Disjoint X Y) (τ : V ⊕ V × V → Bool) :
    ∑ y ∈ P.Yo, τ (.inl y) = ∑ v ∈ P.Q \ P.C, (τ (.inl v) + ∑ w ∈ P.rt v, τ (.inl w)) +
      ∑ v ∈ P.C, (τ (.inl v) + ∑ w ∈ P.rt v, τ (.inl w)) + ∑ s ∈ P.R1, τ (.inl s) := by
  rw [P.sum_Yo hXY, Z, sum_union P.disjoint_Q_R1, sum_sdiff P.C_sub_Q]
  congr 1
  refine sum_congr rfl fun s hs => ?_
  rw [P.rt_R1 hs, sum_empty, add_zero]

/-- **The parity in model one** under `do(X := x)`. -/
theorem parity_false (hXY : Disjoint X Y) (x ν : V ⊕ V × V → Bool) :
    ∑ y ∈ P.Yo, ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν (.inl y) =
      ∑ v ∈ P.Q, ν (.inl v) + ∑ v ∈ P.C ∪ P.S1, bnd G P.T (Setup.lat ν) v +
        ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.S1), x (.inl s) := by
  have hdisj : Disjoint P.C P.S1 :=
    disjoint_left.2 fun v hC hS => (mem_sdiff.1 (P.S1_sub hS).1).2 hC
  rw [P.sum_Yo_split hXY, sum_congr rfl fun v hv => P.own_out hG false x ν
      (mem_sdiff.1 hv).1 (mem_sdiff.1 hv).2,
    sum_congr rfl fun c hc => P.own_C_false hG x ν hc, P.sum_R1 hG, sum_union hdisj,
    ← sum_sdiff P.C_sub_Q (f := fun v => ν (.inl v)), sum_add_distrib]
  ring

/-- **The parity in model two** under `do(X := x)`. -/
theorem parity_true (hXY : Disjoint X Y) (x ν : V ⊕ V × V → Bool) :
    ∑ y ∈ P.Yo, ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl y) =
      ∑ v ∈ P.Q, ν (.inl v) +
        ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.C), x (.inl s) := by
  classical
  set τ := ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν
  have hfp : ∑ c ∈ P.C, ∑ s ∈ P.setup.fp c, τ (.inl s) = ∑ s ∈ P.R1, τ (.inl s) +
      ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.C), x (.inl s) := by
    rw [P.sum_fp_eq, ← sum_filter_add_sum_filter_not _ (fun s => s ∈ X), add_comm]
    congr 1
    · refine sum_congr ?_ fun _ _ => rfl
      ext s
      rw [P.mem_R1]
      simp only [mem_filter]
      tauto
    · rw [filter_filter]
      refine sum_congr (by ext s; simp only [mem_filter]; tauto) fun s hs => ?_
      exact SCM.solve_intervene_of_mem _ ν (mem_map_of_mem _ (mem_filter.1 hs).2.1)
  rw [P.sum_Yo_split hXY, sum_congr rfl fun v hv => P.own_out hG true x ν
      (mem_sdiff.1 hv).1 (mem_sdiff.1 hv).2,
    sum_congr rfl fun c hc => P.own_C_true hG x ν hc, sum_add_distrib, sum_add_distrib, hfp,
    sum_bnd_self, add_zero, ← sum_sdiff P.C_sub_Q (f := fun v => ν (.inl v))]
  set a := ∑ s ∈ P.R1, τ (.inl s)
  calc _ = ∑ v ∈ P.Q \ P.C, ν (.inl v) + ∑ v ∈ P.C, ν (.inl v) +
        ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.C), x (.inl s) + (a + a) := by
        ring
    _ = _ := by rw [bool_add_self, add_zero]

/-- A bidirected edge leaving a set `A` with `C ⊆ A ⊆ T` that avoids a vertex of `T`. -/
theorem exists_leaving {A : Finset V} (hCA : P.C ⊆ A) {t : V} (ht : t ∈ P.T) (htA : t ∉ A) :
    ∃ q ∈ bedges G P.T, q.1 ∈ A ∧ q.2 ∉ A := by
  obtain ⟨c₀, hc₀⟩ := P.setup.d_nonempty
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1
    (P.fail.connected c₀ (P.fail.ssubset.subset hc₀) t ht)
  obtain ⟨a, b, hab, ha, hb⟩ := exists_step_of_reflTransGen (P := (· ∈ A)) hr (hCA hc₀) htA
  exact ⟨(a, b), mem_bedges.2 ⟨hab.1, mem_coe.1 hab.2.1, mem_coe.1 hab.2.2⟩, ha, hb⟩

/-- **Model one gives the target a fair parity** under `do(X := x)`. -/
theorem probOf_false (hXY : Disjoint X Y) (x : V ⊕ V × V → Bool) (b : Bool) :
    (FiniteDist.pi P.setup.noise).probOf (fun ν =>
      ∑ y ∈ P.Yo, ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν (.inl y) = b) =
        1 / 2 := by
  classical
  obtain ⟨t, ht⟩ := P.meets
  obtain ⟨htT, htX⟩ := mem_inter.1 ht
  have htA : t ∉ P.C ∪ P.S1 := by
    rintro h
    rcases mem_union.1 h with h | h
    · exact notMem_X_of_mem_D (P.sub h) htX
    · exact (P.S1_sub h).2 htX
  obtain ⟨q, hq, hq1, hq2⟩ := P.exists_leaving subset_union_left htT htA
  let e : V ⊕ V × V → Bool := Sum.elim 0 (single q)
  let φ : (V ⊕ V × V → Bool) → V ⊕ V × V → Bool := fun ν => ν + e
  have hφφ : ∀ ν, φ (φ ν) = ν := fun ν => by
    funext j
    simp only [φ, Pi.add_apply, add_assoc, bool_add_self, add_zero]
  have hcross : ∑ v ∈ P.C ∪ P.S1, bnd G P.T (single q) v = 1 := by
    simp only [bnd_single hq]
    rw [sum_add_distrib, sum_ite_eq, sum_ite_eq]
    simp only [hq1, hq2, ↓reduceIte, add_zero]
  have hpar : ∀ ν, ∑ y ∈ P.Yo, ((P.setup.scm hG false).intervene (X.map .inl) x).solve (φ ν)
      (.inl y) = ∑ y ∈ P.Yo, ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν
        (.inl y) + 1 := by
    intro ν
    rw [P.parity_false hG hXY, P.parity_false hG hXY]
    have hl : Setup.lat (φ ν) = Setup.lat ν + single q := rfl
    have hQ : ∑ v ∈ P.Q, (φ ν) (.inl v) = ∑ v ∈ P.Q, ν (.inl v) := by
      simp [φ, e]
    rw [hl, hQ, ← hcross]
    simp only [bnd_add, sum_add_distrib]
    ring
  unfold FiniteDist.probOf
  refine IDCompletenessBow.prob_eq_of_involution _ _ φ hφφ (fun ν => ?_) (q' := 1 / 2)
    (by norm_num) fun ν _ => ?_
  · simp only [mem_filter, mem_univ, true_and, hpar]
    cases ∑ y ∈ P.Yo, ((P.setup.scm hG false).intervene (X.map .inl) x).solve ν (.inl y) <;>
      cases b <;> decide
  · rw [FiniteDist.pi_add_eq _ _ _ fun j hj => ?_]
    rcases j with v | p
    · exact absurd hj (by simp [e])
    · rfl

/-- **Model two gives the target a biased parity** under `do(X := x)`. -/
theorem probOf_true_ne (hXY : Disjoint X Y) (x : V ⊕ V × V → Bool) (b : Bool) :
    (FiniteDist.pi P.setup.noise).probOf (fun ν =>
      ∑ y ∈ P.Yo, ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl y) = b) ≠
        1 / 2 := by
  set κ := ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.C), x (.inl s)
  have h : ∀ ν : V ⊕ V × V → Bool,
      (∑ y ∈ P.Yo, ((P.setup.scm hG true).intervene (X.map .inl) x).solve ν (.inl y) = b) ↔
        ∑ j ∈ P.Q.map .inl, ν j = b + κ := by
    intro ν
    have hs : ∑ j ∈ P.Q.map .inl, ν j = ∑ v ∈ P.Q, ν (.inl v) := sum_map _ _ _
    rw [P.parity_true hG hXY x ν, hs]
    constructor
    · rintro rfl
      rw [add_assoc, bool_add_self, add_zero]
    · intro h
      rw [h, add_assoc, bool_add_self, add_zero]
  rw [FiniteDist.probOf_congr _ h]
  refine probOf_parity_ne_half _ _ (fun j hj => ?_) _
  obtain ⟨v, hv, rfl⟩ := mem_map.1 hj
  have : v ∉ P.T \ P.C := (mem_sdiff.1 (P.Q_sub hv)).2
  change (if v ∈ P.T \ P.C then FiniteDist.uniform else quarterBit) = quarterBit
  simp [this]

end RoutedPair

/-- **Non-identifiability of the effect from a routed pair.** Let `G` be an acyclic directed
mixed graph, `X` and `Y` disjoint, and suppose a routed pair for the effect of `X` on `Y`
exists. On the canonical DAG of `G`, with every vertex of `G` observed, for every
configuration `x` there is a configuration `w` agreeing with `x` on the copy of `X` at which
the effect `P(Y = w_Y | do(X := w_X))` is not identifiable from the observed law within the
class of Boolean models whose observed law is strictly positive. -/
theorem not_identifiableFrom_effect (hG : G.IsAcyclic) {X Y : Finset V} (hXY : Disjoint X Y)
    (P : RoutedPair G X Y) (x : V ⊕ V × V → Bool) :
    ∃ w : V ⊕ V × V → Bool, (∀ j ∈ X.map .inl, w j = x j) ∧
      ¬ SCM.IdentifiableFrom
        {m : SCM.Model G.canonicalDAG (fun _ => Bool) |
          ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
        (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w) := by
  classical
  set S := P.setup
  by_contra hcon
  push Not at hcon
  have hXY' : ∀ j ∈ Y.map .inl, j ∉ (X.map .inl : Finset (V ⊕ V × V)) := by
    intro j hj hj'
    obtain ⟨v, hv, rfl⟩ := mem_map.1 hj
    obtain ⟨u, hu, he⟩ := mem_map.1 hj'
    rw [Function.Embedding.inl_apply, Function.Embedding.inl_apply] at he
    exact disjoint_left.1 hXY (Sum.inl_injective he ▸ hu) hv
  have hmarg : ∀ c : V ⊕ V × V → Bool,
      ((S.scm hG false).intervene (X.map .inl) x).dist.margAt (Y.map .inl) c =
        ((S.scm hG true).intervene (X.map .inl) x).dist.margAt (Y.map .inl) c := by
    intro c
    let wc : V ⊕ V × V → Bool := fun j => if j ∈ X.map .inl then x j else c j
    have hwc : ∀ j ∈ X.map .inl, wc j = x j := fun j hj => by simp only [wc, hj, ↓reduceIte]
    have hid := hcon wc hwc (S.model hG false) (S.margAt_pos hG false)
      (S.model hG true) (S.margAt_pos hG true) (S.marginal_eq hG)
    change ((S.scm hG false).intervene (X.map .inl) wc).dist.margAt (Y.map .inl) wc =
      ((S.scm hG true).intervene (X.map .inl) wc).dist.margAt (Y.map .inl) wc at hid
    have hX : ∀ i, ((S.scm hG i).intervene (X.map .inl) wc).dist =
        ((S.scm hG i).intervene (X.map .inl) x).dist := fun i =>
      (S.scm hG i).dist_intervene_congr hwc
    have hY : ∀ i, ((S.scm hG i).intervene (X.map .inl) x).dist.margAt (Y.map .inl) wc =
        ((S.scm hG i).intervene (X.map .inl) x).dist.margAt (Y.map .inl) c := fun i =>
      FiniteDist.margAt_congr _ _ fun j hj => by simp only [wc, hXY' j hj, ↓reduceIte]
    rw [hX, hX, hY, hY] at hid
    exact hid
  have hm := marginal_eq_of_margAt_eq hmarg
  have hYo : ∀ y ∈ P.Yo, y ∈ Y := fun y hy => by
    rcases mem_union.1 hy with h | h
    · exact (mem_sdiff.1 h).1
    · exact (mem_inter.1 h).1
  have hp := FiniteDist.probOf_eq_of_marginal_eq hm
    (fun τ => ∑ y ∈ P.Yo, τ (.inl y) = true) fun τ τ' h => by
      rw [sum_congr rfl fun y hy => h (.inl y) (mem_map_of_mem _ (hYo y hy))]
  rw [SCM.probOf_dist, SCM.probOf_dist, SCM.noiseDist_intervene, SCM.noiseDist_intervene,
    S.noiseDist_scm, S.noiseDist_scm] at hp
  exact P.probOf_true_ne hG hXY x true (hp ▸ P.probOf_false hG hXY x true)

end IDCompleteness

end CausalInference
