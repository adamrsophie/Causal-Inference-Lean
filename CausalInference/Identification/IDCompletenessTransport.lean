/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessRouting

/-!
# Two bit countermodels with a transport channel

Let `G` be an acyclic directed mixed graph on `V`, `X` and `Y` disjoint, and `D` the ancestors
of `Y` inside `V \ X`. The Boolean countermodels of `IDCompleteness.not_identifiableFrom_effect`
need a routed pair: directed paths from the inner set to `Y` that avoid the rest of the hedge.
This file removes that requirement by giving every vertex of the canonical DAG the value type
`Bool × Bool`.

The first bit is the hedge layer: the Boolean models of `IDCompleteness.Setup.model` for a
routed pair `P : RoutedPair G X Z` whose target `Z` lies in `D` (for a general pair `(C, T)`,
take `Z = C`, where routing is trivial). The second bit is a transport channel along a fixed
successor `IDCompleteness.Transport.next` that sends each vertex of `D \ Y` to a child in `D`.
The transport bit of `w` is the sum, over the vertices `p` of `D \ Y` with `next p = w`, of the
payload of `p`, plus a noise bit that is true with probability `1/4`; the payload of `p` is its
transport bit plus, when `p` lies in the target `P.Yo` of the hedge parity, its hedge bit. The
sum over `Y` of the payloads telescopes to the hedge parity plus transport noise
(`IDCompleteness.Transport.sum_pay_Y`), wherever the successor runs.

## Main results

* `IDCompleteness.Transport.marginal_eq`: the two models have the same law of the observed
  vertices (the shear of the hedge layer, the transport layer being the same function of the
  observed hedge bits in both models).
* `IDCompleteness.Transport.margAt_pos`: the observed law of each model is strictly positive.
* `IDCompleteness.Transport.probOf_false` and `IDCompleteness.Transport.probOf_true_ne`:
  under `do(X := x)` the transported parity over `Y` is a fair bit in model one and a biased bit
  in model two.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

/-! ### Models given by mechanisms that read the parents, with any value type -/

section MechSCM

variable {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
  {β η : Type} [Inhabited β] [Fintype η]

/-- The parent values of `v`, extended by the default value off the parents. -/
def extendParD (v : W) (z : D.parentsFinset v → β) : W → β :=
  fun u => if h : u ∈ D.parentsFinset v then z ⟨u, h⟩ else default

/-- The mechanism `mech v σ e` depends on the configuration `σ` only through the parents
of `v`. -/
def ReadsParentsD (mech : W → (W → β) → η → β) : Prop :=
  ∀ v σ σ' e, (∀ u, D.Adj u v → σ u = σ' u) → mech v σ e = mech v σ' e

/-- The structural causal model on `D` with value type `β` and noise type `η` at every vertex,
whose structural function at `v` is the mechanism `mech v` applied to the parent values. -/
def mechSCM (hD : D.IsAcyclic) (mech : W → (W → β) → η → β) (noise : W → FiniteDist η) :
    SCM D (fun _ => β) (fun _ => η) where
  acyclic := hD
  f v z e := mech v (extendParD D v z) e
  noise := noise

variable {D} {hD : D.IsAcyclic} {mech : W → (W → β) → η → β} {noise : W → FiniteDist η}

theorem mechSCM_f (hm : ReadsParentsD D mech) (v : W) (σ : W → β) (e : η) :
    (mechSCM D hD mech noise).f v ((D.parentsFinset v).restrict σ) e = mech v σ e :=
  hm v _ _ e fun _ hu => by simp [extendParD, hu]

/-- The solution of `mechSCM` is characterized by the mechanisms. -/
theorem solve_mechSCM_iff (hm : ReadsParentsD D mech) {ν : W → η} {σ : W → β} :
    (mechSCM D hD mech noise).solve ν = σ ↔ ∀ v, σ v = mech v σ (ν v) := by
  rw [eq_comm, ← SCM.isSolution_iff]
  exact forall_congr' fun v => by rw [mechSCM_f hm]

/-- The solution of a submodel of `mechSCM` is characterized by the mechanisms. -/
theorem solve_intervene_mechSCM_iff (hm : ReadsParentsD D mech) (X : Finset W) (x : W → β)
    {ν : W → η} {σ : W → β} :
    ((mechSCM D hD mech noise).intervene X x).solve ν = σ ↔
      (∀ v ∈ X, σ v = x v) ∧ ∀ v ∉ X, σ v = mech v σ (ν v) := by
  rw [eq_comm, ← SCM.isSolution_iff, SCM.isSolution_intervene_iff]
  exact and_congr_right' (forall₂_congr fun v _ => by rw [mechSCM_f hm])

end MechSCM

variable {V : Type} [Fintype V] [DecidableEq V] {G : ADMG V} [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj]

/-- A product of products of laws of bits is the product law over the pairs of indices. -/
theorem probOf_pi_curry {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Bool → FiniteDist Bool)
    (E : (ι → Bool → Bool) → Prop) [DecidablePred E] :
    (FiniteDist.pi fun i => FiniteDist.pi (p i)).probOf E =
      (FiniteDist.pi fun q : ι × Bool => p q.1 q.2).probOf (fun ω => E (Function.curry ω)) := by
  classical
  unfold FiniteDist.probOf FiniteDist.prob
  rw [sum_filter, sum_filter]
  refine Fintype.sum_equiv (Equiv.curry ι Bool Bool).symm _ _ fun ν => ?_
  simp [Fintype.prod_prod_type]

namespace Transport

/-! ### The transport successor -/

omit [DecidableRel G.bidirected.Adj] in
/-- Every vertex of `D \ Y` has a child in `D`, where `D` is the set of ancestors of `Y`
outside `X`. -/
theorem exists_next {X Y : Finset V} {p : V} (hp : p ∈ ancIn G (univ \ X) Y \ Y) :
    ∃ u ∈ ancIn G (univ \ X) Y, G.directed.Adj p u := by
  obtain ⟨hpD, hpY⟩ := mem_sdiff.1 hp
  obtain ⟨hpa, -⟩ := mem_inter.1 hpD
  obtain ⟨y, hy, hpath⟩ := ADMG.mem_ancestorsOfFinset.1 hpa
  rcases hpath.cases_head with rfl | ⟨u, hpu, huy⟩
  · exact absurd hy hpY
  · exact ⟨u, mem_inter.2 ⟨ADMG.mem_ancestorsOfFinset.2 ⟨y, hy, huy⟩, mem_coe.1 hpu.2.2⟩,
      hpu.1⟩

/-- The transport successor: a child in `D` of each vertex of `D \ Y`. -/
noncomputable def next (G : ADMG V) [DecidableRel G.directed.Adj] (X Y : Finset V) (p : V) : V :=
  if h : p ∈ ancIn G (univ \ X) Y \ Y then Classical.choose (exists_next h) else p

omit [DecidableRel G.bidirected.Adj] in
theorem next_spec {X Y : Finset V} {p : V} (hp : p ∈ ancIn G (univ \ X) Y \ Y) :
    next G X Y p ∈ ancIn G (univ \ X) Y ∧ G.directed.Adj p (next G X Y p) := by
  unfold next
  rw [dite_eq_left hp]
  exact Classical.choose_spec (exists_next hp)

open Classical in
/-- The transport inputs of `w`: the vertices of `D \ Y` whose successor is `w`. -/
noncomputable def into (G : ADMG V) [DecidableRel G.directed.Adj] (X Y : Finset V) (w : V) :
    Finset V :=
  (ancIn G (univ \ X) Y \ Y).filter fun p => next G X Y p = w

omit [DecidableRel G.bidirected.Adj] in
theorem mem_into {X Y : Finset V} {w p : V} :
    p ∈ into G X Y w ↔ p ∈ ancIn G (univ \ X) Y \ Y ∧ next G X Y p = w := by
  unfold into
  rw [mem_filter]

omit [DecidableRel G.bidirected.Adj] in
/-- Transport inputs are parents. -/
theorem into_adj {X Y : Finset V} {w p : V} (hp : p ∈ into G X Y w) : G.directed.Adj p w := by
  obtain ⟨hp', rfl⟩ := mem_into.1 hp
  exact (next_spec hp').2

/-! ### The two bit models -/

variable {X Z : Finset V} (P : RoutedPair G X Z) (Y : Finset V)

/-- The transport base of `w`: the sum of the payloads of its transport inputs, for hedge bits
`hv` and transport bits `τ`. -/
noncomputable def tbase (hv : V → Bool) (w : V) (τ : V ⊕ V × V → Bool) : Bool :=
  ∑ p ∈ into G X Y w, (τ (.inl p) + if p ∈ P.Yo then hv p else 0)

/-- The transport mechanisms for hedge bits `hv`: an observed vertex is its transport base plus
its noise bit; a latent vertex is its noise bit. -/
noncomputable def tmech (hv : V → Bool) : V ⊕ V × V → (V ⊕ V × V → Bool) → Bool → Bool
  | .inl w, τ, e => tbase P Y hv w τ + e
  | .inr _, _, e => e

/-- The two bit mechanisms of model `i`: the first bit follows the hedge mechanism of
`P.setup` on the first bits, the second bit the transport mechanism. -/
noncomputable def pmech (i : Bool) (j : V ⊕ V × V) (σ : V ⊕ V × V → Bool × Bool)
    (e : Bool → Bool) : Bool × Bool :=
  (P.setup.mech i j (fun k => (σ k).1) (e false),
    tmech P Y (fun v => (σ (.inl v)).1) j (fun k => (σ k).2) (e true))

/-- The noise law of a vertex: two independent bits, the first with the law of the hedge
layer, the second true with probability `1/4`. -/
noncomputable def pnoise (j : V ⊕ V × V) : FiniteDist (Bool → Bool) :=
  FiniteDist.pi fun b => if b then quarterBit else P.setup.noise j

omit [DecidableRel G.bidirected.Adj] in
theorem tbase_congr {hv hv' : V → Bool} {w : V} {τ τ' : V ⊕ V × V → Bool}
    (h : ∀ p ∈ into G X Y w, τ (.inl p) = τ' (.inl p) ∧ hv p = hv' p) :
    tbase P Y hv w τ = tbase P Y hv' w τ' :=
  sum_congr rfl fun p hp => by rw [(h p hp).1, (h p hp).2]

omit [DecidableRel G.bidirected.Adj] in
/-- The transport mechanisms read only parents. -/
theorem tmech_reads (hv : V → Bool) : ReadsParents G.canonicalDAG (tmech P Y hv) := by
  intro j τ τ' e h
  rcases j with w | q
  · exact congrArg (· + e) (tbase_congr P Y fun p hp =>
      ⟨h _ (ADMG.canonicalDAG_adj_inl_inl.2 (into_adj hp)), rfl⟩)
  · rfl

/-- The two bit mechanisms read only parents. -/
theorem pmech_reads (i : Bool) : ReadsParentsD G.canonicalDAG (pmech P Y i) := by
  intro j σ σ' e h
  have h1 := P.setup.readsParents i j (fun k => (σ k).1) (fun k => (σ' k).1) (e false)
    fun u hu => by rw [h u hu]
  have h2 : tmech P Y (fun v => (σ (.inl v)).1) j (fun k => (σ k).2) (e true) =
      tmech P Y (fun v => (σ' (.inl v)).1) j (fun k => (σ' k).2) (e true) := by
    rcases j with w | q
    · refine congrArg (· + e true) (tbase_congr P Y fun p hp => ?_)
      have := h _ (ADMG.canonicalDAG_adj_inl_inl.2 (into_adj hp))
      exact ⟨by rw [this], by rw [this]⟩
    · rfl
  simp only [pmech, h1, h2]

/-- Model `i` with two bits at every vertex, on the canonical DAG. -/
noncomputable def pscm (hG : G.IsAcyclic) (i : Bool) :
    SCM G.canonicalDAG (fun _ => Bool × Bool) (fun _ => Bool → Bool) :=
  mechSCM G.canonicalDAG hG.canonicalDAG (pmech P Y i) (pnoise P)

/-- Model `i` with two bits at every vertex, bundled with its noise types. -/
noncomputable def pmodel (hG : G.IsAcyclic) (i : Bool) :
    SCM.Model G.canonicalDAG (fun _ => Bool × Bool) :=
  ⟨fun _ => Bool → Bool, pscm P Y hG i⟩

/-- The transport layer alone, for fixed hedge bits `hv`, as a Boolean model. -/
noncomputable def tscm (hG : G.IsAcyclic) (hv : V → Bool) :
    SCM G.canonicalDAG (fun _ => Bool) (fun _ => Bool) :=
  boolSCM G.canonicalDAG hG.canonicalDAG (tmech P Y hv) fun _ => quarterBit

/-! ### Solutions -/

variable (hG : G.IsAcyclic)

/-- The solution of the two bit model follows the mechanisms. -/
theorem solve_apply (i : Bool) (ν : V ⊕ V × V → Bool → Bool) (j : V ⊕ V × V) :
    (pscm P Y hG i).solve ν j = pmech P Y i j ((pscm P Y hG i).solve ν) (ν j) :=
  (solve_mechSCM_iff (pmech_reads P Y i)).1 rfl j

/-- **The hedge layer.** The first bits of the solution of the two bit model are the solution
of the Boolean model `P.setup.scm` at the first noise bits. -/
theorem fst_solve (i : Bool) (ν : V ⊕ V × V → Bool → Bool) :
    (fun j => ((pscm P Y hG i).solve ν j).1) = (P.setup.scm hG i).solve (fun j => ν j false) :=
  ((solve_boolSCM_iff (P.setup.readsParents i)).2 fun j =>
    congrArg Prod.fst (solve_apply P Y hG i ν j)).symm

/-- **The transport layer.** The second bits of the solution of the two bit model are the
solution of the transport model for the observed first bits, at the second noise bits. -/
theorem snd_solve (i : Bool) (ν : V ⊕ V × V → Bool → Bool) :
    (fun j => ((pscm P Y hG i).solve ν j).2) =
      (tscm P Y hG fun v => ((pscm P Y hG i).solve ν (.inl v)).1).solve (fun j => ν j true) :=
  ((solve_boolSCM_iff (tmech_reads P Y _)).2 fun j =>
    congrArg Prod.snd (solve_apply P Y hG i ν j)).symm

/-- Under `do(X := x)`, the first bits are the solution of the intervened Boolean model. -/
theorem fst_solve_intervene (i : Bool) (x : V ⊕ V × V → Bool × Bool)
    (ν : V ⊕ V × V → Bool → Bool) :
    (fun j => (((pscm P Y hG i).intervene (X.map .inl) x).solve ν j).1) =
      ((P.setup.scm hG i).intervene (X.map .inl) (fun j => (x j).1)).solve
        (fun j => ν j false) := by
  have h := (solve_intervene_mechSCM_iff (hD := hG.canonicalDAG) (noise := pnoise P) (ν := ν)
    (pmech_reads P Y i) (X.map .inl) x).1 rfl
  exact ((solve_intervene_boolSCM_iff (P.setup.readsParents i) _ _).2
    ⟨fun j hj => congrArg Prod.fst (h.1 j hj), fun j hj => congrArg Prod.fst (h.2 j hj)⟩).symm

/-- Under `do(X := x)`, the second bit of a vertex outside `X` follows the transport
mechanism. -/
theorem snd_solve_intervene (i : Bool) (x : V ⊕ V × V → Bool × Bool)
    (ν : V ⊕ V × V → Bool → Bool) {v : V} (hv : v ∉ X) :
    (((pscm P Y hG i).intervene (X.map .inl) x).solve ν (.inl v)).2 =
      tbase P Y (fun u => (((pscm P Y hG i).intervene (X.map .inl) x).solve ν (.inl u)).1) v
        (fun k => (((pscm P Y hG i).intervene (X.map .inl) x).solve ν k).2) + ν (.inl v) true :=
  congrArg Prod.snd (((solve_intervene_mechSCM_iff (hD := hG.canonicalDAG) (noise := pnoise P)
    (ν := ν) (pmech_reads P Y i) (X.map .inl) x).1 rfl).2 _ (RoutedPair.inl_notMem hv))

/-! ### Telescoping along the transport successor -/

omit [DecidableRel G.bidirected.Adj] in
/-- The target of the hedge parity lies in the target of the routed pair. -/
theorem Yo_sub : P.Yo ⊆ Z := fun y hy => by
  rcases mem_union.1 (show y ∈ P.Yo from hy) with h | h
  · exact (mem_sdiff.1 h).1
  · exact (mem_inter.1 h).1

omit [DecidableRel G.bidirected.Adj] in
/-- **Telescoping.** If every vertex of `D` follows the transport equation with noise `e`, the
payloads of `Y` sum to the noise over `D` plus the hedge bits of the target `P.Yo`. -/
theorem sum_pay_Y (hXY : Disjoint X Y) (hZ : Z ⊆ ancIn G (univ \ X) Y) (hv : V → Bool)
    (τ : V ⊕ V × V → Bool) (e : V → Bool)
    (h : ∀ v ∈ ancIn G (univ \ X) Y, τ (.inl v) = tbase P Y hv v τ + e v) :
    ∑ y ∈ Y, (τ (.inl y) + if y ∈ P.Yo then hv y else 0) =
      ∑ v ∈ ancIn G (univ \ X) Y, e v + ∑ v ∈ P.Yo, hv v := by
  classical
  set D := ancIn G (univ \ X) Y
  set pay : V → Bool := fun p => τ (.inl p) + if p ∈ P.Yo then hv p else 0
  have hYD : Y ⊆ D :=
    subset_ancIn fun v hv => mem_sdiff.2 ⟨mem_univ v, disjoint_right.1 hXY hv⟩
  have hfib : ∑ v ∈ D, tbase P Y hv v τ = ∑ p ∈ D \ Y, pay p := by
    rw [← sum_fiberwise_of_maps_to (s := D \ Y) (t := D) (g := next G X Y)
      (fun p hp => (next_spec hp).1) pay]
    refine sum_congr rfl fun v _ => sum_congr ?_ fun _ _ => rfl
    ext p
    rw [mem_into, mem_filter]
  have hD : ∑ v ∈ D, pay v = ∑ p ∈ D \ Y, pay p + ∑ v ∈ D, e v + ∑ v ∈ P.Yo, hv v := by
    simp only [pay]
    rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 ((Yo_sub P).trans hZ),
      sum_congr rfl h, sum_add_distrib, hfib]
  have hs := sum_sdiff hYD (f := pay)
  set A := ∑ p ∈ D \ Y, pay p
  calc ∑ y ∈ Y, pay y = (A + ∑ y ∈ Y, pay y) + A := by
        rw [add_comm A, add_assoc, bool_add_self, add_zero]
    _ = (A + A) + (∑ v ∈ D, e v + ∑ v ∈ P.Yo, hv v) := by rw [hs, hD]; ring
    _ = _ := by rw [bool_add_self, zero_add]

/-- The transported parity of a two bit configuration: the sum over `Y` of the payloads, the
second bit plus, on the target `P.Yo` of the hedge parity, the first bit. -/
noncomputable def payY (τ : V ⊕ V × V → Bool × Bool) : Bool :=
  ∑ y ∈ Y, ((τ (.inl y)).2 + if y ∈ P.Yo then (τ (.inl y)).1 else 0)

omit [DecidableRel G.bidirected.Adj] in
/-- A routed pair whose target lies in `D` has its target disjoint from `X`. -/
theorem disjoint_of_sub (hZ : Z ⊆ ancIn G (univ \ X) Y) : Disjoint X Z :=
  disjoint_right.2 fun _ hz => RoutedPair.notMem_X_of_mem_D (hZ hz)

/-- **The transported parity under `do(X := x)`**: the transport noise over `D` plus the hedge
parity of the intervened Boolean model. -/
theorem payY_intervene (hXY : Disjoint X Y) (hZ : Z ⊆ ancIn G (univ \ X) Y) (i : Bool)
    (x : V ⊕ V × V → Bool × Bool) (ν : V ⊕ V × V → Bool → Bool) :
    payY P Y (((pscm P Y hG i).intervene (X.map .inl) x).solve ν) =
      ∑ v ∈ ancIn G (univ \ X) Y, ν (.inl v) true +
        ∑ y ∈ P.Yo, ((P.setup.scm hG i).intervene (X.map .inl) (fun j => (x j).1)).solve
          (fun j => ν j false) (.inl y) := by
  set τ := ((pscm P Y hG i).intervene (X.map .inl) x).solve ν
  unfold payY
  rw [sum_pay_Y P Y hXY hZ (fun u => (τ (.inl u)).1) (fun k => (τ k).2)
    (fun v => ν (.inl v) true) fun v hv =>
      snd_solve_intervene P Y hG i x ν (RoutedPair.notMem_X_of_mem_D hv)]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  exact congrFun (fst_solve_intervene P Y hG i x ν) (.inl y)

/-- **The transported parity in model one** under `do(X := x)`. -/
theorem parity_false (hXY : Disjoint X Y) (hZ : Z ⊆ ancIn G (univ \ X) Y)
    (x : V ⊕ V × V → Bool × Bool) (ν : V ⊕ V × V → Bool → Bool) :
    payY P Y (((pscm P Y hG false).intervene (X.map .inl) x).solve ν) =
      ∑ v ∈ ancIn G (univ \ X) Y, ν (.inl v) true +
        (∑ v ∈ P.Q, ν (.inl v) false +
          ∑ v ∈ P.C ∪ P.S1, bnd G P.T (Setup.lat fun j => ν j false) v +
          ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.S1), (x (.inl s)).1) := by
  rw [payY_intervene P Y hG hXY hZ, P.parity_false hG (disjoint_of_sub Y hZ)]

/-- **The transported parity in model two** under `do(X := x)`. -/
theorem parity_true (hXY : Disjoint X Y) (hZ : Z ⊆ ancIn G (univ \ X) Y)
    (x : V ⊕ V × V → Bool × Bool) (ν : V ⊕ V × V → Bool → Bool) :
    payY P Y (((pscm P Y hG true).intervene (X.map .inl) x).solve ν) =
      ∑ v ∈ ancIn G (univ \ X) Y, ν (.inl v) true +
        (∑ v ∈ P.Q, ν (.inl v) false +
          ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.C), (x (.inl s)).1) := by
  rw [payY_intervene P Y hG hXY hZ, P.parity_true hG (disjoint_of_sub Y hZ)]

/-! ### The laws of the transported parity -/

omit [DecidableRel G.bidirected.Adj] in
/-- The noise law of the two bit model, as a product law over the pairs of a vertex and a
layer. -/
theorem probOf_pnoise (E : (V ⊕ V × V → Bool → Bool) → Prop) [DecidablePred E] :
    (FiniteDist.pi (pnoise P)).probOf E =
      (FiniteDist.pi fun r : (V ⊕ V × V) × Bool =>
        if r.2 then quarterBit else P.setup.noise r.1).probOf (fun ω => E (Function.curry ω)) :=
  probOf_pi_curry (fun j b => if b then quarterBit else P.setup.noise j) E

/-- **Model one gives the transported parity a fair law** under `do(X := x)`. -/
theorem probOf_false (hXY : Disjoint X Y) (hZ : Z ⊆ ancIn G (univ \ X) Y)
    (x : V ⊕ V × V → Bool × Bool) (b : Bool) :
    (FiniteDist.pi (pnoise P)).probOf (fun ν =>
      payY P Y (((pscm P Y hG false).intervene (X.map .inl) x).solve ν) = b) = 1 / 2 := by
  classical
  rw [probOf_pnoise]
  simp only [parity_false P Y hG hXY hZ]
  obtain ⟨t, ht⟩ := P.meets
  obtain ⟨htT, htX⟩ := mem_inter.1 ht
  have htA : t ∉ P.C ∪ P.S1 := by
    rintro h
    rcases mem_union.1 h with h | h
    · exact RoutedPair.notMem_X_of_mem_D (P.sub h) htX
    · exact (P.S1_sub h).2 htX
  obtain ⟨q, hq, hq1, hq2⟩ := P.exists_leaving subset_union_left htT htA
  let e : (V ⊕ V × V) × Bool → Bool := fun r => match r with
    | (.inr p, false) => single q p
    | _ => 0
  let φ : ((V ⊕ V × V) × Bool → Bool) → (V ⊕ V × V) × Bool → Bool := fun ω => ω + e
  have hφφ : ∀ ω, φ (φ ω) = ω := fun ω => by
    funext r
    simp only [φ, Pi.add_apply, add_assoc, bool_add_self, add_zero]
  have hcross : ∑ v ∈ P.C ∪ P.S1, bnd G P.T (single q) v = 1 := by
    simp only [bnd_single hq]
    rw [sum_add_distrib, sum_ite_eq, sum_ite_eq]
    simp only [hq1, hq2, ↓reduceIte, add_zero]
  set κ := ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.S1), (x (.inl s)).1
  set F : ((V ⊕ V × V) × Bool → Bool) → Bool := fun ω =>
    ∑ v ∈ ancIn G (univ \ X) Y, Function.curry ω (.inl v) true +
      (∑ v ∈ P.Q, Function.curry ω (.inl v) false +
        ∑ v ∈ P.C ∪ P.S1, bnd G P.T (Setup.lat fun j => Function.curry ω j false) v + κ)
  have hpar : ∀ ω, F (φ ω) = F ω + 1 := by
    intro ω
    have hl : (Setup.lat fun j => Function.curry (φ ω) j false) =
        (Setup.lat fun j => Function.curry ω j false) + single q := rfl
    have h1 : ∑ v ∈ ancIn G (univ \ X) Y, Function.curry (φ ω) (.inl v) true =
        ∑ v ∈ ancIn G (univ \ X) Y, Function.curry ω (.inl v) true := by
      simp [φ, e, Function.curry]
    have h2 : ∑ v ∈ P.Q, Function.curry (φ ω) (.inl v) false =
        ∑ v ∈ P.Q, Function.curry ω (.inl v) false := by
      simp [φ, e, Function.curry]
    simp only [F]
    rw [h1, h2, hl, ← hcross]
    simp only [bnd_add, sum_add_distrib]
    ring
  unfold FiniteDist.probOf
  refine IDCompletenessBow.prob_eq_of_involution _ _ φ hφφ (fun ω => ?_) (q' := 1 / 2)
    (by norm_num) fun ω _ => ?_
  · simp only [mem_filter, mem_univ, true_and]
    change F (φ ω) = b ↔ ¬ F ω = b
    rw [hpar]
    cases F ω <;> cases b <;> decide
  · rw [FiniteDist.pi_add_eq _ _ _ fun r hr => ?_]
    rcases r with ⟨j | p, _ | _⟩
    · exact absurd hr (by simp [e])
    · exact absurd hr (by simp [e])
    · rfl
    · exact absurd hr (by simp [e])

/-- **Model two gives the transported parity a biased law** under `do(X := x)`. -/
theorem probOf_true_ne (hXY : Disjoint X Y) (hZ : Z ⊆ ancIn G (univ \ X) Y)
    (x : V ⊕ V × V → Bool × Bool) (b : Bool) :
    (FiniteDist.pi (pnoise P)).probOf (fun ν =>
      payY P Y (((pscm P Y hG true).intervene (X.map .inl) x).solve ν) = b) ≠ 1 / 2 := by
  classical
  rw [probOf_pnoise]
  simp only [parity_true P Y hG hXY hZ]
  set κ := ∑ s ∈ (P.T \ P.C).filter (fun s => s ∈ X ∧ P.ch s ∈ P.C), (x (.inl s)).1
  set A : Finset ((V ⊕ V × V) × Bool) :=
    ((ancIn G (univ \ X) Y).map .inl ×ˢ {true}) ∪ (P.Q.map .inl ×ˢ {false})
  have hA : ∀ ω : (V ⊕ V × V) × Bool → Bool, ∑ r ∈ A, ω r =
      ∑ v ∈ ancIn G (univ \ X) Y, Function.curry ω (.inl v) true +
        ∑ v ∈ P.Q, Function.curry ω (.inl v) false := by
    intro ω
    rw [sum_union (disjoint_left.2 fun r h1 h2 => by
      simp only [mem_product, mem_singleton] at h1 h2
      rw [h1.2] at h2
      exact Bool.noConfusion h2.2)]
    simp [Function.curry]
  have h : ∀ ω : (V ⊕ V × V) × Bool → Bool,
      (∑ v ∈ ancIn G (univ \ X) Y, Function.curry ω (.inl v) true +
        (∑ v ∈ P.Q, Function.curry ω (.inl v) false + κ) = b) ↔ ∑ r ∈ A, ω r = b + κ := by
    intro ω
    rw [hA, ← add_assoc]
    constructor
    · rintro rfl
      rw [add_assoc, bool_add_self, add_zero]
    · intro h
      rw [h, add_assoc, bool_add_self, add_zero]
  rw [FiniteDist.probOf_congr _ h]
  refine probOf_parity_ne_half _ _ (fun r hr => ?_) _
  rcases mem_union.1 hr with hr | hr
  · obtain ⟨hr1, hr2⟩ := mem_product.1 hr
    rw [mem_singleton.1 hr2]
    rfl
  · obtain ⟨hr1, hr2⟩ := mem_product.1 hr
    obtain ⟨v, hv, hvr⟩ := mem_map.1 hr1
    have : v ∉ P.T \ P.C := (mem_sdiff.1 (P.Q_sub hv)).2
    rw [mem_singleton.1 hr2, ← hvr]
    change (if v ∈ P.T \ P.C then FiniteDist.uniform else quarterBit) = quarterBit
    simp [this]

/-! ### Equal observed laws -/

/-- The shear of the two bit noise: the shear of the hedge layer on the first bits, the second
bits unchanged. -/
noncomputable def pshear (ν : V ⊕ V × V → Bool → Bool) : V ⊕ V × V → Bool → Bool :=
  fun j b => cond b (ν j true) (P.setup.shear hG (fun k => ν k false) j)

theorem pshear_pshear (ν : V ⊕ V × V → Bool → Bool) : pshear P hG (pshear P hG ν) = ν := by
  funext j b
  cases b
  · exact congrFun (P.setup.shear_shear hG (fun k => ν k false)) j
  · rfl

/-- The shear preserves the two bit noise law. -/
theorem pi_pshear (ν : V ⊕ V × V → Bool → Bool) :
    FiniteDist.pi (pnoise P) (pshear P hG ν) = FiniteDist.pi (pnoise P) ν := by
  rw [FiniteDist.pi_apply, FiniteDist.pi_apply]
  refine prod_congr rfl fun j _ => ?_
  simp only [pnoise, FiniteDist.pi_apply, Fintype.prod_bool]
  congr 1
  rcases j with v | p
  · simp [pshear, Setup.shear]
  · change FiniteDist.uniform _ = FiniteDist.uniform _
    rw [FiniteDist.uniform_apply, FiniteDist.uniform_apply]

/-- **The shear carries model one to model two** on the observed vertices. -/
theorem solve_pshear (ν : V ⊕ V × V → Bool → Bool) (v : V) :
    (pscm P Y hG true).solve (pshear P hG ν) (.inl v) = (pscm P Y hG false).solve ν (.inl v) := by
  have hfst : ∀ u : V, ((pscm P Y hG true).solve (pshear P hG ν) (.inl u)).1 =
      ((pscm P Y hG false).solve ν (.inl u)).1 := by
    intro u
    rw [congrFun (fst_solve P Y hG true _) (.inl u), congrFun (fst_solve P Y hG false _) (.inl u)]
    change (P.setup.scm hG true).solve (P.setup.shear hG fun k => ν k false) (.inl u) = _
    rw [P.setup.solve_shear hG]
    simp
  have hv : (fun u => ((pscm P Y hG true).solve (pshear P hG ν) (.inl u)).1) =
      fun u => ((pscm P Y hG false).solve ν (.inl u)).1 := funext hfst
  refine Prod.ext (hfst v) ?_
  rw [congrFun (snd_solve P Y hG true _) (.inl v), congrFun (snd_solve P Y hG false _) (.inl v),
    hv]
  rfl

/-- **Equal observed laws.** The two bit models one and two have the same law of the observed
vertices. -/
theorem marginal_eq : (pscm P Y hG false).dist.marginal ADMG.canonicalObs =
    (pscm P Y hG true).dist.marginal ADMG.canonicalObs := by
  unfold FiniteDist.marginal SCM.dist
  rw [FiniteDist.map_map, FiniteDist.map_map]
  change (FiniteDist.pi (pnoise P)).map _ = (FiniteDist.pi (pnoise P)).map _
  conv_rhs => rw [← FiniteDist.map_comp_eq_of_bijective _
    (Function.Involutive.bijective (pshear_pshear P hG)) (pi_pshear P hG)]
  congr 1
  funext ν
  funext ⟨j, hj⟩
  obtain ⟨v, -, rfl⟩ := mem_map.1 hj
  simp only [Function.comp, Finset.restrict]
  exact (solve_pshear P Y hG ν v).symm

/-! ### Positivity -/

/-- **Positivity.** The observed law of the two bit model one is strictly positive. -/
theorem margAt_pos_false (w : V ⊕ V × V → Bool × Bool) :
    0 < (pscm P Y hG false).dist.margAt ADMG.canonicalObs w := by
  classical
  have h1 := P.setup.margAt_pos_false hG (fun j => (w j).1)
  rw [SCM.margAt_dist, P.setup.noiseDist_scm] at h1
  obtain ⟨ν1, hν1⟩ : ∃ ν1 : V ⊕ V × V → Bool, ∀ j ∈ ADMG.canonicalObs,
      (P.setup.scm hG false).solve ν1 j = (w j).1 := by
    by_contra hne
    push Not at hne
    rw [FiniteDist.probOf_eq_zero _ fun u hu => by
      obtain ⟨j, hj, hne'⟩ := hne u
      exact hne' (hu j hj)] at h1
    exact lt_irrefl _ h1
  let hv : V → Bool := fun v => (w (.inl v)).1
  let σ2 : V ⊕ V × V → Bool := Sum.elim (fun v => (w (.inl v)).2) 0
  let ν2 : V ⊕ V × V → Bool := Sum.elim (fun v => (w (.inl v)).2 + tbase P Y hv v σ2) 0
  have hσ2 : (tscm P Y hG hv).solve ν2 = σ2 := by
    refine (solve_boolSCM_iff (tmech_reads P Y hv)).2 fun j => ?_
    rcases j with v | p
    · change (w (.inl v)).2 = tbase P Y hv v σ2 + ((w (.inl v)).2 + tbase P Y hv v σ2)
      rw [add_comm (w (.inl v)).2, ← add_assoc, bool_add_self, zero_add]
    · rfl
  let ν : V ⊕ V × V → Bool → Bool := fun j b => cond b (ν2 j) (ν1 j)
  have hfst : ∀ u : V, ((pscm P Y hG false).solve ν (.inl u)).1 = (w (.inl u)).1 := by
    intro u
    rw [congrFun (fst_solve P Y hG false ν) (.inl u)]
    exact hν1 _ (mem_map_of_mem _ (mem_univ u))
  have hsol : ∀ u : V, (pscm P Y hG false).solve ν (.inl u) = w (.inl u) := by
    intro u
    refine Prod.ext (hfst u) ?_
    rw [congrFun (snd_solve P Y hG false ν) (.inl u)]
    have hv' : (fun u => ((pscm P Y hG false).solve ν (.inl u)).1) = hv := funext hfst
    rw [hv']
    exact congrFun hσ2 (.inl u)
  have hpos : 0 < FiniteDist.pi (pnoise P) ν := by
    rw [FiniteDist.pi_apply]
    refine prod_pos fun j _ => ?_
    simp only [pnoise, FiniteDist.pi_apply, Fintype.prod_bool]
    exact mul_pos (quarterBit_pos _) (P.setup.noise_pos j _)
  rw [SCM.margAt_dist]
  change 0 < (FiniteDist.pi (pnoise P)).probOf _
  refine hpos.trans_le (FiniteDist.le_probOf _ ν ?_)
  intro j hj
  obtain ⟨v, -, rfl⟩ := mem_map.1 hj
  exact hsol v

/-- **Positivity of both two bit models.** -/
theorem margAt_pos (i : Bool) (w : V ⊕ V × V → Bool × Bool) :
    0 < (pscm P Y hG i).dist.margAt ADMG.canonicalObs w := by
  cases i
  · exact margAt_pos_false P Y hG w
  · rw [← FiniteDist.marginal_restrict, ← marginal_eq P Y hG, FiniteDist.marginal_restrict]
    exact margAt_pos_false P Y hG w

end Transport

end IDCompleteness

end CausalInference
