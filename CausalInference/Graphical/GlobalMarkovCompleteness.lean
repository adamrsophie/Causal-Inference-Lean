/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.GlobalMarkov
public import CausalInference.Graphical.GlobalMarkovCompletenessLemmas

/-!
# Completeness of d-separation

The converse half of Pearl (2009), Theorem 1.2.4, which the book attributes to Verma and Pearl
(1988), see also Geiger, Verma and Pearl (1990): if `x` and `y` are d-connected given `Z` in an
acyclic graph `G`, some distribution factorizing according to `G` violates `{x} ⫫ {y} | Z`.
Together with the soundness half (`Digraph.Factorizes.condIndep_of_dSep`) this characterizes
d-separation as the conditional independences shared by all distributions that factorize
according to `G`. The witnesses take Boolean values at every vertex. This is the weak form of
completeness (for each d-connection there is some factorizing distribution that violates the
independence); the stronger statement of a single distribution that is faithful to `G` is not
proved here.

Every witness is the law of a structural model with Boolean rules (`Digraph.BoolRule`, in
`CausalInference.Graphical.GlobalMarkovCompletenessLemmas`): a rule makes `x` and `y` agree in
every solution in which all of `Z` is false, and has a noise value whose solution makes `x` true
and all of `Z` false.

## Main definitions

* `Digraph.trekRule`: a fair bit at the top of a trek, copied along directed paths avoiding `Z`.
* `Digraph.colliderRule`: the exclusive or of two fair bits at a collider, copied to every
  descendant of the collider.
* `Digraph.trailRule`: the rule for a simple active trail. Each trail vertex is the exclusive
  or of its trail parents (a non-collider copies its unique trail parent, or is a fair bit if
  it has none; a collider is the exclusive or of its two trail parents); each collider is
  copied along a fixed shortest directed path to `Z`; every other vertex is false.

## Main results

The staged results, each under an extra hypothesis:
* `Digraph.exists_factorizes_not_condIndep_of_reflTransGen`: a directed path from `x` to `y`
  avoiding `Z`.
* `Digraph.exists_factorizes_not_condIndep_of_trek`: a trek (a fork with top `t`, or a
  directed path) avoiding `Z`.
* `Digraph.exists_factorizes_not_condIndep_of_collider_mem` and
  `Digraph.exists_factorizes_not_condIndep_of_collider`: one collider `x → c ← y` with `c ∈ Z`,
  or with `c` an ancestor of a vertex of `Z`.

The general theorem and its consequences:
* `Digraph.exists_factorizes_not_condIndep_of_dConn`: **completeness of d-separation** for
  single vertices.
* `Digraph.exists_factorizes_not_condIndep_of_adj`: the single-edge case, as a corollary.
* `Digraph.dSep_iff_forall_factorizes_condIndep`: for acyclic `G`, `{x}` and `{y}` are
  d-separated by `Z` if and only if `{x} ⫫ {y} | Z` holds in every distribution over binary
  variables that factorizes according to `G`; `Digraph.dSep_iff_forall_factorizes_condIndep'`
  is the version for arbitrary finsets `X` and `Y`.

## Minimality used

The general proof takes an active trail from `x` to `y` with no repeated vertex
(`Digraph.IsDTrail`) that minimizes the measure `Digraph.trailMeasure`: the number of states of
the trail plus, summed over its colliders `c`, the length `Digraph.distZ` of a shortest
directed path from `c` to `Z`. The shortest paths follow the function `Digraph.nextZ`. Minimality
is used only for two facts: such a path from a collider meets the trail only at the collider
(`Digraph.IsDTrail.iterate_nextZ_notMem_of_min`), and the paths from two distinct colliders are
disjoint (`Digraph.IsDTrail.iterate_nextZ_ne_of_min'`). If either failed, a shortcut through the
path would give an active simple trail of smaller measure.

## References

* T. Verma and J. Pearl (1988), *Causal networks: semantics and expressiveness*.
* D. Geiger, T. Verma and J. Pearl (1990), *Identifying independence in Bayesian networks*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 1.2.3,
  Theorem 1.2.4.
-/

@[expose] public section

namespace Digraph

open CausalInference Finset Relation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]

/-! ### Treks and directed paths -/

open Classical in
/-- The rule for a trek with top `t` avoiding `Z`: `t` is a fair bit, every vertex outside `Z`
with a parent reachable from `t` by a directed path outside `Z` copies such a parent, and every
other vertex is false. -/
noncomputable def trekRule (t : V) (Z : Finset V) : G.BoolRule where
  F v x e := if v = t then e else
    if h : v ∉ Z ∧ ∃ u, ReflTransGen (fun a b => G.Adj a b ∧ b ∉ Z) t u ∧ G.Adj u v then
      x (Classical.choose h.2) else false
  congr v x x' e hxx' := by
    split_ifs with h1 h2
    · rfl
    · exact hxx' _ (Classical.choose_spec h2.2).2
    · rfl
  F_false v := by split_ifs <;> rfl

theorem trekRule_sol {t : V} {Z : Finset V} {n σ : V → Bool} (hG : G.IsAcyclic)
    (hσ : (trekRule (G := G) t Z).Sol n σ) {v : V}
    (hv : ReflTransGen (fun a b => G.Adj a b ∧ b ∉ Z) t v) : σ v = n t := by
  induction v using hG.wellFounded_adj.induction with
  | _ v ih =>
    rw [hσ v]
    simp only [trekRule]
    split_ifs with h1 h2
    · rw [h1]
    · exact ih _ (Classical.choose_spec h2.2).2 (Classical.choose_spec h2.2).1
    · exfalso
      rcases hv.cases_tail with rfl | ⟨u, hu, huv, hvZ⟩
      · exact h1 rfl
      · exact h2 ⟨hvZ, u, hu, huv⟩

/-- **Completeness for a trek.** If `t` is outside `Z` and there are directed paths from `t` to
`x` and from `t` to `y` all of whose vertices lie outside `Z` (a trail without colliders that
avoids `Z`), then some distribution over binary variables factorizes according to the acyclic
graph `G` and violates `{x} ⫫ {y} | Z`: the one in which `t` is a fair bit, the vertices
reachable from `t` outside `Z` copy it, and all other vertices are constant. -/
theorem exists_factorizes_not_condIndep_of_trek (hG : G.IsAcyclic) {t x y : V} {Z : Finset V}
    (ht : t ∉ Z) (hx : ReflTransGen (fun a b => G.Adj a b ∧ b ∉ Z) t x)
    (hy : ReflTransGen (fun a b => G.Adj a b ∧ b ∉ Z) t y) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {x} {y} Z := by
  refine (trekRule t Z).exists_factorizes_not_condIndep hG
    (fun n σ hσ _ => by rw [trekRule_sol hG hσ hx, trekRule_sol hG hσ hy])
    ⟨fun _ => true, fun σ hσ => ⟨trekRule_sol hG hσ hx, fun z hz => ?_⟩⟩
  rw [hσ z]
  simp only [trekRule]
  split_ifs with h1 h2
  · exact absurd (h1 ▸ hz) ht
  · exact absurd hz h2.1
  · rfl

/-- **Completeness for a directed path.** If there is a directed path from `x` to `y` all of
whose vertices lie outside `Z`, then some distribution over binary variables factorizes
according to the acyclic graph `G` and violates `{x} ⫫ {y} | Z`. -/
theorem exists_factorizes_not_condIndep_of_reflTransGen (hG : G.IsAcyclic) {x y : V}
    {Z : Finset V} (hx : x ∉ Z) (h : ReflTransGen (fun a b => G.Adj a b ∧ b ∉ Z) x y) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {x} {y} Z :=
  exists_factorizes_not_condIndep_of_trek hG hx ReflTransGen.refl h

/-! ### One collider -/

open Classical in
/-- The rule for a collider `x → c ← y` with `x ≠ y`: `x` and `y` are fair bits, `c` is their
exclusive or, every proper descendant of `c` copies a parent that is a descendant of `c`, and
every other vertex is false. -/
noncomputable def colliderRule {x c y : V} (hxc : G.Adj x c) (hyc : G.Adj y c) : G.BoolRule where
  F v σ e := if v = x then e else if v = y then e else if v = c then xor (σ x) (σ y) else
    if h : ∃ u, ReflTransGen G.Adj c u ∧ G.Adj u v then σ (Classical.choose h) else false
  congr v σ σ' e hσσ' := by
    split_ifs with h1 h2 h3 h4
    · rfl
    · rfl
    · subst h3
      rw [hσσ' x hxc, hσσ' y hyc]
    · exact hσσ' _ (Classical.choose_spec h4).2
    · rfl
  F_false v := by split_ifs <;> rfl

theorem colliderRule_sol {x c y : V} (hxc : G.Adj x c) (hyc : G.Adj y c) {n σ : V → Bool}
    (hG : G.IsAcyclic) (hσ : (colliderRule hxc hyc).Sol n σ) {v : V}
    (hv : ReflTransGen G.Adj c v) : σ v = σ c := by
  have hx : ¬ ReflTransGen G.Adj c x := fun h => hG x (TransGen.head' hxc h)
  have hy : ¬ ReflTransGen G.Adj c y := fun h => hG y (TransGen.head' hyc h)
  induction v using hG.wellFounded_adj.induction with
  | _ v ih =>
    by_cases hvc : v = c
    · rw [hvc]
    rw [hσ v]
    simp only [colliderRule]
    split_ifs with h1 h2 h4
    · exact absurd (h1 ▸ hv) hx
    · exact absurd (h2 ▸ hv) hy
    · exact ih _ (Classical.choose_spec h4).2 (Classical.choose_spec h4).1
    · exfalso
      rcases hv.cases_tail with h | ⟨u, hu, huv⟩
      · exact hvc h
      · exact h4 ⟨u, hu, huv⟩

/-- **Completeness for one collider.** If `x → c ← y` with `x` and `y` outside `Z` and `c` in
`Z` or an ancestor of a vertex of `Z`, then some distribution over binary variables factorizes
according to the acyclic graph `G` and violates `{x} ⫫ {y} | Z`: for `x ≠ y`, the one in which
`x` and `y` are fair bits, `c` is their exclusive or, every proper descendant of `c` copies a
parent descending from `c`, and all other vertices are constant. -/
theorem exists_factorizes_not_condIndep_of_collider (hG : G.IsAcyclic) {x c y : V}
    {Z : Finset V} (hxc : G.Adj x c) (hyc : G.Adj y c) (hx : x ∉ Z) (hy : y ∉ Z)
    (hc : c ∈ G.ancestorsOf ↑Z) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {x} {y} Z := by
  by_cases hxy : x = y
  · subst hxy
    exact exists_factorizes_not_condIndep_of_reflTransGen hG hx ReflTransGen.refl
  have hcx : c ≠ x := fun h => hG.irrefl x (h ▸ hxc)
  have hcy : c ≠ y := fun h => hG.irrefl y (h ▸ hyc)
  have hσc : ∀ {n σ : V → Bool}, (colliderRule hxc hyc).Sol n σ → σ c = xor (σ x) (σ y) := by
    intro n σ hσ
    rw [hσ c]
    simp [colliderRule, hcx, hcy]
  have hσx : ∀ {n σ : V → Bool}, (colliderRule hxc hyc).Sol n σ → σ x = n x := by
    intro n σ hσ
    rw [hσ x]
    simp [colliderRule]
  have hσy : ∀ {n σ : V → Bool}, (colliderRule hxc hyc).Sol n σ → σ y = n y := by
    intro n σ hσ
    rw [hσ y]
    simp [colliderRule, Ne.symm hxy]
  obtain ⟨z, hz, hcz⟩ := hc
  refine (colliderRule hxc hyc).exists_factorizes_not_condIndep hG (fun n σ hσ hZ => ?_)
    ⟨fun _ => true, fun σ hσ => ⟨hσx hσ, fun w hw => ?_⟩⟩
  · have := hZ z hz
    rw [colliderRule_sol hxc hyc hG hσ hcz, hσc hσ] at this
    simpa using this
  · by_cases hwc : ReflTransGen G.Adj c w
    · rw [colliderRule_sol hxc hyc hG hσ hwc, hσc hσ, hσx hσ, hσy hσ]
      rfl
    · rw [hσ w]
      simp only [colliderRule]
      split_ifs with h1 h2 h3 h4
      · exact absurd (h1 ▸ hw) hx
      · exact absurd (h2 ▸ hw) hy
      · exact absurd (h3 ▸ ReflTransGen.refl) hwc
      · exact absurd ((Classical.choose_spec h4).1.tail (Classical.choose_spec h4).2) hwc
      · rfl

/-- **Completeness for one conditioned collider.** If `x → c ← y` with `x` and `y` outside `Z`
and `c ∈ Z`, then some distribution over binary variables factorizes according to the acyclic
graph `G` and violates `{x} ⫫ {y} | Z`. -/
theorem exists_factorizes_not_condIndep_of_collider_mem (hG : G.IsAcyclic) {x c y : V}
    {Z : Finset V} (hxc : G.Adj x c) (hyc : G.Adj y c) (hx : x ∉ Z) (hy : y ∉ Z) (hc : c ∈ Z) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {x} {y} Z :=
  exists_factorizes_not_condIndep_of_collider hG hxc hyc hx hy (subset_ancestorsOf _ hc)

/-! ### The general case -/

section General

variable {Z : Finset V}

/-- The pair of consecutive states `(s, t)` of the list `L` with `t` at the vertex `v`, if
any. -/
def predPair (v : V) : List (V × Bool) → Option ((V × Bool) × (V × Bool))
  | s :: t :: l => if t.1 = v then some (s, t) else predPair v (t :: l)
  | _ => none

/-- The state that follows the state at the vertex `v` in the list `L`, if any. -/
def succOf (v : V) : List (V × Bool) → Option (V × Bool)
  | s :: t :: l => if s.1 = v then some t else succOf v (t :: l)
  | _ => none

/-- The parent of `v` that precedes `v` on the trail `L`, if the trail enters `v` through an
arrowhead. -/
def leftPar (L : List (V × Bool)) (v : V) : Option V :=
  (predPair v L).bind fun q => if q.2.2 then some q.1.1 else none

/-- The parent of `v` that follows `v` on the trail `L`, if the trail leaves `v` along an edge
pointing into `v`. -/
def rightPar (L : List (V × Bool)) (v : V) : Option V :=
  (succOf v L).bind fun t => if t.2 then none else some t.1

omit [Fintype V] in
theorem predPair_spec : ∀ {L : List (V × Bool)} {v : V} {s t : V × Bool},
    predPair v L = some (s, t) → ∃ A B, L = A ++ s :: t :: B ∧ t.1 = v
  | a :: b :: l, v, s, t, h => by
    simp only [predPair] at h
    split_ifs at h with hb
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], l, rfl, hb⟩
    · obtain ⟨A, B, hAB, ht⟩ := predPair_spec h
      exact ⟨a :: A, B, by simp [hAB], ht⟩
  | [], _, _, _, h => by simp [predPair] at h
  | [_], _, _, _, h => by simp [predPair] at h

omit [Fintype V] in
theorem succOf_spec : ∀ {L : List (V × Bool)} {v : V} {t : V × Bool},
    succOf v L = some t → ∃ A s B, L = A ++ s :: t :: B ∧ s.1 = v
  | a :: b :: l, v, t, h => by
    simp only [succOf] at h
    split_ifs at h with ha
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨[], a, l, rfl, ha⟩
    · obtain ⟨A, s, B, hAB, hs⟩ := succOf_spec h
      exact ⟨a :: A, s, B, by simp [hAB], hs⟩
  | [], _, _, h => by simp [succOf] at h
  | [_], _, _, h => by simp [succOf] at h

omit [Fintype V] in
theorem predPair_of_eq {A B : List (V × Bool)} {s t : V × Bool}
    (hnd : ((A ++ s :: t :: B).map Prod.fst).Nodup) :
    predPair t.1 (A ++ s :: t :: B) = some (s, t) := by
  induction A with
  | nil => simp [predPair]
  | cons a A ih =>
    rw [List.cons_append, List.map_cons, List.nodup_cons] at hnd
    cases A with
    | nil =>
      have hst : s.1 ≠ t.1 := fun h => by
        have := hnd.2
        simp only [List.nil_append, List.map_cons, List.nodup_cons, List.mem_cons] at this
        exact this.1 (Or.inl h)
      simp [predPair, hst]
    | cons b A =>
      have hbt : b.1 ≠ t.1 := fun h => by
        have := hnd.2
        rw [List.cons_append, List.map_cons, List.nodup_cons] at this
        exact this.1 (by simp [h])
      rw [List.cons_append, List.cons_append, predPair]
      simp only [hbt, ite_false]
      exact ih hnd.2

omit [Fintype V] in
theorem succOf_of_eq {A B : List (V × Bool)} {s t : V × Bool}
    (hnd : ((A ++ s :: t :: B).map Prod.fst).Nodup) :
    succOf s.1 (A ++ s :: t :: B) = some t := by
  induction A with
  | nil => simp [succOf]
  | cons a A ih =>
    rw [List.cons_append, List.map_cons, List.nodup_cons] at hnd
    have has : a.1 ≠ s.1 := fun h => hnd.1 (by simp [h])
    cases A with
    | nil => simp [succOf, has]
    | cons b A =>
      rw [List.cons_append, List.cons_append, succOf]
      simp only [has, ite_false]
      exact ih hnd.2

omit [Fintype V] in
theorem predPair_head {s : V × Bool} {B : List (V × Bool)}
    (hnd : ((s :: B).map Prod.fst).Nodup) : predPair s.1 (s :: B) = none := by
  cases h : predPair s.1 (s :: B) with
  | none => rfl
  | some q =>
    obtain ⟨p, t⟩ := q
    obtain ⟨A, B', hAB, ht⟩ := predPair_spec h
    rw [List.map_cons, List.nodup_cons] at hnd
    refine absurd ?_ hnd.1
    cases A with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hAB
      rw [hAB.2, ← ht]
      simp
    | cons a A =>
      simp only [List.cons_append, List.cons.injEq] at hAB
      rw [hAB.2, ← ht]
      simp

omit [Fintype V] in
theorem succOf_last {A : List (V × Bool)} {s : V × Bool}
    (hnd : ((A ++ [s]).map Prod.fst).Nodup) : succOf s.1 (A ++ [s]) = none := by
  cases h : succOf s.1 (A ++ [s]) with
  | none => rfl
  | some t =>
    obtain ⟨A', s', B', hAB, hs⟩ := succOf_spec h
    obtain ⟨-, -, h3⟩ := eq_of_append_cons_eq_append_cons hnd hAB hs.symm
    simp at h3

omit [Fintype V] in
theorem leftPar_of_eq {A B : List (V × Bool)} {s t : V × Bool}
    (hnd : ((A ++ s :: t :: B).map Prod.fst).Nodup) :
    leftPar (A ++ s :: t :: B) t.1 = if t.2 then some s.1 else none := by
  simp [leftPar, predPair_of_eq hnd]

omit [Fintype V] in
theorem leftPar_of_false {A S : List (V × Bool)} {s : V × Bool}
    (hnd : ((A ++ s :: S).map Prod.fst).Nodup) (hs : s.2 = false) :
    leftPar (A ++ s :: S) s.1 = none := by
  rcases List.eq_nil_or_concat A with rfl | ⟨A', p, rfl⟩
  · simp [leftPar, predPair_head (by simpa using hnd)]
  · have hnd' : ((A' ++ p :: s :: S).map Prod.fst).Nodup := by simpa using hnd
    have := leftPar_of_eq hnd'
    rw [hs] at this
    simpa using this

omit [Fintype V] in
theorem rightPar_of_eq {A B : List (V × Bool)} {s t : V × Bool}
    (hnd : ((A ++ s :: t :: B).map Prod.fst).Nodup) :
    rightPar (A ++ s :: t :: B) s.1 = if t.2 then none else some t.1 := by
  simp [rightPar, succOf_of_eq hnd]

omit [Fintype V] in
theorem rightPar_last {A : List (V × Bool)} {s : V × Bool}
    (hnd : ((A ++ [s]).map Prod.fst).Nodup) : rightPar (A ++ [s]) s.1 = none := by
  simp [rightPar, succOf_last hnd]

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsDTrail.leftPar_adj {x y v u : V} {L : List (V × Bool)} (hL : G.IsDTrail Z x y L)
    (h : leftPar L v = some u) : G.Adj u v := by
  simp only [leftPar, Option.bind_eq_some_iff] at h
  obtain ⟨⟨p, t⟩, hq, ht⟩ := h
  split_ifs at ht with ht2
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨A, B, hAB, rfl⟩ := predPair_spec hq
  have := isChain_append_cons_cons (hAB ▸ hL.chain)
  obtain ⟨t, b⟩ := t
  dsimp only at ht2
  subst ht2
  exact (bayesBall_adj_true.1 this).1

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsDTrail.rightPar_adj {x y v u : V} {L : List (V × Bool)} (hL : G.IsDTrail Z x y L)
    (h : rightPar L v = some u) : G.Adj u v := by
  simp only [rightPar, Option.bind_eq_some_iff] at h
  obtain ⟨t, hq, ht⟩ := h
  split_ifs at ht with ht2
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨A, s, B, hAB, rfl⟩ := succOf_spec hq
  have := isChain_append_cons_cons (hAB ▸ hL.chain)
  obtain ⟨t, b⟩ := t
  simp only [Bool.not_eq_true] at ht2
  subst ht2
  exact this.1

variable (G Z) in
/-- `G.OnDescent Z L u`: `u` lies on the shortest path from a collider `c` of `L` to `Z`, before
its last vertex: `u = nextZ^[k] c` with `k < distZ c`. -/
def OnDescent (L : List (V × Bool)) (u : V) : Prop :=
  ∃ c k, IsCollider L c ∧ k < G.distZ Z c ∧ u = (G.nextZ Z)^[k] c

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem OnDescent.adj {L : List (V × Bool)} {x y u : V} (hL : G.IsDTrail Z x y L)
    (hu : G.OnDescent Z L u) : G.Adj u (G.nextZ Z u) := by
  obtain ⟨c, k, hc, hk, rfl⟩ := hu
  have := iterate_nextZ_adj (hL.mem_ancestorsOf_of_isCollider hc) hk
  rwa [Function.iterate_succ_apply'] at this

open Classical in
/-- The rule for a simple active trail `L`. A vertex of the trail is the exclusive or of its
trail parents (it copies its unique trail parent if it is a non-collider, and it is the
exclusive or of its two trail parents if it is a collider); a vertex of the trail without trail
parents is a fair bit. A vertex off the trail that follows a vertex `u` on the shortest path
from a collider to `Z` copies `u`. Every other vertex is false. -/
noncomputable def trailRule {x y : V} {L : List (V × Bool)} (hL : G.IsDTrail Z x y L) :
    G.BoolRule where
  F v σ e := if v ∈ L.map Prod.fst then
      (if leftPar L v = none ∧ rightPar L v = none then e else
        xor ((leftPar L v).elim false σ) ((rightPar L v).elim false σ))
    else if h : ∃ u, G.OnDescent Z L u ∧ G.nextZ Z u = v then σ (Classical.choose h) else false
  congr v σ σ' e hσσ' := by
    have hl : (leftPar L v).elim false σ = (leftPar L v).elim false σ' := by
      cases h : leftPar L v with
      | none => rfl
      | some u => exact hσσ' u (hL.leftPar_adj h)
    have hr : (rightPar L v).elim false σ = (rightPar L v).elim false σ' := by
      cases h : rightPar L v with
      | none => rfl
      | some u => exact hσσ' u (hL.rightPar_adj h)
    split_ifs with h1 h2 h3
    · rfl
    · rw [hl, hr]
    · obtain ⟨h4, h5⟩ := Classical.choose_spec h3
      have h6 := h4.adj hL
      rw [h5] at h6
      exact hσσ' _ h6
    · rfl
  F_false v := by
    split_ifs with h1 h2 h3
    · rfl
    · cases leftPar L v <;> cases rightPar L v <;> rfl
    · rfl
    · rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem IsDTrail.eq_of_last {x y : V} {L A : List (V × Bool)} {s : V × Bool}
    (hL : G.IsDTrail Z x y L) (hLe : L = A ++ [s]) : s.1 = y := by
  have := hL.last
  rw [hLe] at this
  simpa using this

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem IsDTrail.notMem_of_nonCollider {x y : V} {L A S : List (V × Bool)} {s : V × Bool}
    (hL : G.IsDTrail Z x y L) (hLe : L = A ++ s :: S)
    (hnc : ∀ t ∈ S.head?, s.2 = true → t.2 = true) : s.1 ∉ Z := by
  cases S with
  | nil => exact (hL.eq_of_last hLe) ▸ hL.last_notMem
  | cons t S =>
    have hst := isChain_append_cons_cons (hLe ▸ hL.chain)
    obtain ⟨v, b⟩ := s
    obtain ⟨w, c⟩ := t
    cases c
    · cases b
      · exact mem_coe.not.1 (bayesBall_adj_false_false.1 hst).2
      · exact absurd (hnc _ rfl rfl) (by simp)
    · exact mem_coe.not.1 (bayesBall_adj_true.1 hst).2

omit [DecidableRel G.Adj] in
theorem trailRule_sol_of_mem {x y v : V} {L : List (V × Bool)} (hL : G.IsDTrail Z x y L)
    {n σ : V → Bool} (hσ : (trailRule hL).Sol n σ) (hv : v ∈ L.map Prod.fst) :
    σ v = if leftPar L v = none ∧ rightPar L v = none then n v else
      xor ((leftPar L v).elim false σ) ((rightPar L v).elim false σ) := by
  rw [hσ v]
  simp only [trailRule, hv, ite_true]

omit [DecidableRel G.Adj] in
/-- Along the shortest path from a collider of a minimal trail to `Z`, every vertex copies the
collider. -/
theorem trailRule_sol_iterate {x y c : V} {L : List (V × Bool)} (hL : G.IsDTrail Z x y L)
    (hmin : ∀ L', G.IsDTrail Z x y L' → G.trailMeasure Z L ≤ G.trailMeasure Z L')
    (hc : IsCollider L c) {n σ : V → Bool} (hσ : (trailRule hL).Sol n σ) :
    ∀ i ≤ G.distZ Z c, σ ((G.nextZ Z)^[i] c) = σ c
  | 0, _ => rfl
  | i + 1, hi => by
    obtain ⟨A, w, B, hcol⟩ := id hc
    have hnot := hL.iterate_nextZ_notMem_of_min hmin hcol (j := i + 1) (by omega) hi
    have hex : ∃ u, G.OnDescent Z L u ∧ G.nextZ Z u = (G.nextZ Z)^[i + 1] c :=
      ⟨_, ⟨c, i, hc, by omega, rfl⟩, (Function.iterate_succ_apply' _ _ _).symm⟩
    rw [hσ ((G.nextZ Z)^[i + 1] c)]
    simp only [trailRule]
    split_ifs
    · obtain ⟨⟨c₂, k₂, hc₂, hk₂, hu⟩, hnext⟩ := Classical.choose_spec hex
      have hcc : c₂ = c := by
        by_contra hne
        refine hL.iterate_nextZ_ne_of_min' hmin hc₂ hc hne (j := k₂ + 1) (j₂ := i + 1)
          (by omega) hi ?_
        rw [Function.iterate_succ_apply', ← hu, hnext]
      subst hcc
      have hki : k₂ = i := by
        have h := hnext
        rw [hu, ← Function.iterate_succ_apply' (G.nextZ Z)] at h
        have := iterate_nextZ_inj (hL.mem_ancestorsOf_of_isCollider hc) (by omega) hi h
        omega
      subst hki
      rw [hu]
      exact trailRule_sol_iterate hL hmin hc hσ k₂ (by omega)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem xor_eq_false_iff_eq {a b : Bool} : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

omit [DecidableRel G.Adj] in
/-- **Agreement given `Z`.** In every solution of the rule of a minimal trail in which all
vertices of `Z` are false, the two endpoints of the trail have the same value: the exclusive
or at each collider is false, so the value is passed along the trail. -/
theorem trailRule_eq_of_zero {x y : V} {L : List (V × Bool)} (hL : G.IsDTrail Z x y L)
    (hmin : ∀ L', G.IsDTrail Z x y L' → G.trailMeasure Z L ≤ G.trailMeasure Z L')
    {n σ : V → Bool} (hσ : (trailRule hL).Sol n σ) (hZ : ∀ z ∈ Z, σ z = false) :
    σ x = σ y := by
  have hcolF : ∀ c, IsCollider L c → σ c = false := by
    intro c hc
    rw [← trailRule_sol_iterate hL hmin hc hσ _ le_rfl]
    exact hZ _ (iterate_nextZ_distZ_mem (hL.mem_ancestorsOf_of_isCollider hc))
  have hnd := hL.nodup
  have tele : ∀ k, ∀ (A : List (V × Bool)) (s : V × Bool) (S : List (V × Bool)),
      L = A ++ s :: S → S.length ≤ k → (∀ t ∈ S.head?, s.2 = true → t.2 = true) →
      σ s.1 = σ y := by
    intro k
    induction k with
    | zero =>
      intro A s S hLe hk _
      rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hk)] at hLe
      rw [hL.eq_of_last hLe]
    | succ k ih =>
      intro A s S hLe hk hnc
      rcases S with _ | ⟨⟨w, b⟩, S'⟩
      · rw [hL.eq_of_last hLe]
      have hmemw : w ∈ L.map Prod.fst := by simp [hLe]
      cases b with
      | true =>
        have hleft : leftPar L w = some s.1 := by
          rw [hLe]
          simpa using leftPar_of_eq (hLe ▸ hnd : ((A ++ s :: (w, true) :: S').map Prod.fst).Nodup)
        rcases S' with _ | ⟨⟨u, ub⟩, S''⟩
        · have e : L = (A ++ [s]) ++ [(w, true)] := by rw [hLe]; simp
          have hright : rightPar L w = none := by
            rw [e]
            exact rightPar_last (s := (w, true)) (e ▸ hnd)
          have hw := trailRule_sol_of_mem hL hσ hmemw
          rw [hleft, hright] at hw
          simp only [reduceCtorEq, false_and, ite_false, Option.elim, Bool.xor_false] at hw
          rw [← hw]
          exact ih (A ++ [s]) (w, true) [] e (Nat.zero_le _) (by simp)
        · have e : L = (A ++ [s]) ++ (w, true) :: (u, ub) :: S'' := by rw [hLe]; simp
          have hright : rightPar L w = if ub then none else some u := by
            rw [e]
            exact rightPar_of_eq (s := (w, true)) (t := (u, ub)) (e ▸ hnd)
          have hw := trailRule_sol_of_mem hL hσ hmemw
          rw [hleft, hright] at hw
          cases ub with
          | true =>
            simp only [reduceCtorEq, false_and, ite_false, ite_true, Option.elim,
              Bool.xor_false] at hw
            rw [← hw]
            exact ih (A ++ [s]) (w, true) ((u, true) :: S'') e
              (by simp at hk ⊢; omega) (by simp)
          | false =>
            simp only [reduceCtorEq, false_and, ite_false, Bool.false_eq_true, Option.elim] at hw
            have hcw : IsCollider L w := ⟨A ++ [s], u, S'', by rw [hLe]; simp⟩
            rw [hcolF w hcw, eq_comm, xor_eq_false_iff_eq] at hw
            rw [hw]
            exact ih (A ++ [s, (w, true)]) (u, false) S'' (by rw [hLe]; simp)
              (by simp at hk ⊢; omega) (by simp)
      | false =>
        obtain ⟨v, sb⟩ := s
        have hsb : sb = false := by
          cases sb
          · rfl
          · exact absurd (hnc _ rfl rfl) (by simp)
        subst hsb
        have hmemv : v ∈ L.map Prod.fst := by simp [hLe]
        have hleft : leftPar L v = none := by
          rw [hLe]
          exact leftPar_of_false (s := (v, false)) (hLe ▸ hnd) rfl
        have hright : rightPar L v = some w := by
          rw [hLe]
          simpa using rightPar_of_eq (hLe ▸ hnd : ((A ++ (v, false) :: (w, false) :: S').map
            Prod.fst).Nodup)
        have hv := trailRule_sol_of_mem hL hσ hmemv
        rw [hleft, hright] at hv
        simp only [reduceCtorEq, and_false, ite_false, Option.elim, Bool.false_xor] at hv
        rw [hv]
        exact ih (A ++ [(v, false)]) (w, false) S' (by rw [hLe]; simp)
          (by simp at hk ⊢; omega) (by simp)
  obtain ⟨S, hS⟩ : ∃ S, L = [] ++ (x, false) :: S := by
    have := hL.head
    rcases L with _ | ⟨a, S⟩
    · simp at this
    · simp only [List.head?_cons, Option.some.injEq] at this
      exact ⟨S, by simp [this]⟩
  exact tele _ [] (x, false) S hS le_rfl (by simp)

omit [DecidableRel G.Adj] in
/-- **The witness for dependence.** With every noise bit true, in the solution of the rule of a
minimal trail the first endpoint is true and every vertex of `Z` is false: non-colliders of
the trail are true, colliders are the exclusive or of two true bits, and the shortest paths
from colliders to `Z` copy the colliders. -/
theorem trailRule_true (hG : G.IsAcyclic) {x y : V} {L : List (V × Bool)}
    (hL : G.IsDTrail Z x y L)
    (hmin : ∀ L', G.IsDTrail Z x y L' → G.trailMeasure Z L ≤ G.trailMeasure Z L')
    {σ : V → Bool} (hσ : (trailRule hL).Sol (fun _ => true) σ) :
    σ x = true ∧ ∀ z ∈ Z, σ z = false := by
  have hnd := hL.nodup
  have hhead : ∀ {A S : List (V × Bool)} {s : V × Bool}, L = A ++ s :: S → s.2 = true →
      A ≠ [] := by
    rintro A S s hLe hs rfl
    have := hL.head
    rw [hLe] at this
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at this
    rw [this] at hs
    exact Bool.noConfusion hs
  have hNC : ∀ v, (∃ (A : List (V × Bool)) (s : V × Bool) (S : List (V × Bool)),
      L = A ++ s :: S ∧ s.1 = v ∧ ∀ t ∈ S.head?, s.2 = true → t.2 = true) → σ v = true := by
    intro v
    induction v using hG.wellFounded_adj.induction with
    | _ v ih =>
      rintro ⟨A, ⟨v', sb⟩, S, hLe, rfl, hnc⟩
      have hmemv : v' ∈ L.map Prod.fst := by simp [hLe]
      have hv := trailRule_sol_of_mem hL hσ hmemv
      cases sb with
      | true =>
        obtain ⟨A', p, rfl⟩ := (List.eq_nil_or_concat A).resolve_left (hhead hLe rfl)
        have e : L = A' ++ p :: (v', true) :: S := by rw [hLe]; simp
        have hleft : leftPar L v' = some p.1 := by
          rw [e]
          simpa using leftPar_of_eq (s := p) (t := (v', true)) (e ▸ hnd)
        have hright : rightPar L v' = none := by
          rcases S with _ | ⟨⟨w, b⟩, S'⟩
          · have e' : L = (A' ++ [p]) ++ [(v', true)] := by rw [hLe]; simp
            rw [e']
            exact rightPar_last (s := (v', true)) (e' ▸ hnd)
          · have hb : b = true := hnc _ rfl rfl
            subst hb
            have e' : L = (A' ++ [p]) ++ (v', true) :: (w, true) :: S' := by rw [hLe]; simp
            rw [e']
            exact rightPar_of_eq (s := (v', true)) (t := (w, true)) (e' ▸ hnd)
        rw [hleft, hright] at hv
        simp only [reduceCtorEq, false_and, ite_false, Option.elim, Bool.xor_false] at hv
        rw [hv]
        have hadj : G.Adj p.1 v' :=
          (bayesBall_adj_true.1 (isChain_append_cons_cons (e ▸ hL.chain))).1
        exact ih p.1 hadj ⟨A', p, (v', true) :: S, e, rfl, by simp⟩
      | false =>
        have hleft : leftPar L v' = none := by
          rw [hLe]
          exact leftPar_of_false (s := (v', false)) (hLe ▸ hnd) rfl
        rcases S with _ | ⟨⟨w, b⟩, S'⟩
        · have hright : rightPar L v' = none := by
            rw [hLe]
            exact rightPar_last (s := (v', false)) (hLe ▸ hnd)
          rw [hleft, hright] at hv
          simpa using hv
        · have hright : rightPar L v' = if b then none else some w := by
            rw [hLe]
            exact rightPar_of_eq (s := (v', false)) (t := (w, b)) (hLe ▸ hnd)
          rw [hleft, hright] at hv
          cases b with
          | true => simpa using hv
          | false =>
            simp only [reduceCtorEq, and_false, ite_false, Bool.false_eq_true, Option.elim,
              Bool.false_xor] at hv
            rw [hv]
            have hadj : G.Adj w v' :=
              (bayesBall_adj_false_false.1 (isChain_append_cons_cons (hLe ▸ hL.chain))).1
            exact ih w hadj ⟨A ++ [(v', false)], (w, false), S', by rw [hLe]; simp, rfl,
              by simp⟩
  have hcolF : ∀ c, IsCollider L c → σ c = false := by
    rintro c ⟨A, w, B, hLe⟩
    obtain ⟨A', p, rfl⟩ := (List.eq_nil_or_concat A).resolve_left (hhead hLe rfl)
    have e : L = A' ++ p :: (c, true) :: (w, false) :: B := by rw [hLe]; simp
    have e' : L = (A' ++ [p]) ++ (c, true) :: (w, false) :: B := by rw [hLe]; simp
    have hmemc : c ∈ L.map Prod.fst := by simp [hLe]
    have hleft : leftPar L c = some p.1 := by
      rw [e]
      simpa using leftPar_of_eq (s := p) (t := (c, true)) (e ▸ hnd)
    have hright : rightPar L c = some w := by
      rw [e']
      exact rightPar_of_eq (s := (c, true)) (t := (w, false)) (e' ▸ hnd)
    have hv := trailRule_sol_of_mem hL hσ hmemc
    rw [hleft, hright] at hv
    simp only [reduceCtorEq, false_and, ite_false, Option.elim] at hv
    rw [hv, hNC p.1 ⟨A', p, (c, true) :: (w, false) :: B, e, rfl, by simp⟩,
      hNC w ⟨A' ++ [p, (c, true)], (w, false), B, by rw [hLe]; simp, rfl, by simp⟩]
    rfl
  obtain ⟨S, hS⟩ : ∃ S, L = [] ++ (x, false) :: S := by
    have := hL.head
    rcases L with _ | ⟨a, S⟩
    · simp at this
    · simp only [List.head?_cons, Option.some.injEq] at this
      exact ⟨S, by simp [this]⟩
  refine ⟨hNC x ⟨[], (x, false), S, hS, rfl, by simp⟩, fun z hz => ?_⟩
  by_cases hzL : z ∈ L.map Prod.fst
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hzL
    obtain ⟨A, S, hLe⟩ := List.append_of_mem hs
    by_cases hnc : ∀ t ∈ S.head?, s.2 = true → t.2 = true
    · exact absurd hz (hL.notMem_of_nonCollider hLe hnc)
    · simp only [not_forall, exists_prop] at hnc
      obtain ⟨t, ht, hs2, ht2⟩ := hnc
      rcases S with _ | ⟨⟨w, tb⟩, S'⟩
      · simp at ht
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ht
      subst ht
      obtain ⟨v, sb⟩ := s
      dsimp only at hs2 ht2 ⊢
      subst hs2
      simp only [Bool.not_eq_true] at ht2
      subst ht2
      exact hcolF v ⟨A, w, S', hLe⟩
  · rw [hσ z]
    simp only [trailRule, hzL, ite_false]
    split_ifs with h
    · obtain ⟨⟨c, k, hc, hk, hu⟩, -⟩ := Classical.choose_spec h
      rw [hu, trailRule_sol_iterate hL hmin hc hσ k hk.le]
      exact hcolF c hc
    · rfl

/-- **Completeness of d-separation** (Pearl 2009, Theorem 1.2.4, converse half, for single
vertices and binary variables). If `x` and `y` are d-connected given `Z` in the acyclic graph
`G`, some distribution over binary variables factorizes according to `G` and violates
`{x} ⫫ {y} | Z`.

The witness is built from an active simple trail from `x` to `y` that minimizes the number of
its states plus, summed over its colliders, the length of a shortest directed path from the
collider to `Z`. On the trail every non-collider copies its trail parent or is a fair bit, and
every collider is the exclusive or of its two trail parents; each collider is copied along a
fixed shortest path to `Z` (the paths follow the function `Digraph.nextZ`); all other vertices
are constant. Minimality is used only to ensure that these shortest paths meet the trail at
their colliders only and are pairwise disjoint: otherwise a shortcut through a path gives a
trail of smaller measure (`Digraph.IsDTrail.surgery_after`, `Digraph.IsDTrail.surgery_before`,
`Digraph.IsDTrail.surgery_merge`). Given all of `Z` false, every collider is false, so the bit
is passed along the trail and the values at `x` and `y` agree. -/
theorem exists_factorizes_not_condIndep_of_dConn (hG : G.IsAcyclic) {x y : V} {Z : Finset V}
    (h : G.DConn {x} {y} ↑Z) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {x} {y} Z := by
  obtain ⟨L, hL, hmin⟩ := exists_isDTrail_min h
  exact (trailRule hL).exists_factorizes_not_condIndep hG
    (fun n σ hσ hZ => trailRule_eq_of_zero hL hmin hσ hZ)
    ⟨fun _ => true, fun σ hσ => trailRule_true hG hL hmin hσ⟩

/-- **Completeness of d-separation for a single edge.** If `u → v` is an edge of an acyclic graph
and neither `u` nor `v` is in `Z`, then some distribution over binary variables factorizes
according to `G` and violates `{u} ⫫ {v} | Z`. -/
theorem exists_factorizes_not_condIndep_of_adj (hG : G.IsAcyclic) {u v : V} (huv : G.Adj u v)
    {Z : Finset V} (hu : u ∉ Z) (hv : v ∉ Z) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ ¬ p.CondIndep {u} {v} Z :=
  exists_factorizes_not_condIndep_of_dConn hG
    (dConn_of_adj huv (mem_coe.not.2 hu) (mem_coe.not.2 hv))

/-- **d-separation is the independence common to all factorizing distributions** (Pearl 2009,
Theorem 1.2.4, both halves, for single vertices). For an acyclic graph, `{x}` and `{y}` are
d-separated by `Z` if and only if `{x} ⫫ {y} | Z` holds in every distribution over binary
variables that factorizes according to `G`. -/
theorem dSep_iff_forall_factorizes_condIndep (hG : G.IsAcyclic) {x y : V} {Z : Finset V} :
    G.DSep {x} {y} ↑Z ↔
      ∀ p : FiniteDist (V → Bool), G.Factorizes p → p.CondIndep {x} {y} Z := by
  refine ⟨fun hsep p hp => hp.condIndep_of_dSep hG (by rwa [coe_singleton, coe_singleton]),
    fun h hc => ?_⟩
  obtain ⟨p, hp, hn⟩ := exists_factorizes_not_condIndep_of_dConn hG hc
  exact hn (h p hp)

/-- The version of `Digraph.dSep_iff_forall_factorizes_condIndep` for arbitrary finsets: for an
acyclic graph, `X` and `Y` are d-separated by `Z` if and only if `X ⫫ Y | Z` holds in every
distribution over binary variables that factorizes according to `G`. -/
theorem dSep_iff_forall_factorizes_condIndep' (hG : G.IsAcyclic) {X Y Z : Finset V} :
    G.DSep ↑X ↑Y ↑Z ↔
      ∀ p : FiniteDist (V → Bool), G.Factorizes p → p.CondIndep X Y Z := by
  refine ⟨fun hsep p hp => hp.condIndep_of_dSep hG hsep, fun h hc => ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := dConn_iff_exists_singleton.1 hc
  obtain ⟨p, hp, hn⟩ := exists_factorizes_not_condIndep_of_dConn hG hxy
  exact hn (((h p hp).mono_left (singleton_subset_iff.2 (mem_coe.1 hx))).mono_right
    (singleton_subset_iff.2 (mem_coe.1 hy)))

end General

end Digraph
