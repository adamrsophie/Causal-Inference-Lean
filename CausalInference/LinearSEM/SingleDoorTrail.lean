/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.SingleDoorGeneric

/-!
# The generic converse of the single-door criterion along an arbitrary open path

Let `x → y` be an edge of an acyclic graph `G` and suppose that `Z` does not d-separate `x` from
`y` in the graph `G'` with `x → y` deleted. This file builds, from an open trail of any length,
a linear SEM on `G'` (hence on `G`) with uncorrelated errors at which the coefficient of `x` in
the regression of `y` on `x` and `Z` is `1` while the path coefficient of `x → y` is `0`, and
deduces the measure-zero form of the converse of the single-door criterion on every graph. A
second witness treats a descendant of `y` in `Z`.

## The witness

The trail is a simple active trail of minimal measure (`Digraph.exists_isDTrail_min`), as in the
completeness proof of d-separation (`Digraph.exists_factorizes_not_condIndep_of_dConn`), with
exclusive or replaced by subtraction (`trailB`, `trailω`):

* a non-collider of the trail copies its unique trail parent, with coefficient `1`; a vertex of
  the trail without trail parents is a unit-variance error;
* a collider is the difference of its two trail parents (coefficients `1` and `-1`), and it is
  copied along a fixed shortest directed path to `Z`;
* every other vertex is its own unit-variance error, and all other coefficients are zero.

All error variances are zero or one, so the covariance is a Gram matrix and both its
invertibility and the regression can be read off from the solutions for single noise vectors
(`isUnit_subCov_of_noiseVal`, `noiseVal_regCoeff`). If all of `Z` vanishes, every collider
vanishes and `x` and `y` agree (`TrailSol.eq_of_zero`); so the value of `y` is a combination of
the values in `insert x Z`. The noise vector equal to one on the trail gives `x` the value `1`
and all of `Z` the value `0`, so the coefficient of `x` is `1`. The indicators of the suffixes
of the trail after each collider, and the unit vectors of the remaining vertices of `Z`, show
that the variables in `insert x Z` are linearly independent (`TrailSol.values`,
`TrailSol.collider_value`).

## Main results

* `SingleDoorGeneric.trailModel_regCoeff`: the witness.
* `SingleDoorGeneric.volume_exceptional_eq_zero_of_not_dSep`: if `Z` does not d-separate `x`
  from `y` in `G'`, the parameter vectors with positive error variances at which the regression
  coefficient equals the path coefficient form a Lebesgue null set.
* `SingleDoorGeneric.exists_model_ne_of_not_dSep`: the existence form, a model on `G` with
  uncorrelated errors of positive variance at which the two coefficients differ.
* `SingleDoorGeneric.volume_exceptional_eq_zero_of_descendant`: the same conclusion when `Z`
  contains a descendant of `y`, with the witness `descModel_regCoeff` (coefficient `1` on
  `x → y` and on a shortest directed path from `y` to `Z`, zero error variance on that path
  after `y`, so that `y` equals the end of the path and its regression coefficient on `x` is
  `0`).
* `SingleDoorGeneric.volume_exceptional_eq_zero_of_not_singleDoor`: the converse in full: if the
  single-door condition fails, the exceptional set is null.
* `SingleDoorGeneric.forall_regCoeff_eq_iff_dSep`,
  `SingleDoorGeneric.forall_regCoeff_eq_iff_singleDoor`: with `LinearSEM.single_door`, the
  equality holds at every parameter vector with positive error variances if and only if the
  single-door condition holds.

Source: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1, Theorem 5.3.1.
-/

@[expose] public section

namespace CausalInference

namespace LinearSEM

open Matrix Finset Relation MeasureTheory Digraph

namespace SingleDoorGeneric

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Models with zero-one error variances -/

section ZeroOne

variable (M : LinearSEM V) (ω : V → ℝ)

/-- The values of the variables of `M` when the error of each vertex `u` is `ω u * n u`. -/
noncomputable def noiseVal (n : V → ℝ) : V → ℝ := M.T *ᵥ fun u => ω u * n u

variable {M ω}

theorem noiseVal_eq_sum (n : V → ℝ) (s : V) :
    noiseVal M ω n s = ∑ u, (M.T s u * ω u) * n u := by
  simp only [noiseVal, mulVec, dotProduct]
  exact Finset.sum_congr rfl fun u _ => by ring

theorem noiseVal_sol (n : V → ℝ) :
    noiseVal M ω n = M.B *ᵥ noiseVal M ω n + fun u => ω u * n u :=
  (M.solution_iff _ _).2 rfl

/-- The values `noiseVal M ω n` are the only solution of the model equations with noise
`ω u * n u`. -/
theorem eq_noiseVal {n τ : V → ℝ} (h : τ = M.B *ᵥ τ + fun u => ω u * n u) :
    τ = noiseVal M ω n :=
  (M.solution_iff τ _).1 h

/-- With zero-one error variances, the implied covariance is the Gram matrix of the rows
`T s u * ω u`. -/
theorem cov_eq_gram (hΩ : M.Ω = diagonal ω) (hω : ∀ v, ω v * ω v = ω v) (a b : V) :
    M.cov a b = ∑ u, (M.T a u * ω u) * (M.T b u * ω u) := by
  have hd : M.Ω.IsDiag := by
    rw [hΩ]
    exact isDiag_diagonal _
  rw [cov_apply_of_isDiag M hd]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hΩ, diagonal_apply_eq]
  calc M.T a u * ω u * M.T b u = M.T a u * (ω u * ω u) * M.T b u := by rw [hω]
    _ = _ := by ring

/-- The covariance block on `S` is invertible as soon as no nontrivial combination of the values
of the variables in `S` vanishes for every noise vector. -/
theorem isUnit_subCov_of_noiseVal (hΩ : M.Ω = diagonal ω) (hω : ∀ v, ω v * ω v = ω v)
    {S : Finset V}
    (hind : ∀ a : V → ℝ, (∀ n, ∑ s ∈ S, a s * noiseVal M ω n s = 0) → ∀ s ∈ S, a s = 0) :
    IsUnit (subCov M.cov S) := by
  refine isUnit_subCov_of_gram (fun s u => M.T s u * ω u) (cov_eq_gram hΩ hω) fun a ha => ?_
  refine hind a fun n => ?_
  simp only [noiseVal_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun u _ => ?_
  have h : ∑ s ∈ S, a s * (M.T s u * ω u) = 0 := ha u
  calc ∑ s ∈ S, a s * (M.T s u * ω u * n u) = (∑ s ∈ S, a s * (M.T s u * ω u)) * n u := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ = 0 := by rw [h, zero_mul]

/-- If every noise vector that makes all variables of `S` vanish also makes `y` vanish, then for
every noise vector the value of `y` is the combination of the values of the variables of `S`
with the regression coefficients of `y` on `S`. -/
theorem noiseVal_regCoeff (hΩ : M.Ω = diagonal ω) (hω : ∀ v, ω v * ω v = ω v) {S : Finset V}
    {y : V} (hu : IsUnit (subCov M.cov S))
    (hrel : ∀ n, (∀ s ∈ S, noiseVal M ω n s = 0) → noiseVal M ω n y = 0) (n : V → ℝ) :
    noiseVal M ω n y = ∑ t, regCoeff M.cov S y t * noiseVal M ω n t := by
  have hg : ∀ u, M.T y u * ω u = ∑ t, regCoeff M.cov S y t * (M.T t u * ω u) :=
    gram_regCoeff (fun s u => M.T s u * ω u) (cov_eq_gram hΩ hω) hu fun n hn => by
      have h := hrel n fun s hs => by
        rw [noiseVal_eq_sum]
        exact hn s hs
      rwa [noiseVal_eq_sum] at h
  simp only [noiseVal_eq_sum]
  calc ∑ u, M.T y u * ω u * n u
      = ∑ u, (∑ t, regCoeff M.cov S y t * (M.T t u * ω u)) * n u :=
        Finset.sum_congr rfl fun u _ => by rw [hg u]
    _ = ∑ t, regCoeff M.cov S y t * ∑ u, M.T t u * ω u * n u := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring

end ZeroOne

/-! ### The model of a minimal open trail -/

section Trail

variable {H : Digraph V} {Z : Finset V} {x y : V} {L : List (V × Bool)}

variable (H Z L) in
open Classical in
/-- The coefficient matrix of the model of the trail `L`. A non-collider of the trail copies its
unique trail parent, a collider is the difference of its two trail parents, a vertex on the
shortest path from a collider to `Z` copies its predecessor on that path, and every other
coefficient is zero. -/
noncomputable def trailB : Matrix V V ℝ :=
  fun v u => if v ∈ L.map Prod.fst then
      (if leftPar L v = some u then 1 else 0) +
        (if rightPar L v = some u then (if leftPar L v = none then 1 else -1) else 0)
    else if h : ∃ u', H.OnDescent Z L u' ∧ H.nextZ Z u' = v then
      (if u = Classical.choose h then 1 else 0)
    else 0

variable (H Z L) in
open Classical in
/-- The error variances of the model of the trail `L`: one at the vertices of the trail without
trail parents and at the vertices off the trail and off the paths to `Z`, zero elsewhere. -/
noncomputable def trailω : V → ℝ :=
  fun v => if v ∈ L.map Prod.fst then
      (if leftPar L v = none ∧ rightPar L v = none then 1 else 0)
    else if ∃ u', H.OnDescent Z L u' ∧ H.nextZ Z u' = v then 0 else 1

theorem trailω_mul (v : V) : trailω H Z L v * trailω H Z L v = trailω H Z L v := by
  simp only [trailω]
  split_ifs <;> norm_num

theorem trailω_nonneg (v : V) : 0 ≤ trailω H Z L v := by
  simp only [trailω]
  split_ifs <;> norm_num

theorem trailB_support (hL : H.IsDTrail Z x y L) (v u : V) (h : trailB H Z L v u ≠ 0) :
    H.Adj u v := by
  classical
  by_cases hv : v ∈ L.map Prod.fst
  · simp only [trailB, ite_eq_left hv] at h
    by_cases hl : leftPar L v = some u
    · exact hL.leftPar_adj hl
    by_cases hr : rightPar L v = some u
    · exact hL.rightPar_adj hr
    simp [hl, hr] at h
  · simp only [trailB, ite_eq_right hv] at h
    by_cases hd : ∃ u', H.OnDescent Z L u' ∧ H.nextZ Z u' = v
    · rw [dite_eq_left_of_eq_true (eq_true hd)] at h
      by_cases hu : u = Classical.choose hd
      · obtain ⟨h1, h2⟩ := Classical.choose_spec hd
        have := h1.adj hL
        rwa [h2, ← hu] at this
      · simp [hu] at h
    · rw [dite_eq_right_of_eq_false (eq_false hd)] at h
      exact absurd rfl h

/-- The linear SEM of the trail `L` on the acyclic graph `H`. -/
noncomputable def trailModel (hH : H.IsAcyclic) (hL : H.IsDTrail Z x y L) : LinearSEM V where
  G := H
  acyclic := hH
  B := trailB H Z L
  B_support := trailB_support hL
  Ω := diagonal (trailω H Z L)
  Ω_posSemidef := PosSemidef.diagonal trailω_nonneg

variable (H Z L) in
/-- `TrailSol H Z L n τ`: `τ` solves the equations of the model of the trail `L` with noise
vector `n`. -/
def TrailSol (n τ : V → ℝ) : Prop :=
  τ = trailB H Z L *ᵥ τ + fun u => trailω H Z L u * n u

theorem trailSol_noiseVal (hH : H.IsAcyclic) (hL : H.IsDTrail Z x y L) (n : V → ℝ) :
    TrailSol H Z L n (noiseVal (trailModel hH hL) (trailω H Z L) n) :=
  noiseVal_sol (M := trailModel hH hL) n

theorem sum_ite_some_mul (o : Option V) (τ : V → ℝ) :
    ∑ u, (if o = some u then (1 : ℝ) else 0) * τ u = o.elim 0 τ := by
  cases o with
  | none => simp
  | some w => simp

variable {n τ : V → ℝ}

theorem TrailSol.of_mem (hτ : TrailSol H Z L n τ) {v : V} (hv : v ∈ L.map Prod.fst) :
    τ v = (if leftPar L v = none ∧ rightPar L v = none then n v else 0) +
      (leftPar L v).elim 0 τ +
        (if leftPar L v = none then 1 else -1) * (rightPar L v).elim 0 τ := by
  have h := congrFun hτ v
  have hrow : (trailB H Z L *ᵥ τ) v = ∑ u, ((if leftPar L v = some u then 1 else 0) * τ u +
      (if leftPar L v = none then 1 else -1) *
        ((if rightPar L v = some u then 1 else 0) * τ u)) := by
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [trailB, ite_eq_left hv]
    split_ifs <;> ring
  rw [Pi.add_apply, hrow, Finset.sum_add_distrib, ← Finset.mul_sum, sum_ite_some_mul,
    sum_ite_some_mul] at h
  rw [h]
  simp only [trailω, ite_eq_left hv]
  split_ifs <;> ring

theorem TrailSol.of_descent (hτ : TrailSol H Z L n τ) {v : V} (hv : v ∉ L.map Prod.fst)
    (hd : ∃ u', H.OnDescent Z L u' ∧ H.nextZ Z u' = v) : τ v = τ (Classical.choose hd) := by
  classical
  have h := congrFun hτ v
  have hrow : (trailB H Z L *ᵥ τ) v = τ (Classical.choose hd) := by
    simp only [mulVec, dotProduct, trailB, ite_eq_right hv, dite_eq_left_of_eq_true (eq_true hd),
      ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Pi.add_apply, hrow] at h
  rw [h]
  simp only [trailω, ite_eq_right hv, ite_eq_left hd, zero_mul, add_zero]

theorem TrailSol.of_off (hτ : TrailSol H Z L n τ) {v : V} (hv : v ∉ L.map Prod.fst)
    (hd : ¬ ∃ u', H.OnDescent Z L u' ∧ H.nextZ Z u' = v) : τ v = n v := by
  classical
  have h := congrFun hτ v
  have hrow : (trailB H Z L *ᵥ τ) v = 0 := by
    simp only [mulVec, dotProduct, trailB, ite_eq_right hv, dite_eq_right_of_eq_false (eq_false hd),
      zero_mul,
      Finset.sum_const_zero]
  rw [Pi.add_apply, hrow] at h
  rw [h]
  simp only [trailω, ite_eq_right hv, ite_eq_right hd, one_mul, zero_add]

omit [Fintype V] [DecidableEq V] in
theorem _root_.Digraph.IsDTrail.ne_nil_of_true (hL : H.IsDTrail Z x y L) {A S : List (V × Bool)}
    {s : V × Bool} (hLe : L = A ++ s :: S) (hs : s.2 = true) : A ≠ [] := by
  rintro rfl
  have := hL.head
  rw [hLe] at this
  simp only [List.nil_append, List.head?_cons, Option.some.injEq] at this
  rw [this] at hs
  exact Bool.noConfusion hs

/-- A non-collider of the trail entered through an arrowhead copies its predecessor. -/
theorem TrailSol.true_nc (hL : H.IsDTrail Z x y L) (hτ : TrailSol H Z L n τ)
    {A S : List (V × Bool)} {s : V × Bool} {w : V} (hLe : L = A ++ s :: (w, true) :: S)
    (hS : ∀ t ∈ S.head?, t.2 = true) : τ w = τ s.1 := by
  have hnd := hL.nodup
  have hleft : leftPar L w = some s.1 := by
    rw [hLe]
    simpa using leftPar_of_eq (hLe ▸ hnd : ((A ++ s :: (w, true) :: S).map Prod.fst).Nodup)
  have hright : rightPar L w = none := by
    rcases S with _ | ⟨⟨u, ub⟩, S'⟩
    · have e : L = (A ++ [s]) ++ [(w, true)] := by rw [hLe]; simp
      rw [e]
      exact rightPar_last (s := (w, true)) (e ▸ hnd)
    · have hub : ub = true := hS _ rfl
      subst hub
      have e : L = (A ++ [s]) ++ (w, true) :: (u, true) :: S' := by rw [hLe]; simp
      have h := rightPar_of_eq (s := (w, true)) (t := (u, true)) (e ▸ hnd)
      rw [← e] at h
      simpa using h
  have hmem : w ∈ L.map Prod.fst := by simp [hLe]
  rw [hτ.of_mem hmem, hleft, hright]
  simp

/-- A collider of the trail is the difference of its two trail parents. -/
theorem TrailSol.collider (hL : H.IsDTrail Z x y L) (hτ : TrailSol H Z L n τ)
    {A S : List (V × Bool)} {s : V × Bool} {w u : V}
    (hLe : L = A ++ s :: (w, true) :: (u, false) :: S) : τ w = τ s.1 - τ u := by
  have hnd := hL.nodup
  have hleft : leftPar L w = some s.1 := by
    rw [hLe]
    simpa using leftPar_of_eq
      (hLe ▸ hnd : ((A ++ s :: (w, true) :: (u, false) :: S).map Prod.fst).Nodup)
  have hright : rightPar L w = some u := by
    have e : L = (A ++ [s]) ++ (w, true) :: (u, false) :: S := by rw [hLe]; simp
    have h := rightPar_of_eq (s := (w, true)) (t := (u, false)) (e ▸ hnd)
    rw [← e] at h
    simpa using h
  have hmem : w ∈ L.map Prod.fst := by simp [hLe]
  rw [hτ.of_mem hmem, hleft, hright]
  simp only [reduceCtorEq, false_and, ite_false, Option.elim]
  ring

/-- A vertex of the trail followed by a parent copies that parent. -/
theorem TrailSol.false_false (hL : H.IsDTrail Z x y L) (hτ : TrailSol H Z L n τ)
    {A S : List (V × Bool)} {v w : V} (hLe : L = A ++ (v, false) :: (w, false) :: S) :
    τ v = τ w := by
  have hnd := hL.nodup
  have hleft : leftPar L v = none := by
    rw [hLe]
    exact leftPar_of_false (s := (v, false)) (hLe ▸ hnd) rfl
  have hright : rightPar L v = some w := by
    rw [hLe]
    simpa using rightPar_of_eq
      (hLe ▸ hnd : ((A ++ (v, false) :: (w, false) :: S).map Prod.fst).Nodup)
  have hmem : v ∈ L.map Prod.fst := by simp [hLe]
  rw [hτ.of_mem hmem, hleft, hright]
  simp

/-- A vertex of the trail without trail parents takes its noise value. -/
theorem TrailSol.top (hL : H.IsDTrail Z x y L) (hτ : TrailSol H Z L n τ)
    {A S : List (V × Bool)} {v : V} (hLe : L = A ++ (v, false) :: S)
    (hS : ∀ t ∈ S.head?, t.2 = true) : τ v = n v := by
  have hnd := hL.nodup
  have hleft : leftPar L v = none := by
    rw [hLe]
    exact leftPar_of_false (s := (v, false)) (hLe ▸ hnd) rfl
  have hright : rightPar L v = none := by
    rcases S with _ | ⟨⟨w, b⟩, S'⟩
    · rw [hLe]
      exact rightPar_last (s := (v, false)) (hLe ▸ hnd)
    · have hb : b = true := hS _ rfl
      subst hb
      rw [hLe]
      simpa using rightPar_of_eq (s := (v, false)) (t := (w, true)) (hLe ▸ hnd)
  have hmem : v ∈ L.map Prod.fst := by simp [hLe]
  rw [hτ.of_mem hmem, hleft, hright]
  simp

/-- Along the shortest path from a collider of a minimal trail to `Z`, every vertex copies the
collider. -/
theorem TrailSol.iterate (hL : H.IsDTrail Z x y L)
    (hmin : ∀ L', H.IsDTrail Z x y L' → H.trailMeasure Z L ≤ H.trailMeasure Z L')
    {c : V} (hc : IsCollider L c) (hτ : TrailSol H Z L n τ) :
    ∀ i ≤ H.distZ Z c, τ ((H.nextZ Z)^[i] c) = τ c
  | 0, _ => rfl
  | i + 1, hi => by
    obtain ⟨A, w, B, hcol⟩ := id hc
    have hnot := hL.iterate_nextZ_notMem_of_min hmin hcol (j := i + 1) (by omega) hi
    have hex : ∃ u, H.OnDescent Z L u ∧ H.nextZ Z u = (H.nextZ Z)^[i + 1] c :=
      ⟨_, ⟨c, i, hc, by omega, rfl⟩, (Function.iterate_succ_apply' _ _ _).symm⟩
    rw [hτ.of_descent hnot hex]
    obtain ⟨⟨c₂, k₂, hc₂, hk₂, hu⟩, hnext⟩ := Classical.choose_spec hex
    have hcc : c₂ = c := by
      by_contra hne
      refine hL.iterate_nextZ_ne_of_min' hmin hc₂ hc hne (j := k₂ + 1) (j₂ := i + 1)
        (by omega) hi ?_
      rw [Function.iterate_succ_apply', ← hu, hnext]
    subst hcc
    have hki : k₂ = i := by
      have h := hnext
      rw [hu, ← Function.iterate_succ_apply' (H.nextZ Z)] at h
      have := iterate_nextZ_inj (hL.mem_ancestorsOf_of_isCollider hc) (by omega) hi h
      omega
    subst hki
    rw [hu]
    exact TrailSol.iterate hL hmin hc hτ k₂ (by omega)

/-- **Agreement given `Z`.** In every solution of the model of a minimal trail in which all
vertices of `Z` vanish, the two endpoints of the trail have the same value: each collider
vanishes, so its two trail parents agree, and the value is passed along the trail. -/
theorem TrailSol.eq_of_zero (hL : H.IsDTrail Z x y L)
    (hmin : ∀ L', H.IsDTrail Z x y L' → H.trailMeasure Z L ≤ H.trailMeasure Z L')
    (hτ : TrailSol H Z L n τ) (hZ : ∀ z ∈ Z, τ z = 0) : τ x = τ y := by
  have hcolF : ∀ c, IsCollider L c → τ c = 0 := by
    intro c hc
    rw [← hτ.iterate hL hmin hc _ le_rfl]
    exact hZ _ (iterate_nextZ_distZ_mem (hL.mem_ancestorsOf_of_isCollider hc))
  have tele : ∀ k, ∀ (A : List (V × Bool)) (s : V × Bool) (S : List (V × Bool)),
      L = A ++ s :: S → S.length ≤ k → (∀ t ∈ S.head?, s.2 = true → t.2 = true) →
      τ s.1 = τ y := by
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
      cases b with
      | true =>
        rcases S' with _ | ⟨⟨u, ub⟩, S''⟩
        · rw [← hτ.true_nc hL hLe (by simp)]
          exact ih (A ++ [s]) (w, true) [] (by rw [hLe]; simp) (Nat.zero_le _) (by simp)
        · cases ub with
          | true =>
            rw [← hτ.true_nc hL hLe (by simp)]
            exact ih (A ++ [s]) (w, true) ((u, true) :: S'') (by rw [hLe]; simp)
              (by simp at hk ⊢; omega) (by simp)
          | false =>
            have hw := hτ.collider hL hLe
            have hcw : IsCollider L w := ⟨A ++ [s], u, S'', by rw [hLe]; simp⟩
            rw [hcolF w hcw] at hw
            rw [show τ s.1 = τ u by linarith]
            exact ih (A ++ [s, (w, true)]) (u, false) S'' (by rw [hLe]; simp)
              (by simp at hk ⊢; omega) (by simp)
      | false =>
        obtain ⟨v, sb⟩ := s
        have hsb : sb = false := by
          cases sb
          · rfl
          · exact absurd (hnc _ rfl rfl) (by simp)
        subst hsb
        rw [hτ.false_false hL hLe]
        exact ih (A ++ [(v, false)]) (w, false) S' (by rw [hLe]; simp)
          (by simp at hk ⊢; omega) (by simp)
  obtain ⟨S, hS⟩ : ∃ S, L = [] ++ (x, false) :: S := by
    have := hL.head
    rcases L with _ | ⟨a, S⟩
    · simp at this
    · simp only [List.head?_cons, Option.some.injEq] at this
      exact ⟨S, by simp [this]⟩
  exact tele _ [] (x, false) S hS le_rfl (by simp)

/-- **Values on the trail.** Suppose the noise vector `n` takes the same value at the two
vertices of every pair of consecutive states of the trail neither of which is a collider. Then
in every solution of the model of the trail each non-collider of the trail takes its noise
value. -/
theorem TrailSol.values (hH : H.IsAcyclic) (hL : H.IsDTrail Z x y L) (hτ : TrailSol H Z L n τ)
    (hn : ∀ (A : List (V × Bool)) (s t : V × Bool) (B : List (V × Bool)),
      L = A ++ s :: t :: B → (s.2 = false ∨ t.2 = true) →
        (t.2 = false ∨ ∀ r ∈ B.head?, r.2 = true) → n s.1 = n t.1) :
    ∀ v, (∃ (A : List (V × Bool)) (s : V × Bool) (S : List (V × Bool)),
      L = A ++ s :: S ∧ s.1 = v ∧ ∀ t ∈ S.head?, s.2 = true → t.2 = true) → τ v = n v := by
  intro v
  induction v using hH.wellFounded_adj.induction with
  | _ v ih =>
    rintro ⟨A, ⟨v', sb⟩, S, hLe, rfl, hnc⟩
    cases sb with
    | true =>
      obtain ⟨A', p, rfl⟩ := (List.eq_nil_or_concat A).resolve_left (hL.ne_nil_of_true hLe rfl)
      have e : L = A' ++ p :: (v', true) :: S := by rw [hLe]; simp
      have hS : ∀ t ∈ S.head?, t.2 = true := fun t ht => hnc t ht rfl
      rw [hτ.true_nc hL e hS]
      have hadj : H.Adj p.1 v' :=
        (bayesBall_adj_true.1 (isChain_append_cons_cons (e ▸ hL.chain))).1
      rw [ih p.1 hadj ⟨A', p, (v', true) :: S, e, rfl, by simp⟩]
      exact hn A' p (v', true) S e (Or.inr rfl) (Or.inr hS)
    | false =>
      rcases S with _ | ⟨⟨w, b⟩, S'⟩
      · exact hτ.top hL hLe (by simp)
      · cases b with
        | true => exact hτ.top hL hLe (by simp)
        | false =>
          rw [hτ.false_false hL hLe]
          have hadj : H.Adj w v' :=
            (bayesBall_adj_false_false.1 (isChain_append_cons_cons (hLe ▸ hL.chain))).1
          rw [ih w hadj ⟨A ++ [(v', false)], (w, false), S', by rw [hLe]; simp, rfl,
            by simp⟩]
          exact (hn A (v', false) (w, false) S' hLe (Or.inl rfl) (Or.inl rfl)).symm

/-- Under the hypothesis of `TrailSol.values`, a collider of the trail takes the difference of
the noise values of its two neighbors on the trail. -/
theorem TrailSol.collider_value (hH : H.IsAcyclic) (hL : H.IsDTrail Z x y L)
    (hτ : TrailSol H Z L n τ)
    (hn : ∀ (A : List (V × Bool)) (s t : V × Bool) (B : List (V × Bool)),
      L = A ++ s :: t :: B → (s.2 = false ∨ t.2 = true) →
        (t.2 = false ∨ ∀ r ∈ B.head?, r.2 = true) → n s.1 = n t.1)
    {A B : List (V × Bool)} {p : V × Bool} {c w : V}
    (hLe : L = A ++ p :: (c, true) :: (w, false) :: B) : τ c = n p.1 - n w := by
  rw [hτ.collider hL hLe, hτ.values hH hL hn p.1 ⟨A, p, (c, true) :: (w, false) :: B, hLe, rfl,
    by simp⟩, hτ.values hH hL hn w ⟨A ++ [p, (c, true)], (w, false), B, by rw [hLe]; simp, rfl,
    by simp⟩]

/-- Every vertex of `Z` is either the end of the shortest path from a collider of a minimal
trail to `Z` (and then copies the collider), or lies off the trail and off these paths (and
then takes its noise value). -/
theorem mem_Z_cases (hL : H.IsDTrail Z x y L)
    (hmin : ∀ L', H.IsDTrail Z x y L' → H.trailMeasure Z L ≤ H.trailMeasure Z L')
    {z : V} (hz : z ∈ Z) :
    (∃ c, IsCollider L c ∧ z = (H.nextZ Z)^[H.distZ Z c] c ∧
      ∀ n τ, TrailSol H Z L n τ → τ z = τ c) ∨
    (z ∉ L.map Prod.fst ∧ ∀ n τ, TrailSol H Z L n τ → τ z = n z) := by
  by_cases hzL : z ∈ L.map Prod.fst
  · left
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hzL
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
      have hc : IsCollider L v := ⟨A, w, S', hLe⟩
      have h0 : H.distZ Z v = 0 :=
        (distZ_eq_zero_iff (hL.mem_ancestorsOf_of_isCollider hc)).2 hz
      exact ⟨v, hc, by rw [h0]; rfl, fun _ _ _ => rfl⟩
  · by_cases hd : ∃ u', H.OnDescent Z L u' ∧ H.nextZ Z u' = z
    · left
      obtain ⟨u, ⟨c, k, hc, hk, rfl⟩, hnext⟩ := id hd
      have hanc := hL.mem_ancestorsOf_of_isCollider hc
      have hzk : z = (H.nextZ Z)^[k + 1] c := by
        rw [Function.iterate_succ_apply', hnext]
      have hk1 : k + 1 = H.distZ Z c := by
        by_contra hne
        exact iterate_nextZ_notMem hanc (j := k + 1) (by omega) (hzk ▸ hz)
      refine ⟨c, hc, by rw [hzk, hk1], fun n τ hτ => ?_⟩
      rw [hzk]
      exact hτ.iterate hL hmin hc (k + 1) (by omega)
    · exact Or.inr ⟨hzL, fun n τ hτ => hτ.of_off hzL hd⟩

/-! ### The dual noise vectors -/

omit [Fintype V] [DecidableEq V] in
/-- A coefficient of a vanishing linear combination is zero when the combined values vanish off
one index and not at it. -/
theorem coeff_eq_zero_of_single {S : Finset V} {a g : V → ℝ} {s₀ : V} (hs₀ : s₀ ∈ S)
    (hg₀ : g s₀ ≠ 0) (hg : ∀ s ∈ S, s ≠ s₀ → g s = 0) (h : ∑ s ∈ S, a s * g s = 0) :
    a s₀ = 0 := by
  rw [Finset.sum_eq_single_of_mem s₀ hs₀ fun s hs hne => by rw [hg s hs hne, mul_zero]] at h
  exact (mul_eq_zero.1 h).resolve_right hg₀

variable (L) in
open Classical in
/-- The indicator of the states of `L` after the first `k + 1` states. -/
noncomputable def suffixInd (k : ℕ) : V → ℝ :=
  fun v => if ∃ (A : List (V × Bool)) (s : V × Bool) (B : List (V × Bool)),
    L = A ++ s :: B ∧ s.1 = v ∧ k < A.length then 1 else 0

omit [Fintype V] [DecidableEq V] in
theorem suffixInd_of_eq (hnd : (L.map Prod.fst).Nodup) {k : ℕ} {A B : List (V × Bool)}
    {s : V × Bool} (hLe : L = A ++ s :: B) :
    suffixInd L k s.1 = if k < A.length then 1 else 0 := by
  by_cases hk : k < A.length
  · rw [ite_eq_left hk]
    unfold suffixInd
    rw [ite_eq_left ⟨A, s, B, hLe, rfl, hk⟩]
  · rw [ite_eq_right hk]
    unfold suffixInd
    rw [ite_eq_right]
    rintro ⟨A', s', B', h2, h3, h4⟩
    obtain ⟨rfl, -, -⟩ := eq_of_append_cons_eq_append_cons (hLe ▸ hnd) (hLe.symm.trans h2) h3.symm
    exact hk h4

omit [Fintype V] [DecidableEq V] in
theorem suffixInd_of_notMem {k : ℕ} {v : V} (hv : v ∉ L.map Prod.fst) : suffixInd L k v = 0 := by
  unfold suffixInd
  rw [ite_eq_right]
  rintro ⟨A, s, B, h, rfl, -⟩
  exact hv (by simp [h])

/-- **The witness of a minimal trail.** In the model of a minimal open trail from `x` to `y`
given `Z`, the covariance block on `insert x Z` is invertible and the coefficient of `x` in the
regression of `y` on `insert x Z` is `1`. -/
theorem trailModel_regCoeff (hH : H.IsAcyclic) (hL : H.IsDTrail Z x y L)
    (hmin : ∀ L', H.IsDTrail Z x y L' → H.trailMeasure Z L ≤ H.trailMeasure Z L') :
    IsUnit (subCov (trailModel hH hL).cov (insert x Z)) ∧
      regCoeff (trailModel hH hL).cov (insert x Z) y x = 1 := by
  set M := trailModel hH hL
  set ω := trailω H Z L
  have hΩ : M.Ω = diagonal ω := rfl
  have hω : ∀ v, ω v * ω v = ω v := trailω_mul
  have hsol : ∀ n, TrailSol H Z L n (noiseVal M ω n) := trailSol_noiseVal hH hL
  have hnd := hL.nodup
  obtain ⟨S₀, hS₀⟩ : ∃ S, L = [] ++ (x, false) :: S := by
    have := hL.head
    rcases L with _ | ⟨a, S⟩
    · simp at this
    · simp only [List.head?_cons, Option.some.injEq] at this
      exact ⟨S, by simp [this]⟩
  have hxL : x ∈ L.map Prod.fst := by simp [hS₀]
  have hxZ : x ∉ Z := hL.notMem_of_nonCollider (s := (x, false)) hS₀ (by simp)
  have hxval : ∀ n, (∀ (A : List (V × Bool)) (s t : V × Bool) (B : List (V × Bool)),
      L = A ++ s :: t :: B → (s.2 = false ∨ t.2 = true) →
        (t.2 = false ∨ ∀ r ∈ B.head?, r.2 = true) → n s.1 = n t.1) →
      noiseVal M ω n x = n x := fun n hn =>
    (hsol n).values hH hL hn x ⟨[], (x, false), S₀, hS₀, rfl, by simp⟩
  -- The noise vector equal to one on the trail.
  set N₁ : V → ℝ := fun v => if v ∈ L.map Prod.fst then 1 else 0
  have hN₁ : ∀ (A : List (V × Bool)) (s t : V × Bool) (B : List (V × Bool)),
      L = A ++ s :: t :: B → (s.2 = false ∨ t.2 = true) →
        (t.2 = false ∨ ∀ r ∈ B.head?, r.2 = true) → N₁ s.1 = N₁ t.1 := by
    intro A s t B hLe _ _
    have h1 : s.1 ∈ L.map Prod.fst := by simp [hLe]
    have h2 : t.1 ∈ L.map Prod.fst := by simp [hLe]
    simp only [N₁, ite_eq_left h1, ite_eq_left h2]
  have hcolN₁ : ∀ c, IsCollider L c → noiseVal M ω N₁ c = 0 := by
    rintro c ⟨A, w, B, hLe⟩
    obtain ⟨A', p, rfl⟩ := (List.eq_nil_or_concat A).resolve_left (hL.ne_nil_of_true hLe rfl)
    have e : L = A' ++ p :: (c, true) :: (w, false) :: B := by rw [hLe]; simp
    rw [(hsol N₁).collider_value hH hL hN₁ e]
    have h1 : p.1 ∈ L.map Prod.fst := by simp [e]
    have h2 : w ∈ L.map Prod.fst := by simp [e]
    simp only [N₁, ite_eq_left h1, ite_eq_left h2, sub_self]
  have hZN₁ : ∀ z ∈ Z, noiseVal M ω N₁ z = 0 := by
    intro z hz
    rcases mem_Z_cases hL hmin hz with ⟨c, hc, -, hzc⟩ | ⟨hzL, hzn⟩
    · rw [hzc _ _ (hsol N₁)]
      exact hcolN₁ c hc
    · rw [hzn _ _ (hsol N₁)]
      simp only [N₁, ite_eq_right hzL]
  have hxN₁ : noiseVal M ω N₁ x = 1 := by
    rw [hxval N₁ hN₁]
    simp only [N₁, ite_eq_left hxL]
  -- Endpoints of distinct colliders are distinct.
  have hend : ∀ c c', IsCollider L c → IsCollider L c' →
      (H.nextZ Z)^[H.distZ Z c] c = (H.nextZ Z)^[H.distZ Z c'] c' → c = c' := by
    intro c c' hc hc' h
    by_contra hne
    exact hL.iterate_nextZ_ne_of_min' hmin hc hc' hne le_rfl le_rfl h
  -- Linear independence of the variables in `insert x Z`.
  have hind : ∀ a : V → ℝ, (∀ n, ∑ s ∈ insert x Z, a s * noiseVal M ω n s = 0) →
      ∀ s ∈ insert x Z, a s = 0 := by
    intro a ha s hs
    rcases Finset.mem_insert.1 hs with rfl | hsZ
    · refine coeff_eq_zero_of_single hs (by rw [hxN₁]; exact one_ne_zero) (fun t ht hne => ?_)
        (ha N₁)
      rcases Finset.mem_insert.1 ht with rfl | htZ
      · exact absurd rfl hne
      · exact hZN₁ t htZ
    rcases mem_Z_cases hL hmin hsZ with ⟨c₀, hc₀, hsc₀, hsval⟩ | ⟨hsL, hsn⟩
    · -- `s` is the end of the path from the collider `c₀`.
      obtain ⟨A₀, w₀, B₀, hLe₀⟩ := id hc₀
      have hf : ∀ (A : List (V × Bool)) (s t : V × Bool) (B : List (V × Bool)),
          L = A ++ s :: t :: B → (s.2 = false ∨ t.2 = true) →
            (t.2 = false ∨ ∀ r ∈ B.head?, r.2 = true) →
              suffixInd L A₀.length s.1 = suffixInd L A₀.length t.1 := by
        intro A s' t B hLe h1 _
        have e : L = (A ++ [s']) ++ t :: B := by rw [hLe]; simp
        rw [suffixInd_of_eq hnd hLe, suffixInd_of_eq hnd e]
        simp only [List.length_append, List.length_singleton]
        by_cases hlen : A.length = A₀.length
        · exfalso
          obtain ⟨-, h2⟩ := List.append_inj (hLe.symm.trans hLe₀) hlen
          simp only [List.cons.injEq] at h2
          obtain ⟨rfl, rfl, -⟩ := h2
          simp at h1
        · by_cases hlt : A₀.length < A.length
          · rw [ite_eq_left hlt, ite_eq_left (by omega)]
          · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      have hcolf : ∀ c, IsCollider L c → c ≠ c₀ → noiseVal M ω (suffixInd L A₀.length) c = 0 := by
        rintro c ⟨A, w, B, hLe⟩ hne
        obtain ⟨A', p, rfl⟩ :=
          (List.eq_nil_or_concat A).resolve_left (hL.ne_nil_of_true hLe rfl)
        have e : L = A' ++ p :: (c, true) :: (w, false) :: B := by rw [hLe]; simp
        have e' : L = (A' ++ [p, (c, true)]) ++ (w, false) :: B := by rw [hLe]; simp
        rw [(hsol (suffixInd L A₀.length)).collider_value hH hL hf e, suffixInd_of_eq hnd e,
          suffixInd_of_eq (s := (w, false)) hnd e']
        simp only [List.length_append, List.length_cons, List.length_nil]
        have h1 : A₀.length ≠ A'.length + 1 := by
          intro hlen
          have e'' : L = (A' ++ [p]) ++ (c, true) :: (w, false) :: B := by rw [hLe]; simp
          obtain ⟨-, h2⟩ := List.append_inj (e''.symm.trans hLe₀) (by simp [hlen])
          simp only [List.cons.injEq, Prod.mk.injEq] at h2
          exact hne h2.1.1
        have h2 : A₀.length ≠ A'.length := by
          intro hlen
          obtain ⟨-, h3⟩ := List.append_inj (e.symm.trans hLe₀) hlen.symm
          simp only [List.cons.injEq, Prod.mk.injEq] at h3
          exact Bool.noConfusion h3.2.1.2
        by_cases hlt : A₀.length < A'.length
        · rw [ite_eq_left hlt, ite_eq_left (by omega), sub_self]
        · rw [ite_eq_right hlt, ite_eq_right (by omega), sub_self]
      have hc₀f : noiseVal M ω (suffixInd L A₀.length) c₀ = -1 := by
        obtain ⟨A', p, hA⟩ :=
          (List.eq_nil_or_concat A₀).resolve_left (hL.ne_nil_of_true hLe₀ rfl)
        have e : L = A' ++ p :: (c₀, true) :: (w₀, false) :: B₀ := by rw [hLe₀, hA]; simp
        have e' : L = (A' ++ [p, (c₀, true)]) ++ (w₀, false) :: B₀ := by rw [hLe₀, hA]; simp
        rw [(hsol (suffixInd L A₀.length)).collider_value hH hL hf e, suffixInd_of_eq hnd e,
          suffixInd_of_eq (s := (w₀, false)) hnd e', hA]
        simp
      refine coeff_eq_zero_of_single hs
        (by rw [hsval _ _ (hsol (suffixInd L A₀.length)), hc₀f]; norm_num)
        (fun t ht hne => ?_) (ha (suffixInd L A₀.length))
      rcases Finset.mem_insert.1 ht with rfl | htZ
      · rw [hxval (suffixInd L A₀.length) hf, suffixInd_of_eq hnd hS₀]
        simp
      rcases mem_Z_cases hL hmin htZ with ⟨c, hc, htc, htval⟩ | ⟨htL, htn⟩
      · rw [htval _ _ (hsol (suffixInd L A₀.length))]
        refine hcolf c hc fun hcc => hne ?_
        rw [htc, hsc₀, hcc]
      · rw [htn _ _ (hsol (suffixInd L A₀.length))]
        exact suffixInd_of_notMem htL
    · -- `s` lies off the trail and off the paths to `Z`.
      set e : V → ℝ := Pi.single s 1
      have he0 : ∀ v ∈ L.map Prod.fst, e v = 0 := fun v hv =>
        Pi.single_eq_of_ne (fun h => hsL (by rw [← h]; exact hv)) _
      have he : ∀ (A : List (V × Bool)) (s t : V × Bool) (B : List (V × Bool)),
          L = A ++ s :: t :: B → (s.2 = false ∨ t.2 = true) →
            (t.2 = false ∨ ∀ r ∈ B.head?, r.2 = true) → e s.1 = e t.1 := by
        intro A s' t B hLe _ _
        rw [he0 _ (by simp [hLe]), he0 _ (by simp [hLe])]
      refine coeff_eq_zero_of_single hs (by rw [hsn _ _ (hsol e)]; simp [e])
        (fun t ht hne => ?_) (ha e)
      rcases Finset.mem_insert.1 ht with rfl | htZ
      · rw [hxval e he]
        exact he0 _ hxL
      rcases mem_Z_cases hL hmin htZ with ⟨c, hc, -, htval⟩ | ⟨-, htn⟩
      · rw [htval _ _ (hsol e)]
        obtain ⟨A, w, B, hLe⟩ := hc
        obtain ⟨A', p, rfl⟩ :=
          (List.eq_nil_or_concat A).resolve_left (hL.ne_nil_of_true hLe rfl)
        have e' : L = A' ++ p :: (c, true) :: (w, false) :: B := by rw [hLe]; simp
        rw [(hsol e).collider_value hH hL he e', he0 _ (by simp [e']), he0 _ (by simp [e']),
          sub_self]
      · rw [htn _ _ (hsol e)]
        exact Pi.single_eq_of_ne hne _
  have hu : IsUnit (subCov M.cov (insert x Z)) := isUnit_subCov_of_noiseVal hΩ hω hind
  refine ⟨hu, ?_⟩
  have hrel : ∀ n, (∀ s ∈ insert x Z, noiseVal M ω n s = 0) → noiseVal M ω n y = 0 := by
    intro n hn
    rw [← (hsol n).eq_of_zero hL hmin fun z hz => hn z (Finset.mem_insert_of_mem hz)]
    exact hn x (Finset.mem_insert_self x Z)
  have hreg := noiseVal_regCoeff hΩ hω hu hrel N₁
  rw [← (hsol N₁).eq_of_zero hL hmin hZN₁, hxN₁,
    Finset.sum_eq_single x (fun t _ hne => ?_) (by simp), hxN₁, mul_one] at hreg
  · exact hreg.symm
  · by_cases ht : t ∈ insert x Z
    · rcases Finset.mem_insert.1 ht with rfl | htZ
      · exact absurd rfl hne
      · rw [hZN₁ t htZ, mul_zero]
    · rw [(regCoeff_isRegCoeff (C := M.cov) y hu).1 t ht, zero_mul]

end Trail

/-! ### The model of a directed path from `y` to `Z` -/

section Descendant

variable {G : Digraph V} {Z : Finset V} {x y : V}

variable (G Z y) in
/-- The vertices `y, nextZ y, nextZ (nextZ y), …` of a shortest directed path from `y` to `Z`. -/
noncomputable abbrev descPath (j : ℕ) : V := (G.nextZ Z)^[j] y

variable (G Z x y) in
open Classical in
/-- The coefficient matrix of the descendant model: coefficient `1` on `x → y` and on the edges of
a shortest directed path from `y` to `Z`, and `0` elsewhere. -/
noncomputable def descB : Matrix V V ℝ :=
  fun v u => if v = y ∧ u = x then 1 else
    if ∃ j < G.distZ Z y, v = descPath G Z y (j + 1) ∧ u = descPath G Z y j then 1 else 0

variable (G Z y) in
open Classical in
/-- The error variances of the descendant model: zero on the path after `y`, one elsewhere. -/
noncomputable def descω : V → ℝ :=
  fun v => if ∃ j, 1 ≤ j ∧ j ≤ G.distZ Z y ∧ v = descPath G Z y j then 0 else 1

omit [Fintype V] [DecidableEq V] in
theorem descω_mul (v : V) : descω G Z y v * descω G Z y v = descω G Z y v := by
  simp only [descω]
  split_ifs <;> norm_num

omit [Fintype V] [DecidableEq V] in
theorem descω_nonneg (v : V) : 0 ≤ descω G Z y v := by
  simp only [descω]
  split_ifs <;> norm_num

omit [Fintype V] in
theorem descB_support (hy : y ∈ G.ancestorsOf ↑Z) (hxy : G.Adj x y) (v u : V)
    (h : descB G Z x y v u ≠ 0) : G.Adj u v := by
  classical
  simp only [descB] at h
  split_ifs at h with h1 h2
  · obtain ⟨rfl, rfl⟩ := h1
    exact hxy
  · obtain ⟨j, hj, rfl, rfl⟩ := h2
    exact iterate_nextZ_adj hy hj
  · exact absurd rfl h

/-- The linear SEM of a shortest directed path from `y` to `Z`, with the edge `x → y`. -/
noncomputable def descModel (hG : G.IsAcyclic) (hy : y ∈ G.ancestorsOf ↑Z) (hxy : G.Adj x y) :
    LinearSEM V where
  G := G
  acyclic := hG
  B := descB G Z x y
  B_support := descB_support hy hxy
  Ω := diagonal (descω G Z y)
  Ω_posSemidef := PosSemidef.diagonal descω_nonneg

omit [Fintype V] [DecidableEq V] in
theorem reflTransGen_descPath (hy : y ∈ G.ancestorsOf ↑Z) :
    ∀ j ≤ G.distZ Z y, ReflTransGen G.Adj y (descPath G Z y j)
  | 0, _ => ReflTransGen.refl
  | j + 1, hj => (reflTransGen_descPath hy j (by omega)).tail (iterate_nextZ_adj hy (by omega))

/-- In the descendant model, every vertex of the path from `y` to `Z` takes the value
`n x + n y`, and every other vertex takes its noise value. -/
theorem descModel_noiseVal (hG : G.IsAcyclic) (hy : y ∈ G.ancestorsOf ↑Z) (hxy : G.Adj x y)
    (n : V → ℝ) (v : V) :
    noiseVal (descModel hG hy hxy) (descω G Z y) n v =
      if ∃ j ≤ G.distZ Z y, v = descPath G Z y j then n x + n y else n v := by
  classical
  set k := G.distZ Z y
  have hinj : ∀ i j, i ≤ k → j ≤ k → descPath G Z y i = descPath G Z y j → i = j :=
    fun i j hi hj h => iterate_nextZ_inj hy hi hj h
  have hxoff : ∀ j ≤ k, x ≠ descPath G Z y j := by
    intro j hj h
    exact hG x (TransGen.head' hxy (h ▸ reflTransGen_descPath hy j hj))
  set τ : V → ℝ := fun v => if ∃ j ≤ k, v = descPath G Z y j then n x + n y else n v
  have hτx : τ x = n x := by
    simp only [τ]
    rw [ite_eq_right]
    rintro ⟨j, hj, h⟩
    exact hxoff j hj h
  have hsol : τ = (descModel hG hy hxy).B *ᵥ τ + fun u => descω G Z y u * n u := by
    funext v
    simp only [Pi.add_apply, mulVec, dotProduct]
    change τ v = ∑ u, descB G Z x y v u * τ u + descω G Z y v * n v
    by_cases hvy : v = y
    · subst hvy
      have hrow : ∀ u, descB G Z x v v u = if u = x then 1 else 0 := by
        intro u
        simp only [descB, true_and]
        by_cases hux : u = x
        · rw [ite_eq_left hux, ite_eq_left hux]
        · rw [ite_eq_right hux, ite_eq_right hux, ite_eq_right]
          rintro ⟨j, hj, h, -⟩
          exact absurd (hinj 0 (j + 1) (Nat.zero_le _) (by omega) h) (by omega)
      have hω : descω G Z v v = 1 := by
        simp only [descω]
        rw [ite_eq_right]
        rintro ⟨j, hj1, hj, h⟩
        exact absurd (hinj 0 j (Nat.zero_le _) hj h) (by omega)
      simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, hτx, hω]
      simp only [τ]
      rw [ite_eq_left ⟨0, Nat.zero_le _, rfl⟩]
    by_cases hvp : ∃ j < k, v = descPath G Z y (j + 1)
    · obtain ⟨j, hj, rfl⟩ := hvp
      have hrow : ∀ u, descB G Z x y (descPath G Z y (j + 1)) u =
          if u = descPath G Z y j then 1 else 0 := by
        intro u
        simp only [descB]
        rw [ite_eq_right (fun h => hvy h.1)]
        by_cases hu : u = descPath G Z y j
        · rw [ite_eq_left ⟨j, hj, rfl, hu⟩, ite_eq_left hu]
        · rw [ite_eq_right hu, ite_eq_right]
          rintro ⟨i, hi, h1, h2⟩
          have := hinj (j + 1) (i + 1) (by omega) (by omega) h1
          exact hu (by rw [h2, show i = j by omega])
      have hω : descω G Z y (descPath G Z y (j + 1)) = 0 := by
        simp only [descω]
        rw [ite_eq_left ⟨j + 1, by omega, by omega, rfl⟩]
      simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, hω, add_zero]
      simp only [τ]
      rw [ite_eq_left ⟨j + 1, by omega, rfl⟩, ite_eq_left ⟨j, by omega, rfl⟩]
    · have hrow : ∀ u, descB G Z x y v u = 0 := by
        intro u
        simp only [descB]
        rw [ite_eq_right (fun h => hvy h.1), ite_eq_right]
        rintro ⟨j, hj, h1, -⟩
        exact hvp ⟨j, hj, h1⟩
      have hoff : ¬ ∃ j ≤ k, v = descPath G Z y j := by
        rintro ⟨j, hj, h⟩
        rcases j with _ | j
        · exact hvy h
        · exact hvp ⟨j, by omega, h⟩
      have hω : descω G Z y v = 1 := by
        simp only [descω]
        rw [ite_eq_right]
        rintro ⟨j, hj1, hj, h⟩
        exact hoff ⟨j, hj, h⟩
      simp only [hrow, zero_mul, Finset.sum_const_zero, zero_add, hω, one_mul]
      simp only [τ]
      rw [ite_eq_right hoff]
  rw [← eq_noiseVal hsol]

/-- **The witness for a descendant of `y` in `Z`.** If `x → y` is an edge, `x ∉ Z`, and `Z`
contains a descendant of `y`, then in the descendant model the covariance block on `insert x Z`
is invertible and the coefficient of `x` in the regression of `y` on `insert x Z` is `0`, while
the path coefficient of `x → y` is `1`. -/
theorem descModel_regCoeff (hG : G.IsAcyclic) (hy : y ∈ G.ancestorsOf ↑Z) (hxy : G.Adj x y)
    (hxZ : x ∉ Z) :
    IsUnit (subCov (descModel hG hy hxy).cov (insert x Z)) ∧
      regCoeff (descModel hG hy hxy).cov (insert x Z) y x = 0 ∧
        (descModel hG hy hxy).B y x = 1 := by
  classical
  set M := descModel hG hy hxy
  set ω := descω G Z y
  set k := G.distZ Z y
  have hΩ : M.Ω = diagonal ω := rfl
  have hω : ∀ v, ω v * ω v = ω v := descω_mul
  have hval := descModel_noiseVal hG hy hxy
  have hxy' : x ≠ y := fun h => hG x (TransGen.single (h ▸ hxy))
  set z := descPath G Z y k
  have hzZ : z ∈ Z := iterate_nextZ_distZ_mem hy
  have hz : ∀ n, noiseVal M ω n z = n x + n y := fun n => by
    rw [hval, ite_eq_left ⟨k, le_rfl, rfl⟩]
  have hyv : ∀ n, noiseVal M ω n y = n x + n y := fun n => by
    rw [hval, ite_eq_left ⟨0, Nat.zero_le _, rfl⟩]
  have hxv : ∀ n, noiseVal M ω n x = n x := fun n => by
    rw [hval, ite_eq_right]
    rintro ⟨j, hj, h⟩
    exact hG x (TransGen.head' hxy (h ▸ reflTransGen_descPath hy j hj))
  have hoff : ∀ t ∈ Z, t ≠ z → ∀ n, noiseVal M ω n t = n t := by
    intro t ht htz n
    rw [hval, ite_eq_right]
    rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact iterate_nextZ_notMem hy hjk ht
    · exact htz (by rw [show j = k by omega])
  have hyoff : ∀ t ∈ Z, t ≠ z → t ≠ y := by
    rintro t ht htz rfl
    have : k = 0 := by
      by_contra hk
      exact iterate_nextZ_notMem hy (j := 0) (by omega) ht
    apply htz
    change t = (G.nextZ Z)^[k] t
    rw [this]
    rfl
  have hxz : x ≠ z := fun h => hxZ (h ▸ hzZ)
  have hind : ∀ a : V → ℝ, (∀ n, ∑ s ∈ insert x Z, a s * noiseVal M ω n s = 0) →
      ∀ s ∈ insert x Z, a s = 0 := by
    intro a ha
    have haz : a z = 0 := by
      refine coeff_eq_zero_of_single (Finset.mem_insert_of_mem hzZ)
        (by rw [hz]; simp [hxy']) (fun t ht hne => ?_) (ha (Pi.single y 1))
      rcases Finset.mem_insert.1 ht with rfl | htZ
      · rw [hxv]
        simp [hxy']
      · rw [hoff t htZ hne]
        simp [hyoff t htZ hne]
    intro s hs
    by_cases hsz : s = z
    · rw [hsz, haz]
    rcases Finset.mem_insert.1 hs with rfl | hsZ
    · refine coeff_eq_zero_of_single hs (by rw [hxv]; simp [hxy']) (fun t ht hne => ?_)
        (ha (Pi.single s 1 - Pi.single y 1))
      rcases Finset.mem_insert.1 ht with rfl | htZ
      · exact absurd rfl hne
      by_cases htz : t = z
      · rw [htz, hz]
        simp [hxy']
      · rw [hoff t htZ htz]
        simp [hne, hyoff t htZ htz]
    · refine coeff_eq_zero_of_single hs (by rw [hoff s hsZ hsz]; simp) (fun t ht hne => ?_)
        (ha (Pi.single s 1))
      rcases Finset.mem_insert.1 ht with rfl | htZ
      · rw [hxv]
        simp [Ne.symm hne]
      by_cases htz : t = z
      · rw [htz, hz]
        simp [Ne.symm (fun h => hxZ (h ▸ hsZ) : s ≠ x), hyoff s hsZ hsz]
      · rw [hoff t htZ htz]
        simp [hne]
  have hu : IsUnit (subCov M.cov (insert x Z)) := isUnit_subCov_of_noiseVal hΩ hω hind
  have hrel : ∀ n, (∀ s ∈ insert x Z, noiseVal M ω n s = 0) → noiseVal M ω n y = 0 := by
    intro n hn
    rw [hyv, ← hz]
    exact hn z (Finset.mem_insert_of_mem hzZ)
  have hB : M.B y x = 1 := by
    change descB G Z x y y x = 1
    simp [descB]
  refine ⟨hu, ?_, hB⟩
  have hreg := noiseVal_regCoeff hΩ hω hu hrel (Pi.single x 1 - Pi.single y 1)
  rw [hyv, Finset.sum_eq_single x (fun t _ hne => ?_) (by simp)] at hreg
  · rw [hxv] at hreg
    simpa [hxy', Ne.symm hxy'] using hreg.symm
  · by_cases ht : t ∈ insert x Z
    · rcases Finset.mem_insert.1 ht with rfl | htZ
      · exact absurd rfl hne
      by_cases htz : t = z
      · rw [htz, hz]
        simp [hxy']
      · rw [hoff t htZ htz]
        simp [hne, hyoff t htZ htz]
    · rw [(regCoeff_isRegCoeff (C := M.cov) y hu).1 t ht, zero_mul]

end Descendant

/-! ### The generic converse -/

/-- **The generic converse of the single-door criterion.** Let `x → y` be an edge of the acyclic
graph `G` and suppose that `Z` does not d-separate `x` from `y` in the graph with `x → y`
deleted. Then the parameter vectors (path coefficients and positive error variances) at which
the coefficient of `x` in the regression of `y` on `x` and `Z` equals the path coefficient of
`x → y` form a Lebesgue null set. The witness making the bias polynomial nonzero is the model of
a minimal open trail (`trailModel_regCoeff`): its regression coefficient is `1` while its path
coefficient of `x → y` is `0`. -/
theorem volume_exceptional_eq_zero_of_not_dSep {G : Digraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {x y : V} {Z : Finset V}
    (h : ¬ (deleteEdgeGraph G x y).DSep {x} {y} ↑Z) :
    volume (exceptional x y (insert x Z) : Set (Param G)) = 0 := by
  have hconn : (deleteEdgeGraph G x y).DConn {x} {y} ↑Z := not_not.1 h
  obtain ⟨L, hL, hmin⟩ := exists_isDTrail_min hconn
  have hH : (deleteEdgeGraph G x y).IsAcyclic :=
    Digraph.IsAcyclic.anti (H := deleteEdgeGraph G x y) (fun _ _ h => h.1) hG
  obtain ⟨hu, hβ⟩ := trailModel_regCoeff hH hL hmin
  refine volume_exceptional_eq_zero_of_model hG (Finset.mem_insert_self x Z) (trailModel hH hL)
    (fun v u h => (trailB_support hL v u h).1) (isDiag_diagonal _) hu ?_
  rw [hβ]
  intro h1
  have hne : trailB (deleteEdgeGraph G x y) Z L y x ≠ 0 := by
    change (trailModel hH hL).B y x ≠ 0
    rw [← h1]
    exact one_ne_zero
  exact (trailB_support hL y x hne).2 ⟨rfl, rfl⟩

/-- **The existence form.** Under the hypotheses of `volume_exceptional_eq_zero_of_not_dSep`
there is a linear SEM on `G` with uncorrelated errors of positive variance at which the
coefficient of `x` in the regression of `y` on `x` and `Z` differs from the path coefficient of
`x → y`. -/
theorem exists_model_ne_of_not_dSep {G : Digraph V} (hG : G.IsAcyclic)
    {x y : V} {Z : Finset V} (h : ¬ (deleteEdgeGraph G x y).DSep {x} {y} ↑Z) :
    ∃ M : LinearSEM V, M.G = G ∧ M.Ω.IsDiag ∧ M.Ω.PosDef ∧
      regCoeff M.cov (insert x Z) y x ≠ M.B y x := by
  classical
  obtain ⟨θ, hθ, hpd, hne⟩ := exists_model_ne hG (volume_exceptional_eq_zero_of_not_dSep hG h)
  exact ⟨_, rfl, isDiag_diagonal _, hpd, hne⟩

/-- **The single-door criterion is exact for generic parameters.** Let `x → y` be an edge of the
acyclic graph `G`, and let `Z` contain neither `x` nor a descendant of `y`. Then the coefficient
of `x` in the regression of `y` on `x` and `Z` equals the path coefficient of `x → y` at every
parameter vector with positive error variances if and only if `Z` d-separates `x` from `y` in
the graph with `x → y` deleted; when it does not, the two differ outside a Lebesgue null set
(`volume_exceptional_eq_zero_of_not_dSep`). -/
theorem forall_regCoeff_eq_iff_dSep {G : Digraph V} [DecidableRel G.Adj] (hG : G.IsAcyclic)
    {x y : V} {Z : Finset V} (hxy : G.Adj x y) (hxZ : x ∉ Z)
    (hZ : ∀ s ∈ Z, ¬ ReflTransGen G.Adj y s) :
    (∀ θ : Param G, (∀ v, 0 < θ (Sum.inr v)) →
        regCoeff (paramCov θ) (insert x Z) y x = paramB θ y x) ↔
      (deleteEdgeGraph G x y).DSep {x} {y} ↑Z := by
  constructor
  · intro h
    by_contra hsep
    obtain ⟨θ, hθ, -, hne⟩ :=
      exists_model_ne hG (volume_exceptional_eq_zero_of_not_dSep hG hsep)
    exact hne (h θ hθ)
  · intro hsep θ hθ
    have hpd : (paramModel hG θ fun v => (hθ v).le).cov.PosDef :=
      cov_posDef _ (posDef_diagonal_iff.2 hθ)
    exact single_door (M := paramModel hG θ fun v => (hθ v).le) (isDiag_diagonal _) hxy hxZ hZ
      hsep (isUnit_submatrix_of_posDef hpd Z) (isUnit_submatrix_of_posDef hpd (insert x Z))

/-- **The converse for a descendant of `y` in `Z`.** If `x → y` is an edge of the acyclic graph
`G`, `x ∉ Z`, and `Z` contains a descendant of `y`, the parameter vectors with positive error
variances at which the coefficient of `x` in the regression of `y` on `x` and `Z` equals the path
coefficient of `x → y` form a Lebesgue null set (whether or not d-separation holds). The witness
is `descModel_regCoeff`. -/
theorem volume_exceptional_eq_zero_of_descendant {G : Digraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {x y : V} {Z : Finset V} (hxy : G.Adj x y) (hxZ : x ∉ Z)
    (h : ∃ s ∈ Z, ReflTransGen G.Adj y s) :
    volume (exceptional x y (insert x Z) : Set (Param G)) = 0 := by
  obtain ⟨s, hs, hys⟩ := h
  have hy : y ∈ G.ancestorsOf ↑Z := ⟨s, Finset.mem_coe.2 hs, hys⟩
  obtain ⟨hu, hβ, hB⟩ := descModel_regCoeff hG hy hxy hxZ
  refine volume_exceptional_eq_zero_of_model hG (Finset.mem_insert_self x Z)
    (descModel hG hy hxy) (fun v u h => descB_support hy hxy v u h) (isDiag_diagonal _) hu ?_
  rw [hβ, hB]
  exact zero_ne_one

/-- **The generic converse of the single-door criterion, in full** (Pearl 2009, Theorem 5.3.1,
converse part). Let `x → y` be an edge of the acyclic graph `G` and `x ∉ Z`. If the single-door
condition fails, that is, `Z` contains a descendant of `y` or does not d-separate `x` from `y`
in the graph with `x → y` deleted, then the parameter vectors with positive error variances at
which the coefficient of `x` in the regression of `y` on `x` and `Z` equals the path coefficient
of `x → y` form a Lebesgue null set. -/
theorem volume_exceptional_eq_zero_of_not_singleDoor {G : Digraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {x y : V} {Z : Finset V} (hxy : G.Adj x y) (hxZ : x ∉ Z)
    (h : ¬ ((∀ s ∈ Z, ¬ ReflTransGen G.Adj y s) ∧ (deleteEdgeGraph G x y).DSep {x} {y} ↑Z)) :
    volume (exceptional x y (insert x Z) : Set (Param G)) = 0 := by
  by_cases hZ : ∀ s ∈ Z, ¬ ReflTransGen G.Adj y s
  · exact volume_exceptional_eq_zero_of_not_dSep hG fun hs => h ⟨hZ, hs⟩
  · push Not at hZ
    exact volume_exceptional_eq_zero_of_descendant hG hxy hxZ hZ

/-- **The single-door criterion is exact.** Let `x → y` be an edge of the acyclic graph `G` and
`x ∉ Z`. The coefficient of `x` in the regression of `y` on `x` and `Z` equals the path
coefficient of `x → y` at every parameter vector with positive error variances if and only if
`Z` contains no descendant of `y` and d-separates `x` from `y` in the graph with `x → y`
deleted; otherwise the two differ outside a Lebesgue null set
(`volume_exceptional_eq_zero_of_not_singleDoor`). -/
theorem forall_regCoeff_eq_iff_singleDoor {G : Digraph V} [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {x y : V} {Z : Finset V} (hxy : G.Adj x y) (hxZ : x ∉ Z) :
    (∀ θ : Param G, (∀ v, 0 < θ (Sum.inr v)) →
        regCoeff (paramCov θ) (insert x Z) y x = paramB θ y x) ↔
      (∀ s ∈ Z, ¬ ReflTransGen G.Adj y s) ∧ (deleteEdgeGraph G x y).DSep {x} {y} ↑Z := by
  constructor
  · intro h
    by_contra hsd
    obtain ⟨θ, hθ, -, hne⟩ :=
      exists_model_ne hG (volume_exceptional_eq_zero_of_not_singleDoor hG hxy hxZ hsd)
    exact hne (h θ hθ)
  · rintro ⟨hZ, hsep⟩
    exact (forall_regCoeff_eq_iff_dSep hG hxy hxZ hZ).2 hsep

end SingleDoorGeneric

end LinearSEM

end CausalInference
