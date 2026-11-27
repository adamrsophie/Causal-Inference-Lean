/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.FiniteDistribution

/-!
# Conditional independence for finite distributions

Conditional independence is defined without division, in product form.

## Main definitions

* `FiniteDist.CondIndepFun p X Y Z`: for random variables `X`, `Y`, `Z` on a finite probability
  space, `P(X = a, Y = b, Z = c) * P(Z = c) = P(X = a, Z = c) * P(Y = b, Z = c)` for all values.
* `FiniteDist.CondIndep p X Y Z`: for a joint distribution on configurations `x : ∀ v, α v` and
  finsets of coordinates `X Y Z : Finset V`, the conditional independence of the restrictions
  `X.restrict`, `Y.restrict`, `Z.restrict`. Thus `p(x, y, z) * p(z) = p(x, z) * p(y, z)` for all
  configurations `x` of `X`, `y` of `Y`, `z` of `Z`.

## Main results

* The semi-graphoid properties, for random variables and for coordinate sets: symmetry,
  decomposition, weak union, contraction.
* The intersection property under positivity. For random variables the hypothesis is positivity
  of the joint law of the variables `Y`, `Z`, `W` (positivity of the masses is not enough,
  `FiniteDist.not_condIndepFun_intersection`); for coordinate sets it is positivity of the masses
  together with pairwise disjointness of `Y`, `Z`, `W`.
* `FiniteDist.condIndepFun_iff_exists_mul`: the factorization criterion,
  `P(X = a, Y = b, Z = c) = f a c * g b c`.
* `FiniteDist.CondIndep.margAt_mul` and `FiniteDist.condIndep_iff_margAt_mul`: the cylinder form
  `p(x_{X ∪ Y ∪ Z}) * p(x_Z) = p(x_{X ∪ Z}) * p(x_{Y ∪ Z})` with full configurations `x`, and
  `FiniteDist.condIndep_of_margAt_eq_mul`, the factorization criterion in that form.

Sources: Dawid (1979), Conditional independence in statistical theory; Pearl (1988),
Probabilistic Reasoning in Intelligent Systems; Lauritzen (1996), Graphical Models, chapter 3.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace FiniteDist

section RandomVariables

variable {Ω β γ δ ε : Type*} [Fintype Ω] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
  [DecidableEq ε]
  (p : FiniteDist Ω) {X : Ω → β} {Y : Ω → γ} {Z : Ω → δ} {W : Ω → ε}

/-- Conditional independence of the random variables `X` and `Y` given `Z`, in product form:
`P(X = a, Y = b, Z = c) * P(Z = c) = P(X = a, Z = c) * P(Y = b, Z = c)` for all values. -/
def CondIndepFun (X : Ω → β) (Y : Ω → γ) (Z : Ω → δ) : Prop :=
  ∀ a b c, p.probOf (fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c) * p.probOf (fun ω => Z ω = c) =
    p.probOf (fun ω => X ω = a ∧ Z ω = c) * p.probOf (fun ω => Y ω = b ∧ Z ω = c)

variable {p}

/-- Symmetry of conditional independence. -/
theorem CondIndepFun.symm (h : p.CondIndepFun X Y Z) : p.CondIndepFun Y X Z := by
  intro b a c
  rw [mul_comm (p.probOf fun ω => Y ω = b ∧ Z ω = c), ← h a b c,
    p.probOf_congr fun ω => and_left_comm]

theorem condIndepFun_comm : p.CondIndepFun X Y Z ↔ p.CondIndepFun Y X Z :=
  ⟨CondIndepFun.symm, CondIndepFun.symm⟩

/-- Conditional independence passes to functions of the second variable. -/
theorem CondIndepFun.of_right [Finite γ] {γ' : Type*} [DecidableEq γ'] {Y' : Ω → γ'}
    (h : p.CondIndepFun X Y Z) (g : γ → γ') (hY : ∀ ω, Y' ω = g (Y ω)) :
    p.CondIndepFun X Y' Z := by
  cases nonempty_fintype γ
  intro a b' c
  have e1 : p.probOf (fun ω => X ω = a ∧ Y' ω = b' ∧ Z ω = c) =
      ∑ b ∈ univ.filter (fun b => g b = b'),
        p.probOf (fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c) := by
    rw [p.probOf_eq_sum Y (univ.filter fun b => g b = b')
      (fun ω hω => by simp [← hY, hω.2.1])]
    refine sum_congr rfl fun b hb => p.probOf_congr fun ω => ?_
    simp only [mem_filter, mem_univ, true_and] at hb
    rw [hY]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, h4 ▸ hb, h3⟩, h4⟩
  have e2 : p.probOf (fun ω => Y' ω = b' ∧ Z ω = c) =
      ∑ b ∈ univ.filter (fun b => g b = b'), p.probOf (fun ω => Y ω = b ∧ Z ω = c) := by
    rw [p.probOf_eq_sum Y (univ.filter fun b => g b = b')
      (fun ω hω => by simp [← hY, hω.1])]
    refine sum_congr rfl fun b hb => p.probOf_congr fun ω => ?_
    simp only [mem_filter, mem_univ, true_and] at hb
    rw [hY]
    constructor
    · rintro ⟨⟨-, h3⟩, h4⟩
      exact ⟨h4, h3⟩
    · rintro ⟨h4, h3⟩
      exact ⟨⟨h4 ▸ hb, h3⟩, h4⟩
  rw [e1, e2, sum_mul, mul_sum]
  exact sum_congr rfl fun b _ => h a b c

/-- Conditional independence passes to functions of the first variable. -/
theorem CondIndepFun.of_left [Finite β] {β' : Type*} [DecidableEq β'] {X' : Ω → β'}
    (h : p.CondIndepFun X Y Z) (g : β → β') (hX : ∀ ω, X' ω = g (X ω)) :
    p.CondIndepFun X' Y Z :=
  (h.symm.of_right g hX).symm

/-- The conditioning variable may be replaced by any variable that determines it and is
determined by it, that is, that induces the same partition of the outcomes. -/
theorem CondIndepFun.of_cond {δ' : Type*} [DecidableEq δ'] {Z' : Ω → δ'}
    (h : p.CondIndepFun X Y Z) (f : δ' → δ) (g : δ → δ') (hZ : ∀ ω, Z ω = f (Z' ω))
    (hZ' : ∀ ω, Z' ω = g (Z ω)) : p.CondIndepFun X Y Z' := by
  intro a b c'
  by_cases hc : ∃ ω₀, Z' ω₀ = c'
  · obtain ⟨ω₀, hω₀⟩ := hc
    have key : ∀ ω, Z' ω = c' ↔ Z ω = f c' := by
      intro ω
      constructor
      · intro hω
        rw [hZ, hω]
      · intro hω
        rw [hZ', hω, ← hω₀, ← hZ]
        exact (hZ' ω₀).symm
    simp only [key]
    exact h a b (f c')
  · push Not at hc
    rw [p.probOf_eq_zero (P := fun ω => X ω = a ∧ Y ω = b ∧ Z' ω = c') fun ω hω => hc ω hω.2.2,
      p.probOf_eq_zero (P := fun ω => X ω = a ∧ Z' ω = c') fun ω hω => hc ω hω.2]
    simp

/-- Decomposition: independence from a pair implies independence from its first component. -/
theorem CondIndepFun.decomp [Finite γ] [Finite ε]
    (h : p.CondIndepFun X (fun ω => (Y ω, W ω)) Z) : p.CondIndepFun X Y Z :=
  h.of_right Prod.fst fun _ => rfl

/-- Weak union: independence from a pair `(Y, W)` given `Z` implies independence from `Y` given
`(Z, W)`. -/
theorem CondIndepFun.weak_union [Finite γ] [Finite ε]
    (h : p.CondIndepFun X (fun ω => (Y ω, W ω)) Z) :
    p.CondIndepFun X Y (fun ω => (Z ω, W ω)) := by
  rintro a b ⟨c, d⟩
  have h1 := h a (b, d) c
  have h2 := h.of_right (Y' := W) Prod.snd (fun _ => rfl) a d c
  simp only [Prod.mk.injEq] at h1 ⊢
  rw [p.probOf_congr (P := fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c ∧ W ω = d)
      (Q := fun ω => X ω = a ∧ (Y ω = b ∧ W ω = d) ∧ Z ω = c) (fun ω => by tauto),
    p.probOf_congr (P := fun ω => Z ω = c ∧ W ω = d) (Q := fun ω => W ω = d ∧ Z ω = c)
      (fun ω => and_comm),
    p.probOf_congr (P := fun ω => X ω = a ∧ Z ω = c ∧ W ω = d)
      (Q := fun ω => X ω = a ∧ W ω = d ∧ Z ω = c) (fun ω => by tauto),
    p.probOf_congr (P := fun ω => Y ω = b ∧ Z ω = c ∧ W ω = d)
      (Q := fun ω => (Y ω = b ∧ W ω = d) ∧ Z ω = c) (fun ω => by tauto)]
  set E := p.probOf fun ω => Z ω = c
  rcases eq_or_ne E 0 with hE | hE
  · have z1 := le_antisymm ((p.probOf_mono (P := fun ω => X ω = a ∧ (Y ω = b ∧ W ω = d) ∧
      Z ω = c) fun ω h => h.2.2).trans_eq hE) (p.probOf_nonneg)
    have z3 := le_antisymm ((p.probOf_mono (P := fun ω => X ω = a ∧ W ω = d ∧ Z ω = c)
      fun ω h => h.2.2).trans_eq hE) (p.probOf_nonneg)
    rw [z1, z3, zero_mul, zero_mul]
  · refine mul_right_cancel₀ hE ?_
    linear_combination (p.probOf fun ω => W ω = d ∧ Z ω = c) * h1 -
      (p.probOf fun ω => (Y ω = b ∧ W ω = d) ∧ Z ω = c) * h2

/-- Contraction: `X ⫫ Y | Z` and `X ⫫ W | (Y, Z)` imply `X ⫫ (Y, W) | Z`. -/
theorem CondIndepFun.contraction (h1 : p.CondIndepFun X Y Z)
    (h2 : p.CondIndepFun X W (fun ω => (Y ω, Z ω))) :
    p.CondIndepFun X (fun ω => (Y ω, W ω)) Z := by
  rintro a ⟨b, d⟩ c
  have hA := h1 a b c
  have hB := h2 a d (b, c)
  simp only [Prod.mk.injEq] at hB ⊢
  rw [p.probOf_congr (P := fun ω => X ω = a ∧ (Y ω = b ∧ W ω = d) ∧ Z ω = c)
      (Q := fun ω => X ω = a ∧ W ω = d ∧ Y ω = b ∧ Z ω = c) (fun ω => by tauto),
    p.probOf_congr (P := fun ω => (Y ω = b ∧ W ω = d) ∧ Z ω = c)
      (Q := fun ω => W ω = d ∧ Y ω = b ∧ Z ω = c) (fun ω => by tauto)]
  set H := p.probOf fun ω => Y ω = b ∧ Z ω = c
  rcases eq_or_ne H 0 with hH | hH
  · have z1 := le_antisymm ((p.probOf_mono (P := fun ω => X ω = a ∧ W ω = d ∧ Y ω = b ∧
      Z ω = c) fun ω h => h.2.2).trans_eq hH) (p.probOf_nonneg)
    have z2 := le_antisymm ((p.probOf_mono (P := fun ω => W ω = d ∧ Y ω = b ∧ Z ω = c)
      fun ω h => h.2).trans_eq hH) (p.probOf_nonneg)
    rw [z1, z2, zero_mul, mul_zero]
  · refine mul_right_cancel₀ hH ?_
    linear_combination (p.probOf fun ω => Z ω = c) * hB +
      (p.probOf fun ω => W ω = d ∧ Y ω = b ∧ Z ω = c) * hA

/-- Intersection: if the joint law of `(Y, Z, W)` is strictly positive, then `X ⫫ Y | (Z, W)`
and `X ⫫ W | (Z, Y)` imply `X ⫫ (Y, W) | Z`. Positivity of the masses `p ω` alone does not
suffice (`FiniteDist.not_condIndepFun_intersection`). -/
theorem CondIndepFun.intersection [Finite ε]
    (hpos : ∀ b c d, 0 < p.probOf (fun ω => Y ω = b ∧ Z ω = c ∧ W ω = d))
    (h1 : p.CondIndepFun X Y (fun ω => (Z ω, W ω)))
    (h2 : p.CondIndepFun X W (fun ω => (Z ω, Y ω))) :
    p.CondIndepFun X (fun ω => (Y ω, W ω)) Z := by
  cases nonempty_fintype ε
  rintro a ⟨b, d⟩ c
  simp only [Prod.mk.injEq]
  set Pbc := p.probOf fun ω => Y ω = b ∧ Z ω = c
  set Pabc := p.probOf fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c
  -- the two hypotheses at a value `e` of `W`, in a common normal form
  have H2 : ∀ e, p.probOf (fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c ∧ W ω = e) * Pbc =
      Pabc * p.probOf (fun ω => Y ω = b ∧ Z ω = c ∧ W ω = e) := by
    intro e
    have h := h2 a e (c, b)
    simp only [Prod.mk.injEq] at h
    rwa [p.probOf_congr (P := fun ω => X ω = a ∧ W ω = e ∧ Z ω = c ∧ Y ω = b)
        (Q := fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c ∧ W ω = e) (fun ω => by tauto),
      p.probOf_congr (P := fun ω => Z ω = c ∧ Y ω = b) (Q := fun ω => Y ω = b ∧ Z ω = c)
        (fun ω => and_comm),
      p.probOf_congr (P := fun ω => X ω = a ∧ Z ω = c ∧ Y ω = b)
        (Q := fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c) (fun ω => by tauto),
      p.probOf_congr (P := fun ω => W ω = e ∧ Z ω = c ∧ Y ω = b)
        (Q := fun ω => Y ω = b ∧ Z ω = c ∧ W ω = e) (fun ω => by tauto)] at h
  have key : ∀ e, p.probOf (fun ω => X ω = a ∧ Z ω = c ∧ W ω = e) * Pbc =
      Pabc * p.probOf (fun ω => Z ω = c ∧ W ω = e) := by
    intro e
    have h := h1 a b (c, e)
    simp only [Prod.mk.injEq] at h
    refine mul_right_cancel₀ (hpos b c e).ne' ?_
    linear_combination (-Pbc) * h + (p.probOf fun ω => Z ω = c ∧ W ω = e) * H2 e
  have hsum : (p.probOf fun ω => X ω = a ∧ Z ω = c) * Pbc =
      Pabc * p.probOf (fun ω => Z ω = c) := by
    rw [p.probOf_eq_sum_univ (P := fun ω => X ω = a ∧ Z ω = c) W,
      p.probOf_eq_sum_univ (P := fun ω => Z ω = c) W, sum_mul, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [p.probOf_congr (P := fun ω => (X ω = a ∧ Z ω = c) ∧ W ω = e)
      (Q := fun ω => X ω = a ∧ Z ω = c ∧ W ω = e) (fun ω => and_assoc), key e]
  have hPbc : 0 < Pbc :=
    (hpos b c d).trans_le (p.probOf_mono fun ω h => ⟨h.1, h.2.1⟩)
  rw [p.probOf_congr (P := fun ω => X ω = a ∧ (Y ω = b ∧ W ω = d) ∧ Z ω = c)
      (Q := fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c ∧ W ω = d) (fun ω => by tauto),
    p.probOf_congr (P := fun ω => (Y ω = b ∧ W ω = d) ∧ Z ω = c)
      (Q := fun ω => Y ω = b ∧ Z ω = c ∧ W ω = d) (fun ω => by tauto)]
  refine mul_right_cancel₀ hPbc.ne' ?_
  linear_combination (p.probOf fun ω => Z ω = c) * H2 d -
    (p.probOf fun ω => Y ω = b ∧ Z ω = c ∧ W ω = d) * hsum

/-- The factorization criterion: `X ⫫ Y | Z` iff the joint mass of `(X, Y, Z)` factors as
`f a c * g b c`. -/
theorem condIndepFun_iff_exists_mul [Finite β] [Finite γ] :
    p.CondIndepFun X Y Z ↔ ∃ (f : β → δ → ℝ) (g : γ → δ → ℝ),
      ∀ a b c, p.probOf (fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c) = f a c * g b c := by
  cases nonempty_fintype β
  cases nonempty_fintype γ
  constructor
  · intro h
    refine ⟨fun a c => if p.probOf (fun ω => Z ω = c) = 0 then 0 else
        p.probOf (fun ω => X ω = a ∧ Z ω = c) / p.probOf (fun ω => Z ω = c),
      fun b c => p.probOf (fun ω => Y ω = b ∧ Z ω = c), fun a b c => ?_⟩
    dsimp only
    split_ifs with hc
    · rw [zero_mul]
      exact le_antisymm ((p.probOf_mono fun ω h => h.2.2).trans_eq hc) p.probOf_nonneg
    · rw [div_mul_eq_mul_div, eq_div_iff hc, h a b c]
  · rintro ⟨f, g, hfg⟩ a b c
    have hac : ∀ a, p.probOf (fun ω => X ω = a ∧ Z ω = c) = f a c * ∑ b', g b' c := by
      intro a
      rw [p.probOf_eq_sum_univ Y, mul_sum]
      refine sum_congr rfl fun b' _ => ?_
      rw [← hfg]
      exact p.probOf_congr fun ω => by tauto
    have hbc : p.probOf (fun ω => Y ω = b ∧ Z ω = c) = g b c * ∑ a', f a' c := by
      rw [p.probOf_eq_sum_univ X, mul_sum]
      refine sum_congr rfl fun a' _ => ?_
      rw [mul_comm, ← hfg]
      exact p.probOf_congr fun ω => by tauto
    have hc : p.probOf (fun ω => Z ω = c) = (∑ a', f a' c) * ∑ b', g b' c := by
      rw [p.probOf_eq_sum_univ X, sum_mul]
      refine sum_congr rfl fun a' _ => ?_
      rw [← hac a']
      exact p.probOf_congr fun ω => and_comm
    rw [hfg, hac a, hbc, hc]
    ring

end RandomVariables

/-! ### Coordinate sets of a joint distribution -/

section Coordinates

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- Overwrite the coordinates of `x` in `S` by the configuration `a` of `S`. -/
def override (S : Finset V) (a : ∀ v : S, α v) (x : ∀ v, α v) : ∀ v, α v :=
  fun v => if h : v ∈ S then a ⟨v, h⟩ else x v

omit [Fintype V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
theorem override_of_mem {S : Finset V} (a : ∀ v : S, α v) (x : ∀ v, α v) {v : V} (h : v ∈ S) :
    override S a x v = a ⟨v, h⟩ := by
  simp [override, h]

omit [Fintype V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
theorem override_of_notMem {S : Finset V} (a : ∀ v : S, α v) (x : ∀ v, α v) {v : V}
    (h : v ∉ S) : override S a x v = x v := by
  simp [override, h]

omit [Fintype V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
@[simp] theorem restrict_override (S : Finset V) (a : ∀ v : S, α v) (x : ∀ v, α v) :
    S.restrict (override S a x) = a :=
  funext fun v => override_of_mem a x v.2

omit [Fintype V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
theorem restrict_override_of_disjoint {S T : Finset V} (hST : Disjoint T S)
    (a : ∀ v : S, α v) (x : ∀ v, α v) : T.restrict (override S a x) = T.restrict x :=
  funext fun v => override_of_notMem a x (disjoint_left.1 hST v.2)

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- Configurations of three pairwise disjoint sets of coordinates can be realized jointly. -/
theorem exists_restrict_eq {X Y Z : Finset V} (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (x₀ : ∀ v, α v) (a : ∀ v : X, α v) (b : ∀ v : Y, α v)
    (c : ∀ v : Z, α v) : ∃ x, X.restrict x = a ∧ Y.restrict x = b ∧ Z.restrict x = c := by
  classical
  refine ⟨override X a (override Y b (override Z c x₀)), by simp, ?_, ?_⟩
  · rw [restrict_override_of_disjoint hXY.symm, restrict_override]
  · rw [restrict_override_of_disjoint hXZ.symm, restrict_override_of_disjoint hYZ.symm,
      restrict_override]

/-- Glue a configuration of `S` and one of `T` into a configuration of `S ∪ T` (the first one
wins on the overlap). -/
def glue (S T : Finset V) (a : ∀ v : S, α v) (b : ∀ v : T, α v) : ∀ v : (S ∪ T : Finset V), α v :=
  fun v => if h : v.1 ∈ S then a ⟨v.1, h⟩ else b ⟨v.1, (mem_union.1 v.2).resolve_left h⟩

omit [Fintype V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
theorem restrict_union_eq_glue (S T : Finset V) (x : ∀ v, α v) :
    (S ∪ T).restrict x = glue S T (S.restrict x) (T.restrict x) := by
  funext v
  by_cases h : v.1 ∈ S <;> simp [glue, Finset.restrict, h]

/-- Conditional independence of the coordinates in `X` and those in `Y` given those in `Z`:
`p(x_X, x_Y, x_Z) * p(x_Z) = p(x_X, x_Z) * p(x_Y, x_Z)` for all configurations of `X`, `Y`,
`Z`, where `p(·)` are marginal masses. -/
def CondIndep (p : FiniteDist (∀ v, α v)) (X Y Z : Finset V) : Prop :=
  p.CondIndepFun (X.restrict (π := α)) (Y.restrict (π := α)) (Z.restrict (π := α))

variable {p : FiniteDist (∀ v, α v)} {X Y Z W : Finset V}

/-- Symmetry. -/
theorem CondIndep.symm (h : p.CondIndep X Y Z) : p.CondIndep Y X Z := CondIndepFun.symm h

theorem condIndep_comm : p.CondIndep X Y Z ↔ p.CondIndep Y X Z :=
  ⟨CondIndep.symm, CondIndep.symm⟩

/-- Conditional independence passes to subsets of the second set. -/
theorem CondIndep.mono_right {Y' : Finset V} (h : p.CondIndep X Y Z) (hY : Y' ⊆ Y) :
    p.CondIndep X Y' Z :=
  CondIndepFun.of_right h (Finset.restrict₂ hY) fun _ => rfl

/-- Conditional independence passes to subsets of the first set. -/
theorem CondIndep.mono_left {X' : Finset V} (h : p.CondIndep X Y Z) (hX : X' ⊆ X) :
    p.CondIndep X' Y Z :=
  (h.symm.mono_right hX).symm

/-- Decomposition: `X ⫫ Y ∪ W | Z` implies `X ⫫ Y | Z`. -/
theorem CondIndep.decomp (h : p.CondIndep X (Y ∪ W) Z) : p.CondIndep X Y Z :=
  h.mono_right subset_union_left

/-- Weak union: `X ⫫ Y ∪ W | Z` implies `X ⫫ Y | Z ∪ W`. -/
theorem CondIndep.weak_union (h : p.CondIndep X (Y ∪ W) Z) : p.CondIndep X Y (Z ∪ W) := by
  have h' : p.CondIndepFun (X.restrict (π := α)) (fun x => (Y.restrict x, W.restrict x))
      (Z.restrict (π := α)) :=
    CondIndepFun.of_right h (fun e => (Finset.restrict₂ subset_union_left e,
      Finset.restrict₂ subset_union_right e)) fun _ => rfl
  exact h'.weak_union.of_cond (fun cd => (Finset.restrict₂ subset_union_left cd,
      Finset.restrict₂ subset_union_right cd))
    (fun cd => glue Z W cd.1 cd.2) (fun _ => rfl) (fun x => restrict_union_eq_glue Z W x)

/-- Contraction: `X ⫫ Y | Z` and `X ⫫ W | Z ∪ Y` imply `X ⫫ Y ∪ W | Z`. -/
theorem CondIndep.contraction (h1 : p.CondIndep X Y Z) (h2 : p.CondIndep X W (Z ∪ Y)) :
    p.CondIndep X (Y ∪ W) Z := by
  have h2' : p.CondIndepFun (X.restrict (π := α)) (W.restrict (π := α))
      (fun x => (Y.restrict x, Z.restrict x)) :=
    CondIndepFun.of_cond h2 (fun bc => glue Z Y bc.2 bc.1)
      (fun e => (Finset.restrict₂ subset_union_right e, Finset.restrict₂ subset_union_left e))
      (fun x => restrict_union_eq_glue Z Y x) (fun _ => rfl)
  exact (CondIndepFun.contraction h1 h2').of_right (fun bd => glue Y W bd.1 bd.2)
    fun x => restrict_union_eq_glue Y W x

/-- Intersection: for a strictly positive distribution and pairwise disjoint `Y`, `Z`, `W`,
`X ⫫ Y | Z ∪ W` and `X ⫫ W | Z ∪ Y` imply `X ⫫ Y ∪ W | Z`. Positivity cannot be dropped
(`FiniteDist.not_condIndep_intersection`), and neither can disjointness: with `Y = W` the two
hypotheses hold trivially. -/
theorem CondIndep.intersection (hp : ∀ x, 0 < p x) (hYZ : Disjoint Y Z) (hYW : Disjoint Y W)
    (hZW : Disjoint Z W) (h1 : p.CondIndep X Y (Z ∪ W)) (h2 : p.CondIndep X W (Z ∪ Y)) :
    p.CondIndep X (Y ∪ W) Z := by
  obtain ⟨x₀⟩ := p.nonempty
  have h1' : p.CondIndepFun (X.restrict (π := α)) (Y.restrict (π := α))
      (fun x => (Z.restrict x, W.restrict x)) :=
    CondIndepFun.of_cond h1 (fun cd => glue Z W cd.1 cd.2)
      (fun e => (Finset.restrict₂ subset_union_left e, Finset.restrict₂ subset_union_right e))
      (fun x => restrict_union_eq_glue Z W x) (fun _ => rfl)
  have h2' : p.CondIndepFun (X.restrict (π := α)) (W.restrict (π := α))
      (fun x => (Z.restrict x, Y.restrict x)) :=
    CondIndepFun.of_cond h2 (fun cb => glue Z Y cb.1 cb.2)
      (fun e => (Finset.restrict₂ subset_union_left e, Finset.restrict₂ subset_union_right e))
      (fun x => restrict_union_eq_glue Z Y x) (fun _ => rfl)
  have hpos : ∀ b c d, 0 < p.probOf (fun x => Y.restrict x = b ∧ Z.restrict x = c ∧
      W.restrict x = d) := by
    intro b c d
    obtain ⟨x, hb, hc, hd⟩ := exists_restrict_eq hYZ hYW hZW x₀ b c d
    exact (hp x).trans_le (p.le_probOf x ⟨hb, hc, hd⟩)
  exact (CondIndepFun.intersection hpos h1' h2').of_right (fun bd => glue Y W bd.1 bd.2)
    fun x => restrict_union_eq_glue Y W x

/-- The joint probability that a configuration agrees with `x` on `X`, `Y` and `Z` is the
marginal mass at `x` on `X ∪ Y ∪ Z`. -/
theorem probOf_restrict_eq_margAt (x : ∀ v, α v) :
    p.probOf (fun y => X.restrict y = X.restrict x ∧ Y.restrict y = Y.restrict x ∧
      Z.restrict y = Z.restrict x) = p.margAt (X ∪ Y ∪ Z) x := by
  rw [margAt_eq_probOf]
  refine p.probOf_congr fun y => ?_
  simp only [restrict_eq_restrict_iff, mem_union, or_imp, forall_and, and_assoc]

theorem probOf_restrict_eq_margAt₂ (x : ∀ v, α v) :
    p.probOf (fun y => X.restrict y = X.restrict x ∧ Z.restrict y = Z.restrict x) =
      p.margAt (X ∪ Z) x := by
  rw [margAt_eq_probOf]
  refine p.probOf_congr fun y => ?_
  simp only [restrict_eq_restrict_iff, mem_union, or_imp, forall_and]

theorem probOf_restrict_eq_margAt₁ (x : ∀ v, α v) :
    p.probOf (fun y => Z.restrict y = Z.restrict x) = p.margAt Z x := by
  rw [margAt_eq_probOf]
  exact p.probOf_congr fun y => restrict_eq_restrict_iff

/-- Conditional independence in cylinder form, with full configurations:
`p(x_{X ∪ Y ∪ Z}) * p(x_Z) = p(x_{X ∪ Z}) * p(x_{Y ∪ Z})`. -/
theorem CondIndep.margAt_mul (h : p.CondIndep X Y Z) (x : ∀ v, α v) :
    p.margAt (X ∪ Y ∪ Z) x * p.margAt Z x = p.margAt (X ∪ Z) x * p.margAt (Y ∪ Z) x := by
  have := h (X.restrict x) (Y.restrict x) (Z.restrict x)
  rwa [probOf_restrict_eq_margAt, probOf_restrict_eq_margAt₁, probOf_restrict_eq_margAt₂,
    probOf_restrict_eq_margAt₂] at this

/-- For pairwise disjoint sets, the cylinder form characterizes conditional independence. -/
theorem condIndep_iff_margAt_mul (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) :
    p.CondIndep X Y Z ↔ ∀ x, p.margAt (X ∪ Y ∪ Z) x * p.margAt Z x =
      p.margAt (X ∪ Z) x * p.margAt (Y ∪ Z) x := by
  refine ⟨fun h => h.margAt_mul, fun h a b c => ?_⟩
  obtain ⟨x₀⟩ := p.nonempty
  obtain ⟨x, rfl, rfl, rfl⟩ := exists_restrict_eq hXY hXZ hYZ x₀ a b c
  rw [probOf_restrict_eq_margAt, probOf_restrict_eq_margAt₁, probOf_restrict_eq_margAt₂,
    probOf_restrict_eq_margAt₂]
  exact h x

/-- The factorization criterion in cylinder form, for pairwise disjoint sets: if the marginal
mass on `X ∪ Y ∪ Z` is `f x * g x` with `f` depending only on the coordinates in `X ∪ Z` and `g`
only on those in `Y ∪ Z`, then `X ⫫ Y | Z`. -/
theorem condIndep_of_margAt_eq_mul (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (f g : (∀ v, α v) → ℝ)
    (hf : ∀ x x', (∀ v ∈ X ∪ Z, x v = x' v) → f x = f x')
    (hg : ∀ x x', (∀ v ∈ Y ∪ Z, x v = x' v) → g x = g x')
    (h : ∀ x, p.margAt (X ∪ Y ∪ Z) x = f x * g x) : p.CondIndep X Y Z := by
  obtain ⟨x₀⟩ := p.nonempty
  refine (condIndepFun_iff_exists_mul).2 ⟨fun a c => f (override X a (override Z c x₀)),
    fun b c => g (override Y b (override Z c x₀)), fun a b c => ?_⟩
  obtain ⟨x, rfl, rfl, rfl⟩ := exists_restrict_eq hXY hXZ hYZ x₀ a b c
  rw [probOf_restrict_eq_margAt, h x]
  congr 1
  · refine hf _ _ fun v hv => ?_
    by_cases hvX : v ∈ X
    · rw [override_of_mem _ _ hvX]
      rfl
    · have hvZ : v ∈ Z := (mem_union.1 hv).resolve_left hvX
      rw [override_of_notMem _ _ hvX, override_of_mem _ _ hvZ]
      rfl
  · refine hg _ _ fun v hv => ?_
    by_cases hvY : v ∈ Y
    · rw [override_of_mem _ _ hvY]
      rfl
    · have hvZ : v ∈ Z := (mem_union.1 hv).resolve_left hvY
      rw [override_of_notMem _ _ hvY, override_of_mem _ _ hvZ]
      rfl

end Coordinates

/-- Intersection fails for random variables when only the masses are positive: under the uniform
distribution on `Bool`, with `X = Y = W` the identity and `Z` constant, `X ⫫ Y | (Z, W)` and
`X ⫫ W | (Z, Y)` hold but `X ⫫ (Y, W) | Z` fails. Here the joint law of `(Y, Z, W)` is not
positive. -/
theorem not_condIndepFun_intersection :
    ∃ (p : FiniteDist Bool) (X Y W : Bool → Bool) (Z : Bool → Unit), (∀ ω, 0 < p ω) ∧
      p.CondIndepFun X Y (fun ω => (Z ω, W ω)) ∧ p.CondIndepFun X W (fun ω => (Z ω, Y ω)) ∧
      ¬ p.CondIndepFun X (fun ω => (Y ω, W ω)) Z := by
  refine ⟨uniform, id, id, id, fun _ => (), fun ω => by simp, ?_, ?_, ?_⟩
  · rintro a b ⟨c, d⟩
    cases a <;> cases b <;> cases d <;> simp [probOf, prob]
  · rintro a b ⟨c, d⟩
    cases a <;> cases b <;> cases d <;> simp [probOf, prob]
  · intro h
    have := h true (false, false) ()
    simp [probOf, prob] at this

/-- Three perfectly correlated fair bits: the law of `(b, b, b)` for a uniform bit `b`. -/
noncomputable def copies3 : FiniteDist (Fin 3 → Bool) := uniform.map fun b _ => b

theorem copies3_apply (x : Fin 3 → Bool) :
    copies3 x = if x 0 = x 2 ∧ x 1 = x 2 then 1 / 2 else 0 := by
  have hconst : ∀ b : Bool, ((fun _ => b) = x) ↔ (x 0 = b ∧ x 1 = b ∧ x 2 = b) := by
    intro b
    constructor
    · rintro rfl
      simp
    · rintro ⟨h0, h1, h2⟩
      funext i
      fin_cases i <;> simp [h0, h1, h2]
  rw [copies3, map_apply, sum_filter, Fintype.sum_bool]
  simp only [hconst, uniform_apply, Fintype.card_bool]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> norm_num

/-- Intersection fails for coordinate sets without positivity: for three perfectly correlated
fair bits, `{0} ⫫ {1} | {2}` and `{0} ⫫ {2} | {1}` hold but `{0} ⫫ {1, 2}` fails. -/
theorem not_condIndep_intersection :
    copies3.CondIndep {0} {1} (∅ ∪ {2}) ∧ copies3.CondIndep {0} {2} (∅ ∪ {1}) ∧
      ¬ copies3.CondIndep {0} ({1} ∪ {2}) ∅ := by
  have huniv : ∀ x, copies3.margAt (univ : Finset (Fin 3)) x = copies3 x := margAt_univ _
  refine ⟨?_, ?_, ?_⟩
  · refine condIndep_of_margAt_eq_mul (by decide) (by decide) (by decide)
      (fun x => if x 0 = x 2 then 1 / 2 else 0) (fun x => if x 1 = x 2 then 1 else 0)
      (fun x x' h => by simp [h 0 (by decide), h 2 (by decide)])
      (fun x x' h => by simp [h 1 (by decide), h 2 (by decide)]) fun x => ?_
    rw [show ({0} ∪ {1} ∪ (∅ ∪ {2}) : Finset (Fin 3)) = univ by decide, huniv, copies3_apply]
    split_ifs <;> simp_all
  · refine condIndep_of_margAt_eq_mul (by decide) (by decide) (by decide)
      (fun x => if x 0 = x 1 then 1 / 2 else 0) (fun x => if x 2 = x 1 then 1 else 0)
      (fun x x' h => by simp [h 0 (by decide), h 1 (by decide)])
      (fun x x' h => by simp [h 2 (by decide), h 1 (by decide)]) fun x => ?_
    rw [show ({0} ∪ {2} ∪ (∅ ∪ {1}) : Finset (Fin 3)) = univ by decide, huniv, copies3_apply]
    split_ifs <;> simp_all
  · intro h
    have key := h.margAt_mul ![true, false, false]
    have hz : copies3 ![true, false, false] = 0 := by
      rw [copies3_apply]
      simp
    rw [show ({0} ∪ ({1} ∪ {2}) ∪ ∅ : Finset (Fin 3)) = univ by decide, huniv, hz] at key
    have h1 : 1 / 2 ≤ copies3.margAt ({0} ∪ ∅) ![true, false, false] := by
      have := copies3.le_probOf (P := fun y => ∀ v ∈ ({0} ∪ ∅ : Finset (Fin 3)),
        y v = ![true, false, false] v) (fun _ => true) (by decide)
      rwa [copies3_apply] at this
    have h2 : 1 / 2 ≤ copies3.margAt ({1} ∪ {2} ∪ ∅) ![true, false, false] := by
      have := copies3.le_probOf (P := fun y => ∀ v ∈ ({1} ∪ {2} ∪ ∅ : Finset (Fin 3)),
        y v = ![true, false, false] v) (fun _ => false) (by decide)
      rwa [copies3_apply] at this
    simp only [union_empty, zero_mul] at key h1 h2
    nlinarith

end FiniteDist

end CausalInference
