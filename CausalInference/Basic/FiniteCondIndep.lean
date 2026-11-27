/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.FiniteDistribution
public import Mathlib.Probability.Independence.Conditional

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
  decomposition, weak union, contraction. The random variables may take values in arbitrary
  types with decidable equality; sums run over the finitely many values actually taken.
* The intersection property under positivity. For random variables the hypothesis is positivity
  of the joint law of the variables `Y`, `Z`, `W` (positivity of the masses is not enough,
  `FiniteDist.not_condIndepFun_intersection`); for coordinate sets it is positivity of the masses
  together with `Y ∩ W ⊆ Z` (`FiniteDist.CondIndep.intersection`).
* `FiniteDist.condIndepFun_iff_exists_mul`: the factorization criterion,
  `P(X = a, Y = b, Z = c) = f a c * g b c`.
* `FiniteDist.condIndepFun_of_forall`: the product identity at the values actually taken implies
  conditional independence.
* `FiniteDist.CondIndep.margAt_mul` and `FiniteDist.condIndep_iff_margAt_mul`: for arbitrary
  finsets, conditional independence is the cylinder form
  `p(x_{X ∪ Y ∪ Z}) * p(x_Z) = p(x_{X ∪ Z}) * p(x_{Y ∪ Z})` with full configurations `x`;
  `FiniteDist.condIndep_empty_iff`, unconditional independence as a product of marginals.
* `FiniteDist.condIndep_iff_exists_margAt_eq_mul`: the factorization criterion in that form, for
  `X ∩ Y ⊆ Z`; `FiniteDist.not_condIndep_of_margAt_eq_mul` shows that the overlap condition is
  needed.
* `FiniteDist.condIndep_sdiff_iff`: coordinates in the conditioning set are irrelevant,
  `X \ Z ⫫ Y \ Z | Z ↔ X ⫫ Y | Z`; `FiniteDist.condIndep_of_subset_left`, `X ⊆ Z → X ⫫ Y | Z`.

* `FiniteDist.condIndepFun_iff_condIndepFun_toMeasure`: the bridge to Mathlib's
  `ProbabilityTheory.CondIndepFun` for the measure `FiniteDist.toMeasure`, through the formula
  `FiniteDist.condExp_indicator_ae_eq` for conditional expectations given a discrete variable.

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
theorem CondIndepFun.of_right {γ' : Type*} [DecidableEq γ'] {Y' : Ω → γ'}
    (h : p.CondIndepFun X Y Z) (g : γ → γ') (hY : ∀ ω, Y' ω = g (Y ω)) :
    p.CondIndepFun X Y' Z := by
  intro a b' c
  have e1 : p.probOf (fun ω => X ω = a ∧ Y' ω = b' ∧ Z ω = c) =
      ∑ b ∈ (univ.image Y).filter (fun b => g b = b'),
        p.probOf (fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c) := by
    rw [p.probOf_eq_sum Y ((univ.image Y).filter fun b => g b = b')
      (fun ω hω => by simp [← hY, hω.2.1])]
    refine sum_congr rfl fun b hb => p.probOf_congr fun ω => ?_
    replace hb := (mem_filter.1 hb).2
    rw [hY]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨h1, h4, h3⟩
    · rintro ⟨h1, h4, h3⟩
      exact ⟨⟨h1, h4 ▸ hb, h3⟩, h4⟩
  have e2 : p.probOf (fun ω => Y' ω = b' ∧ Z ω = c) =
      ∑ b ∈ (univ.image Y).filter (fun b => g b = b'),
        p.probOf (fun ω => Y ω = b ∧ Z ω = c) := by
    rw [p.probOf_eq_sum Y ((univ.image Y).filter fun b => g b = b')
      (fun ω hω => by simp [← hY, hω.1])]
    refine sum_congr rfl fun b hb => p.probOf_congr fun ω => ?_
    replace hb := (mem_filter.1 hb).2
    rw [hY]
    constructor
    · rintro ⟨⟨-, h3⟩, h4⟩
      exact ⟨h4, h3⟩
    · rintro ⟨h4, h3⟩
      exact ⟨⟨h4 ▸ hb, h3⟩, h4⟩
  rw [e1, e2, sum_mul, mul_sum]
  exact sum_congr rfl fun b _ => h a b c

/-- Conditional independence passes to functions of the first variable. -/
theorem CondIndepFun.of_left {β' : Type*} [DecidableEq β'] {X' : Ω → β'}
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
theorem CondIndepFun.decomp
    (h : p.CondIndepFun X (fun ω => (Y ω, W ω)) Z) : p.CondIndepFun X Y Z :=
  h.of_right Prod.fst fun _ => rfl

/-- Weak union: independence from a pair `(Y, W)` given `Z` implies independence from `Y` given
`(Z, W)`. -/
theorem CondIndepFun.weak_union
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
theorem CondIndepFun.intersection
    (hpos : ∀ b c d, 0 < p.probOf (fun ω => Y ω = b ∧ Z ω = c ∧ W ω = d))
    (h1 : p.CondIndepFun X Y (fun ω => (Z ω, W ω)))
    (h2 : p.CondIndepFun X W (fun ω => (Z ω, Y ω))) :
    p.CondIndepFun X (fun ω => (Y ω, W ω)) Z := by
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
    rw [p.probOf_eq_sum_image (P := fun ω => X ω = a ∧ Z ω = c) W,
      p.probOf_eq_sum_image (P := fun ω => Z ω = c) W, sum_mul, mul_sum]
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
theorem condIndepFun_iff_exists_mul :
    p.CondIndepFun X Y Z ↔ ∃ (f : β → δ → ℝ) (g : γ → δ → ℝ),
      ∀ a b c, p.probOf (fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c) = f a c * g b c := by
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
    have hac : ∀ a, p.probOf (fun ω => X ω = a ∧ Z ω = c) =
        f a c * ∑ b' ∈ univ.image Y, g b' c := by
      intro a
      rw [p.probOf_eq_sum_image Y, mul_sum]
      refine sum_congr rfl fun b' _ => ?_
      rw [← hfg]
      exact p.probOf_congr fun ω => by tauto
    have hbc : p.probOf (fun ω => Y ω = b ∧ Z ω = c) = g b c * ∑ a' ∈ univ.image X, f a' c := by
      rw [p.probOf_eq_sum_image X, mul_sum]
      refine sum_congr rfl fun a' _ => ?_
      rw [mul_comm, ← hfg]
      exact p.probOf_congr fun ω => by tauto
    have hc : p.probOf (fun ω => Z ω = c) =
        (∑ a' ∈ univ.image X, f a' c) * ∑ b' ∈ univ.image Y, g b' c := by
      rw [p.probOf_eq_sum_image X, sum_mul]
      refine sum_congr rfl fun a' _ => ?_
      rw [← hac a']
      exact p.probOf_congr fun ω => and_comm
    rw [hfg, hac a, hbc, hc]
    ring

/-- Conditional independence passes to any function of the first variable and the conditioning
variable: `X ⫫ Y | Z` implies `φ(X, Z) ⫫ Y | Z`. -/
theorem CondIndepFun.of_left_cond {β' : Type*} [DecidableEq β'] (h : p.CondIndepFun X Y Z)
    {X' : Ω → β'} (φ : β → δ → β') (hX : ∀ ω, X' ω = φ (X ω) (Z ω)) :
    p.CondIndepFun X' Y Z := by
  obtain ⟨f, g, hfg⟩ := condIndepFun_iff_exists_mul.1 h
  refine condIndepFun_iff_exists_mul.2
    ⟨fun a' c => ∑ a ∈ (univ.image X).filter (fun a => φ a c = a'), f a c, g, fun a' b c => ?_⟩
  rw [p.probOf_eq_sum X ((univ.image X).filter fun a => φ a c = a') (fun ω hω => by
    simp [← hω.2.2, ← hX, hω.1]), sum_mul]
  refine sum_congr rfl fun a ha => ?_
  rw [← hfg]
  refine p.probOf_congr fun ω => ?_
  replace ha := (mem_filter.1 ha).2
  constructor
  · rintro ⟨⟨-, h2, h3⟩, h4⟩
    exact ⟨h4, h2, h3⟩
  · rintro ⟨h4, h2, h3⟩
    exact ⟨⟨by rw [hX, h4, h3, ha], h2, h3⟩, h4⟩

/-- Conditional independence passes to any function of the second variable and the conditioning
variable: `X ⫫ Y | Z` implies `X ⫫ ψ(Y, Z) | Z`. -/
theorem CondIndepFun.of_right_cond {γ' : Type*} [DecidableEq γ'] (h : p.CondIndepFun X Y Z)
    {Y' : Ω → γ'} (ψ : γ → δ → γ') (hY : ∀ ω, Y' ω = ψ (Y ω) (Z ω)) :
    p.CondIndepFun X Y' Z :=
  (h.symm.of_left_cond ψ hY).symm

variable (p) in
/-- The conditioning variable is conditionally independent of anything given itself. -/
theorem condIndepFun_cond_left : p.CondIndepFun Z Y Z := by
  intro a b c
  by_cases hac : a = c
  · subst hac
    rw [p.probOf_congr (P := fun ω => Z ω = a ∧ Y ω = b ∧ Z ω = a)
        (Q := fun ω => Y ω = b ∧ Z ω = a) (fun ω => by tauto),
      p.probOf_congr (P := fun ω => Z ω = a ∧ Z ω = a) (Q := fun ω => Z ω = a)
        (fun ω => and_self_iff), mul_comm]
  · rw [p.probOf_eq_zero (P := fun ω => Z ω = a ∧ Y ω = b ∧ Z ω = c)
        fun ω hω => hac (hω.1.symm.trans hω.2.2),
      p.probOf_eq_zero (P := fun ω => Z ω = a ∧ Z ω = c) fun ω hω => hac (hω.1.symm.trans hω.2),
      zero_mul, zero_mul]

/-- The product identity at the values actually taken suffices: if
`P(X = a, Y = b, Z = c) * P(Z = c) = P(X = a, Z = c) * P(Y = b, Z = c)` holds whenever
`(a, b, c) = (X ω, Y ω, Z ω)` for some outcome `ω`, then `X ⫫ Y | Z`. For a fixed `c`, the two
sides agree on realized pairs, the left side vanishes on the others, and both sides sum to
`P(Z = c) ^ 2` over all pairs of values, so they agree everywhere. -/
theorem condIndepFun_of_forall
    (h : ∀ ω, p.probOf (fun ω' => X ω' = X ω ∧ Y ω' = Y ω ∧ Z ω' = Z ω) *
        p.probOf (fun ω' => Z ω' = Z ω) =
      p.probOf (fun ω' => X ω' = X ω ∧ Z ω' = Z ω) * p.probOf (fun ω' => Y ω' = Y ω ∧ Z ω' = Z ω)) :
    p.CondIndepFun X Y Z := by
  intro a b c
  set F : β × γ → ℝ := fun ab =>
    p.probOf (fun ω => X ω = ab.1 ∧ Y ω = ab.2 ∧ Z ω = c) * p.probOf (fun ω => Z ω = c)
  set G : β × γ → ℝ := fun ab =>
    p.probOf (fun ω => X ω = ab.1 ∧ Z ω = c) * p.probOf (fun ω => Y ω = ab.2 ∧ Z ω = c)
  have hle : ∀ ab, F ab ≤ G ab := by
    rintro ⟨a, b⟩
    by_cases hω : ∃ ω, X ω = a ∧ Y ω = b ∧ Z ω = c
    · obtain ⟨ω, rfl, rfl, rfl⟩ := hω
      exact (h ω).le
    · push Not at hω
      simp only [F, G]
      rw [p.probOf_eq_zero fun ω h' => hω ω h'.1 h'.2.1 h'.2.2, zero_mul]
      exact mul_nonneg p.probOf_nonneg p.probOf_nonneg
  have hF : ∑ ab ∈ univ.image X ×ˢ univ.image Y, F ab =
      p.probOf (fun ω => Z ω = c) * p.probOf (fun ω => Z ω = c) := by
    simp only [F, sum_product, ← sum_mul]
    congr 1
    rw [p.probOf_eq_sum_image (P := fun ω => Z ω = c) X]
    refine sum_congr rfl fun a _ => ?_
    rw [p.probOf_eq_sum_image (P := fun ω => Z ω = c ∧ X ω = a) Y]
    exact sum_congr rfl fun b _ => p.probOf_congr fun ω => by tauto
  have hG : ∑ ab ∈ univ.image X ×ˢ univ.image Y, G ab =
      p.probOf (fun ω => Z ω = c) * p.probOf (fun ω => Z ω = c) := by
    have e1 : p.probOf (fun ω => Z ω = c) =
        ∑ a ∈ univ.image X, p.probOf (fun ω => X ω = a ∧ Z ω = c) := by
      rw [p.probOf_eq_sum_image (P := fun ω => Z ω = c) X]
      exact sum_congr rfl fun a _ => p.probOf_congr fun ω => and_comm
    have e2 : p.probOf (fun ω => Z ω = c) =
        ∑ b ∈ univ.image Y, p.probOf (fun ω => Y ω = b ∧ Z ω = c) := by
      rw [p.probOf_eq_sum_image (P := fun ω => Z ω = c) Y]
      exact sum_congr rfl fun b _ => p.probOf_congr fun ω => and_comm
    simp only [G, sum_product]
    rw [show p.probOf (fun ω => Z ω = c) * p.probOf (fun ω => Z ω = c) =
      (∑ a ∈ univ.image X, p.probOf (fun ω => X ω = a ∧ Z ω = c)) *
        ∑ b ∈ univ.image Y, p.probOf (fun ω => Y ω = b ∧ Z ω = c) by rw [← e1, ← e2],
      sum_mul_sum]
  by_cases hab : ∃ ω₁ ω₂, X ω₁ = a ∧ Y ω₂ = b
  · obtain ⟨ω₁, ω₂, rfl, rfl⟩ := hab
    exact (sum_eq_sum_iff_of_le fun ab _ => hle ab).1 (hF.trans hG.symm) (X ω₁, Y ω₂)
      (mem_product.2 ⟨mem_image_of_mem X (mem_univ _), mem_image_of_mem Y (mem_univ _)⟩)
  · push Not at hab
    by_cases ha : ∃ ω, X ω = a
    · obtain ⟨ω₁, hω₁⟩ := ha
      rw [p.probOf_eq_zero (P := fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c)
          fun ω hω => hab ω₁ ω hω₁ hω.2.1,
        p.probOf_eq_zero (P := fun ω => Y ω = b ∧ Z ω = c) fun ω hω => hab ω₁ ω hω₁ hω.1]
      simp
    · push Not at ha
      rw [p.probOf_eq_zero (P := fun ω => X ω = a ∧ Y ω = b ∧ Z ω = c) fun ω hω => ha ω hω.1,
        p.probOf_eq_zero (P := fun ω => X ω = a ∧ Z ω = c) fun ω hω => ha ω hω.1]
      simp

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

/-- Adding the conditioning coordinates to the first set preserves conditional independence. -/
theorem CondIndep.union_cond_left (h : p.CondIndep X Y Z) : p.CondIndep (X ∪ Z) Y Z :=
  CondIndepFun.of_left_cond h (glue X Z) fun x => restrict_union_eq_glue X Z x

/-- Adding the conditioning coordinates to the second set preserves conditional independence. -/
theorem CondIndep.union_cond_right (h : p.CondIndep X Y Z) : p.CondIndep X (Y ∪ Z) Z :=
  h.symm.union_cond_left.symm

/-- Coordinates in the conditioning set are irrelevant on either side:
`X ⫫ Y | Z` holds exactly when `X \ Z ⫫ Y \ Z | Z` does. -/
theorem condIndep_sdiff_iff : p.CondIndep (X \ Z) (Y \ Z) Z ↔ p.CondIndep X Y Z := by
  constructor
  · intro h
    have h' := h.union_cond_left.union_cond_right
    rw [sdiff_union_self_eq_union, sdiff_union_self_eq_union] at h'
    exact (h'.mono_left subset_union_left).mono_right subset_union_left
  · intro h
    exact (h.mono_left sdiff_subset).mono_right sdiff_subset

variable (p) in
/-- Coordinates contained in the conditioning set are conditionally independent of anything:
`X ⊆ Z` implies `X ⫫ Y | Z`. -/
theorem condIndep_of_subset_left (h : X ⊆ Z) : p.CondIndep X Y Z :=
  CondIndepFun.of_left (condIndepFun_cond_left p) (Finset.restrict₂ h) fun _ => rfl

variable (p) in
/-- `Y ⊆ Z` implies `X ⫫ Y | Z`. -/
theorem condIndep_of_subset_right (h : Y ⊆ Z) : p.CondIndep X Y Z :=
  (condIndep_of_subset_left p h).symm

variable (p) in
/-- The empty set of coordinates is conditionally independent of anything. -/
theorem condIndep_empty_left : p.CondIndep ∅ Y Z := condIndep_of_subset_left p (empty_subset Z)

variable (p) in
/-- Anything is conditionally independent of the empty set of coordinates. -/
theorem condIndep_empty_right : p.CondIndep X ∅ Z := condIndep_of_subset_right p (empty_subset Z)

/-- Intersection for pairwise disjoint `Y`, `Z`, `W`; the general form is
`FiniteDist.CondIndep.intersection`. -/
private theorem CondIndep.intersection_of_disjoint (hp : ∀ x, 0 < p x) (hYZ : Disjoint Y Z)
    (hYW : Disjoint Y W) (hZW : Disjoint Z W) (h1 : p.CondIndep X Y (Z ∪ W))
    (h2 : p.CondIndep X W (Z ∪ Y)) :
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

/-- Intersection: for a strictly positive distribution with `Y ∩ W ⊆ Z`,
`X ⫫ Y | Z ∪ W` and `X ⫫ W | Z ∪ Y` imply `X ⫫ Y ∪ W | Z`. Positivity cannot be dropped
(`FiniteDist.not_condIndep_intersection`), and neither can the overlap condition: with `Y = W`
outside `Z` the two hypotheses hold trivially. Overlaps of `Y` and `W` inside `Z` are harmless. -/
theorem CondIndep.intersection (hp : ∀ x, 0 < p x) (hYW : Y ∩ W ⊆ Z)
    (h1 : p.CondIndep X Y (Z ∪ W)) (h2 : p.CondIndep X W (Z ∪ Y)) :
    p.CondIndep X (Y ∪ W) Z := by
  have hYW' : Disjoint (Y \ Z) (W \ Z) := disjoint_left.2 fun v hY hW =>
    (mem_sdiff.1 hY).2 (hYW (mem_inter.2 ⟨(mem_sdiff.1 hY).1, (mem_sdiff.1 hW).1⟩))
  have h1' : p.CondIndep X (Y \ Z) (Z ∪ W \ Z) := by
    rw [union_sdiff_self_eq_union]
    exact h1.mono_right sdiff_subset
  have h2' : p.CondIndep X (W \ Z) (Z ∪ Y \ Z) := by
    rw [union_sdiff_self_eq_union]
    exact h2.mono_right sdiff_subset
  refine (CondIndep.intersection_of_disjoint hp sdiff_disjoint hYW' disjoint_sdiff h1'
    h2').union_cond_right.mono_right fun v hv => ?_
  simp only [mem_union, mem_sdiff] at hv ⊢
  tauto

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

/-- The cylinder form characterizes conditional independence, for arbitrary finsets `X`, `Y`,
`Z`: `X ⫫ Y | Z` iff `p(x_{X ∪ Y ∪ Z}) * p(x_Z) = p(x_{X ∪ Z}) * p(x_{Y ∪ Z})` for every full
configuration `x`. Configurations of `X`, `Y`, `Z` that disagree on an overlap are covered by
`FiniteDist.condIndepFun_of_forall`. -/
theorem condIndep_iff_margAt_mul :
    p.CondIndep X Y Z ↔ ∀ x, p.margAt (X ∪ Y ∪ Z) x * p.margAt Z x =
      p.margAt (X ∪ Z) x * p.margAt (Y ∪ Z) x := by
  refine ⟨fun h => h.margAt_mul, fun h => condIndepFun_of_forall fun x => ?_⟩
  rw [probOf_restrict_eq_margAt, probOf_restrict_eq_margAt₁, probOf_restrict_eq_margAt₂,
    probOf_restrict_eq_margAt₂]
  exact h x

/-- Unconditional independence is the product of the marginals:
`X ⫫ Y | ∅` iff `p(x_{X ∪ Y}) = p(x_X) * p(x_Y)` for every configuration `x`. No disjointness is
needed; for `X = Y` the statement says that the coordinates in `X` are almost surely constant. -/
theorem condIndep_empty_iff :
    p.CondIndep X Y ∅ ↔ ∀ x, p.margAt (X ∪ Y) x = p.margAt X x * p.margAt Y x := by
  simp only [condIndep_iff_margAt_mul, union_empty, margAt_empty, mul_one]

/-- The factorization criterion in cylinder form for pairwise disjoint sets; the general form is
`FiniteDist.condIndep_of_margAt_eq_mul`. -/
private theorem condIndep_of_margAt_eq_mul_of_disjoint (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
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

/-- The factorization criterion in cylinder form, for `X ∩ Y ⊆ Z`: if the marginal mass on
`X ∪ Y ∪ Z` is `f x * g x` with `f` depending only on the coordinates in `X ∪ Z` and `g` only on
those in `Y ∪ Z`, then `X ⫫ Y | Z`. The overlap condition cannot be dropped
(`FiniteDist.not_condIndep_of_margAt_eq_mul`). -/
theorem condIndep_of_margAt_eq_mul (hXY : X ∩ Y ⊆ Z) (f g : (∀ v, α v) → ℝ)
    (hf : ∀ x x', (∀ v ∈ X ∪ Z, x v = x' v) → f x = f x')
    (hg : ∀ x x', (∀ v ∈ Y ∪ Z, x v = x' v) → g x = g x')
    (h : ∀ x, p.margAt (X ∪ Y ∪ Z) x = f x * g x) : p.CondIndep X Y Z := by
  have hXY' : Disjoint (X \ Z) (Y \ Z) := disjoint_left.2 fun v hX hY =>
    (mem_sdiff.1 hX).2 (hXY (mem_inter.2 ⟨(mem_sdiff.1 hX).1, (mem_sdiff.1 hY).1⟩))
  rw [← condIndep_sdiff_iff]
  refine condIndep_of_margAt_eq_mul_of_disjoint hXY' sdiff_disjoint sdiff_disjoint f g ?_ ?_ ?_
  · rw [sdiff_union_self_eq_union]
    exact hf
  · rw [sdiff_union_self_eq_union]
    exact hg
  · intro x
    rw [show X \ Z ∪ Y \ Z ∪ Z = X ∪ Y ∪ Z by ext v; simp only [mem_union, mem_sdiff]; tauto]
    exact h x

/-- The converse of the factorization criterion, for arbitrary finsets: if `X ⫫ Y | Z`, the
marginal mass on `X ∪ Y ∪ Z` is `f x * g x` with `f` depending only on the coordinates in
`X ∪ Z` and `g` only on those in `Y ∪ Z` (take `f = p(x_{X ∪ Z}) / p(x_Z)`, zero where
`p(x_Z) = 0`, and `g = p(x_{Y ∪ Z})`). -/
theorem CondIndep.exists_margAt_eq_mul (h : p.CondIndep X Y Z) :
    ∃ f g : (∀ v, α v) → ℝ, (∀ x x', (∀ v ∈ X ∪ Z, x v = x' v) → f x = f x') ∧
      (∀ x x', (∀ v ∈ Y ∪ Z, x v = x' v) → g x = g x') ∧
      ∀ x, p.margAt (X ∪ Y ∪ Z) x = f x * g x := by
  refine ⟨fun x => if p.margAt Z x = 0 then 0 else p.margAt (X ∪ Z) x / p.margAt Z x,
    fun x => p.margAt (Y ∪ Z) x, fun x x' hxx' => ?_, fun x x' hxx' => p.margAt_congr _ hxx',
    fun x => ?_⟩
  · have hZ : p.margAt Z x = p.margAt Z x' :=
      p.margAt_congr _ fun v hv => hxx' v (mem_union_right _ hv)
    simp only [hZ, p.margAt_congr _ hxx']
  · dsimp only
    split_ifs with hZ
    · rw [zero_mul]
      exact le_antisymm ((p.margAt_anti subset_union_right x).trans_eq hZ) (p.margAt_nonneg _ _)
    · rw [div_mul_eq_mul_div, eq_div_iff hZ, h.margAt_mul x]

/-- **The factorization criterion in cylinder form**, for `X ∩ Y ⊆ Z`: `X ⫫ Y | Z` iff the
marginal mass on `X ∪ Y ∪ Z` is a product of a function of the coordinates in `X ∪ Z` and a
function of those in `Y ∪ Z`. -/
theorem condIndep_iff_exists_margAt_eq_mul (hXY : X ∩ Y ⊆ Z) :
    p.CondIndep X Y Z ↔ ∃ f g : (∀ v, α v) → ℝ,
      (∀ x x', (∀ v ∈ X ∪ Z, x v = x' v) → f x = f x') ∧
      (∀ x x', (∀ v ∈ Y ∪ Z, x v = x' v) → g x = g x') ∧
      ∀ x, p.margAt (X ∪ Y ∪ Z) x = f x * g x :=
  ⟨CondIndep.exists_margAt_eq_mul, fun ⟨f, g, hf, hg, h⟩ =>
    condIndep_of_margAt_eq_mul hXY f g hf hg h⟩

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
  · refine condIndep_of_margAt_eq_mul (by decide)
      (fun x => if x 0 = x 2 then 1 / 2 else 0) (fun x => if x 1 = x 2 then 1 else 0)
      (fun x x' h => by simp [h 0 (by decide), h 2 (by decide)])
      (fun x x' h => by simp [h 1 (by decide), h 2 (by decide)]) fun x => ?_
    rw [show ({0} ∪ {1} ∪ (∅ ∪ {2}) : Finset (Fin 3)) = univ by decide, huniv, copies3_apply]
    split_ifs <;> simp_all
  · refine condIndep_of_margAt_eq_mul (by decide)
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

/-- The factorization criterion `FiniteDist.condIndep_of_margAt_eq_mul` fails without
`X ∩ Y ⊆ Z`: for one fair bit, with `X = Y = {0}` and `Z = ∅`, the marginal mass on
`X ∪ Y ∪ Z` is `f x * g x` with `f = p(x_{0})` and `g = 1`, but the bit is not independent of
itself (`1 / 2 ≠ 1 / 4`). -/
theorem not_condIndep_of_margAt_eq_mul :
    ∃ (p : FiniteDist (Fin 1 → Bool)) (f g : (Fin 1 → Bool) → ℝ),
      (∀ x x', (∀ v ∈ ({0} ∪ ∅ : Finset (Fin 1)), x v = x' v) → f x = f x') ∧
      (∀ x x', (∀ v ∈ ({0} ∪ ∅ : Finset (Fin 1)), x v = x' v) → g x = g x') ∧
      (∀ x, p.margAt ({0} ∪ {0} ∪ ∅) x = f x * g x) ∧ ¬ p.CondIndep {0} {0} ∅ := by
  refine ⟨uniform, fun x => uniform.margAt {0} x, fun _ => 1,
    fun x x' h => uniform.margAt_congr _ fun v hv => h v (by simpa using hv),
    fun _ _ _ => rfl, fun x => by simp, fun h => ?_⟩
  have key := (condIndep_empty_iff.1 h) (fun _ => true)
  have h0 : (uniform : FiniteDist (Fin 1 → Bool)).margAt {0} (fun _ => true) = 1 / 2 := by
    rw [show ({0} : Finset (Fin 1)) = univ by decide, margAt_univ, uniform_apply]
    simp
  rw [union_self, h0] at key
  norm_num at key

/-! ### Bridge to Mathlib's conditional independence -/

section Mathlib

open MeasureTheory ProbabilityTheory

variable {Ω δ : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The real-valued measure of a set is its probability. -/
theorem measureReal_toMeasure (p : FiniteDist Ω) (B : Set Ω) [DecidablePred (· ∈ B)] :
    p.toMeasure.real B = p.probOf (· ∈ B) := by
  have h := p.toMeasure_real_finset (univ.filter (· ∈ B))
  rw [show ((univ.filter (· ∈ B) : Finset Ω) : Set Ω) = B by ext; simp] at h
  exact h

/-- A set integral against the associated measure is an expectation. -/
theorem setIntegral_toMeasure (p : FiniteDist Ω) (s : Set Ω) (f : Ω → ℝ) :
    ∫ ω in s, f ω ∂p.toMeasure = p.expect (s.indicator f) := by
  rw [← integral_indicator (Set.toFinite s).measurableSet, integral_toMeasure]

variable [MeasurableSpace δ] [DiscreteMeasurableSpace δ]

/-- The ratio `P(A ∩ {Z = Z ω}) / P(Z = Z ω)` as a function of the outcome `ω`: the conditional
probability of `A` given the value of `Z` at outcomes of positive mass. At an outcome whose fiber
`{Z = Z ω}` has probability zero the value is `0` by the convention `x / 0 = 0`; such outcomes form
a null set, and the results below use the function only almost everywhere. -/
noncomputable def condProbFun (p : FiniteDist Ω) (Z : Ω → δ) (A : Set Ω) : Ω → ℝ :=
  (fun c => p.toMeasure.real (A ∩ Z ⁻¹' {c}) / p.toMeasure.real (Z ⁻¹' {c})) ∘ Z

/-- **Conditional expectation given a discrete variable.** The conditional expectation of the
indicator of `A` given the sigma-algebra generated by `Z` is, almost everywhere,
`P(A ∩ {Z = Z ω}) / P(Z = Z ω)`. -/
theorem condExp_indicator_ae_eq (p : FiniteDist Ω) (Z : Ω → δ) (A : Set Ω) :
    p.toMeasure⟦A | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[p.toMeasure]
      p.condProbFun Z A := by
  classical
  have hZ : Measurable Z := fun s _ => (Set.toFinite _).measurableSet
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hZ.comap_le ?_ ?_ ?_ ?_
  · exact (integrable_const (1 : ℝ)).indicator (Set.toFinite A).measurableSet
  · intro s _ _; exact Integrable.of_finite.integrableOn
  · rintro s ⟨S, -, rfl⟩ _
    rw [setIntegral_toMeasure, setIntegral_toMeasure]
    simp only [expect, condProbFun, measureReal_toMeasure]
    rw [← sum_fiberwise_of_maps_to (t := univ.image Z) (g := Z)
        (fun ω _ => mem_image_of_mem Z (mem_univ ω)),
      ← sum_fiberwise_of_maps_to (t := univ.image Z) (g := Z)
        (fun ω _ => mem_image_of_mem Z (mem_univ ω))]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_filter, sum_filter]
    have hN : (p.probOf fun x => x ∈ Z ⁻¹' {c}) = ∑ i, if Z i = c then p i else 0 := by
      simp [probOf, prob, sum_filter]
    have hM : (p.probOf fun x => x ∈ A ∩ Z ⁻¹' {c}) =
        ∑ i, if Z i = c then p i * A.indicator (fun _ => (1 : ℝ)) i else 0 := by
      simp only [probOf, prob, sum_filter]
      refine sum_congr rfl fun i _ => ?_
      by_cases h1 : Z i = c <;> by_cases h2 : i ∈ A <;> simp [h1, h2]
    by_cases hc : c ∈ S
    · have e1 : ∀ i, (if Z i = c then p i * (Z ⁻¹' S).indicator ((fun c =>
          (p.probOf fun x => x ∈ A ∩ Z ⁻¹' {c}) / p.probOf fun x => x ∈ Z ⁻¹' {c}) ∘ Z) i
          else 0) = (if Z i = c then p i else 0) * ((p.probOf fun x => x ∈ A ∩ Z ⁻¹' {c}) /
            p.probOf fun x => x ∈ Z ⁻¹' {c}) := fun i => by
        by_cases h1 : Z i = c
        · simp [h1, hc]
        · simp [h1]
      have e2 : ∀ i, (if Z i = c then p i * (Z ⁻¹' S).indicator (A.indicator fun _ => 1) i
          else 0) = if Z i = c then p i * A.indicator (fun _ => (1 : ℝ)) i else 0 := fun i => by
        by_cases h1 : Z i = c
        · simp [h1, hc]
        · simp [h1]
      rw [sum_congr rfl fun i _ => e1 i, sum_congr rfl fun i _ => e2 i, ← sum_mul, ← hN, ← hM]
      rcases eq_or_ne (p.probOf fun x => x ∈ Z ⁻¹' {c}) 0 with h0 | h0
      · rw [h0, zero_mul]
        exact (le_antisymm ((p.probOf_mono fun x hx => hx.2).trans_eq h0) p.probOf_nonneg).symm
      · field_simp
    · refine (sum_eq_zero fun i _ => ?_).trans (sum_eq_zero fun i _ => ?_).symm
      · by_cases h1 : Z i = c
        · simp [h1, hc]
        · simp [h1]
      · by_cases h1 : Z i = c
        · simp [h1, hc]
        · simp [h1]
  · exact ((Measurable.of_discrete (f := fun c => p.toMeasure.real (A ∩ Z ⁻¹' {c}) /
      p.toMeasure.real (Z ⁻¹' {c}))).comp
        (comap_measurable Z)).stronglyMeasurable.aestronglyMeasurable

omit [MeasurableSpace δ] [DiscreteMeasurableSpace δ] in
open scoped Classical in
/-- `condProbFun` as a ratio of probabilities. -/
theorem condProbFun_eq [DecidableEq δ] (p : FiniteDist Ω) (Z : Ω → δ) (A : Set Ω) (ω : Ω) :
    p.condProbFun Z A ω =
      p.probOf (fun x => x ∈ A ∧ Z x = Z ω) / p.probOf (fun x => Z x = Z ω) := by
  classical
  simp only [condProbFun, Function.comp_apply, measureReal_toMeasure]
  congr 1 <;> exact p.probOf_congr fun x => by simp

/-- A point has nonzero measure exactly when its mass is positive. -/
theorem toMeasure_singleton_ne_zero (p : FiniteDist Ω) (ω : Ω) :
    p.toMeasure {ω} ≠ 0 ↔ 0 < p ω := by
  have h := p.toMeasure_apply_finset {ω}
  rw [coe_singleton] at h
  rw [h, Ne, ENNReal.ofReal_eq_zero, not_le]
  simp [prob]

omit [Fintype Ω] in
/-- Every function on a finite space with measurable singletons is measurable. -/
theorem measurable_of_fintype [Finite Ω] {α : Type*} [MeasurableSpace α] (f : Ω → α) :
    Measurable f :=
  fun _ _ => (Set.toFinite _).measurableSet

/-- **Bridge to Mathlib's conditional independence.** For a finite sample space with measurable
singletons (and a standard Borel structure, which Mathlib's definition requires), values with
measurable singletons, and a conditioning variable with a discrete sigma-algebra,
`p.CondIndepFun X Y Z` holds iff `X` and `Y` are conditionally independent given the
sigma-algebra generated by `Z` under `p.toMeasure`, in the sense of
`ProbabilityTheory.CondIndepFun`. Null values of `Z` impose nothing on either side. -/
theorem condIndepFun_iff_condIndepFun_toMeasure [StandardBorelSpace Ω] {β γ : Type*}
    [DecidableEq β] [DecidableEq γ] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ] [DecidableEq δ] (p : FiniteDist Ω)
    (X : Ω → β) (Y : Ω → γ) (Z : Ω → δ) :
    p.CondIndepFun X Y Z ↔ ProbabilityTheory.CondIndepFun (MeasurableSpace.comap Z inferInstance)
      (measurable_of_fintype Z).comap_le X Y p.toMeasure := by
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul (measurable_of_fintype X)
    (measurable_of_fintype Y)]
  have key : ∀ A B C : Set Ω,
      (p.toMeasure[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap Z inferInstance]
        =ᵐ[p.toMeasure] fun ω =>
        p.toMeasure[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap Z inferInstance] ω *
          p.toMeasure[C.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap Z inferInstance] ω) ↔
      ∀ ω, 0 < p ω → p.condProbFun Z A ω = p.condProbFun Z B ω * p.condProbFun Z C ω := by
    intro A B C
    refine (Filter.EventuallyEq.congr_left (condExp_indicator_ae_eq p Z A)).trans
      ((Filter.EventuallyEq.congr_right
        ((condExp_indicator_ae_eq p Z B).mul (condExp_indicator_ae_eq p Z C))).trans ?_)
    rw [Filter.EventuallyEq, ae_iff_of_countable]
    simp only [toMeasure_singleton_ne_zero, Pi.mul_apply]
  simp only [key, condProbFun_eq]
  -- the fiber mass is positive at a point of positive mass
  have hN : ∀ ω, 0 < p ω → 0 < p.probOf (fun x => Z x = Z ω) := fun ω hω =>
    hω.trans_le (p.le_probOf ω rfl)
  constructor
  · intro h s t _ _ ω hω
    have hN' := (hN ω hω).ne'
    have hs : ∀ c, p.probOf (fun x => x ∈ X ⁻¹' s ∧ Z x = c) =
        ∑ a ∈ (univ.image X).filter (· ∈ s), p.probOf (fun x => X x = a ∧ Z x = c) := by
      intro c
      rw [p.probOf_eq_sum X _ (fun x hx => mem_filter.2 ⟨mem_image_of_mem X (mem_univ x), hx.1⟩)]
      refine sum_congr rfl fun a ha => p.probOf_congr fun x => ⟨fun h => ⟨h.2, h.1.2⟩,
        fun h => ⟨⟨by rw [Set.mem_preimage, h.1]; exact (mem_filter.1 ha).2, h.2⟩, h.1⟩⟩
    have ht : ∀ c, p.probOf (fun x => x ∈ Y ⁻¹' t ∧ Z x = c) =
        ∑ b ∈ (univ.image Y).filter (· ∈ t), p.probOf (fun x => Y x = b ∧ Z x = c) := by
      intro c
      rw [p.probOf_eq_sum Y _ (fun x hx => mem_filter.2 ⟨mem_image_of_mem Y (mem_univ x), hx.1⟩)]
      refine sum_congr rfl fun b hb => p.probOf_congr fun x => ⟨fun h => ⟨h.2, h.1.2⟩,
        fun h => ⟨⟨by rw [Set.mem_preimage, h.1]; exact (mem_filter.1 hb).2, h.2⟩, h.1⟩⟩
    have hst : ∀ c, p.probOf (fun x => x ∈ X ⁻¹' s ∩ Y ⁻¹' t ∧ Z x = c) =
        ∑ a ∈ (univ.image X).filter (· ∈ s), ∑ b ∈ (univ.image Y).filter (· ∈ t),
          p.probOf (fun x => X x = a ∧ Y x = b ∧ Z x = c) := by
      intro c
      rw [p.probOf_eq_sum X _ (fun x hx => mem_filter.2 ⟨mem_image_of_mem X (mem_univ x),
        hx.1.1⟩)]
      refine sum_congr rfl fun a ha => ?_
      rw [p.probOf_eq_sum Y _ (fun x hx => mem_filter.2 ⟨mem_image_of_mem Y (mem_univ x),
        hx.1.1.2⟩)]
      refine sum_congr rfl fun b hb => p.probOf_congr fun x => ⟨fun h => ⟨h.1.2, h.2, h.1.1.2⟩,
        fun h => ⟨⟨⟨⟨by rw [Set.mem_preimage, h.1]; exact (mem_filter.1 ha).2,
          by rw [Set.mem_preimage, h.2.1]; exact (mem_filter.1 hb).2⟩, h.2.2⟩, h.1⟩, h.2.1⟩⟩
    have core : p.probOf (fun x => x ∈ X ⁻¹' s ∩ Y ⁻¹' t ∧ Z x = Z ω) *
        p.probOf (fun x => Z x = Z ω) = p.probOf (fun x => x ∈ X ⁻¹' s ∧ Z x = Z ω) *
          p.probOf (fun x => x ∈ Y ⁻¹' t ∧ Z x = Z ω) := by
      rw [hst, hs, ht, sum_mul, sum_mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun b _ => h a b (Z ω)
    rw [div_mul_div_comm, div_eq_div_iff hN' (mul_ne_zero hN' hN'), ← core, mul_assoc]
    congr!
  · intro h a b c
    by_cases hc : ∃ ω, Z ω = c ∧ 0 < p ω
    · obtain ⟨ω, rfl, hω⟩ := hc
      have hN' := (hN ω hω).ne'
      have key := h {a} {b} (measurableSet_singleton a) (measurableSet_singleton b) ω hω
      rw [div_mul_div_comm, div_eq_div_iff hN' (mul_ne_zero hN' hN'), ← mul_assoc] at key
      have key := mul_right_cancel₀ hN' key
      rw [p.probOf_congr (P := fun x => X x = a ∧ Y x = b ∧ Z x = Z ω)
          (Q := fun x => x ∈ X ⁻¹' {a} ∩ Y ⁻¹' {b} ∧ Z x = Z ω) (fun x => by simp [and_assoc]),
        p.probOf_congr (P := fun x => X x = a ∧ Z x = Z ω)
          (Q := fun x => x ∈ X ⁻¹' {a} ∧ Z x = Z ω) (fun x => by simp),
        p.probOf_congr (P := fun x => Y x = b ∧ Z x = Z ω)
          (Q := fun x => x ∈ Y ⁻¹' {b} ∧ Z x = Z ω) (fun x => by simp)]
      convert key using 3
    · push Not at hc
      have h0 : p.probOf (fun x => Z x = c) = 0 :=
        sum_eq_zero fun ω hω => le_antisymm (hc ω (mem_filter.1 hω).2) (p.nonneg ω)
      rw [h0, mul_zero, le_antisymm ((p.probOf_mono fun x hx => hx.2).trans_eq h0)
        p.probOf_nonneg, zero_mul]

end Mathlib

end FiniteDist

end CausalInference
