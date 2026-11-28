/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PartialIdentification.IdentifiedSet
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The separate effects of two drugs observed only in combination

NICE DSU TSD 17, Section 2.1, illustrates identification with two drugs: if data are only
available on the combined effect of the two drugs given together, the individual effect of
each drug cannot be separated; it can be estimated under a structural assumption such as that
the two drugs have effects of the same size. The document states this in words; the model
below is the simplest one that makes it precise.

A model `JointEffect.Model` has a baseline mean `a` and additive effects `b₁`, `b₂` of the two
drugs: the mean outcome under the regimen `(d₁, d₂)` is `a + b₁ 1{d₁} + b₂ 1{d₂}`. Only the
regimens "neither drug" and "both drugs" are observed, so the observation is the pair of mean
outcomes `(a, a + b₁ + b₂)`.

## Main results

* `JointEffect.not_pointIdentified_effects`: the pair `(b₁, b₂)` is not point identified; the
  models `(0, 1, 0)` and `(0, 0, 1)` give the same observation.
* `JointEffect.identifiedSet_effects`: at the observation `(o₀, o₁)` the identified set of
  `(b₁, b₂)` is the whole line `t₁ + t₂ = o₁ - o₀`.
* `JointEffect.pointIdentified_combined`: the combined effect `b₁ + b₂` is point identified.
* `JointEffect.pointIdentified_effects_of_equal`,
  `JointEffect.identifiedSet_effects_of_equal`: under the restriction `b₁ = b₂` both effects
  are point identified, equal to `(o₁ - o₀) / 2`.

The restriction carries the whole answer: under `b₁ = 2 b₂` instead, the same observation gives
other values (`JointEffect.effects_depend_on_restriction`).
-/

@[expose] public section

namespace CausalInference

namespace JointEffect

/-- A model of two drugs with additive effects: the baseline mean `a` and the effects `b₁`,
`b₂` of the first and second drug. -/
structure Model where
  /-- The mean outcome with neither drug. -/
  a : ℝ
  /-- The effect of the first drug. -/
  b₁ : ℝ
  /-- The effect of the second drug. -/
  b₂ : ℝ

namespace Model

/-- The mean outcome under the regimen `(d₁, d₂)`: `a + b₁ 1{d₁} + b₂ 1{d₂}`. -/
def mean (m : Model) (d₁ d₂ : Bool) : ℝ :=
  m.a + (if d₁ then m.b₁ else 0) + (if d₂ then m.b₂ else 0)

/-- The observation: the mean outcomes under the two regimens in the data, neither drug and
both drugs. -/
def obs (m : Model) : ℝ × ℝ := (m.mean false false, m.mean true true)

/-- The parameter: the pair of separate effects. -/
def effects (m : Model) : ℝ × ℝ := (m.b₁, m.b₂)

/-- The combined effect of the two drugs given together. -/
def combined (m : Model) : ℝ := m.b₁ + m.b₂

@[simp] theorem obs_eq (m : Model) : m.obs = (m.a, m.a + m.b₁ + m.b₂) := by
  simp [obs, mean]

end Model

open Model

/-- **The separate effects are not identified from the combination.** The models with effects
`(1, 0)` and `(0, 1)` and baseline `0` give the same observation `(0, 1)`. -/
theorem not_pointIdentified_effects : ¬ PointIdentified Set.univ obs effects := by
  rw [not_pointIdentified_iff]
  refine ⟨⟨0, 1, 0⟩, trivial, ⟨0, 0, 1⟩, trivial, ?_, ?_⟩
  · simp
  · simp [effects]

/-- **The identified set of the separate effects** at the observation `(o₀, o₁)` is the line
`t₁ + t₂ = o₁ - o₀`. -/
theorem identifiedSet_effects (o : ℝ × ℝ) :
    identifiedSet Set.univ obs effects o = {t | t.1 + t.2 = o.2 - o.1} := by
  ext t
  simp only [identifiedSet, Set.mem_image, Set.mem_ofPred_eq, Set.mem_univ, true_and]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [← hm]
    simp [effects]
    ring
  · intro ht
    refine ⟨⟨o.1, t.1, t.2⟩, ?_, rfl⟩
    rw [obs_eq]
    ext
    · rfl
    · simp only
      linarith

/-- The combined effect `b₁ + b₂` is point identified: it is the difference of the two
observed means. -/
theorem pointIdentified_combined : PointIdentified Set.univ obs combined := by
  rw [pointIdentified_iff_exists_factor]
  exact ⟨fun o => o.2 - o.1, fun m _ => by simp [combined]; ring⟩

/-- The models with effects of the same size. -/
def EqualEffects : Set Model := {m | m.b₁ = m.b₂}

/-- **Equal effects identify both effects**: each is half the difference of the two observed
means. -/
theorem effects_eq_of_equal {m : Model} (hm : m ∈ EqualEffects) :
    m.effects = ((m.obs.2 - m.obs.1) / 2, (m.obs.2 - m.obs.1) / 2) := by
  have h : m.b₁ = m.b₂ := hm
  simp only [effects, obs_eq, Prod.mk.injEq]
  constructor <;> linarith

/-- Under the restriction `b₁ = b₂` the separate effects are point identified. -/
theorem pointIdentified_effects_of_equal : PointIdentified EqualEffects obs effects := by
  rw [pointIdentified_iff_exists_factor]
  exact ⟨fun o => ((o.2 - o.1) / 2, (o.2 - o.1) / 2), fun m hm => effects_eq_of_equal hm⟩

/-- Under the restriction `b₁ = b₂` the identified set at the observation `(o₀, o₁)` is the
single point `((o₁ - o₀) / 2, (o₁ - o₀) / 2)`. -/
theorem identifiedSet_effects_of_equal (o : ℝ × ℝ) :
    identifiedSet EqualEffects obs effects o = {((o.2 - o.1) / 2, (o.2 - o.1) / 2)} := by
  ext t
  simp only [identifiedSet, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, ⟨hm, rfl⟩, rfl⟩
    exact effects_eq_of_equal hm
  · rintro rfl
    refine ⟨⟨o.1, (o.2 - o.1) / 2, (o.2 - o.1) / 2⟩, ⟨rfl, ?_⟩, rfl⟩
    rw [obs_eq]
    ext
    · rfl
    · simp only
      ring

/-- **The answer is carried by the restriction.** At the observation `(0, 1)` the restriction
`b₁ = b₂` gives the effects `(1/2, 1/2)`, while the restriction `b₁ = 2 b₂` gives `(2/3, 1/3)`;
both models reproduce the observation. -/
theorem effects_depend_on_restriction :
    (⟨0, 1 / 2, 1 / 2⟩ : Model).obs = (0, 1) ∧ (⟨0, 2 / 3, 1 / 3⟩ : Model).obs = (0, 1) ∧
      (⟨0, 1 / 2, 1 / 2⟩ : Model) ∈ EqualEffects ∧
      (⟨0, 2 / 3, 1 / 3⟩ : Model).b₁ = 2 * (⟨0, 2 / 3, 1 / 3⟩ : Model).b₂ ∧
      (⟨0, 1 / 2, 1 / 2⟩ : Model).effects ≠ (⟨0, 2 / 3, 1 / 3⟩ : Model).effects := by
  refine ⟨?_, ?_, rfl, by norm_num, ?_⟩
  · simp only [obs_eq]; norm_num
  · simp only [obs_eq]; norm_num
  · simp only [effects, ne_eq, Prod.mk.injEq]; norm_num

end JointEffect

end CausalInference
