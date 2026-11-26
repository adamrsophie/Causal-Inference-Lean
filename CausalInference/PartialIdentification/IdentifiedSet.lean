/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Subsingleton

/-!
# Identified sets and point identification

A generic, probability-free framework for partial identification in the sense of Manski.
A type `M` of models carries an observation map `obs : M → O` (the observed data law, or any
observable summary of it) and a parameter `θ : M → Θ`. A set `S : Set M` collects the models
satisfying the maintained assumptions.

## Main definitions

* `CausalInference.identifiedSet S obs θ o`: the set `{θ m | m ∈ S, obs m = o}` of parameter
  values compatible with the observation `o` and the assumptions `S`.
* `CausalInference.PointIdentified S obs θ`: any two models in `S` with equal observations have
  equal parameters.

## Main results

* `pointIdentified_iff_subsingleton`: point identification holds if and only if every
  identified set has at most one element.
* `pointIdentified_iff_exists_factor`: point identification holds if and only if `θ` factors
  through `obs` on `S` (for a nonempty parameter type).
* `identifiedSet_eq_singleton`: under point identification the identified set at an attainable
  observation is a singleton.
* `identifiedSet_mono`: stronger assumptions give a smaller identified set.
* `identifiedSet_inter_subset`: the identified set under a conjunction of assumptions is
  contained in the intersection of the identified sets.
* `not_pointIdentified_iff`: non-identification is witnessed by two models in `S` with equal
  observations and different parameters.

## References

* C. F. Manski, *Partial Identification of Probability Distributions*, Springer, 2003.
-/

@[expose] public section

namespace CausalInference

universe u v w

variable {M : Type u} {O : Type v} {Θ : Type w}

/-- The identified set of the parameter `θ` at the observed value `o` under the maintained
assumptions `S`: all values `θ m` for models `m ∈ S` whose observation `obs m` equals `o`. -/
def identifiedSet (S : Set M) (obs : M → O) (θ : M → Θ) (o : O) : Set Θ :=
  θ '' {m | m ∈ S ∧ obs m = o}

/-- The parameter `θ` is point identified on the model class `S` from the observation `obs`:
any two models of `S` that produce the same observation have the same parameter value. -/
def PointIdentified (S : Set M) (obs : M → O) (θ : M → Θ) : Prop :=
  ∀ m ∈ S, ∀ m' ∈ S, obs m = obs m' → θ m = θ m'

variable {S S' : Set M} {obs : M → O} {θ : M → Θ}

@[simp]
theorem mem_identifiedSet {o : O} {t : Θ} :
    t ∈ identifiedSet S obs θ o ↔ ∃ m ∈ S, obs m = o ∧ θ m = t := by
  simp [identifiedSet, and_assoc]

/-- A model in `S` contributes its parameter value to the identified set at its own
observation. -/
theorem mem_identifiedSet_self {m : M} (hm : m ∈ S) : θ m ∈ identifiedSet S obs θ (obs m) :=
  mem_identifiedSet.2 ⟨m, hm, rfl, rfl⟩

/-- Point identification holds if and only if every identified set has at most one element. -/
theorem pointIdentified_iff_subsingleton :
    PointIdentified S obs θ ↔ ∀ o, (identifiedSet S obs θ o).Subsingleton := by
  constructor
  · rintro h o _ ⟨m, ⟨hm, rfl⟩, rfl⟩ _ ⟨m', ⟨hm', hmo⟩, rfl⟩
    exact h m hm m' hm' hmo.symm
  · intro h m hm m' hm' hobs
    exact h (obs m) (mem_identifiedSet_self hm) (hobs ▸ mem_identifiedSet_self hm')

/-- Under point identification, the identified set at the observation of a model `m ∈ S` is
exactly the singleton `{θ m}`. -/
theorem identifiedSet_eq_singleton (h : PointIdentified S obs θ) {m : M} (hm : m ∈ S) :
    identifiedSet S obs θ (obs m) = {θ m} :=
  (pointIdentified_iff_subsingleton.1 h (obs m)).eq_singleton_of_mem
    (mem_identifiedSet_self hm)

/-- Point identification holds if and only if the parameter factors through the observation on
the model class: there is `f : O → Θ` with `θ m = f (obs m)` for every `m ∈ S`. The parameter
type is assumed nonempty; without this the factor `f` may fail to exist when `S` is empty and
`O` is not. -/
theorem pointIdentified_iff_exists_factor [Nonempty Θ] :
    PointIdentified S obs θ ↔ ∃ f : O → Θ, ∀ m ∈ S, θ m = f (obs m) := by
  classical
  constructor
  · intro h
    refine ⟨fun o => if hex : ∃ m ∈ S, obs m = o then θ hex.choose else Classical.arbitrary Θ,
      fun m hm => ?_⟩
    have hex : ∃ m' ∈ S, obs m' = obs m := ⟨m, hm, rfl⟩
    simp only
    rw [dite_eq_left hex]
    exact h m hm _ hex.choose_spec.1 hex.choose_spec.2.symm
  · rintro ⟨f, hf⟩ m hm m' hm' hobs
    rw [hf m hm, hf m' hm', hobs]

/-- Stronger maintained assumptions (a smaller model class) give a smaller identified set. -/
theorem identifiedSet_mono (h : S' ⊆ S) (o : O) :
    identifiedSet S' obs θ o ⊆ identifiedSet S obs θ o :=
  Set.image_mono fun _ hm => ⟨h hm.1, hm.2⟩

/-- Point identification is inherited by any smaller model class. -/
theorem PointIdentified.mono (h : PointIdentified S obs θ) (hS : S' ⊆ S) :
    PointIdentified S' obs θ :=
  fun m hm m' hm' hobs => h m (hS hm) m' (hS hm') hobs

/-- The identified set under the conjunction of two assumptions is contained in the
intersection of the two identified sets. -/
theorem identifiedSet_inter_subset (o : O) :
    identifiedSet (S ∩ S') obs θ o ⊆ identifiedSet S obs θ o ∩ identifiedSet S' obs θ o :=
  Set.subset_inter (identifiedSet_mono Set.inter_subset_left o)
    (identifiedSet_mono Set.inter_subset_right o)

/-- The parameter fails to be point identified if and only if two models of `S` produce the same
observation but different parameter values. -/
theorem not_pointIdentified_iff :
    ¬ PointIdentified S obs θ ↔ ∃ m ∈ S, ∃ m' ∈ S, obs m = obs m' ∧ θ m ≠ θ m' := by
  simp [PointIdentified]

/-- Two distinct parameter values in the same identified set witness non-identification. -/
theorem not_pointIdentified_of_mem {o : O} {t t' : Θ} (ht : t ∈ identifiedSet S obs θ o)
    (ht' : t' ∈ identifiedSet S obs θ o) (hne : t ≠ t') : ¬ PointIdentified S obs θ :=
  fun h => hne (pointIdentified_iff_subsingleton.1 h o ht ht')

end CausalInference
