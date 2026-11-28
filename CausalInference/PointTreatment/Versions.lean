/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Basic
public import CausalInference.Interference.Basic

/-!
# Point treatment: treatment versions and the consistency identity

A treatment may be delivered in several versions. Let `V` be the set of versions, each carrying
a treatment level `label v : Bool`, and let `R a i` be the outcome of unit `i` when the units
receive the version vector `a : ι → V`. Two restrictions make the unit level potential outcomes
`Y(0), Y(1)` well defined (Rubin 1980, the stable unit treatment value assumption; VanderWeele
2009, treatment variation irrelevance):

* **no interference**: `R a i` depends on `a` only through the version `a i` of unit `i`;
* **irrelevance of versions**: changing the version of unit `i` to another version with the same
  label does not change the outcome of `i`.

Together, and when every label is delivered by some version, they are equivalent to the
existence of potential outcomes `Y : Bool → ι → ℝ` with `R a i = Y (label (a i)) i`
(`exists_potentialOutcomes_iff`). The consistency identity follows: the outcome observed under
the realized version vector is the potential outcome of the treatment level received.

## Main definitions

* `NoInterferenceVersions R`: no interference at the level of versions.
* `VersionIrrelevance label R`: versions with the same label give the same outcome.
* `NoHiddenVersions label`: each treatment level is delivered by exactly one version.

## Main results

* `NoHiddenVersions.versionIrrelevance`, `NoHiddenVersions.surjective`: a single version per
  level makes the versions irrelevant.
* `exists_potentialOutcomes_iff`: the two restrictions hold exactly when the outcomes are given
  by unit level potential outcomes of the label.
* `exists_isObservedOutcome_of_versions`: the consistency identity `Y = Y(A)` for every realized
  version vector, in the form `IsObservedOutcome` of this library, with outcomes indexed by
  label vectors that satisfy `Interference.NoInterference`.

## References

* D. B. Rubin, comment on *Randomization analysis of experimental data: the Fisher
  randomization test* by D. Basu, Journal of the American Statistical Association 75 (1980).
* T. J. VanderWeele, *Concerning the consistency assumption in causal inference*, Epidemiology
  20 (2009).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

variable {ι V : Type*}

/-- No interference for outcomes indexed by version vectors: the outcome of unit `i` depends on
the version vector `a` only through the version `a i` received by `i`. -/
def NoInterferenceVersions (R : (ι → V) → ι → ℝ) : Prop :=
  ∀ (a a' : ι → V) (i : ι), a i = a' i → R a i = R a' i

/-- Irrelevance of versions: replacing the version of unit `i` by another version with the same
treatment label does not change the outcome of `i`. -/
def VersionIrrelevance [DecidableEq ι] (label : V → Bool) (R : (ι → V) → ι → ℝ) : Prop :=
  ∀ (a : ι → V) (i : ι) (v : V), label v = label (a i) → R (Function.update a i v) i = R a i

/-- No hidden versions: each treatment level is delivered by exactly one version. -/
def NoHiddenVersions (label : V → Bool) : Prop := ∀ t, ∃! v, label v = t

/-- With a single version per level every level is delivered. -/
theorem NoHiddenVersions.surjective {label : V → Bool} (h : NoHiddenVersions label) :
    Function.Surjective label :=
  fun t => (h t).exists

/-- **A single version per level makes the versions irrelevant**: the only version with the
label of `a i` is `a i` itself. -/
theorem NoHiddenVersions.versionIrrelevance [DecidableEq ι] {label : V → Bool}
    (h : NoHiddenVersions label) (R : (ι → V) → ι → ℝ) : VersionIrrelevance label R := by
  intro a i v hv
  rw [(h (label (a i))).unique hv rfl, Function.update_eq_self]

/-- **Unit level potential outcomes from versions.** If every treatment level is delivered by
some version, no interference and irrelevance of versions hold exactly when there are potential
outcomes `Y : Bool → ι → ℝ` with `R a i = Y (label (a i)) i` for every version vector `a` and
unit `i`. In the forward direction `Y t i` is the outcome of `i` when every unit receives a
chosen version of level `t`. -/
theorem exists_potentialOutcomes_iff [DecidableEq ι] {label : V → Bool}
    (hsurj : Function.Surjective label) {R : (ι → V) → ι → ℝ} :
    (NoInterferenceVersions R ∧ VersionIrrelevance label R) ↔
      ∃ Y : Bool → ι → ℝ, ∀ (a : ι → V) (i : ι), R a i = Y (label (a i)) i := by
  constructor
  · rintro ⟨hni, hvi⟩
    choose v hv using hsurj
    refine ⟨fun t i => R (fun _ => v t) i, fun a i => ?_⟩
    set c : ι → V := fun _ => v (label (a i))
    have h1 : R a i = R (Function.update c i (a i)) i :=
      hni _ _ i (by rw [Function.update_self])
    have h2 : R (Function.update c i (a i)) i = R c i :=
      hvi c i (a i) (by simp only [c, hv])
    rw [h1, h2]
  · rintro ⟨Y, hY⟩
    refine ⟨fun a a' i h => by rw [hY a i, hY a' i, h], fun a i v hv => ?_⟩
    rw [hY, hY, Function.update_self, hv]

/-- **The consistency identity from versions.** If every treatment level is delivered by some
version, and no interference and irrelevance of versions hold, there are potential outcomes `Y`
such that, for every realized version vector `a` with treatment `A i = label (a i)`, the
observed outcome `R a` is the potential outcome of the treatment received
(`IsObservedOutcome A Y (R a)`). Moreover the outcomes indexed by label vectors,
`b ↦ (i ↦ Y (b i) i)`, satisfy the no interference condition of `CausalInference.Interference`,
and their unit outcome at level `label (a i)` is `R a i`. -/
theorem exists_isObservedOutcome_of_versions [DecidableEq ι] {label : V → Bool}
    (hsurj : Function.Surjective label) {R : (ι → V) → ι → ℝ} (hni : NoInterferenceVersions R)
    (hvi : VersionIrrelevance label R) :
    ∃ Y : Bool → ι → ℝ, (∀ a : ι → V, IsObservedOutcome (fun i => label (a i)) Y (R a)) ∧
      Interference.NoInterference (fun (b : ι → Bool) (i : ι) => Y (b i) i) ∧
      ∀ (a : ι → V) (i : ι),
        Interference.unitOutcome (fun (b : ι → Bool) (i : ι) => Y (b i) i) i (label (a i)) =
          R a i := by
  obtain ⟨Y, hY⟩ := (exists_potentialOutcomes_iff hsurj).1 ⟨hni, hvi⟩
  exact ⟨Y, fun a i => hY a i, fun b b' i h => by simp only [h], fun a i => (hY a i).symm⟩

/-- **Hidden versions break the potential outcomes.** On one unit with three versions, two of
them labeled `true` and giving different outcomes, no potential outcomes `Y` represent the
outcomes: `R a i = Y (label (a i)) i` fails for every `Y`. -/
theorem not_exists_potentialOutcomes_of_hiddenVersions :
    ¬ ∃ Y : Bool → Unit → ℝ, ∀ (a : Unit → Fin 3) (i : Unit),
      (fun (a : Unit → Fin 3) (_ : Unit) => ((a ()).val : ℝ)) a i =
        Y ((fun v : Fin 3 => decide (v ≠ 0)) (a i)) i := by
  rintro ⟨Y, hY⟩
  have h1 := hY (fun _ => 1) ()
  have h2 := hY (fun _ => 2) ()
  simp only [ne_eq, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true,
    decide_true] at h1 h2
  norm_num [← h1] at h2

end PointTreatment

end CausalInference
