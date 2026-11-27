/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Potential outcomes under interference

Under interference the potential outcome of a unit is indexed by the whole assignment vector:
`Y : (ι → Bool) → ι → ℝ`, where `Y a i` is the outcome of unit `i` when the units are assigned
according to `a` (`true` means treated). This file sets up the basic restrictions on `Y`.

## Main definitions

* `CausalInference.Interference.NoInterference`: the no-interference component of SUTVA;
  `Y a i` depends on `a` only through `a i`.
* `CausalInference.Interference.PartialInterference`: for a partition of the units into groups
  given by `g : ι → G`, `Y a i` depends on `a` only through the assignments in the group of `i`.
* `CausalInference.Interference.ExposureDepends`: for an exposure mapping `f`, `Y a i` depends
  on `a` only through the exposure `f a i`.
* `CausalInference.Interference.StratifiedInterference`: `Y a i` depends on `a` only through
  the unit's own assignment `a i` and the number of treated units in the group of `i`.

## Main results

* `NoInterference.partialInterference`: no interference implies partial interference for every
  partition.
* `NoInterference.eq_unitOutcome`: under no interference, `Y a i` equals the classical potential
  outcome `y1 i` or `y0 i` according to `a i`.
* `exposureDepends_iff_exists`: dependence through an exposure mapping is the same as `Y`
  factoring through it.
* `noInterference_iff_exposureDepends`, `partialInterference_iff_exposureDepends`: both
  restrictions are instances of exposure dependence.
* `NoInterference.stratifiedInterference`, `StratifiedInterference.partialInterference`:
  stratified interference lies between no interference and partial interference.

Source: M. G. Hudgens and M. E. Halloran (2008), Toward causal inference with interference;
the exposure mapping formulation follows P. M. Aronow and C. Samii (2017), Estimating average
causal effects under general interference.
-/

@[expose] public section

namespace CausalInference

namespace Interference

variable {ι G E : Type*}

/-- No interference (the no-interference component of SUTVA): the outcome of unit `i` depends
on the assignment vector only through the unit's own assignment `a i`. -/
def NoInterference (Y : (ι → Bool) → ι → ℝ) : Prop :=
  ∀ a b : ι → Bool, ∀ i, a i = b i → Y a i = Y b i

/-- Partial interference for the partition of units into groups given by `g : ι → G`: the
outcome of unit `i` depends on the assignment vector only through the assignments of the units
in the same group as `i`. -/
def PartialInterference (g : ι → G) (Y : (ι → Bool) → ι → ℝ) : Prop :=
  ∀ a b : ι → Bool, ∀ i, (∀ j, g j = g i → a j = b j) → Y a i = Y b i

/-- No interference implies partial interference for every partition into groups. -/
theorem NoInterference.partialInterference {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y)
    (g : ι → G) : PartialInterference g Y :=
  fun a b i hab ↦ h a b i (hab i rfl)

/-- The classical unit level potential outcome of unit `i` under treatment `t`: the outcome
when every unit receives `t`. Under no interference this is the outcome of `i` under any
assignment that gives `i` the treatment `t`. -/
def unitOutcome (Y : (ι → Bool) → ι → ℝ) (i : ι) (t : Bool) : ℝ :=
  Y (fun _ ↦ t) i

/-- The classical potential outcome under treatment, `y1 i`. -/
def y1 (Y : (ι → Bool) → ι → ℝ) (i : ι) : ℝ := unitOutcome Y i true

/-- The classical potential outcome under control, `y0 i`. -/
def y0 (Y : (ι → Bool) → ι → ℝ) (i : ι) : ℝ := unitOutcome Y i false

/-- Under no interference the outcome of unit `i` under any assignment vector `a` is the
classical potential outcome of `i` at its own treatment `a i`. -/
theorem NoInterference.eq_unitOutcome {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y)
    (a : ι → Bool) (i : ι) : Y a i = unitOutcome Y i (a i) :=
  h a _ i rfl

/-- Under no interference, `Y a i = y1 i` if `i` is treated and `Y a i = y0 i` otherwise. -/
theorem NoInterference.eq_ite {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y)
    (a : ι → Bool) (i : ι) : Y a i = if a i then y1 Y i else y0 Y i := by
  rw [h.eq_unitOutcome]
  cases a i <;> rfl

/-- The outcomes depend on the assignment vector only through the exposure mapping
`f : (ι → Bool) → ι → E`: two assignment vectors giving unit `i` the same exposure give `i`
the same outcome. -/
def ExposureDepends (f : (ι → Bool) → ι → E) (Y : (ι → Bool) → ι → ℝ) : Prop :=
  ∀ a b : ι → Bool, ∀ i, f a i = f b i → Y a i = Y b i

/-- Dependence through an exposure mapping is equivalent to the existence of exposure level
potential outcomes `y i e` with `Y a i = y i (f a i)`. -/
theorem exposureDepends_iff_exists (f : (ι → Bool) → ι → E) (Y : (ι → Bool) → ι → ℝ) :
    ExposureDepends f Y ↔ ∃ y : ι → E → ℝ, ∀ a i, Y a i = y i (f a i) := by
  classical
  constructor
  · intro h
    refine ⟨fun i e ↦ if he : ∃ a, f a i = e then Y he.choose i else 0, fun a i ↦ ?_⟩
    have he : ∃ b, f b i = f a i := ⟨a, rfl⟩
    simp only [he, ↓reduceDIte]
    exact h a _ i he.choose_spec.symm
  · rintro ⟨y, hy⟩ a b i hab
    rw [hy a i, hy b i, hab]

/-- No interference is exposure dependence for the exposure mapping `a ↦ a i`. -/
theorem noInterference_iff_exposureDepends (Y : (ι → Bool) → ι → ℝ) :
    NoInterference Y ↔ ExposureDepends (fun a i ↦ a i) Y :=
  Iff.rfl

/-- The group exposure mapping for `g : ι → G`: unit `i` is exposed to the assignments of the
members of its own group, with nonmembers recorded as `false`. -/
def groupExposure [DecidableEq G] (g : ι → G) (a : ι → Bool) (i : ι) : ι → Bool :=
  fun j ↦ if g j = g i then a j else false

/-- Two assignment vectors give unit `i` the same group exposure exactly when they agree on the
group of `i`. -/
theorem groupExposure_eq_iff [DecidableEq G] (g : ι → G) (a b : ι → Bool) (i : ι) :
    groupExposure g a i = groupExposure g b i ↔ ∀ j, g j = g i → a j = b j := by
  constructor
  · intro h j hj
    simpa [groupExposure, hj] using congrFun h j
  · intro h
    funext j
    by_cases hj : g j = g i
    · simp [groupExposure, hj, h j hj]
    · simp [groupExposure, hj]

/-- Partial interference is exposure dependence for the group exposure mapping. -/
theorem partialInterference_iff_exposureDepends [DecidableEq G] (g : ι → G)
    (Y : (ι → Bool) → ι → ℝ) :
    PartialInterference g Y ↔ ExposureDepends (groupExposure g) Y := by
  simp only [PartialInterference, ExposureDepends, groupExposure_eq_iff]

/-- If the exposure `f` determines the exposure `f'` (equal `f` exposures give equal `f'`
exposures), then dependence through `f'` implies dependence through `f`. -/
theorem ExposureDepends.of_finer {E' : Type*} {f : (ι → Bool) → ι → E}
    {f' : (ι → Bool) → ι → E'} {Y : (ι → Bool) → ι → ℝ} (h : ExposureDepends f' Y)
    (hff' : ∀ a b i, f a i = f b i → f' a i = f' b i) : ExposureDepends f Y :=
  fun a b i hab ↦ h a b i (hff' a b i hab)

/-- The stratified interference exposure for the partition `g : ι → G`: the pair formed by the
unit's own assignment and the number of treated units in its group. -/
def stratifiedExposure [Fintype ι] [DecidableEq G] (g : ι → G) (a : ι → Bool) (i : ι) :
    Bool × ℕ :=
  (a i, (Finset.univ.filter fun j ↦ g j = g i ∧ a j = true).card)

/-- Stratified interference (Hudgens and Halloran): the outcome of unit `i` depends on the
assignment vector only through the unit's own assignment and the number of treated units in
the group of `i`. It is exposure dependence for `stratifiedExposure g`. -/
def StratifiedInterference [Fintype ι] [DecidableEq G] (g : ι → G)
    (Y : (ι → Bool) → ι → ℝ) : Prop :=
  ExposureDepends (stratifiedExposure g) Y

/-- No interference implies stratified interference for every partition into groups. -/
theorem NoInterference.stratifiedInterference [Fintype ι] [DecidableEq G]
    {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y) (g : ι → G) :
    StratifiedInterference g Y :=
  ExposureDepends.of_finer h fun _ _ _ hab ↦ (Prod.ext_iff.1 hab).1

/-- Stratified interference implies partial interference for the same partition: an assignment
of the group of `i` determines both `a i` and the number treated in that group. -/
theorem StratifiedInterference.partialInterference [Fintype ι] [DecidableEq G] {g : ι → G}
    {Y : (ι → Bool) → ι → ℝ} (h : StratifiedInterference g Y) : PartialInterference g Y := by
  refine fun a b i hab ↦ h a b i ?_
  have hfilter : (Finset.univ.filter fun j ↦ g j = g i ∧ a j = true) =
      Finset.univ.filter fun j ↦ g j = g i ∧ b j = true :=
    Finset.filter_congr fun j _ ↦ ⟨fun ⟨hj, ha⟩ ↦ ⟨hj, hab j hj ▸ ha⟩,
      fun ⟨hj, hb⟩ ↦ ⟨hj, (hab j hj).symm ▸ hb⟩⟩
  simp only [stratifiedExposure, hab i rfl, hfilter]

end Interference

end CausalInference
