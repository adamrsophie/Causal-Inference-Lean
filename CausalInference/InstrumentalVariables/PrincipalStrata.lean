/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.Basic

/-!
# Principal strata of a binary instrumental variable model

Each unit belongs to exactly one principal stratum, determined by its pair of potential
treatments `(D false, D true)` (Angrist, Imbens and Rubin, 1996): always-takers `(true, true)`,
never-takers `(false, false)`, compliers `(false, true)` and defiers `(true, false)`.

## Main definitions

* `CausalInference.IVModel.Stratum`: the four principal strata.
* `IVModel.stratum`: the set of units in a given stratum; `IVModel.alwaysTakers`,
  `IVModel.neverTakers`, `IVModel.compliers`, `IVModel.defiers`.

## Main results

* `IVModel.iUnion_stratum`, `IVModel.pairwise_disjoint_stratum`: the strata partition `Ω`.
* `IVModel.measurableSet_stratum`: each stratum is measurable.
* `IVModel.sum_measureReal_stratum`: for a probability measure the stratum shares sum to `1`.
* `IVModel.measure_defiers_eq_zero`: under (almost sure) monotonicity the defiers are a null set;
  `IVModel.ae_eq_alwaysTakers`, `IVModel.ae_eq_neverTakers`: then `{D false = 1}` is the
  always-takers and `{D true = 0}` the never-takers, up to null sets.
* `IVModel.DReal_sub_DReal`, `IVModel.sub_eq_indicator_sub_indicator`: the pointwise identities
  behind the first-stage and reduced-form decompositions.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace IVModel

/-- The four principal strata of a binary instrument and binary treatment. -/
inductive Stratum
  /-- Units treated whatever the instrument value. -/
  | alwaysTaker
  /-- Units untreated whatever the instrument value. -/
  | neverTaker
  /-- Units treated exactly when the instrument is `true`. -/
  | complier
  /-- Units treated exactly when the instrument is `false`. -/
  | defier
  deriving DecidableEq

instance : Fintype Stratum where
  elems := {.alwaysTaker, .neverTaker, .complier, .defier}
  complete s := by cases s <;> simp

/-- The stratum of a pair of potential treatments `(D false, D true)`. -/
def stratumOfPair : Bool × Bool → Stratum
  | (true, true) => .alwaysTaker
  | (false, false) => .neverTaker
  | (false, true) => .complier
  | (true, false) => .defier

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω)

/-- The principal stratum of the unit `ω`, determined by `(D false ω, D true ω)`. -/
def stratumOf (ω : Ω) : Stratum := stratumOfPair (M.D false ω, M.D true ω)

/-- The set of units in the principal stratum `s`. -/
def stratum (s : Stratum) : Set Ω := {ω | M.stratumOf ω = s}

/-- The always-takers: units with `D false = true` and `D true = true`. -/
def alwaysTakers : Set Ω := M.stratum .alwaysTaker

/-- The never-takers: units with `D false = false` and `D true = false`. -/
def neverTakers : Set Ω := M.stratum .neverTaker

/-- The compliers: units with `D false = false` and `D true = true`. -/
def compliers : Set Ω := M.stratum .complier

/-- The defiers: units with `D false = true` and `D true = false`. -/
def defiers : Set Ω := M.stratum .defier

/-- Membership in a principal stratum is decidable. -/
instance (s : Stratum) : DecidablePred (· ∈ M.stratum s) :=
  fun ω ↦ inferInstanceAs (Decidable (M.stratumOf ω = s))

variable {M}

theorem mem_alwaysTakers {ω : Ω} :
    ω ∈ M.alwaysTakers ↔ M.D false ω = true ∧ M.D true ω = true := by
  simp only [alwaysTakers, stratum, stratumOf, Set.mem_ofPred_eq]
  cases M.D false ω <;> cases M.D true ω <;> simp [stratumOfPair]

theorem mem_neverTakers {ω : Ω} :
    ω ∈ M.neverTakers ↔ M.D false ω = false ∧ M.D true ω = false := by
  simp only [neverTakers, stratum, stratumOf, Set.mem_ofPred_eq]
  cases M.D false ω <;> cases M.D true ω <;> simp [stratumOfPair]

theorem mem_compliers {ω : Ω} :
    ω ∈ M.compliers ↔ M.D false ω = false ∧ M.D true ω = true := by
  simp only [compliers, stratum, stratumOf, Set.mem_ofPred_eq]
  cases M.D false ω <;> cases M.D true ω <;> simp [stratumOfPair]

theorem mem_defiers {ω : Ω} :
    ω ∈ M.defiers ↔ M.D false ω = true ∧ M.D true ω = false := by
  simp only [defiers, stratum, stratumOf, Set.mem_ofPred_eq]
  cases M.D false ω <;> cases M.D true ω <;> simp [stratumOfPair]

variable (M)

/-- Every unit lies in some principal stratum. -/
theorem iUnion_stratum : ⋃ s, M.stratum s = Set.univ :=
  Set.eq_univ_of_forall fun ω ↦ Set.mem_iUnion.2 ⟨M.stratumOf ω, rfl⟩

/-- Distinct principal strata are disjoint. -/
theorem pairwise_disjoint_stratum : Pairwise (Function.onFun Disjoint M.stratum) :=
  fun _ _ hst ↦ Set.disjoint_left.2 fun _ h₁ h₂ ↦ hst (h₁.symm.trans h₂)

/-- Each principal stratum is a measurable set. -/
theorem measurableSet_stratum (s : Stratum) : MeasurableSet (M.stratum s) :=
  ((M.measurable_D false).prodMk (M.measurable_D true))
    (Set.to_countable (stratumOfPair ⁻¹' {s})).measurableSet

/-- For a probability measure, the probabilities of the four principal strata sum to `1`. -/
theorem sum_measureReal_stratum {μ : Measure Ω} [IsProbabilityMeasure μ] :
    ∑ s, μ.real (M.stratum s) = 1 := by
  rw [← measureReal_iUnion_fintype M.pairwise_disjoint_stratum M.measurableSet_stratum,
    M.iUnion_stratum, probReal_univ]

theorem measurableSet_compliers : MeasurableSet M.compliers := M.measurableSet_stratum _

theorem measurableSet_defiers : MeasurableSet M.defiers := M.measurableSet_stratum _

/-- Under monotonicity (`D false ≤ D true` almost surely), the defiers form a null set. -/
theorem measure_defiers_eq_zero {μ : Measure Ω} (h : M.Monotonicity μ) : μ M.defiers = 0 := by
  refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 h)
  obtain ⟨h₁, h₂⟩ := mem_defiers.1 hω
  simp [h₁, h₂]

/-- Under monotonicity, `{D false = 1}` equals the always-takers up to a null set (the
defiers). -/
theorem ae_eq_alwaysTakers {μ : Measure Ω} (hM : M.Monotonicity μ) :
    ({ω | M.D false ω = true} : Set Ω) =ᵐ[μ] M.alwaysTakers := by
  filter_upwards [hM] with ω h
  rw [mem_alwaysTakers]
  revert h
  cases M.D false ω <;> cases M.D true ω <;> simp

/-- Under monotonicity, `{D true = 0}` equals the never-takers up to a null set (the
defiers). -/
theorem ae_eq_neverTakers {μ : Measure Ω} (hM : M.Monotonicity μ) :
    ({ω | M.D true ω = true}ᶜ : Set Ω) =ᵐ[μ] M.neverTakers := by
  filter_upwards [hM] with ω h
  change (¬ M.D true ω = true ↔ ω ∈ M.neverTakers)
  rw [mem_neverTakers]
  revert h
  cases M.D false ω <;> cases M.D true ω <;> simp

/-- Pointwise first-stage identity: `D true - D false = 1_compliers - 1_defiers`, with the
treatments coded as real numbers. -/
theorem DReal_sub_DReal (ω : Ω) :
    M.DReal true ω - M.DReal false ω =
      M.compliers.indicator 1 ω - M.defiers.indicator 1 ω := by
  simp only [DReal, Set.indicator, mem_compliers, mem_defiers]
  cases M.D false ω <;> cases M.D true ω <;> simp

/-- Pointwise reduced-form identity: for any family `g d` indexed by the treatment value,
`g (D true) - g (D false) = (g true - g false) 1_compliers - (g true - g false) 1_defiers`. -/
theorem sub_eq_indicator_sub_indicator (g : Bool → Ω → ℝ) (ω : Ω) :
    g (M.D true ω) ω - g (M.D false ω) ω =
      M.compliers.indicator (fun ω ↦ g true ω - g false ω) ω -
        M.defiers.indicator (fun ω ↦ g true ω - g false ω) ω := by
  simp only [Set.indicator, mem_compliers, mem_defiers]
  cases M.D false ω <;> cases M.D true ω <;> simp

end IVModel

end CausalInference
