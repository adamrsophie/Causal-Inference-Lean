/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.Examples
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Population adjustment: when the entropy balancing parameter is unique

Let `Δᵢ` be the centered features of the units `i : ι` (a nonempty finite set) and
`Q(β) = log ∑ᵢ exp(βᵀΔᵢ)` the dual of entropy balancing.

* **Two minimizers.** Two minimizers `β`, `β'` of `Q` have the same weights and differ by a
  direction orthogonal to every `Δᵢ` (`entropyWeights_eq_and_dotProduct_eq_zero_of_isMinOn`).
* **Uniqueness exactly under spanning.** If `Q` has a minimizer, it is the only one exactly when
  the `Δᵢ` span `ℝ^p` (`forall_isMinOn_eq_iff_span`): a nonzero `v` orthogonal to every `Δᵢ`
  (`exists_ne_zero_forall_dotProduct_eq_zero`) moves a minimizer along a line of minimizers.
  With the existence theorem, `Q` has exactly one minimizer exactly when a strictly positive
  probability vector balances the `Δᵢ` and the `Δᵢ` span `ℝ^p`
  (`existsUnique_isMinOn_logPartition_iff`).
* **Instances.** For the three unit example `Δ = (-1, 1, 1)` the minimizer `-(log 2) / 2` is
  unique (`existsUnique_isMinOn_logPartition_threeUnitDelta`). For the two units
  `Δ = ((-1, 0), (1, 0))` of `ℝ²`, which do not span, the minimizers are the line `β₀ = 0`
  (`isMinOn_logPartition_lineDelta_iff`), all with the weights `(1/2, 1/2)`
  (`entropyWeights_lineDelta`), and no minimizer is unique
  (`not_existsUnique_isMinOn_logPartition_lineDelta`).

The existence of finite exponential weights that balance, exactly at a target in the relative
interior of the convex hull, is `exists_tiltWeight_mem_balancingSet_iff`.

## Main results

* `entropyWeights_eq_and_dotProduct_eq_zero_of_isMinOn`,
  `exists_ne_zero_forall_dotProduct_eq_zero`, `forall_isMinOn_eq_iff_span`,
  `existsUnique_isMinOn_logPartition_iff`.
* `existsUnique_isMinOn_logPartition_threeUnitDelta`, `isMinOn_logPartition_lineDelta_iff`,
  `entropyWeights_lineDelta`, `not_existsUnique_isMinOn_logPartition_lineDelta`.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open Finset

variable {ι : Type*} [Fintype ι] {p : ℕ} {Δ : ι → Fin p → ℝ}

/-- **Two minimizers of the dual have the same weights and differ by an orthogonal
direction**: if `β` and `β'` minimize `Q`, then their entropy weights agree and
`(β - β')ᵀΔᵢ = 0` for every `i`. -/
theorem entropyWeights_eq_and_dotProduct_eq_zero_of_isMinOn [Nonempty ι] {β β' : Fin p → ℝ}
    (hβ : IsMinOn (logPartition Δ) Set.univ β) (hβ' : IsMinOn (logPartition Δ) Set.univ β') :
    entropyWeights Δ β = entropyWeights Δ β' ∧ ∀ i, (β - β') ⬝ᵥ Δ i = 0 :=
  ⟨(entropyWeights_eq_balancingWeights hβ).trans (entropyWeights_eq_balancingWeights hβ').symm,
    (isMinOn_logPartition_iff_of_isMinOn hβ' β).1 hβ⟩

omit [Fintype ι] in
/-- **A proper span has a nonzero orthogonal vector**: if the `Δᵢ` do not span `ℝ^p`, some
`v ≠ 0` satisfies `vᵀΔᵢ = 0` for every `i`. -/
theorem exists_ne_zero_forall_dotProduct_eq_zero
    (hspan : Submodule.span ℝ (Set.range Δ) ≠ ⊤) :
    ∃ v : Fin p → ℝ, v ≠ 0 ∧ ∀ i, v ⬝ᵥ Δ i = 0 := by
  obtain ⟨f, hf0, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hspan) inferInstance
  set v : Fin p → ℝ := fun j => f fun k => if j = k then 1 else 0 with hv_def
  have hfv : ∀ y, f y = v ⬝ᵥ y := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ f y, dotProduct]
    simp only [hv_def, smul_eq_mul, mul_comm]
  refine ⟨v, fun h => hf0 (LinearMap.ext fun y => by rw [hfv, h, zero_dotProduct]; rfl),
    fun i => ?_⟩
  have hmem : f (Δ i) ∈ (Submodule.span ℝ (Set.range Δ)).map f :=
    Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
  rw [hmap, Submodule.mem_bot] at hmem
  rw [← hfv, hmem]

/-- **The minimizer is unique exactly when the features span**: if `β` minimizes `Q`, every
minimizer equals `β` if and only if the `Δᵢ` span `ℝ^p`. -/
theorem forall_isMinOn_eq_iff_span [Nonempty ι] {β : Fin p → ℝ}
    (hβ : IsMinOn (logPartition Δ) Set.univ β) :
    (∀ β', IsMinOn (logPartition Δ) Set.univ β' → β' = β) ↔
      Submodule.span ℝ (Set.range Δ) = ⊤ := by
  constructor
  · intro huniq
    by_contra hspan
    obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_dotProduct_eq_zero hspan
    have hmin : IsMinOn (logPartition Δ) Set.univ (β + v) :=
      (isMinOn_logPartition_iff_of_isMinOn hβ (β + v)).2 fun i => by
        rw [add_sub_cancel_left]; exact hv i
    exact hv0 (add_eq_left.1 (huniq _ hmin))
  · intro hspan β' hβ'
    rw [eq_dualMinimizer_of_span hspan hβ', eq_dualMinimizer_of_span hspan hβ]

/-- **Existence and uniqueness of the dual parameter**: `Q` has exactly one minimizer if and only
if some strictly positive probability vector balances the `Δᵢ` and the `Δᵢ` span `ℝ^p`. -/
theorem existsUnique_isMinOn_logPartition_iff [Nonempty ι] :
    (∃! β, IsMinOn (logPartition Δ) Set.univ β) ↔
      (∃ q ∈ balancingSet Δ, ∀ i, 0 < q i) ∧ Submodule.span ℝ (Set.range Δ) = ⊤ := by
  constructor
  · rintro ⟨β, hβ, huniq⟩
    exact ⟨exists_isMinOn_logPartition_iff.1 ⟨β, hβ⟩, (forall_isMinOn_eq_iff_span hβ).1 huniq⟩
  · rintro ⟨hpos, hspan⟩
    obtain ⟨β, hβ⟩ := exists_isMinOn_logPartition hpos
    exact ⟨β, hβ, (forall_isMinOn_eq_iff_span hβ).2 hspan⟩

/-! ### Instances -/

/-- **The three unit example has a unique dual parameter**, `-(log 2) / 2`. -/
theorem existsUnique_isMinOn_logPartition_threeUnitDelta :
    (∃! β, IsMinOn (logPartition threeUnitDelta) Set.univ β) ∧
      ∀ β, IsMinOn (logPartition threeUnitDelta) Set.univ β → β = threeUnitBeta := by
  have hmin := isMinOn_logPartition_threeUnitDelta
  have huniq := (forall_isMinOn_eq_iff_span hmin).2 threeUnitDelta_span
  exact ⟨⟨threeUnitBeta, hmin, huniq⟩, huniq⟩

/-- Two units of `ℝ²` with centered features `(-1, 0)` and `(1, 0)`: they do not span `ℝ²`. -/
def lineDelta : Fin 2 → Fin 2 → ℝ := ![![-1, 0], ![1, 0]]

/-- The centered features of `lineDelta` do not span `ℝ²`: `(0, 1)` is orthogonal to both. -/
theorem lineDelta_span_ne_top : Submodule.span ℝ (Set.range lineDelta) ≠ ⊤ := by
  intro h
  have : ∀ y ∈ Submodule.span ℝ (Set.range lineDelta), y 1 = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; fin_cases i <;> simp [lineDelta]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  have h1 := this ![0, 1] (h ▸ Submodule.mem_top)
  simp at h1

/-- `β = 0` minimizes the dual of `lineDelta`: the uniform weights balance `(-1, 0)` and
`(1, 0)`. -/
theorem isMinOn_logPartition_lineDelta_zero :
    IsMinOn (logPartition lineDelta) Set.univ 0 := by
  rw [isMinOn_logPartition_iff, momentBalanced_zero_iff]
  funext j
  fin_cases j <;> simp [lineDelta, Fin.sum_univ_two]

/-- **The minimizers of the degenerate example form a line**: `β` minimizes the dual of
`lineDelta` exactly when `β₀ = 0`. -/
theorem isMinOn_logPartition_lineDelta_iff (β : Fin 2 → ℝ) :
    IsMinOn (logPartition lineDelta) Set.univ β ↔ β 0 = 0 := by
  rw [isMinOn_logPartition_iff_of_isMinOn isMinOn_logPartition_lineDelta_zero β]
  constructor
  · intro h
    simpa [lineDelta, dotProduct, Fin.sum_univ_two] using h 1
  · intro h i
    fin_cases i <;> simp [lineDelta, dotProduct, Fin.sum_univ_two, h]

/-- **Every minimizer of the degenerate example has the weights `(1/2, 1/2)`.** -/
theorem entropyWeights_lineDelta {β : Fin 2 → ℝ}
    (hβ : IsMinOn (logPartition lineDelta) Set.univ β) :
    entropyWeights lineDelta β = fun _ => 1 / 2 := by
  rw [(entropyWeights_eq_and_dotProduct_eq_zero_of_isMinOn hβ
    isMinOn_logPartition_lineDelta_zero).1]
  funext i
  simp [entropyWeights, partitionFunction]

/-- **No unique minimizer in the degenerate example**: `(0, 0)` and `(0, 1)` both minimize the
dual of `lineDelta`, so it has no unique minimizer. -/
theorem not_existsUnique_isMinOn_logPartition_lineDelta :
    IsMinOn (logPartition lineDelta) Set.univ ![0, 0] ∧
      IsMinOn (logPartition lineDelta) Set.univ ![0, 1] ∧
      ¬ ∃! β, IsMinOn (logPartition lineDelta) Set.univ β := by
  refine ⟨(isMinOn_logPartition_lineDelta_iff _).2 rfl,
    (isMinOn_logPartition_lineDelta_iff _).2 rfl, fun h => ?_⟩
  exact lineDelta_span_ne_top (existsUnique_isMinOn_logPartition_iff.1 h).2

end PopulationAdjustment

end CausalInference
