/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.EntropyDuality
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Population adjustment: existence and uniqueness of the entropy balancing weights

Let `Δᵢ` be the centered features of the units `i : ι`.

* **Existence.** If some strictly positive probability vector balances the `Δᵢ`, the dual
  `Q(β) = log ∑ᵢ exp(βᵀΔᵢ)` attains its minimum (`exists_isMinOn_logPartition`). The exponential
  sum grows linearly off the balanced directions (`one_add_mul_norm_le_sum_exp`), so the minimum
  over the range of `β ↦ (βᵀΔᵢ)ᵢ` is attained on a compact ball. Conversely, the weights of a
  minimizer are strictly positive and feasible, so a minimizer exists exactly when a strictly
  positive feasible point does (`exists_isMinOn_logPartition_iff`).
* **The estimated parameter as a function of the data.** `dualMinimizer Δ` is a minimizer of `Q`
  whenever one exists (`isMinOn_dualMinimizer`), and `balancingWeights Δ` are its weights. The
  weights do not depend on the choice of minimizer (`entropyWeights_eq_balancingWeights`): they
  are the unique minimizer of the negative entropy over the feasible set
  (`balancingWeights_isMinOn`, `existsUnique_isMinOn_negEntropy`).
* **Uniqueness of the parameter.** Two minimizers differ by a vector orthogonal to every `Δᵢ`
  (`isMinOn_logPartition_iff_of_isMinOn`); when the `Δᵢ` span `ℝ^p` the minimizer is unique
  (`eq_dualMinimizer_of_span`) and `Q` is strictly convex (`strictConvexOn_logPartition_of_span`).
* **The Karush, Kuhn and Tucker characterization.** A strictly positive feasible `q` minimizes the
  negative entropy exactly when `log qᵢ` is affine in `Δᵢ` (`isMinOn_negEntropy_iff`).

## Main definitions

* `designMap Δ`: the linear map `β ↦ (βᵀΔᵢ)ᵢ`.
* `dualMinimizer Δ`, `balancingWeights Δ`.

## Main results

* `one_add_mul_norm_le_sum_exp`, `exists_isMinOn_logPartition`,
  `exists_isMinOn_logPartition_iff`.
* `isMinOn_dualMinimizer`, `momentBalanced_dualMinimizer`, `entropyWeights_eq_balancingWeights`,
  `balancingWeights_isMinOn`, `existsUnique_isMinOn_negEntropy`.
* `isMinOn_logPartition_iff_of_isMinOn`, `eq_dualMinimizer_of_span`,
  `strictConvexOn_logPartition_of_span`, `isMinOn_negEntropy_iff`.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open Finset

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-! ### Existence of a dual minimizer -/

section Existence

variable (Δ : ι → Fin p → ℝ)

/-- The **design map** `β ↦ (βᵀΔᵢ)ᵢ` from parameters to linear predictors. -/
def designMap : (Fin p → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun β i := β ⬝ᵥ Δ i
  map_add' β γ := funext fun i => add_dotProduct β γ (Δ i)
  map_smul' c β := funext fun i => by simp [smul_dotProduct]

variable {Δ}

/-- **Linear growth of the exponential sum off the balanced directions.** If `q > 0`,
`∑ᵢ qᵢ = 1` and `∑ᵢ qᵢ aᵢ = 0`, then `∑ᵢ exp(aᵢ) ≥ 1 + (min q) ‖a‖`. The largest coordinate
`M` of `a` is nonnegative and bounds every `|aᵢ|` by `M / min q`. -/
theorem one_add_mul_norm_le_sum_exp [Nonempty ι] {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hqs : ∑ i, q i = 1) {k₀ : ι} (hk₀ : ∀ i, q k₀ ≤ q i) {a : ι → ℝ}
    (ha : ∑ i, q i * a i = 0) : 1 + q k₀ * ‖a‖ ≤ ∑ i, Real.exp (a i) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image univ a univ_nonempty
  set M := a k
  have hsumM : ∑ i, q i * (M - a i) = M := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hqs, ha, sub_zero, one_mul]
  have hterm : ∀ i, 0 ≤ q i * (M - a i) :=
    fun i => mul_nonneg (hq i).le (sub_nonneg.2 (hk i (mem_univ _)))
  have hM0 : 0 ≤ M := hsumM ▸ Finset.sum_nonneg fun i _ => hterm i
  have hbound : ∀ i, q k₀ * |a i| ≤ M := by
    intro i
    have hb : q i * (M - a i) ≤ M := by
      have := Finset.single_le_sum (fun j _ => hterm j) (mem_univ i)
      rwa [hsumM] at this
    have hai := hk i (mem_univ _)
    have hq1 : q i ≤ 1 := hqs ▸ Finset.single_le_sum (fun j _ => (hq j).le) (mem_univ i)
    rcases le_or_gt 0 (a i) with h | h
    · rw [abs_of_nonneg h]
      nlinarith [(hq k₀).le, hk₀ i]
    · rw [abs_of_neg h]
      nlinarith [hk₀ i, (hq i).le]
  have hnorm : q k₀ * ‖a‖ ≤ M := by
    have : ‖a‖ ≤ M / q k₀ := by
      refine (pi_norm_le_iff_of_nonneg (div_nonneg hM0 (hq k₀).le)).2 fun i => ?_
      rw [Real.norm_eq_abs, le_div_iff₀ (hq k₀), mul_comm]
      exact hbound i
    calc q k₀ * ‖a‖ ≤ q k₀ * (M / q k₀) := mul_le_mul_of_nonneg_left this (hq k₀).le
      _ = M := by have := (hq k₀).ne'; field_simp
  have h2 : Real.exp M ≤ ∑ i, Real.exp (a i) :=
    Finset.single_le_sum (f := fun i => Real.exp (a i)) (fun i _ => (Real.exp_pos _).le)
      (mem_univ k)
  linarith [Real.add_one_le_exp M]

/-- A probability vector lives on a nonempty index type. -/
theorem nonempty_of_sum_eq_one {q : ι → ℝ} (hq : ∑ i, q i = 1) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  simp at hq

/-- **A strictly positive feasible point gives a dual minimizer.** If some `q > 0` with
`∑ᵢ qᵢ = 1` balances the `Δᵢ`, then `Q` attains its minimum. The function `a ↦ ∑ᵢ exp(aᵢ)` is
minimized over a closed ball of the range of the design map, which is compact; linear growth
keeps the points of the range outside the ball above the value `card ι` at `0`. -/
theorem exists_isMinOn_logPartition (hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i) :
    ∃ β, IsMinOn (logPartition Δ) Set.univ β := by
  obtain ⟨q, ⟨-, hqs, hqb⟩, hq⟩ := hpos
  have : Nonempty ι := nonempty_of_sum_eq_one hqs
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image univ q univ_nonempty
  set c := q k₀ with hc
  have hc0 : 0 < c := hq k₀
  set L := LinearMap.range (designMap Δ)
  have hL : ∀ a ∈ L, ∑ i, q i * a i = 0 := by
    rintro a ⟨β, rfl⟩
    exact sum_mul_dotProduct_eq_zero hqb β
  set F : (ι → ℝ) → ℝ := fun a => ∑ i, Real.exp (a i)
  have hF : Continuous F := by fun_prop
  set R := (Fintype.card ι : ℝ) / c
  set K := Metric.closedBall (0 : ι → ℝ) R ∩ (L : Set (ι → ℝ))
  have hK : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right (Submodule.isClosed_of_finiteDimensional L)
  have h0K : (0 : ι → ℝ) ∈ K :=
    ⟨Metric.mem_closedBall_self (by positivity), L.zero_mem⟩
  obtain ⟨a₀, ha₀K, hmin⟩ := hK.exists_isMinOn ⟨0, h0K⟩ hF.continuousOn
  obtain ⟨β₀, hβ₀⟩ := ha₀K.2
  have hF0 : F 0 = Fintype.card ι := by simp [F]
  have hZ : ∀ u, partitionFunction Δ u = F (designMap Δ u) := fun u => rfl
  refine ⟨β₀, fun u _ => Real.log_le_log (partitionFunction_pos β₀) ?_⟩
  rw [hZ, hZ, hβ₀]
  have hu : designMap Δ u ∈ L := ⟨u, rfl⟩
  by_cases hR : ‖designMap Δ u‖ ≤ R
  · exact hmin ⟨by simpa using hR, hu⟩
  · have hgrow := one_add_mul_norm_le_sum_exp hq hqs (fun i => hk₀ i (mem_univ _)) (hL _ hu)
    have hcR : c * R = Fintype.card ι := by simp only [R]; field_simp
    have : (Fintype.card ι : ℝ) < F (designMap Δ u) := by
      have := mul_lt_mul_of_pos_left (not_le.1 hR) hc0
      change 1 + c * ‖designMap Δ u‖ ≤ F (designMap Δ u) at hgrow
      linarith
    have : F a₀ ≤ F 0 := hmin h0K
    linarith

/-- **A dual minimizer exists exactly when a strictly positive feasible point does.** -/
theorem exists_isMinOn_logPartition_iff [Nonempty ι] :
    (∃ β, IsMinOn (logPartition Δ) Set.univ β) ↔ ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i := by
  refine ⟨fun ⟨β, hβ⟩ => ⟨entropyWeights Δ β, ?_, entropyWeights_pos β⟩,
    exists_isMinOn_logPartition⟩
  exact (entropyWeights_mem_balancingSet_iff β).2 ((isMinOn_logPartition_iff β).1 hβ)

end Existence

/-! ### The estimated parameter and weights as functions of the data -/

section Estimate

variable (Δ : ι → Fin p → ℝ)

open Classical in
/-- The **dual minimizer**: a minimizer of `Q(β) = log ∑ᵢ exp(βᵀΔᵢ)` when one exists (chosen),
and `0` otherwise. Every result about it assumes a strictly positive feasible point, which is
equivalent to the existence of a minimizer (`exists_isMinOn_logPartition_iff`). -/
noncomputable def dualMinimizer : Fin p → ℝ :=
  if h : ∃ β, IsMinOn (logPartition Δ) Set.univ β then h.choose else 0

/-- The **entropy balancing weights** of the data: the weights of the dual minimizer. -/
noncomputable def balancingWeights : ι → ℝ := entropyWeights Δ (dualMinimizer Δ)

variable {Δ}

/-- The dual minimizer minimizes `Q` when a strictly positive feasible point exists. -/
theorem isMinOn_dualMinimizer (hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i) :
    IsMinOn (logPartition Δ) Set.univ (dualMinimizer Δ) := by
  have h := exists_isMinOn_logPartition hpos
  simp only [dualMinimizer, h, ↓reduceDIte]
  exact h.choose_spec

/-- The dual minimizer solves the balance equation `∑ᵢ exp(βᵀΔᵢ) Δᵢ = 0`. -/
theorem momentBalanced_dualMinimizer (hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i) :
    MomentBalanced (fun i => Real.exp (dualMinimizer Δ ⬝ᵥ Δ i)) Δ 0 := by
  obtain ⟨q, hq, hqpos⟩ := hpos
  have : Nonempty ι := nonempty_of_sum_eq_one hq.2.1
  exact (isMinOn_logPartition_iff _).1 (isMinOn_dualMinimizer ⟨q, hq, hqpos⟩)

/-- The weights of any dual minimizer are feasible and are the unique minimizer of the negative
entropy over the feasible set. -/
theorem entropyWeights_isMinOn_of_isMinOn [Nonempty ι] {β : Fin p → ℝ}
    (hβ : IsMinOn (logPartition Δ) Set.univ β) :
    entropyWeights Δ β ∈ balancingSet Δ ∧ IsMinOn negEntropy (balancingSet Δ) (entropyWeights Δ β)
      ∧ ∀ v ∈ balancingSet Δ, negEntropy v ≤ negEntropy (entropyWeights Δ β) →
        v = entropyWeights Δ β := by
  obtain ⟨h1, -, h3, h4⟩ := entropyWeights_isMinOn ((isMinOn_logPartition_iff β).1 hβ)
  exact ⟨h1, h3, h4⟩

/-- **The weights do not depend on the choice of minimizer**: every minimizer `β` of `Q` has the
entropy weights `balancingWeights Δ`. -/
theorem entropyWeights_eq_balancingWeights [Nonempty ι] {β : Fin p → ℝ}
    (hβ : IsMinOn (logPartition Δ) Set.univ β) : entropyWeights Δ β = balancingWeights Δ := by
  have hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i :=
    exists_isMinOn_logPartition_iff.1 ⟨β, hβ⟩
  obtain ⟨h1, -, h4⟩ := entropyWeights_isMinOn_of_isMinOn hβ
  obtain ⟨h1', h3', -⟩ := entropyWeights_isMinOn_of_isMinOn (isMinOn_dualMinimizer hpos)
  exact (h4 _ h1' (h3' h1)).symm

/-- **The entropy balancing weights.** When a strictly positive feasible point exists, the
weights `balancingWeights Δ` are strictly positive, feasible, minimize the negative entropy over
the feasible set and are its unique minimizer. -/
theorem balancingWeights_isMinOn (hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i) :
    (∀ i, 0 < balancingWeights Δ i) ∧ balancingWeights Δ ∈ balancingSet Δ ∧
      IsMinOn negEntropy (balancingSet Δ) (balancingWeights Δ) ∧
      ∀ v ∈ balancingSet Δ, negEntropy v ≤ negEntropy (balancingWeights Δ) →
        v = balancingWeights Δ := by
  obtain ⟨q, hq, hqpos⟩ := hpos
  have : Nonempty ι := nonempty_of_sum_eq_one hq.2.1
  exact ⟨entropyWeights_pos _, entropyWeights_isMinOn_of_isMinOn (isMinOn_dualMinimizer
    ⟨q, hq, hqpos⟩)⟩

/-- **Existence and uniqueness of the entropy balancing solution.** With a strictly positive
feasible point, the negative entropy has exactly one minimizer over the feasible set, the
balancing weights; it is also the unique minimizer among the strictly positive feasible
points. -/
theorem existsUnique_isMinOn_negEntropy (hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i) :
    (∃! q, q ∈ balancingSet Δ ∧ IsMinOn negEntropy (balancingSet Δ) q) ∧
      ∀ q, q ∈ balancingSet Δ → (∀ i, 0 < q i) →
        IsMinOn negEntropy {v ∈ balancingSet Δ | ∀ i, 0 < v i} q → q = balancingWeights Δ := by
  obtain ⟨h0, h1, h3, h4⟩ := balancingWeights_isMinOn hpos
  refine ⟨⟨balancingWeights Δ, ⟨h1, h3⟩, fun q ⟨hq, hqmin⟩ => h4 q hq (hqmin h1)⟩,
    fun q hq _ hqmin => h4 q hq (hqmin ⟨h1, h0⟩)⟩

end Estimate

/-! ### Uniqueness of the dual parameter -/

section Uniqueness

variable {Δ : ι → Fin p → ℝ}

/-- **The minimizers form an affine set**: if `β` minimizes `Q`, then `β'` minimizes `Q` exactly
when `(β' - β)ᵀΔᵢ = 0` for every `i`. -/
theorem isMinOn_logPartition_iff_of_isMinOn [Nonempty ι] {β : Fin p → ℝ}
    (hβ : IsMinOn (logPartition Δ) Set.univ β) (β' : Fin p → ℝ) :
    IsMinOn (logPartition Δ) Set.univ β' ↔ ∀ i, (β' - β) ⬝ᵥ Δ i = 0 := by
  constructor
  · intro hβ'
    have heq : entropyWeights Δ β' = entropyWeights Δ β := by
      rw [entropyWeights_eq_balancingWeights hβ, entropyWeights_eq_balancingWeights hβ']
    set k := logPartition Δ β' - logPartition Δ β
    have hconst : ∀ i, (β' - β) ⬝ᵥ Δ i = k := by
      intro i
      have := congrArg Real.log (congrFun heq i)
      rw [log_entropyWeights, log_entropyWeights] at this
      rw [sub_dotProduct]
      linarith
    have h1 := (entropyWeights_isMinOn_of_isMinOn hβ).1
    have hzero := sum_mul_dotProduct_eq_zero h1.2.2 (β' - β)
    simp only [hconst, ← Finset.sum_mul, h1.2.1, one_mul] at hzero
    exact fun i => (hconst i).trans hzero
  · intro h u _
    have hZ : partitionFunction Δ β' = partitionFunction Δ β := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have := h i
      rw [sub_dotProduct, sub_eq_zero] at this
      rw [this]
    simp only [Set.mem_ofPred_eq, logPartition, hZ]
    exact hβ (Set.mem_univ u)

/-- **Uniqueness of the dual parameter when the features span**: if the `Δᵢ` span `ℝ^p`, every
minimizer of `Q` is the dual minimizer. -/
theorem eq_dualMinimizer_of_span (hspan : Submodule.span ℝ (Set.range Δ) = ⊤) {β : Fin p → ℝ}
    (hβ : IsMinOn (logPartition Δ) Set.univ β) : β = dualMinimizer Δ := by
  by_cases hι : Nonempty ι
  · have hpos := exists_isMinOn_logPartition_iff.1 ⟨β, hβ⟩
    have h := (isMinOn_logPartition_iff_of_isMinOn hβ (dualMinimizer Δ)).1
      (isMinOn_dualMinimizer hpos)
    have hall : ∀ y ∈ Submodule.span ℝ (Set.range Δ), (dualMinimizer Δ - β) ⬝ᵥ y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h i
      | zero => exact dotProduct_zero _
      | add y z _ _ hy hz => rw [dotProduct_add, hy, hz, add_zero]
      | smul c y _ hy => rw [dotProduct_smul, hy, smul_zero]
    exact (sub_eq_zero.1 (dotProduct_self_eq_zero.1 (hall _ (hspan ▸ Submodule.mem_top)))).symm
  · -- with no units the span is `{0}`, so `p = 0` and every parameter is `0`
    rw [not_nonempty_iff] at hι
    have hbot : Submodule.span ℝ (Set.range Δ) = ⊥ := by simp [Set.range_eq_empty]
    have htop : (⊤ : Submodule ℝ (Fin p → ℝ)) = ⊥ := hspan.symm.trans hbot
    have h1 : β ∈ (⊥ : Submodule ℝ (Fin p → ℝ)) := htop ▸ Submodule.mem_top
    have h2 : dualMinimizer Δ ∈ (⊥ : Submodule ℝ (Fin p → ℝ)) := htop ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at h1 h2
    rw [h1, h2]

/-- **Strict convexity of the dual at a spanning feasible design**: if the `Δᵢ` span `ℝ^p` and
some probability vector balances them, `Q` is strictly convex. -/
theorem strictConvexOn_logPartition_of_span (hspan : Submodule.span ℝ (Set.range Δ) = ⊤)
    {q : ι → ℝ} (hq : q ∈ balancingSet Δ) : StrictConvexOn ℝ Set.univ (logPartition Δ) := by
  have : Nonempty ι := nonempty_of_sum_eq_one hq.2.1
  exact strictConvexOn_logPartition
    (forall_const_dotProduct_imp_of_span hspan hq.2.2 (by rw [hq.2.1]; exact one_ne_zero))

/-- **The Karush, Kuhn and Tucker characterization**: a strictly positive feasible `q` minimizes
the negative entropy over the feasible set exactly when `log qᵢ = λ + βᵀΔᵢ` for some multipliers
`λ` and `β` (the stationarity condition of the Lagrangian). -/
theorem isMinOn_negEntropy_iff {q : ι → ℝ} (hq : q ∈ balancingSet Δ) (hpos : ∀ i, 0 < q i) :
    IsMinOn negEntropy (balancingSet Δ) q ↔
      ∃ (l : ℝ) (β : Fin p → ℝ), ∀ i, Real.log (q i) = l + β ⬝ᵥ Δ i := by
  have : Nonempty ι := nonempty_of_sum_eq_one hq.2.1
  constructor
  · intro hmin
    have hp : ∃ v ∈ balancingSet Δ, ∀ i, 0 < v i := ⟨q, hq, hpos⟩
    obtain ⟨-, h1, h3, h4⟩ := balancingWeights_isMinOn hp
    have heq : q = balancingWeights Δ := h4 q hq (hmin h1)
    refine ⟨-logPartition Δ (dualMinimizer Δ), dualMinimizer Δ, fun i => ?_⟩
    rw [heq, balancingWeights, log_entropyWeights]
    ring
  · rintro ⟨l, β, h⟩
    have hqw : q = fun i => tiltWeight Δ 0 l β i := by
      funext i
      rw [tiltWeight, sub_zero, ← h i, Real.exp_log (hpos i)]
    rw [hqw] at hq ⊢
    obtain ⟨h1, h2⟩ := tiltWeight_mem_balancingSet_iff (Δ := Δ) l β
    rw [h2 hq]
    exact (entropyWeights_isMinOn (h1.1 hq).2).2.2.1

end Uniqueness

end PopulationAdjustment

end CausalInference
