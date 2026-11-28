/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.TiltWeights
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Population adjustment: the entropy balancing program and its dual

Entropy balancing (Hainmueller 2012) chooses the weights of the units of a sample as the
probability vector closest to the uniform weights in entropy among those that balance the
features at a target. With the **centered features** `Δᵢ = φ(xᵢ) - t` of the units `i : ι`, the
program is

`minimize ∑ᵢ qᵢ log qᵢ` over `q ≥ 0`, `∑ᵢ qᵢ = 1`, `∑ᵢ qᵢ Δᵢ = 0` (`balancingSet`).

Its dual is the log partition function `Q(β) = log ∑ᵢ exp(βᵀΔᵢ)` (`logPartition`), and the
weights of a dual parameter are `qᵢ(β) = exp(βᵀΔᵢ) / ∑ⱼ exp(βᵀΔⱼ)` (`entropyWeights`), the
normalized exponential tilting weights `tiltWeight` (`entropyWeights_eq_tiltWeight`).
This is the computation of matching adjusted indirect comparison (Signorovitch and coauthors
2010; Phillippo and coauthors 2018), whose weights are these tilting weights up to a constant
factor.

* **Weak duality.** `-Q(β) ≤ ∑ᵢ qᵢ log qᵢ` for every dual parameter and every feasible `q`
  (`neg_logPartition_le_negEntropy`), by Gibbs' inequality (`sum_mul_log_le_negEntropy`).
* **Optimality.** When `β` balances, `∑ᵢ exp(βᵀΔᵢ) Δᵢ = 0`, the weights `q(β)` are feasible,
  attain `-Q(β)`, and are the unique minimizer of the entropy over the whole closed feasible set
  (`entropyWeights_isMinOn`).
* **The dual.** `Q` is convex (`convexOn_logPartition`); `β` minimizes `Q` exactly when it
  balances (`isMinOn_logPartition_iff`), the first order condition `∇Q(β) = 0`.
* **Strict convexity.** `Q` is strictly convex exactly when no nonzero `v` has `vᵀΔᵢ` constant in
  `i` (`strictConvexOn_logPartition`, `not_strictConvexOn_logPartition`). That the `Δᵢ` span the
  space is not enough: a single unit with `Δ = 1` has `Q(β) = β`
  (`not_strictConvexOn_logPartition_example`). Spanning together with a balancing weight vector
  of nonzero total is enough (`forall_const_dotProduct_imp_of_span`); the partition function
  itself is strictly convex as soon as the `Δᵢ` span (`strictConvexOn_partitionFunction`).
* **Multipliers.** Tilting weights `exp(α + βᵀΔᵢ)` with any `(α, β)` are feasible exactly when
  `e^α = 1 / ∑ᵢ exp(βᵀΔᵢ)` and `β` balances (`tiltWeight_mem_balancingSet_iff`).

## Main definitions

* `balancingSet Δ`, `negEntropy`, `partitionFunction`, `logPartition`, `entropyWeights`.

## Main results

* `sum_mul_log_le_negEntropy`, `neg_logPartition_le_negEntropy`, `entropyWeights_isMinOn`.
* `isMinOn_logPartition_iff`, `convexOn_logPartition`, `strictConvexOn_logPartition`,
  `not_strictConvexOn_logPartition`, `strictConvexOn_partitionFunction`.
* `tiltWeight_mem_balancingSet_iff`.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open Finset

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-! ### The program -/

section Program

variable (Δ : ι → Fin p → ℝ)

/-- The **feasible set of entropy balancing**: probability vectors `q` that balance the centered
features, `∑ᵢ qᵢ Δᵢ = 0`. -/
def balancingSet : Set (ι → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ MomentBalanced q Δ 0}

/-- The **negative entropy** `∑ᵢ qᵢ log qᵢ` of a weight vector (with Mathlib's `log 0 = 0`, so
`0 log 0 = 0`). -/
noncomputable def negEntropy (q : ι → ℝ) : ℝ := ∑ i, q i * Real.log (q i)

/-- The **partition function** `Z(β) = ∑ᵢ exp(βᵀΔᵢ)`. -/
noncomputable def partitionFunction (β : Fin p → ℝ) : ℝ := ∑ i, Real.exp (β ⬝ᵥ Δ i)

/-- The **dual objective**, the log partition function `Q(β) = log ∑ᵢ exp(βᵀΔᵢ)`. -/
noncomputable def logPartition (β : Fin p → ℝ) : ℝ := Real.log (partitionFunction Δ β)

/-- The **entropy balancing weights** of a dual parameter, `exp(βᵀΔᵢ) / ∑ⱼ exp(βᵀΔⱼ)`. -/
noncomputable def entropyWeights (β : Fin p → ℝ) (i : ι) : ℝ :=
  Real.exp (β ⬝ᵥ Δ i) / partitionFunction Δ β

variable {Δ}

/-- Balance at zero of the centered features is balance at `t` of the features. -/
theorem momentBalanced_sub_iff {w : ι → ℝ} {z : ι → Fin p → ℝ} {t : Fin p → ℝ} :
    MomentBalanced w (fun i => z i - t) 0 ↔ MomentBalanced w z t := by
  simp only [MomentBalanced, sub_zero]

/-- Membership of the feasible set for the centered features `zᵢ - t`: a probability vector
whose weighted mean of the `zᵢ` is `t`. -/
theorem mem_balancingSet_sub_iff {z : ι → Fin p → ℝ} {t : Fin p → ℝ} {q : ι → ℝ} :
    q ∈ balancingSet (fun i => z i - t) ↔ (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∑ i, q i • z i = t := by
  simp only [balancingSet, Set.mem_ofPred_eq, momentBalanced_sub_iff]
  exact and_congr_right fun _ => ⟨fun ⟨h1, h2⟩ => ⟨h1, (momentBalanced_iff_sum_smul_eq h1).1 h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, (momentBalanced_iff_sum_smul_eq h1).2 h2⟩⟩

theorem partitionFunction_pos [Nonempty ι] (β : Fin p → ℝ) : 0 < partitionFunction Δ β :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem entropyWeights_pos [Nonempty ι] (β : Fin p → ℝ) (i : ι) : 0 < entropyWeights Δ β i :=
  div_pos (Real.exp_pos _) (partitionFunction_pos β)

theorem sum_entropyWeights [Nonempty ι] (β : Fin p → ℝ) : ∑ i, entropyWeights Δ β i = 1 := by
  simp only [entropyWeights, ← Finset.sum_div]
  exact div_self (partitionFunction_pos β).ne'

/-- The entropy weights are the normalized exponential weights. -/
theorem entropyWeights_eq_normalizedWeights (β : Fin p → ℝ) :
    entropyWeights Δ β = normalizedWeights fun i => Real.exp (β ⬝ᵥ Δ i) := rfl

/-- The logarithm of an entropy weight is affine in `Δᵢ`: `log qᵢ(β) = βᵀΔᵢ - Q(β)`. -/
theorem log_entropyWeights [Nonempty ι] (β : Fin p → ℝ) (i : ι) :
    Real.log (entropyWeights Δ β i) = β ⬝ᵥ Δ i - logPartition Δ β := by
  rw [entropyWeights, Real.log_div (Real.exp_pos _).ne' (partitionFunction_pos β).ne',
    Real.log_exp, logPartition]

/-- **The entropy weights are the tilting weights** with features `φ`, centering `t` and
intercept `-Q(β)`: for `Δᵢ = φ(xᵢ) - t`, `qᵢ(β) = exp(-Q(β) + βᵀ(φ(xᵢ) - t))`. -/
theorem entropyWeights_eq_tiltWeight [Nonempty ι] {𝒳 : Type*} (φ : 𝒳 → Fin p → ℝ)
    (x : ι → 𝒳) (t β : Fin p → ℝ) (i : ι) :
    entropyWeights (fun j => φ (x j) - t) β i =
      tiltWeight φ t (-logPartition (fun j => φ (x j) - t) β) β (x i) := by
  rw [tiltWeight, Real.exp_add, Real.exp_neg, logPartition,
    Real.exp_log (partitionFunction_pos β), entropyWeights, div_eq_inv_mul]

/-- `βᵀ ∑ᵢ vᵢ Δᵢ = ∑ᵢ vᵢ βᵀΔᵢ`. -/
theorem sum_mul_dotProduct (β : Fin p → ℝ) (v : ι → ℝ) :
    ∑ i, v i * (β ⬝ᵥ Δ i) = β ⬝ᵥ ∑ i, v i • Δ i := by
  rw [dotProduct_sum]
  simp [dotProduct_smul]

theorem momentBalanced_zero_iff {v : ι → ℝ} : MomentBalanced v Δ 0 ↔ ∑ i, v i • Δ i = 0 := by
  simp only [MomentBalanced, sub_zero]

/-- A balanced weight vector annihilates every linear predictor: `∑ᵢ vᵢ βᵀΔᵢ = 0`. -/
theorem sum_mul_dotProduct_eq_zero {v : ι → ℝ} (hv : MomentBalanced v Δ 0) (β : Fin p → ℝ) :
    ∑ i, v i * (β ⬝ᵥ Δ i) = 0 := by
  rw [sum_mul_dotProduct, momentBalanced_zero_iff.1 hv, dotProduct_zero]

/-- The entropy weights are feasible exactly when the dual parameter balances:
`∑ᵢ exp(βᵀΔᵢ) Δᵢ = 0`. -/
theorem entropyWeights_mem_balancingSet_iff [Nonempty ι] (β : Fin p → ℝ) :
    entropyWeights Δ β ∈ balancingSet Δ ↔ MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0 := by
  have h : entropyWeights Δ β = fun i => (partitionFunction Δ β)⁻¹ * Real.exp (β ⬝ᵥ Δ i) := by
    funext i; rw [entropyWeights, div_eq_inv_mul]
  simp only [balancingSet, Set.mem_ofPred_eq, sum_entropyWeights, true_and,
    fun i => (entropyWeights_pos (Δ := Δ) β i).le, implies_true]
  rw [h, momentBalanced_smul_iff (inv_ne_zero (partitionFunction_pos β).ne')]

end Program

/-! ### Gibbs' inequality and weak duality -/

section Duality

variable {Δ : ι → Fin p → ℝ}

/-- The termwise Gibbs inequality: for `v ≥ 0` and `q > 0`, `v log q - v log v ≤ q - v`, with
equality only when `v = q`. -/
theorem mul_log_sub_mul_log_le {v q : ℝ} (hv : 0 ≤ v) (hq : 0 < q) :
    v * Real.log q - v * Real.log v ≤ q - v ∧
      (v * Real.log q - v * Real.log v = q - v → v = q) := by
  rcases hv.eq_or_lt with rfl | hv
  · simp only [zero_mul, sub_zero, Real.log_zero]
    exact ⟨hq.le, fun h => absurd h.symm hq.ne'⟩
  have hx : 0 < q / v := div_pos hq hv
  have key : v * Real.log q - v * Real.log v = v * Real.log (q / v) := by
    rw [Real.log_div hq.ne' hv.ne']; ring
  have hle : v * Real.log (q / v) ≤ q - v := by
    have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx) hv.le
    rwa [mul_sub, mul_div_cancel₀ _ hv.ne', mul_one] at this
  refine ⟨key ▸ hle, fun h => ?_⟩
  by_contra hne
  have h1 : q / v ≠ 1 := fun h1 => hne ((div_eq_one_iff_eq hv.ne').1 h1).symm
  have := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos hx h1) hv
  rw [mul_sub, mul_div_cancel₀ _ hv.ne', mul_one, ← key] at this
  exact this.ne h

/-- **Gibbs' inequality**: for `v ≥ 0` and `q > 0` with the same total,
`∑ᵢ vᵢ log qᵢ ≤ ∑ᵢ vᵢ log vᵢ`, with equality only when `v = q`. -/
theorem sum_mul_log_le_negEntropy {v q : ι → ℝ} (hv : ∀ i, 0 ≤ v i) (hq : ∀ i, 0 < q i)
    (hs : ∑ i, v i = ∑ i, q i) :
    ∑ i, v i * Real.log (q i) ≤ negEntropy v ∧
      (negEntropy v ≤ ∑ i, v i * Real.log (q i) → v = q) := by
  have hterm := fun i => mul_log_sub_mul_log_le (hv i) (hq i)
  have hsum : ∑ i, (q i - v i) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hdiff : ∑ i, v i * Real.log (q i) - negEntropy v =
      ∑ i, (v i * Real.log (q i) - v i * Real.log (v i)) := by
    rw [negEntropy, Finset.sum_sub_distrib]
  have hle : ∑ i, v i * Real.log (q i) - negEntropy v ≤ 0 := by
    rw [hdiff, ← hsum]
    exact Finset.sum_le_sum fun i _ => (hterm i).1
  refine ⟨by linarith, fun h => funext fun i => ?_⟩
  have h0 : ∑ i, ((q i - v i) - (v i * Real.log (q i) - v i * Real.log (v i))) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, ← hdiff]
    linarith
  have hnn : ∀ j ∈ (univ : Finset ι),
      0 ≤ (q j - v j) - (v j * Real.log (q j) - v j * Real.log (v j)) :=
    fun j _ => sub_nonneg.2 (hterm j).1
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 i (mem_univ _)
  exact (hterm i).2 (by linarith)

/-- The cross entropy of a feasible `v` against the entropy weights is `-Q(β)`. -/
theorem sum_mul_log_entropyWeights [Nonempty ι] {v : ι → ℝ} (hv : v ∈ balancingSet Δ)
    (β : Fin p → ℝ) : ∑ i, v i * Real.log (entropyWeights Δ β i) = -logPartition Δ β := by
  obtain ⟨-, hvs, hvb⟩ := hv
  simp only [log_entropyWeights, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hvs,
    sum_mul_dotProduct_eq_zero hvb, one_mul, zero_sub]

/-- **Weak duality**: for every dual parameter `β` and every feasible `v`,
`-Q(β) ≤ ∑ᵢ vᵢ log vᵢ`. -/
theorem neg_logPartition_le_negEntropy [Nonempty ι] (β : Fin p → ℝ) {v : ι → ℝ}
    (hv : v ∈ balancingSet Δ) : -logPartition Δ β ≤ negEntropy v := by
  have h := (sum_mul_log_le_negEntropy hv.1 (entropyWeights_pos (Δ := Δ) β)
    (by rw [hv.2.1, sum_entropyWeights])).1
  rwa [sum_mul_log_entropyWeights hv] at h

/-- **Optimality of the exponential weights** (strong duality): if `β` balances the centered
features, `∑ᵢ exp(βᵀΔᵢ) Δᵢ = 0`, the entropy weights `q(β)` are feasible, have negative
entropy `-Q(β)`, minimize the negative entropy over the feasible set, and are its unique
minimizer. -/
theorem entropyWeights_isMinOn [Nonempty ι] {β : Fin p → ℝ}
    (hβ : MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0) :
    entropyWeights Δ β ∈ balancingSet Δ ∧ negEntropy (entropyWeights Δ β) = -logPartition Δ β ∧
      IsMinOn negEntropy (balancingSet Δ) (entropyWeights Δ β) ∧
      ∀ v ∈ balancingSet Δ, negEntropy v ≤ negEntropy (entropyWeights Δ β) →
        v = entropyWeights Δ β := by
  have hf := (entropyWeights_mem_balancingSet_iff β).2 hβ
  have hH : negEntropy (entropyWeights Δ β) = -logPartition Δ β :=
    sum_mul_log_entropyWeights hf β
  refine ⟨hf, hH, fun v hv => ?_, fun v hv hle => ?_⟩
  · simp only [Set.mem_ofPred_eq]
    rw [hH]; exact neg_logPartition_le_negEntropy β hv
  · refine (sum_mul_log_le_negEntropy hv.1 (entropyWeights_pos (Δ := Δ) β)
      (by rw [hv.2.1, sum_entropyWeights])).2 ?_
    rw [sum_mul_log_entropyWeights hv, ← hH]
    exact hle

end Duality

/-! ### The dual objective -/

section Dual

variable {Δ : ι → Fin p → ℝ}

theorem partitionFunction_line (β v : Fin p → ℝ) (s : ℝ) :
    partitionFunction Δ (β + s • v) = ∑ i, Real.exp (β ⬝ᵥ Δ i + s * (v ⬝ᵥ Δ i)) := by
  simp [partitionFunction, add_dotProduct, smul_dotProduct]

/-- **The minimizers of the dual are the balancing parameters**: `β` minimizes
`Q(β) = log ∑ᵢ exp(βᵀΔᵢ)` exactly when `∑ᵢ exp(βᵀΔᵢ) Δᵢ = 0` (`∇Q(β) = 0`). One direction is the
tangent line inequality `exp(y) ≥ 1 + y` at `(u - β)ᵀΔᵢ`; the other differentiates `Z` along
the direction of the imbalance. -/
theorem isMinOn_logPartition_iff [Nonempty ι] (β : Fin p → ℝ) :
    IsMinOn (logPartition Δ) Set.univ β ↔
      MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0 := by
  rw [momentBalanced_zero_iff]
  have hZ : IsMinOn (logPartition Δ) Set.univ β ↔
      ∀ u, partitionFunction Δ β ≤ partitionFunction Δ u := by
    simp only [isMinOn_univ_iff, logPartition]
    exact forall_congr' fun u =>
      Real.log_le_log_iff (partitionFunction_pos β) (partitionFunction_pos u)
  rw [hZ]
  constructor
  · intro hmin
    set G := ∑ i, Real.exp (β ⬝ᵥ Δ i) • Δ i with hG
    have hderiv : HasDerivAt (fun s : ℝ => ∑ i, Real.exp (β ⬝ᵥ Δ i + s * (G ⬝ᵥ Δ i)))
        (∑ i, Real.exp (β ⬝ᵥ Δ i + 0 * (G ⬝ᵥ Δ i)) * (G ⬝ᵥ Δ i)) 0 := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      have h1 : HasDerivAt (fun s : ℝ => β ⬝ᵥ Δ i + s * (G ⬝ᵥ Δ i)) (G ⬝ᵥ Δ i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (G ⬝ᵥ Δ i)).const_add (β ⬝ᵥ Δ i)
      exact h1.exp
    have hloc : IsLocalMin (fun s : ℝ => ∑ i, Real.exp (β ⬝ᵥ Δ i + s * (G ⬝ᵥ Δ i))) 0 := by
      refine Filter.Eventually.of_forall fun s => ?_
      have h0 := partitionFunction_line (Δ := Δ) β G 0
      have hs := partitionFunction_line (Δ := Δ) β G s
      simp only [zero_smul, add_zero] at h0
      change (∑ i, Real.exp (β ⬝ᵥ Δ i + 0 * (G ⬝ᵥ Δ i))) ≤
        ∑ i, Real.exp (β ⬝ᵥ Δ i + s * (G ⬝ᵥ Δ i))
      rw [← h0, ← hs]
      exact hmin _
    have h0 := hloc.hasDerivAt_eq_zero hderiv
    simp only [zero_mul, add_zero] at h0
    have hGG : G ⬝ᵥ G = 0 := by
      rw [← h0, hG, dotProduct_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dotProduct_smul, smul_eq_mul, mul_comm]
    exact dotProduct_self_eq_zero.1 hGG
  · intro hβ u
    have hexp : ∀ i, Real.exp (β ⬝ᵥ Δ i) * (1 + (u - β) ⬝ᵥ Δ i) ≤ Real.exp (u ⬝ᵥ Δ i) := by
      intro i
      have h := Real.add_one_le_exp ((u - β) ⬝ᵥ Δ i)
      have he : Real.exp (u ⬝ᵥ Δ i) = Real.exp (β ⬝ᵥ Δ i) * Real.exp ((u - β) ⬝ᵥ Δ i) := by
        rw [← Real.exp_add, sub_dotProduct]; ring_nf
      rw [he]
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    have hsum : ∑ i, Real.exp (β ⬝ᵥ Δ i) * (1 + (u - β) ⬝ᵥ Δ i) = partitionFunction Δ β := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, sum_mul_dotProduct, hβ,
        dotProduct_zero, add_zero, partitionFunction]
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => hexp i

/-- The termwise exponent of the convexity argument: with `A = Z(x)` and `B = Z(y)`,
`exp((a x + b y)ᵀΔᵢ) e^{-c} = exp(a (xᵀΔᵢ - log A) + b (yᵀΔᵢ - log B))` for
`c = a log A + b log B`. -/
theorem exp_dotProduct_combo (x y : Fin p → ℝ) (a b : ℝ) (i : ι) :
    Real.exp ((a • x + b • y) ⬝ᵥ Δ i) *
        Real.exp (-(a * logPartition Δ x + b * logPartition Δ y)) =
      Real.exp (a * (x ⬝ᵥ Δ i - logPartition Δ x) + b * (y ⬝ᵥ Δ i - logPartition Δ y)) := by
  rw [← Real.exp_add, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  congr 1
  ring

theorem sum_exp_sub_logPartition [Nonempty ι] (x : Fin p → ℝ) :
    ∑ i, Real.exp (x ⬝ᵥ Δ i - logPartition Δ x) = 1 := by
  simp only [Real.exp_sub, logPartition, Real.exp_log (partitionFunction_pos x), ← Finset.sum_div]
  exact div_self (partitionFunction_pos x).ne'

/-- **The dual objective is convex.** Convexity of `exp` applied termwise to
`a (xᵀΔᵢ - Q(x)) + b (yᵀΔᵢ - Q(y))` gives `Z(a x + b y) ≤ exp(a Q(x) + b Q(y))`. -/
theorem convexOn_logPartition [Nonempty ι] : ConvexOn ℝ Set.univ (logPartition Δ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set c := a * logPartition Δ x + b * logPartition Δ y
  have key : partitionFunction Δ (a • x + b • y) * Real.exp (-c) ≤ 1 := by
    rw [partitionFunction, Finset.sum_mul]
    calc ∑ i, Real.exp ((a • x + b • y) ⬝ᵥ Δ i) * Real.exp (-c)
        = ∑ i, Real.exp (a * (x ⬝ᵥ Δ i - logPartition Δ x) +
            b * (y ⬝ᵥ Δ i - logPartition Δ y)) :=
          Finset.sum_congr rfl fun i _ => exp_dotProduct_combo x y a b i
      _ ≤ ∑ i, (a * Real.exp (x ⬝ᵥ Δ i - logPartition Δ x) +
            b * Real.exp (y ⬝ᵥ Δ i - logPartition Δ y)) :=
          Finset.sum_le_sum fun i _ => by
            simpa [smul_eq_mul] using
              convexOn_exp.2 (Set.mem_univ (x ⬝ᵥ Δ i - logPartition Δ x))
                (Set.mem_univ (y ⬝ᵥ Δ i - logPartition Δ y)) ha hb hab
      _ = 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            sum_exp_sub_logPartition, sum_exp_sub_logPartition, mul_one, mul_one, hab]
  have hle : partitionFunction Δ (a • x + b • y) ≤ Real.exp c := by
    have := mul_le_mul_of_nonneg_right key (Real.exp_pos c).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at this
  calc logPartition Δ (a • x + b • y) ≤ Real.log (Real.exp c) :=
        Real.log_le_log (partitionFunction_pos _) hle
    _ = c := Real.log_exp c

/-- **Strict convexity of the dual.** If no nonzero `v` has `vᵀΔᵢ` constant in `i`, the log
partition function is strictly convex. Along a segment between distinct points some term of the
convexity argument is strict, since otherwise `(x - y)ᵀΔᵢ = Q(x) - Q(y)` for every `i`. -/
theorem strictConvexOn_logPartition [Nonempty ι]
    (h : ∀ v : Fin p → ℝ, (∀ i j, v ⬝ᵥ Δ i = v ⬝ᵥ Δ j) → v = 0) :
    StrictConvexOn ℝ Set.univ (logPartition Δ) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set c := a * logPartition Δ x + b * logPartition Δ y
  have hex : ∃ i, x ⬝ᵥ Δ i - logPartition Δ x ≠ y ⬝ᵥ Δ i - logPartition Δ y := by
    by_contra hne
    push Not at hne
    refine hxy (sub_eq_zero.1 (h (x - y) fun i j => ?_))
    have hi := hne i
    have hj := hne j
    rw [sub_dotProduct, sub_dotProduct]
    linarith
  obtain ⟨i₀, hi₀⟩ := hex
  have key : partitionFunction Δ (a • x + b • y) * Real.exp (-c) < 1 := by
    rw [partitionFunction, Finset.sum_mul]
    calc ∑ i, Real.exp ((a • x + b • y) ⬝ᵥ Δ i) * Real.exp (-c)
        = ∑ i, Real.exp (a * (x ⬝ᵥ Δ i - logPartition Δ x) +
            b * (y ⬝ᵥ Δ i - logPartition Δ y)) :=
          Finset.sum_congr rfl fun i _ => exp_dotProduct_combo x y a b i
      _ < ∑ i, (a * Real.exp (x ⬝ᵥ Δ i - logPartition Δ x) +
            b * Real.exp (y ⬝ᵥ Δ i - logPartition Δ y)) := by
          refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, mem_univ _, ?_⟩
          · simpa [smul_eq_mul] using
              convexOn_exp.2 (Set.mem_univ (x ⬝ᵥ Δ i - logPartition Δ x))
                (Set.mem_univ (y ⬝ᵥ Δ i - logPartition Δ y)) ha.le hb.le hab
          · simpa [smul_eq_mul] using
              strictConvexOn_exp.2 (Set.mem_univ (x ⬝ᵥ Δ i₀ - logPartition Δ x))
                (Set.mem_univ (y ⬝ᵥ Δ i₀ - logPartition Δ y)) hi₀ ha hb hab
      _ = 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            sum_exp_sub_logPartition, sum_exp_sub_logPartition, mul_one, mul_one, hab]
  have hlt : partitionFunction Δ (a • x + b • y) < Real.exp c := by
    have := mul_lt_mul_of_pos_right key (Real.exp_pos c)
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at this
  calc logPartition Δ (a • x + b • y) < Real.log (Real.exp c) :=
        Real.log_lt_log (partitionFunction_pos _) hlt
    _ = c := Real.log_exp c

/-- **The dual is affine along a direction of constant linear predictor**: if `vᵀΔᵢ = k` for
every `i`, then `Q(β + s v) = Q(β) + s k`. -/
theorem logPartition_add_smul_of_const [Nonempty ι] {v : Fin p → ℝ} {k : ℝ}
    (hv : ∀ i, v ⬝ᵥ Δ i = k) (β : Fin p → ℝ) (s : ℝ) :
    logPartition Δ (β + s • v) = logPartition Δ β + s * k := by
  have hZ : partitionFunction Δ (β + s • v) = Real.exp (s * k) * partitionFunction Δ β := by
    rw [partitionFunction_line, partitionFunction, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv i, ← Real.exp_add, add_comm]
  rw [logPartition, hZ, Real.log_mul (Real.exp_pos _).ne' (partitionFunction_pos β).ne',
    Real.log_exp, logPartition, add_comm]

/-- **The condition of strict convexity is necessary**: if some nonzero `v` has `vᵀΔᵢ` constant
in `i`, the log partition function is not strictly convex. -/
theorem not_strictConvexOn_logPartition [Nonempty ι] {v : Fin p → ℝ} (hv0 : v ≠ 0)
    {k : ℝ} (hv : ∀ i, v ⬝ᵥ Δ i = k) : ¬ StrictConvexOn ℝ Set.univ (logPartition Δ) := by
  intro hs
  have h := hs.2 (Set.mem_univ 0) (Set.mem_univ v) hv0.symm (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have h1 := logPartition_add_smul_of_const hv 0 1
  have h2 := logPartition_add_smul_of_const hv 0 (1 / 2)
  simp only [zero_add, one_smul, one_mul, smul_zero] at h1 h2 h
  rw [h1, h2] at h
  simp only [smul_eq_mul] at h
  linarith

/-- **Spanning does not give strict convexity**: for a single unit with centered feature
`Δ = 1 ∈ ℝ¹`, the features span `ℝ¹` but `Q(β) = β` is not strictly convex. -/
theorem not_strictConvexOn_logPartition_example :
    Submodule.span ℝ (Set.range fun _ : Fin 1 => (fun _ : Fin 1 => (1 : ℝ))) = ⊤ ∧
      ¬ StrictConvexOn ℝ Set.univ (logPartition fun _ : Fin 1 => (fun _ : Fin 1 => (1 : ℝ))) := by
  refine ⟨?_, not_strictConvexOn_logPartition (v := fun _ => 1) (k := 1)
    (fun h => by simpa using congrFun h 0) fun i => by simp [dotProduct]⟩
  refine Submodule.eq_top_iff'.2 fun u => ?_
  have hu : u = u 0 • (fun _ : Fin 1 => (1 : ℝ)) := by
    funext j; fin_cases j; simp
  rw [hu]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/-- **Spanning features and a balanced weight vector give the condition of strict convexity**:
if the `Δᵢ` span `ℝ^p` and some weights with nonzero total balance them, then no nonzero `v` has
`vᵀΔᵢ` constant in `i`. -/
theorem forall_const_dotProduct_imp_of_span (hspan : Submodule.span ℝ (Set.range Δ) = ⊤)
    {q : ι → ℝ} (hq : MomentBalanced q Δ 0) (hq1 : ∑ i, q i ≠ 0) (v : Fin p → ℝ)
    (hv : ∀ i j, v ⬝ᵥ Δ i = v ⬝ᵥ Δ j) : v = 0 := by
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    have hzero : v ⬝ᵥ Δ i₀ = 0 := by
      have h := sum_mul_dotProduct_eq_zero hq v
      simp only [hv _ i₀, ← Finset.sum_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hq1
    have hall : ∀ y ∈ Submodule.span ℝ (Set.range Δ), v ⬝ᵥ y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; rw [hv i i₀, hzero]
      | zero => exact dotProduct_zero _
      | add y z _ _ hy hz => rw [dotProduct_add, hy, hz, add_zero]
      | smul c y _ hy => rw [dotProduct_smul, hy, smul_zero]
    exact dotProduct_self_eq_zero.1 (hall v (hspan ▸ Submodule.mem_top))
  · exact absurd (by simp [not_nonempty_iff.1 hι]) hq1

/-- **The partition function is strictly convex when the features span**: if the `Δᵢ` span
`ℝ^p`, then `Z(β) = ∑ᵢ exp(βᵀΔᵢ)` is strictly convex (distinct points differ on some `Δᵢ`, and
`exp` is strictly convex). -/
theorem strictConvexOn_partitionFunction (hspan : Submodule.span ℝ (Set.range Δ) = ⊤) :
    StrictConvexOn ℝ Set.univ (partitionFunction Δ) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hex : ∃ i, x ⬝ᵥ Δ i ≠ y ⬝ᵥ Δ i := by
    by_contra hne
    push Not at hne
    have hall : ∀ z ∈ Submodule.span ℝ (Set.range Δ), (x - y) ⬝ᵥ z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨i, rfl⟩ := hz; rw [sub_dotProduct, hne i, sub_self]
      | zero => exact dotProduct_zero _
      | add z w _ _ hz hw => rw [dotProduct_add, hz, hw, add_zero]
      | smul c z _ hz => rw [dotProduct_smul, hz, smul_zero]
    exact hxy (sub_eq_zero.1 (dotProduct_self_eq_zero.1 (hall _ (hspan ▸ Submodule.mem_top))))
  obtain ⟨i₀, hi₀⟩ := hex
  simp only [partitionFunction, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, mem_univ _, ?_⟩
  · have := convexOn_exp.2 (Set.mem_univ (x ⬝ᵥ Δ i)) (Set.mem_univ (y ⬝ᵥ Δ i)) ha.le hb.le hab
    simpa [add_dotProduct, smul_dotProduct] using this
  · have := strictConvexOn_exp.2 (Set.mem_univ (x ⬝ᵥ Δ i₀)) (Set.mem_univ (y ⬝ᵥ Δ i₀)) hi₀ ha hb
      hab
    simpa [add_dotProduct, smul_dotProduct] using this

/-- **The two constraints determine the multipliers**: tilting weights `exp(α + βᵀΔᵢ)` with any
`(α, β)` are feasible exactly when `e^α = 1 / Z(β)` and `β` balances; they are then the entropy
weights of `β`. -/
theorem tiltWeight_mem_balancingSet_iff [Nonempty ι] (α : ℝ) (β : Fin p → ℝ) :
    ((fun i => tiltWeight Δ 0 α β i) ∈ balancingSet Δ ↔
      Real.exp α = 1 / partitionFunction Δ β ∧
        MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0) ∧
    ((fun i => tiltWeight Δ 0 α β i) ∈ balancingSet Δ →
      (fun i => tiltWeight Δ 0 α β i) = entropyWeights Δ β) := by
  have hZ := partitionFunction_pos (Δ := Δ) β
  have hw : ∀ i, tiltWeight Δ 0 α β i = Real.exp α * Real.exp (β ⬝ᵥ Δ i) := fun i => by
    rw [tiltWeight_eq_exp_mul, sub_zero]
  have hsum : ∑ i, tiltWeight Δ 0 α β i = Real.exp α * partitionFunction Δ β := by
    simp only [hw, ← Finset.mul_sum, partitionFunction]
  have h1 : (fun i => tiltWeight Δ 0 α β i) ∈ balancingSet Δ ↔
      Real.exp α = 1 / partitionFunction Δ β ∧
        MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0 := by
    simp only [balancingSet, Set.mem_ofPred_eq, hsum, fun i => (tiltWeight_pos Δ 0 α β i).le,
      implies_true, true_and, eq_div_iff hZ.ne']
    simp only [hw]
    rw [momentBalanced_smul_iff (Real.exp_pos α).ne']
  refine ⟨h1, fun hf => funext fun i => ?_⟩
  rw [hw, (h1.1 hf).1, entropyWeights, one_div, div_eq_inv_mul]

end Dual

end PopulationAdjustment

end CausalInference
