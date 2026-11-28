/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.TriangularArrayLimit
public import CausalInference.Estimation.GaussianLinearImage

/-!
# The Lindeberg central limit theorem for vector triangular arrays

Row `n` is a finite family of independent, centered, square integrable random vectors
`X n i` in `ℝ^ι` (`EuclideanSpace ℝ ι`) on a probability space `(Ω n, P n)`. If for every
direction `t` the projected variances sum to `tᵀ S t`, with `S` positive semidefinite, and the
Lindeberg condition `∑_i E[‖X_{n,i}‖² 1{ε < ‖X_{n,i}‖}] → 0` holds for every `ε > 0`, then the row
sums converge in distribution to `N(0, S)`.

The proof is the device of Cramér and Wold, run on characteristic functions because the
probability spaces change with `n`: the characteristic function of a vector at `t` is that of its
projection on `t` at `1`, and each projection is a real Lindeberg array, since
`⟪y, t⟫² 1{ε < |⟪y, t⟫|} ≤ c² ‖y‖² 1{ε / c < ‖y‖}` for `c = ‖t‖ + 1`.

## Main results

* `CausalInference.TriangularArray.indicator_inner_sq_le`: the pointwise Lindeberg comparison.
* `CausalInference.TriangularArray.tendstoInDistribution_sum_euclidean`: **the vector Lindeberg
  central limit theorem**.

## References

* H. Cramér and H. Wold (1936), *Some theorems on distribution functions*, Journal of the London
  Mathematical Society 11.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace CausalInference

namespace TriangularArray

/-- **Lindeberg terms of a projection.** For `c = ‖t‖ + 1` and `ε` real,
`⟪y, t⟫² 1{ε < |⟪y, t⟫|} ≤ c² ‖y‖² 1{ε / c < ‖y‖}`. Cauchy and Schwarz:
`|⟪y, t⟫| ≤ c ‖y‖`. -/
theorem indicator_inner_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (y t : E) (ε : ℝ) :
    {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) ⟪y, t⟫ ≤
      (‖t‖ + 1) ^ 2 * {z : E | ε / (‖t‖ + 1) < ‖z‖}.indicator (fun z ↦ ‖z‖ ^ 2) y := by
  set c := ‖t‖ + 1 with hc
  have hc0 : 0 < c := by positivity
  have hcs : |⟪y, t⟫| ≤ c * ‖y‖ := by
    calc |⟪y, t⟫| ≤ ‖y‖ * ‖t‖ := abs_real_inner_le_norm _ _
      _ ≤ c * ‖y‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  by_cases hx : ε < |⟪y, t⟫|
  · have hx' : ε / c < ‖y‖ := by
      rw [div_lt_iff₀ hc0]
      linarith
    rw [Set.indicator_of_mem (show ⟪y, t⟫ ∈ {x : ℝ | ε < |x|} from hx),
      Set.indicator_of_mem (show y ∈ {z : E | ε / c < ‖z‖} from hx')]
    have h1 : ⟪y, t⟫ ^ 2 = |⟪y, t⟫| ^ 2 := (sq_abs _).symm
    rw [h1]
    have := pow_le_pow_left₀ (abs_nonneg _) hcs 2
    rw [mul_pow] at this
    exact this
  · rw [Set.indicator_of_notMem (show ⟪y, t⟫ ∉ {x : ℝ | ε < |x|} from hx)]
    exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The vector Lindeberg central limit theorem.** For each `n` let `X n 0, …, X n (k n - 1)` be
independent centered square integrable random vectors in `ℝ^ι` on a probability space
`(Ω n, P n)`. Let `S` be positive semidefinite with `∑_i E[⟪X_{n,i}, t⟫²] → tᵀ S t` for every `t`,
and let the Lindeberg condition `∑_i E[‖X_{n,i}‖² 1{ε < ‖X_{n,i}‖}] → 0` hold for every `ε > 0`.
Then the row sums `∑_i X_{n,i}` converge in distribution to every `Y` with law `N(0, S)`. -/
theorem tendstoInDistribution_sum_euclidean {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {k : ℕ → ℕ}
    {X : (n : ℕ) → Fin (k n) → Ω n → EuclideanSpace ℝ ι} (hind : ∀ n, iIndepFun (X n) (P n))
    (h2 : ∀ n i, MemLp (X n i) 2 (P n)) (h0 : ∀ n i, ∫ ω, X n i ω ∂P n = 0)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hcov : ∀ t, Tendsto (fun n ↦ ∑ i, ∫ ω, ⟪X n i ω, t⟫ ^ 2 ∂P n) atTop
      (𝓝 (WithLp.ofLp t ⬝ᵥ S *ᵥ WithLp.ofLp t)))
    (hL : ∀ ε, 0 < ε → Tendsto (fun n ↦ ∑ i, ∫ ω,
      {y : EuclideanSpace ℝ ι | ε < ‖y‖}.indicator (fun y ↦ ‖y‖ ^ 2) (X n i ω) ∂P n) atTop
      (𝓝 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ ι} (hY : HasLaw Y (multivariateGaussian 0 S) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Y P P' := by
  have hXm : ∀ n i, AEMeasurable (X n i) (P n) := fun n i ↦
    (h2 n i).aestronglyMeasurable.aemeasurable
  have hsum : ∀ n, AEMeasurable (fun ω ↦ ∑ i, X n i ω) (P n) := fun n ↦
    Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm n i
  refine TendstoInDistribution.of_tendsto_charFun hsum hY.aemeasurable fun t ↦ ?_
  have hAm : ∀ r : ℝ, MeasurableSet {y : EuclideanSpace ℝ ι | r < ‖y‖} := fun r ↦
    measurableSet_lt measurable_const (by fun_prop)
  have hAm' : ∀ r : ℝ, MeasurableSet {x : ℝ | r < |x|} := fun r ↦
    measurableSet_lt measurable_const (by fun_prop)
  -- the projected array
  have hind' : ∀ n, iIndepFun (fun i ω ↦ ⟪X n i ω, t⟫) (P n) := fun n ↦
    (hind n).comp (fun _ y ↦ ⟪y, t⟫) fun _ ↦ by fun_prop
  have h2' : ∀ n i, MemLp (fun ω ↦ ⟪X n i ω, t⟫) 2 (P n) := fun n i ↦ (h2 n i).inner_const t
  have h0' : ∀ n i, ∫ ω, ⟪X n i ω, t⟫ ∂P n = 0 := fun n i ↦ by
    calc ∫ ω, ⟪X n i ω, t⟫ ∂P n = ∫ ω, ⟪t, X n i ω⟫ ∂P n :=
          integral_congr_ae (ae_of_all _ fun ω ↦ real_inner_comm _ _)
      _ = ⟪t, ∫ ω, X n i ω ∂P n⟫ := integral_inner ((h2 n i).integrable one_le_two) t
      _ = 0 := by rw [h0 n i, inner_zero_right]
  have hL' : ∀ ε, 0 < ε → Tendsto (fun n ↦ ∑ i,
      ∫ ω, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) ⟪X n i ω, t⟫ ∂P n) atTop (𝓝 0) := by
    intro ε hε
    set c := ‖t‖ + 1 with hc
    have hc0 : 0 < c := by positivity
    have hlim : Tendsto (fun n ↦ c ^ 2 * ∑ i, ∫ ω,
        {y : EuclideanSpace ℝ ι | ε / c < ‖y‖}.indicator (fun y ↦ ‖y‖ ^ 2) (X n i ω) ∂P n)
        atTop (𝓝 0) := by
      simpa using (hL (ε / c) (by positivity)).const_mul (c ^ 2)
    refine squeeze_zero (fun n ↦ Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦
      Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _) (fun n ↦ ?_) hlim
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hsq : Integrable (fun ω ↦ ‖X n i ω‖ ^ 2) (P n) :=
      (h2 n i).integrable_norm_pow two_ne_zero
    have hI : Integrable (fun ω ↦ {y : EuclideanSpace ℝ ι | ε / c < ‖y‖}.indicator
        (fun y ↦ ‖y‖ ^ 2) (X n i ω)) (P n) := by
      refine hsq.mono ((((by fun_prop : Measurable fun y : EuclideanSpace ℝ ι ↦ ‖y‖ ^ 2).indicator
        (hAm _)).comp_aemeasurable (hXm n i)).aestronglyMeasurable) (ae_of_all _ fun ω ↦ ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _),
        abs_of_nonneg (sq_nonneg _)]
      exact Set.indicator_le_self' (fun _ _ ↦ sq_nonneg _) _
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦
      Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _) (hI.const_mul _)
      (ae_of_all _ fun ω ↦ indicator_inner_sq_le (X n i ω) t ε)
  have hYt := hasLaw_inner_multivariateGaussian hS hY t
  have hclt := tendstoInDistribution_sum hind' h2' h0' (hcov t) hL' hYt
  have hc1 := hclt.tendsto_charFun 1
  rw [charFun_map_eq_charFun_map_inner_one hY.aemeasurable t]
  refine hc1.congr fun n ↦ ?_
  rw [charFun_map_eq_charFun_map_inner_one (hsum n) t]
  congr 2
  funext ω
  rw [sum_inner]

end TriangularArray

end CausalInference
