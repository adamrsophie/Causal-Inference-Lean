/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapDual

/-!
# The linear expansion of the bootstrap dual minimizer

Write `β₀ = tiltMinimizer` for the population tilt, `w₀ = w_{β₀}`, `Δ = φ - t`,
`M = E[w₀ Δ Δᵀ]` for the tilted second moment matrix (nonsingular under the margin condition)
and `s_y = n⁻¹ ∑ᵢ w₀(xᵢ) Δ(xᵢ)` for the resample mean of the balance function at `β₀`. For the
bootstrap dual minimizer `β*(y)` and `u = β*(y) - β₀`,

`√n ‖u‖ = O_{P*}(1)` and `√n (u + M⁻¹ s_y) = o_{P*}(1)`,

in conditional probability, in probability (`bootstrapTilt_linear`).

The proof is a second order expansion of the tilt around `β₀` at every record:
`|w_{β₀ + u}(x) c - w₀(x) c - ∑ₖ uₖ w₀(x) c Δₖ(x)| ≤ exp(p ‖β₀‖ B) |c| (p ‖u‖ B)²` when
`p ‖u‖ B ≤ 1` (`abs_tiltWeight_add_mul_sub_le`). At a feasible resample the first order condition
`n⁻¹ ∑ᵢ w_{β*}(xᵢ) Δ(xᵢ) = 0` then gives `s_y + M u = e` with `|e| ≤ Z ‖u‖`, where `Z` is small:
it collects `‖u‖` and the deviations of the resample second moments from `M`. Solving with `M⁻¹`
gives both statements, the first since `‖u‖ ≤ 2 L ∑ⱼ |s_{y,j}|` once `Z` is small, and
`√n s_y = O_{P*}(1)` by the conditional Chebyshev bound and the central limit theorem of the data.

## Main results

* `abs_tiltWeight_add_mul_sub_le`, `abs_tiltWeight_add_mul_sub_le'`: the pointwise expansions.
* `abs_resampleMean_tiltWeight_expansion_le`, `abs_resampleMean_tiltWeight_sub_le`: the same
  for resample means.
* `resampleMean_tiltWeight_bootstrapTilt_eq_zero`: the resample first order condition.
* `bootstrapTilt_linear`: the linear expansion of the bootstrap dual minimizer.

## References

* A. W. van der Vaart (1998), *Asymptotic Statistics*, Cambridge University Press, chapter 23.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap

variable {𝒳 : Type*} {p : ℕ}

/-! ### Deterministic expansions -/

/-- **Second order expansion of the tilt** at one record: for `p ‖u‖ B ≤ 1`,
`|w_{β₀ + u}(x) c - w₀(x) c - ∑ₖ uₖ w₀(x) c Δₖ(x)| ≤ exp(p ‖β₀‖ B) |c| (p ‖u‖ B)²`. -/
theorem abs_tiltWeight_add_mul_sub_le {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (β₀ u : Fin p → ℝ) (x : 𝒳) (c : ℝ) (hu : p * (‖u‖ * B) ≤ 1) :
    |tiltWeight φ t 0 (β₀ + u) x * c - tiltWeight φ t 0 β₀ x * c -
        ∑ k, u k * (tiltWeight φ t 0 β₀ x * c * (φ x k - t k))| ≤
      Real.exp (p * (‖β₀‖ * B)) * |c| * (p * (‖u‖ * B)) ^ 2 := by
  obtain ⟨v, hv⟩ : ∃ v, v = u ⬝ᵥ (φ x - t) := ⟨_, rfl⟩
  have hvb : |v| ≤ p * (‖u‖ * B) := hv ▸ abs_dotProduct_feature_le hB u x
  have hsum : ∑ k, u k * (tiltWeight φ t 0 β₀ x * c * (φ x k - t k)) =
      tiltWeight φ t 0 β₀ x * c * v := by
    simp only [hv, dotProduct, Pi.sub_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum, tiltWeight_add, ← hv]
  have he : tiltWeight φ t 0 β₀ x * Real.exp v * c - tiltWeight φ t 0 β₀ x * c -
      tiltWeight φ t 0 β₀ x * c * v = tiltWeight φ t 0 β₀ x * c * (Real.exp v - 1 - v) := by ring
  rw [he, abs_mul, abs_mul, abs_of_pos (tiltWeight_pos _ _ _ _ _)]
  have h1 := Real.abs_exp_sub_one_sub_id_le (hvb.trans hu)
  have hw := (tiltWeight_mem_Icc (hB x) (le_refl ‖β₀‖)).2
  have hv2 : v ^ 2 ≤ (p * (‖u‖ * B)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hvb 2
  calc tiltWeight φ t 0 β₀ x * |c| * |Real.exp v - 1 - v|
      ≤ Real.exp (p * (‖β₀‖ * B)) * |c| * v ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hw (abs_nonneg _)) h1 (abs_nonneg _)
          (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hv2 (by positivity)

/-- **First order bound of the tilt** at one record: for `p ‖u‖ B ≤ 1`,
`|w_{β₀ + u}(x) c - w₀(x) c| ≤ exp(p ‖β₀‖ B) |c| (2 p ‖u‖ B)`. -/
theorem abs_tiltWeight_add_mul_sub_le' {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (β₀ u : Fin p → ℝ) (x : 𝒳) (c : ℝ) (hu : p * (‖u‖ * B) ≤ 1) :
    |tiltWeight φ t 0 (β₀ + u) x * c - tiltWeight φ t 0 β₀ x * c| ≤
      Real.exp (p * (‖β₀‖ * B)) * |c| * (2 * (p * (‖u‖ * B))) := by
  have hvb := abs_dotProduct_feature_le hB u x
  rw [tiltWeight_add]
  have he : tiltWeight φ t 0 β₀ x * Real.exp (u ⬝ᵥ (φ x - t)) * c - tiltWeight φ t 0 β₀ x * c =
      tiltWeight φ t 0 β₀ x * c * (Real.exp (u ⬝ᵥ (φ x - t)) - 1) := by ring
  rw [he, abs_mul, abs_mul, abs_of_pos (tiltWeight_pos _ _ _ _ _)]
  have h1 := Real.abs_exp_sub_one_le (hvb.trans hu)
  have hw := (tiltWeight_mem_Icc (hB x) (le_refl ‖β₀‖)).2
  calc tiltWeight φ t 0 β₀ x * |c| * |Real.exp (u ⬝ᵥ (φ x - t)) - 1|
      ≤ Real.exp (p * (‖β₀‖ * B)) * |c| * (2 * |u ⬝ᵥ (φ x - t)|) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hw (abs_nonneg _)) h1 (abs_nonneg _)
          (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **Second order expansion of a resample mean of the tilt.** -/
theorem abs_resampleMean_tiltWeight_expansion_le {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (β₀ u : Fin p → ℝ) {n : ℕ} (y : Fin n → 𝒳 × Bool × ℝ)
    (g : 𝒳 × Bool × ℝ → ℝ) (hu : p * (‖u‖ * B) ≤ 1) :
    |resampleMean (fun z => tiltWeight φ t 0 (β₀ + u) z.1 * g z) n y -
        resampleMean (fun z => tiltWeight φ t 0 β₀ z.1 * g z) n y -
        ∑ k, u k * resampleMean (fun z => tiltWeight φ t 0 β₀ z.1 * g z * (φ z.1 k - t k)) n y| ≤
      Real.exp (p * (‖β₀‖ * B)) * (p * (‖u‖ * B)) ^ 2 * resampleMean (fun z => |g z|) n y := by
  have e : resampleMean (fun z => tiltWeight φ t 0 (β₀ + u) z.1 * g z -
      tiltWeight φ t 0 β₀ z.1 * g z -
        ∑ k, u k * (tiltWeight φ t 0 β₀ z.1 * g z * (φ z.1 k - t k))) n y =
      resampleMean (fun z => tiltWeight φ t 0 (β₀ + u) z.1 * g z) n y -
        resampleMean (fun z => tiltWeight φ t 0 β₀ z.1 * g z) n y -
        ∑ k, u k * resampleMean (fun z => tiltWeight φ t 0 β₀ z.1 * g z * (φ z.1 k - t k)) n y := by
    simp only [resampleMean_sub, resampleMean_sum, resampleMean_const_mul]
  rw [← e, ← resampleMean_const_mul]
  refine abs_resampleMean_le y fun i => ?_
  have := abs_tiltWeight_add_mul_sub_le hB β₀ u (y i).1 (g (y i)) hu
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **First order bound of a resample mean of the tilt.** -/
theorem abs_resampleMean_tiltWeight_sub_le {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (β₀ u : Fin p → ℝ) {n : ℕ} (y : Fin n → 𝒳 × Bool × ℝ)
    (g : 𝒳 × Bool × ℝ → ℝ) (hu : p * (‖u‖ * B) ≤ 1) :
    |resampleMean (fun z => tiltWeight φ t 0 (β₀ + u) z.1 * g z) n y -
        resampleMean (fun z => tiltWeight φ t 0 β₀ z.1 * g z) n y| ≤
      Real.exp (p * (‖β₀‖ * B)) * (2 * (p * (‖u‖ * B))) * resampleMean (fun z => |g z|) n y := by
  rw [← resampleMean_sub, ← resampleMean_const_mul]
  refine abs_resampleMean_le y fun i => ?_
  have := abs_tiltWeight_add_mul_sub_le' hB β₀ u (y i).1 (g (y i)) hu
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **The resample first order condition**: at a sample that admits strictly positive
balancing weights, `n⁻¹ ∑ᵢ w_{β*}(xᵢ) Δⱼ(xᵢ) = 0`. -/
theorem resampleMean_tiltWeight_bootstrapTilt_eq_zero (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    {n : ℕ} {y : Fin n → 𝒳 × Bool × ℝ}
    (hfeas : ∃ q ∈ balancingSet (fun i : Fin n => φ (y i).1 - t), ∀ i, 0 < q i) (j : Fin p) :
    resampleMean (fun z => tiltWeight φ t 0 (bootstrapTilt φ t n y) z.1 * (φ z.1 j - t j)) n y =
      0 := by
  have hbal := congrFun (momentBalanced_dualMinimizer hfeas) j
  have : ∑ i, Real.exp (bootstrapTilt φ t n y ⬝ᵥ (φ (y i).1 - t)) * (φ (y i).1 j - t j) = 0 := by
    simpa [MomentBalanced, Finset.sum_apply, sub_zero, smul_eq_mul, bootstrapTilt] using hbal
  simp only [resampleMean, tiltWeight, zero_add, this, mul_zero]

/-- The sup norm is at most the sum of the absolute coordinates. -/
theorem norm_le_sum_abs (u : Fin p → ℝ) : ‖u‖ ≤ ∑ l, |u l| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun l _ => abs_nonneg _)).2 fun l => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun l => |u l|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ l)

/-- A coordinate of a matrix times a vector. -/
theorem abs_mulVec_apply_le (A : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ) (l : Fin p) :
    |(A *ᵥ v) l| ≤ ∑ j, |A l j| * |v j| := by
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  simp [abs_mul]

/-! ### Small and bounded terms of the resample -/

section Probability

variable [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

theorem ResampleTendstoZero.abs {X : (n : ℕ) → Ω → (Fin n → 𝒳 × Bool × ℝ) → ℝ}
    (h : ResampleTendstoZero P O X) : ResampleTendstoZero P O fun n ω y => |X n ω y| :=
  h.of_le (ResampleEventually.of_eventually (Eventually.of_forall fun _ _ _ => by
    rw [abs_abs]))

theorem ResampleBounded.abs {X : (n : ℕ) → Ω → (Fin n → 𝒳 × Bool × ℝ) → ℝ}
    (h : ResampleBounded P O X) : ResampleBounded P O fun n ω y => |X n ω y| :=
  h.of_le (ResampleEventually.of_eventually (Eventually.of_forall fun _ _ _ => by
    rw [abs_abs]))

/-- **Consistency of the bootstrap dual minimizer**: `‖β*(y) - β₀‖ → 0` in conditional
probability, in probability. -/
theorem resampleTendstoZero_norm_bootstrapTilt_sub [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) :
    ResampleTendstoZero P O fun n _ y =>
      ‖bootstrapTilt φ t n y - tiltMinimizer (P.map (O 0)) φ t‖ := fun ε hε =>
  (resampleEventually_bootstrapTilt hO hφ hB hδ hmargin hε).mono fun _ _ _ h => by
    rw [abs_norm]; exact h.2.2

/-- **The linear expansion of the bootstrap dual minimizer.** Under an i.i.d. sample, a
measurable feature with `‖φ(x) - t‖ ≤ B` and the margin condition, for `u = β*(y) - β₀` and
`s_y` the resample mean of `w₀ Δ`: `√n ‖u‖` is bounded and every coordinate of
`√n (u + M⁻¹ s_y)` is small, in conditional probability, in probability. -/
theorem bootstrapTilt_linear [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) :
    ResampleBounded P O (fun n _ y =>
      √(n : ℝ) * ‖bootstrapTilt φ t n y - tiltMinimizer (P.map (O 0)) φ t‖) ∧
    ∀ l, ResampleTendstoZero P O fun n _ y =>
      √(n : ℝ) * ((bootstrapTilt φ t n y - tiltMinimizer (P.map (O 0)) φ t) l +
        ((tiltedSecondMoment (P.map (O 0)) φ t (tiltMinimizer (P.map (O 0)) φ t))⁻¹ *ᵥ
          fun j => resampleMean (fun z => tiltWeight φ t 0 (tiltMinimizer (P.map (O 0)) φ t) z.1 *
            (φ z.1 j - t j)) n y) l) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set β₀ := tiltMinimizer ν φ t with hβ₀
  set M := tiltedSecondMoment ν φ t β₀ with hM
  set Mi := M⁻¹ with hMi
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 (det_tiltedSecondMoment_ne_zero hφ hB hδ
    hmargin β₀)
  set W := Real.exp (p * (‖β₀‖ * B)) with hW
  set w₀ : 𝒳 → ℝ := tiltWeight φ t 0 β₀ with hw₀
  set Lc := ∑ l, ∑ j, |Mi l j| + 1 with hLc
  have hLc0 : 0 < Lc := by positivity
  have hcol : ∀ j, ∑ l, |Mi l j| ≤ Lc := fun j => by
    have : ∑ l, |Mi l j| ≤ ∑ l, ∑ j, |Mi l j| := Finset.sum_le_sum fun l _ =>
      Finset.single_le_sum (f := fun j => |Mi l j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  have hrow : ∀ l, ∑ j, |Mi l j| ≤ Lc := fun l => by
    have : ∑ j, |Mi l j| ≤ ∑ l, ∑ j, |Mi l j| :=
      Finset.single_le_sum (f := fun l => ∑ j, |Mi l j|) (fun _ _ => by positivity)
        (Finset.mem_univ l)
    linarith
  set B' := |B| with hB'
  have hBB' : ∀ x, ‖φ x - t‖ ≤ B' := fun x => (hB x).trans (le_abs_self B)
  set C := Real.exp (p * (‖β₀‖ * B')) * (p * B') ^ 2 * B' with hC
  set r₀ := 1 / (p * B' + 1) with hr₀
  have hr₀0 : 0 < r₀ := by positivity
  -- the record functions and their limits
  have hΔ : ∀ x j, |φ x j - t j| ≤ B' := fun x j => abs_apply_le_of_norm_le (hBB' x) j
  have hwb : ∀ x, |w₀ x| ≤ W := fun x => by
    rw [abs_of_pos (tiltWeight_pos _ _ _ _ _)]
    exact (tiltWeight_mem_Icc (hB x) le_rfl).2
  have hSm : ∀ j, Measurable fun z : 𝒳 × Bool × ℝ => w₀ z.1 * (φ z.1 j - t j) := fun j =>
    (measurable_tiltWeight_fst hφ t β₀).mul ((measurable_feature_fst hφ j).sub_const _)
  have hMm : ∀ j k, Measurable fun z : 𝒳 × Bool × ℝ =>
      w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k) := fun j k =>
    (hSm j).mul ((measurable_feature_fst hφ k).sub_const _)
  have hS2 : ∀ j, MemLp (fun z : 𝒳 × Bool × ℝ => w₀ z.1 * (φ z.1 j - t j)) 2 ν := fun j =>
    memLp_two_of_abs_le (hSm j) (C := W * B') fun z => by
      rw [abs_mul]
      exact mul_le_mul (hwb _) (hΔ _ j) (abs_nonneg _) ((abs_nonneg _).trans (hwb z.1))
  have hM2 : ∀ j k, MemLp (fun z : 𝒳 × Bool × ℝ =>
      w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) 2 ν := fun j k =>
    memLp_two_of_abs_le (hMm j k) (C := W * B' * B') fun z => by
      rw [abs_mul, abs_mul]
      have h1 := (abs_nonneg _).trans (hwb z.1)
      have h2 := (abs_nonneg _).trans (hΔ z.1 j)
      exact mul_le_mul (mul_le_mul (hwb _) (hΔ _ j) (abs_nonneg _) h1) (hΔ _ k) (abs_nonneg _)
        (by positivity)
  have hS0 : ∀ j, ∫ z, w₀ z.1 * (φ z.1 j - t j) ∂(P.map (O 0)) = 0 := fun j =>
    integral_tiltWeight_tiltMinimizer_mul_sub hφ hB hδ hmargin j
  have hMint : ∀ j k, ∫ z, w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k) ∂(P.map (O 0)) =
      M j k := fun j k => by rw [hM, hν]; simp [tiltedSecondMoment, w₀]
  set s : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → Fin p → ℝ :=
    fun n y j => resampleMean (fun z => w₀ z.1 * (φ z.1 j - t j)) n y with hs
  set My : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → Fin p → Fin p → ℝ :=
    fun n y j k => resampleMean (fun z => w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) n y
    with hMy
  set u : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → Fin p → ℝ :=
    fun n y => bootstrapTilt φ t n y - β₀ with hu
  have hsB : ∀ j, ResampleBounded P O fun n _ y => √(n : ℝ) * s n y j := fun j => by
    have := resampleBounded_sqrt_mul_resampleMean_sub_integral hO (hSm j) (hS2 j)
    simpa only [hS0, sub_zero] using this
  have hMT : ∀ j k, ResampleTendstoZero P O fun n _ y => My n y j k - M j k := fun j k => by
    have := resampleTendstoZero_resampleMean_sub_integral hO (hMm j k) (hM2 j k)
    simpa only [hMint] using this
  have huT : ResampleTendstoZero P O fun n _ y => ‖u n y‖ :=
    resampleTendstoZero_norm_bootstrapTilt_sub hO hφ hB hδ hmargin
  -- the small factor
  set Z : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → ℝ :=
    fun n y => p * C * ‖u n y‖ + ∑ j, ∑ k, |My n y j k - M j k| with hZ
  have hZT : ResampleTendstoZero P O fun n _ y => Z n y :=
    (huT.const_mul _).add (ResampleTendstoZero.sum _ fun j _ =>
      ResampleTendstoZero.sum _ fun k _ => (hMT j k).abs)
  -- the deterministic step on the good event
  have hgood := (resampleEventually_bootstrapTilt hO hφ hB hδ hmargin hr₀0).and
    (hZT (1 / (2 * (p * Lc + 1))) (by positivity))
  have hdet : ∀ n (y : Fin n → 𝒳 × Bool × ℝ), 0 < n →
      (∃ q ∈ balancingSet (fun i : Fin n => φ (y i).1 - t), ∀ i, 0 < q i) →
      ‖u n y‖ < r₀ → (∀ l, |u n y l + (Mi *ᵥ s n y) l| ≤ Lc * (Z n y * ‖u n y‖)) := by
    intro n y hn hfeas hur l
    have hpu : p * (‖u n y‖ * B') ≤ 1 := by
      have : p * (‖u n y‖ * B') ≤ p * (r₀ * B') := by gcongr
      refine this.trans ?_
      have h2 : p * (r₀ * B') = r₀ * (p * B') := by ring
      rw [h2, hr₀, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    -- the first order condition and the expansion, coordinate by coordinate
    have he : ∀ j, |s n y j + (M *ᵥ u n y) j| ≤ Z n y * ‖u n y‖ := fun j => by
      have hfoc := resampleMean_tiltWeight_bootstrapTilt_eq_zero φ t hfeas j
      have hexp := abs_resampleMean_tiltWeight_expansion_le hBB' β₀ (u n y) y
        (fun z => φ z.1 j - t j) hpu
      have hb : bootstrapTilt φ t n y = β₀ + u n y := by simp [hu]
      rw [← hb, hfoc] at hexp
      have hbar : resampleMean (fun z => |φ z.1 j - t j|) n y ≤ B' := by
        calc _ ≤ resampleMean (fun _ => B') n y := resampleMean_mono y fun i => hΔ _ j
          _ = B' := resampleMean_const y hn B'
      have hexp' : |s n y j + ∑ k, u n y k * My n y j k| ≤ C * ‖u n y‖ ^ 2 := by
        have h0 : s n y j + ∑ k, u n y k * My n y j k = -(0 - s n y j -
            ∑ k, u n y k * My n y j k) := by ring
        rw [h0, abs_neg]
        refine hexp.trans ?_
        calc _ ≤ Real.exp (p * (‖β₀‖ * B')) * (p * (‖u n y‖ * B')) ^ 2 * B' :=
              mul_le_mul_of_nonneg_left hbar (by positivity)
          _ = C * ‖u n y‖ ^ 2 := by rw [hC]; ring
      have hsplit : s n y j + (M *ᵥ u n y) j = (s n y j + ∑ k, u n y k * My n y j k) -
          ∑ k, u n y k * (My n y j k - M j k) := by
        simp only [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
        have : ∑ k, M j k * u n y k = ∑ k, u n y k * M j k :=
          Finset.sum_congr rfl fun k _ => mul_comm _ _
        rw [this]; ring
      have hrest : |∑ k, u n y k * (My n y j k - M j k)| ≤
          ‖u n y‖ * ∑ j, ∑ k, |My n y j k - M j k| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ k, |u n y k * (My n y j k - M j k)| ≤ ∑ k, ‖u n y‖ * |My n y j k - M j k| :=
              Finset.sum_le_sum fun k _ => by
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_right (abs_apply_le_of_norm_le le_rfl k)
                  (abs_nonneg _)
          _ = ‖u n y‖ * ∑ k, |My n y j k - M j k| := by rw [Finset.mul_sum]
          _ ≤ ‖u n y‖ * ∑ j, ∑ k, |My n y j k - M j k| :=
              mul_le_mul_of_nonneg_left (Finset.single_le_sum
                (f := fun j => ∑ k, |My n y j k - M j k|)
                (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j))
                (norm_nonneg _)
      rw [hsplit]
      refine (abs_sub _ _).trans ?_
      have hpC : C * ‖u n y‖ ^ 2 ≤ p * C * ‖u n y‖ * ‖u n y‖ := by
        have hC0 : 0 ≤ C := by rw [hC]; positivity
        have hp1 : (1 : ℝ) ≤ p ∨ p = 0 := by
          rcases Nat.eq_zero_or_pos p with h | h
          · right; simp [h]
          · left; exact_mod_cast h
        rcases hp1 with h | h
        · nlinarith [norm_nonneg (u n y), mul_nonneg hC0 (sq_nonneg ‖u n y‖)]
        · have : C = 0 := by simp [hC, h]
          rw [this]; simp
      calc |s n y j + ∑ k, u n y k * My n y j k| + |∑ k, u n y k * (My n y j k - M j k)|
          ≤ p * C * ‖u n y‖ * ‖u n y‖ + ‖u n y‖ * ∑ j, ∑ k, |My n y j k - M j k| := by
            linarith
        _ = Z n y * ‖u n y‖ := by rw [hZ]; ring
    -- solve with the inverse
    have hsol : u n y + Mi *ᵥ s n y = Mi *ᵥ (s n y + M *ᵥ u n y) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hMi, Matrix.nonsing_inv_mul M hMu,
        Matrix.one_mulVec, add_comm]
    have := congrFun hsol l
    simp only [Pi.add_apply] at this
    rw [this]
    refine (abs_mulVec_apply_le _ _ l).trans ?_
    calc ∑ j, |Mi l j| * |(s n y + M *ᵥ u n y) j| ≤ ∑ j, |Mi l j| * (Z n y * ‖u n y‖) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
      _ = (∑ j, |Mi l j|) * (Z n y * ‖u n y‖) := by rw [Finset.sum_mul]
      _ ≤ Lc * (Z n y * ‖u n y‖) := mul_le_mul_of_nonneg_right (hrow l)
          (mul_nonneg (by rw [hZ]; positivity) (norm_nonneg _))
  -- the bound on `‖u‖`
  have hubound : ResampleEventually P O fun n _ y =>
      |√(n : ℝ) * ‖u n y‖| ≤ abs (2 * Lc * ∑ j, |√(n : ℝ) * s n y j|) := by
    refine hgood.mono fun n ω y ⟨⟨hn, hfeas, hur⟩, hZs⟩ => ?_
    have hl := hdet n y hn hfeas hur
    have hZ0 : 0 ≤ Z n y := by rw [hZ]; positivity
    rw [abs_of_nonneg hZ0] at hZs
    have hsq := Real.sqrt_nonneg (n : ℝ)
    have hnorm : ‖u n y‖ ≤ p * (Lc * (Z n y * ‖u n y‖)) + Lc * ∑ j, |s n y j| := by
      refine (norm_le_sum_abs _).trans ?_
      calc ∑ l, |u n y l| ≤ ∑ l, (Lc * (Z n y * ‖u n y‖) + ∑ j, |Mi l j| * |s n y j|) :=
            Finset.sum_le_sum fun l _ => by
              have h1 : |u n y l| ≤ |u n y l + (Mi *ᵥ s n y) l| + |(Mi *ᵥ s n y) l| := by
                have := abs_sub (u n y l + (Mi *ᵥ s n y) l) ((Mi *ᵥ s n y) l)
                simpa using this
              linarith [hl l, abs_mulVec_apply_le Mi (s n y) l]
        _ = p * (Lc * (Z n y * ‖u n y‖)) + ∑ j, (∑ l, |Mi l j|) * |s n y j| := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, Finset.sum_comm]
            simp only [Finset.sum_mul]
        _ ≤ p * (Lc * (Z n y * ‖u n y‖)) + Lc * ∑ j, |s n y j| := by
            rw [Finset.mul_sum]
            gcongr with j
            exact hcol j
    have hsmall : p * (Lc * Z n y) ≤ 1 / 2 := by
      have h1 : p * Lc * Z n y ≤ (p * Lc + 1) * Z n y :=
        mul_le_mul_of_nonneg_right (by linarith) hZ0
      have h2 : (p * Lc + 1) * Z n y < 1 / 2 := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (p * Lc + 1))] at hZs
        nlinarith
      nlinarith
    have hu2 : ‖u n y‖ ≤ 2 * Lc * ∑ j, |s n y j| := by
      have : p * (Lc * (Z n y * ‖u n y‖)) ≤ 1 / 2 * ‖u n y‖ := by
        have := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (u n y))
        nlinarith
      nlinarith
    rw [abs_of_nonneg (mul_nonneg hsq (norm_nonneg _)), abs_of_nonneg (by positivity)]
    calc √(n : ℝ) * ‖u n y‖ ≤ √(n : ℝ) * (2 * Lc * ∑ j, |s n y j|) :=
          mul_le_mul_of_nonneg_left hu2 hsq
      _ = 2 * Lc * ∑ j, |√(n : ℝ) * s n y j| := by
          simp only [abs_mul, abs_of_nonneg hsq, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hBdd : ResampleBounded P O fun n _ y => √(n : ℝ) * ‖u n y‖ :=
    ((ResampleBounded.sum _ fun j _ => (hsB j).abs).const_mul (2 * Lc)).of_le hubound
  refine ⟨hBdd, fun l => ?_⟩
  have hT := (hZT.mul_bounded hBdd).const_mul Lc
  refine hT.of_le (hgood.mono fun n ω y ⟨⟨hn, hfeas, hur⟩, _⟩ => ?_)
  have hl := hdet n y hn hfeas hur l
  have hsq := Real.sqrt_nonneg (n : ℝ)
  have hZ0 : 0 ≤ Z n y := by rw [hZ]; positivity
  have hR : 0 ≤ Lc * (Z n y * (√(n : ℝ) * ‖u n y‖)) := by positivity
  change |√(n : ℝ) * (u n y l + (Mi *ᵥ s n y) l)| ≤ |Lc * (Z n y * (√(n : ℝ) * ‖u n y‖))|
  rw [abs_mul, abs_of_nonneg hsq, abs_of_nonneg hR]
  calc √(n : ℝ) * |u n y l + (Mi *ᵥ s n y) l| ≤ √(n : ℝ) * (Lc * (Z n y * ‖u n y‖)) :=
        mul_le_mul_of_nonneg_left hl hsq
    _ = Lc * (Z n y * (√(n : ℝ) * ‖u n y‖)) := by ring

end Probability

end PopulationAdjustment

end CausalInference
