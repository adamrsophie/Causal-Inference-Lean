/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapChebyshev
public import Mathlib.Analysis.Convex.Extrema

/-!
# Consistency of the bootstrap dual minimizer

The entropy balancing weights of a resample `y` are the weights of the minimizer `β*(y)` of the
convex dual objective `β ↦ log ∑ᵢ exp(βᵀ(φ(xᵢ) - t))`, which is `log n` plus the logarithm of the
resample mean `L_y(β)` of the tilt `w_β(x) = exp(βᵀ(φ(x) - t))`. A minimizer exists exactly when
the resample admits strictly positive balancing weights (`exists_isMinOn_logPartition_iff`).

The argument is deterministic at each resample. If `L_y(β₀) < L_y(b)` on the sphere
`‖b - β₀‖ = r`, the minimum of the objective over the closed ball is interior, hence a global
minimum by convexity, and every global minimum `β` satisfies `‖β - β₀‖ < r`
(`exists_isMinOn_of_lt_sphere`). Around the population tilt `β₀`, with `u = b - β₀`,
`|uᵀ(φ(x) - t)| ≤ 1` and `exp v - 1 ≥ v + v²/4` for `|v| ≤ 1`,
`L_y(β₀ + u) - L_y(β₀) ≥ uᵀ s_y + uᵀ M_y u / 4`, where `s_y` and `M_y` are the resample means of
`w₀ (φ - t)` and `w₀ (φ - t)(φ - t)ᵀ`. By the bootstrap law of large numbers `s_y → 0` (the
population balance equations) and `M_y → M = tiltedSecondMoment` in conditional probability, in
probability, and `uᵀ M u ≥ exp(-p ‖β₀‖ B) δ³ ‖u‖²` by the margin condition. This gives the
separation, hence feasibility and `‖β*(y) - β₀‖ < r`, with conditional probability tending to
one, in probability.

Only the resample means at the single point `β₀` enter; no uniform law over a parameter set is
used.

## Main results

* `quarter_sq_le_exp_sub_one_sub`: `x²/4 ≤ exp x - 1 - x` for `|x| ≤ 1`.
* `exists_isMinOn_of_lt_sphere`: the deterministic convexity argument.
* `bootstrapTilt_feasible_and_norm_sub_lt`: feasibility and localization of the bootstrap dual
  minimizer from the separation on a sphere.
* `quadratic_le_tiltedSecondMoment`: the quadratic lower bound of the population second moment.
* `resampleEventually_bootstrapTilt`: with conditional probability tending to one, in
  probability, the resample admits strictly positive balancing weights and
  `‖β*(y) - β₀‖ < ε`.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap

/-! ### Deterministic facts -/

/-- **A quadratic lower bound for the exponential**: `x²/4 ≤ exp x - 1 - x` for `|x| ≤ 1`. -/
theorem quarter_sq_le_exp_sub_one_sub {x : ℝ} (hx : |x| ≤ 1) :
    x ^ 2 / 4 ≤ Real.exp x - 1 - x := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.succ_eq_add_one]
    at h
  norm_num at h
  have h3 : |x| ^ 3 ≤ x ^ 2 := by
    rw [pow_succ, ← sq_abs x]
    exact mul_le_of_le_one_right (by positivity) hx
  have := (abs_le.1 h).1
  nlinarith

theorem resampleMean_mono {𝒪 : Type*} {n : ℕ} (y : Fin n → 𝒪) {f g : 𝒪 → ℝ}
    (h : ∀ i, f (y i) ≤ g (y i)) : resampleMean f n y ≤ resampleMean g n y := by
  simp only [resampleMean]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)

variable {p : ℕ}

/-- **The convexity argument.** Let `f` be convex and continuous on `ℝ^p` with `f(β₀) < f(b)` on
the sphere `‖b - β₀‖ = r`, `r > 0`. Then `f` has a global minimizer and every global minimizer
satisfies `‖β - β₀‖ < r`. -/
theorem exists_isMinOn_of_lt_sphere {f : (Fin p → ℝ) → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hc : Continuous f) {β₀ : Fin p → ℝ} {r : ℝ} (hr : 0 < r)
    (hsep : ∀ b, ‖b - β₀‖ = r → f β₀ < f b) :
    (∃ β, IsMinOn f Set.univ β) ∧ ∀ β, IsMinOn f Set.univ β → ‖β - β₀‖ < r := by
  refine ⟨?_, fun β hβ => ?_⟩
  · obtain ⟨x, hxK, hx⟩ := (isCompact_closedBall β₀ r).exists_isMinOn
      ⟨β₀, Metric.mem_closedBall_self hr.le⟩ hc.continuousOn
    have hlt : dist x β₀ < r := by
      rcases (Metric.mem_closedBall.1 hxK).lt_or_eq with h | h
      · exact h
      · have h1 := hsep x (by rw [← dist_eq_norm]; exact h)
        have h2 : f x ≤ f β₀ := hx (Metric.mem_closedBall_self hr.le)
        linarith
    have hloc : IsLocalMin f x := hx.isLocalMin (Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball.2 hlt)) Metric.ball_subset_closedBall)
    exact ⟨x, fun y _ => IsMinOn.of_isLocalMin_of_convex_univ hloc hf y⟩
  · by_contra hfar
    push Not at hfar
    set d := ‖β - β₀‖ with hd
    have hd0 : 0 < d := hr.trans_le hfar
    set s := r / d with hs
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := (div_le_one hd0).2 hfar
    set b := (1 - s) • β₀ + s • β with hb
    have hbsub : b - β₀ = s • (β - β₀) := by rw [hb, sub_smul, one_smul, smul_sub]; abel
    have hbn : ‖b - β₀‖ = r := by
      rw [hbsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hs, div_mul_cancel₀ _ hd0.ne']
    have h1 := hsep b hbn
    have h2 := hf.2 (Set.mem_univ β₀) (Set.mem_univ β) (sub_nonneg.2 hs1) hs0 (by ring)
    have h3 : f β ≤ f β₀ := hβ (Set.mem_univ β₀)
    simp only [smul_eq_mul] at h2
    rw [← hb] at h2
    nlinarith

variable {𝒳 : Type*}

/-- The partition function of a sample is `n` times the resample mean of the tilt. -/
theorem partitionFunction_eq_resampleMean (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) {n : ℕ}
    (y : Fin n → 𝒳 × Bool × ℝ) (b : Fin p → ℝ) :
    partitionFunction (fun i : Fin n => φ (y i).1 - t) b =
      n * resampleMean (fun z => tiltWeight φ t 0 b z.1) n y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [partitionFunction]
  rw [resampleMean, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul,
    partitionFunction]
  simp [tiltWeight]

theorem continuous_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (Δ : ι → Fin p → ℝ) :
    Continuous (logPartition Δ) :=
  (continuous_finsetSum _ fun _ _ => (continuous_id.dotProduct continuous_const).rexp).log
    fun β => (partitionFunction_pos (Δ := Δ) β).ne'

/-- **Feasibility and localization of the bootstrap dual minimizer.** For a sample `y` of size
`n > 0`, if the resample mean of the tilt at `β₀` is below its values on the sphere
`‖b - β₀‖ = r`, then the sample admits strictly positive balancing weights and
`‖β*(y) - β₀‖ < r`. -/
theorem bootstrapTilt_feasible_and_norm_sub_lt (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) {n : ℕ}
    (hn : 0 < n) (y : Fin n → 𝒳 × Bool × ℝ) {β₀ : Fin p → ℝ} {r : ℝ} (hr : 0 < r)
    (hsep : ∀ b, ‖b - β₀‖ = r → resampleMean (fun z => tiltWeight φ t 0 β₀ z.1) n y <
      resampleMean (fun z => tiltWeight φ t 0 b z.1) n y) :
    (∃ q ∈ balancingSet (fun i : Fin n => φ (y i).1 - t), ∀ i, 0 < q i) ∧
      ‖bootstrapTilt φ t n y - β₀‖ < r := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Δ := fun i : Fin n => φ (y i).1 - t with hΔ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsep' : ∀ b, ‖b - β₀‖ = r → logPartition Δ β₀ < logPartition Δ b := fun b hb => by
    refine Real.log_lt_log (partitionFunction_pos (Δ := Δ) β₀) ?_
    rw [partitionFunction_eq_resampleMean, partitionFunction_eq_resampleMean]
    exact mul_lt_mul_of_pos_left (hsep b hb) hnR
  obtain ⟨hex, hloc⟩ := exists_isMinOn_of_lt_sphere convexOn_logPartition
    (continuous_logPartition Δ) hr hsep'
  have hpos := (exists_isMinOn_logPartition_iff (Δ := Δ)).1 hex
  exact ⟨hpos, hloc _ (isMinOn_dualMinimizer hpos)⟩

/-! ### The quadratic lower bound of the population second moment -/

variable [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)}

/-- **The quadratic lower bound.** Under bounded features and the margin condition, for every
`β` and every direction `u`,
`exp(-p ‖β‖ B) (‖u‖ δ)² δ ≤ ∑ⱼ ∑ₖ uⱼ uₖ M(β)ⱼₖ = E[w_β (uᵀ(φ(X) - t))²]`. -/
theorem quadratic_le_tiltedSecondMoment [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (β u : Fin p → ℝ) :
    Real.exp (-(p * (‖β‖ * B))) * (‖u‖ * δ) ^ 2 * δ ≤
      ∑ j, ∑ k, u j * u k * tiltedSecondMoment ν φ t β j k := by
  have hint : ∀ j k, Integrable (fun z : 𝒳 × Bool × ℝ =>
      tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) ν := fun j k => by
    have := integrable_tiltWeight_mul_of_abs_le (ν := ν) hφ hB β
      (((measurable_feature_fst hφ j).sub_const (t j)).mul
        ((measurable_feature_fst hφ k).sub_const (t k)))
      (C := B * B) fun z => by
        simp only [Pi.mul_apply]
        rw [abs_mul]
        exact mul_le_mul (abs_apply_le_of_norm_le (hB z.1) j)
          (abs_apply_le_of_norm_le (hB z.1) k) (abs_nonneg _)
          ((abs_nonneg _).trans (abs_apply_le_of_norm_le (hB z.1) j))
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [Pi.mul_apply, mul_assoc]
  have hsum : ∑ j, ∑ k, u j * u k * tiltedSecondMoment ν φ t β j k =
      ∫ z, tiltWeight φ t 0 β z.1 * (u ⬝ᵥ (φ z.1 - t)) ^ 2 ∂ν := by
    have hpt : ∀ z : 𝒳 × Bool × ℝ, tiltWeight φ t 0 β z.1 * (u ⬝ᵥ (φ z.1 - t)) ^ 2 =
        ∑ j, ∑ k, u j * u k *
          (tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) := fun z => by
      simp only [dotProduct, Pi.sub_apply]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hint j k).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => (hint j k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    simp [tiltedSecondMoment]
  rw [hsum]
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  obtain ⟨hS, hSδ⟩ := margin_set_of_ne_zero hφ hmargin hu
  have hnorm : 0 ≤ ‖u‖ * δ := mul_nonneg (norm_nonneg _) hδ.le
  have hi : Integrable (fun z : 𝒳 × Bool × ℝ => tiltWeight φ t 0 β z.1 * (u ⬝ᵥ (φ z.1 - t)) ^ 2)
      ν := by
    have : (fun z : 𝒳 × Bool × ℝ => tiltWeight φ t 0 β z.1 * (u ⬝ᵥ (φ z.1 - t)) ^ 2) =
        fun z => ∑ j, ∑ k, u j * u k *
          (tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) := by
      funext z
      simp only [dotProduct, Pi.sub_apply]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hint j k).const_mul _
  have h := le_integral_of_le_on hi (fun z => mul_nonneg (tiltWeight_pos _ _ _ _ _).le
    (sq_nonneg _)) hS (c := Real.exp (-(p * (‖β‖ * B))) * (‖u‖ * δ) ^ 2) fun z hz => by
      simp only [Set.mem_ofPred_eq] at hz
      exact mul_le_mul (tiltWeight_mem_Icc (hB z.1) le_rfl).1 (pow_le_pow_left₀ hnorm hz 2)
        (by positivity) (tiltWeight_pos _ _ _ _ _).le
  calc Real.exp (-(p * (‖β‖ * B))) * (‖u‖ * δ) ^ 2 * δ
      ≤ Real.exp (-(p * (‖β‖ * B))) * (‖u‖ * δ) ^ 2 * ν.real _ :=
        mul_le_mul_of_nonneg_left hSδ (by positivity)
    _ ≤ _ := h

/-! ### Consistency in conditional probability -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Bounded record functions are square integrable.** -/
theorem memLp_two_of_abs_le [IsFiniteMeasure ν] {f : 𝒳 × Bool × ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ z, |f z| ≤ C) : MemLp f 2 ν :=
  MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs]; exact hC z)

/-- **Consistency of the bootstrap dual minimizer.** For an i.i.d. sample of records under a
probability measure, a measurable feature with `‖φ(x) - t‖ ≤ B` and the margin condition, and
every `ε > 0`: with conditional probability tending to one, in probability, the resample `y` of
size `n` has `n > 0`, admits strictly positive balancing weights, and its dual minimizer
satisfies `‖β*(y) - β₀‖ < ε`, `β₀ = tiltMinimizer`. -/
theorem resampleEventually_bootstrapTilt [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {ε : ℝ} (hε : 0 < ε) :
    ResampleEventually P O fun n _ y => 0 < n ∧
      (∃ q ∈ balancingSet (fun i : Fin n => φ (y i).1 - t), ∀ i, 0 < q i) ∧
        ‖bootstrapTilt φ t n y - tiltMinimizer (P.map (O 0)) φ t‖ < ε := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set β₀ := tiltMinimizer ν φ t with hβ₀
  set W := Real.exp (p * (‖β₀‖ * B)) with hW
  set w₀ : 𝒳 → ℝ := tiltWeight φ t 0 β₀ with hw₀
  set B' := |B| with hB'
  have hBB' : ∀ x, ‖φ x - t‖ ≤ B' := fun x => (hB x).trans (le_abs_self B)
  set lam := Real.exp (-(p * (‖β₀‖ * B))) * δ ^ 2 * δ with hlam
  have hlam0 : 0 < lam := by positivity
  set r := min ε (1 / (p * B' + 1)) with hr
  have hr0 : 0 < r := lt_min hε (by positivity)
  have hrB : p * (r * B') ≤ 1 := by
    have h1 : r ≤ 1 / (p * B' + 1) := min_le_right _ _
    have h2 : p * (r * B') = r * (p * B') := by ring
    rw [h2]
    calc r * (p * B') ≤ 1 / (p * B' + 1) * (p * B') :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  set ηM := lam / (2 * ((p : ℝ) ^ 2 + 1)) with hηM
  set ηs := lam * r / (16 * ((p : ℝ) + 1)) with hηs
  have hηM0 : 0 < ηM := by positivity
  have hηs0 : 0 < ηs := by positivity
  -- the record functions
  have hwb : ∀ x, |w₀ x| ≤ W := fun x => by
    rw [abs_of_pos (tiltWeight_pos _ _ _ _ _)]
    exact (tiltWeight_mem_Icc (hB x) le_rfl).2
  have hΔ : ∀ x j, |φ x j - t j| ≤ B := fun x j => abs_apply_le_of_norm_le (hB x) j
  have hSm : ∀ j, Measurable fun z : 𝒳 × Bool × ℝ => w₀ z.1 * (φ z.1 j - t j) := fun j =>
    (measurable_tiltWeight_fst hφ t β₀).mul ((measurable_feature_fst hφ j).sub_const _)
  have hMm : ∀ j k, Measurable fun z : 𝒳 × Bool × ℝ =>
      w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k) := fun j k =>
    (hSm j).mul ((measurable_feature_fst hφ k).sub_const _)
  have hS2 : ∀ j, MemLp (fun z : 𝒳 × Bool × ℝ => w₀ z.1 * (φ z.1 j - t j)) 2 ν := fun j =>
    memLp_two_of_abs_le (hSm j) (C := W * B) fun z => by
      rw [abs_mul]
      exact mul_le_mul (hwb _) (hΔ _ j) (abs_nonneg _) ((abs_nonneg _).trans (hwb z.1))
  have hM2 : ∀ j k, MemLp (fun z : 𝒳 × Bool × ℝ =>
      w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) 2 ν := fun j k =>
    memLp_two_of_abs_le (hMm j k) (C := W * B * B) fun z => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hwb _) (hΔ _ j) (abs_nonneg _) ((abs_nonneg _).trans
        (hwb z.1))) (hΔ _ k) (abs_nonneg _) (by
          have := (abs_nonneg _).trans (hwb z.1); have := (abs_nonneg _).trans (hΔ z.1 j)
          positivity)
  have hS0 : ∀ j, ∫ z, w₀ z.1 * (φ z.1 j - t j) ∂ν = 0 := fun j =>
    integral_tiltWeight_tiltMinimizer_mul_sub hφ hB hδ hmargin j
  have hMint : ∀ j k, ∫ z, w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k) ∂ν =
      tiltedSecondMoment ν φ t β₀ j k := fun j k => by simp [tiltedSecondMoment, w₀]
  have hEs : ResampleEventually P O fun n _ y => ∀ j,
      |resampleMean (fun z => w₀ z.1 * (φ z.1 j - t j)) n y| < ηs :=
    ResampleEventually.forall_finite fun j => by
      have := resampleTendstoZero_resampleMean_sub_integral hO (hSm j) (hS2 j) ηs hηs0
      have h0 := hS0 j
      rw [hν] at h0
      simpa only [h0, sub_zero] using this
  have hEM : ResampleEventually P O fun n _ y => ∀ j k,
      |resampleMean (fun z => w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) n y -
        tiltedSecondMoment ν φ t β₀ j k| < ηM :=
    ResampleEventually.forall_finite fun j => ResampleEventually.forall_finite fun k => by
      have := resampleTendstoZero_resampleMean_sub_integral hO (hMm j k) (hM2 j k) ηM hηM0
      have h0 := hMint j k
      rw [hν] at h0
      simpa only [h0] using this
  have hEn : ResampleEventually P O fun n (_ : Ω) (_ : Fin n → 𝒳 × Bool × ℝ) => 0 < n :=
    ResampleEventually.of_eventually ((eventually_ge_atTop 1).mono fun n hn _ _ => hn)
  refine ((hEn.and hEs).and hEM).mono fun n ω y ⟨⟨hn, hs⟩, hM⟩ => ?_
  have hsep : ∀ b, ‖b - β₀‖ = r → resampleMean (fun z => tiltWeight φ t 0 β₀ z.1) n y <
      resampleMean (fun z => tiltWeight φ t 0 b z.1) n y := by
    intro b hb
    set u := b - β₀ with hu
    have hbu : b = β₀ + u := by rw [hu]; abel
    -- the pointwise Taylor bound
    have hpt : ∀ i, w₀ (y i).1 + (∑ j, u j * (w₀ (y i).1 * (φ (y i).1 j - t j)) +
        1 / 4 * ∑ j, ∑ k, u j * u k *
          (w₀ (y i).1 * (φ (y i).1 j - t j) * (φ (y i).1 k - t k))) ≤
        tiltWeight φ t 0 b (y i).1 := fun i => by
      set v := u ⬝ᵥ (φ (y i).1 - t) with hv
      have hv1 : |v| ≤ 1 := (abs_dotProduct_feature_le hBB' u (y i).1).trans
        (by rw [hb]; exact hrB)
      have hq := quarter_sq_le_exp_sub_one_sub hv1
      have hlin : ∑ j, u j * (w₀ (y i).1 * (φ (y i).1 j - t j)) = w₀ (y i).1 * v := by
        simp only [hv, dotProduct, Pi.sub_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hquad : ∑ j, ∑ k, u j * u k *
          (w₀ (y i).1 * (φ (y i).1 j - t j) * (φ (y i).1 k - t k)) = w₀ (y i).1 * v ^ 2 := by
        simp only [hv, dotProduct, Pi.sub_apply]
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hlin, hquad, hbu, tiltWeight_add, ← hv]
      have hw0 : 0 < w₀ (y i).1 := tiltWeight_pos _ _ _ _ _
      nlinarith [mul_le_mul_of_nonneg_left hq hw0.le]
    have hmono := resampleMean_mono y (f := fun z => w₀ z.1 + (∑ j, u j * (w₀ z.1 *
      (φ z.1 j - t j)) + 1 / 4 * ∑ j, ∑ k, u j * u k *
        (w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)))) (g := fun z => tiltWeight φ t 0 b z.1) hpt
    simp only [resampleMean_add, resampleMean_sum, resampleMean_const_mul] at hmono
    set s : Fin p → ℝ := fun j => resampleMean (fun z => w₀ z.1 * (φ z.1 j - t j)) n y
    set My : Fin p → Fin p → ℝ := fun j k =>
      resampleMean (fun z => w₀ z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) n y
    set M := tiltedSecondMoment ν φ t β₀
    have hquadM := quadratic_le_tiltedSecondMoment (ν := ν) hφ hB hδ hmargin β₀ u
    rw [hb] at hquadM
    have hu_j : ∀ j, |u j| ≤ r := fun j => by
      rw [← hb]; exact abs_apply_le_of_norm_le le_rfl j
    have hlinb : |∑ j, u j * s j| ≤ p * r * ηs := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |u j * s j| ≤ ∑ _j : Fin p, r * ηs := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]; exact mul_le_mul (hu_j j) (hs j).le (abs_nonneg _) hr0.le
        _ = p * r * ηs := by simp [Finset.card_univ]; ring
    have hquadb : |∑ j, ∑ k, u j * u k * My j k - ∑ j, ∑ k, u j * u k * M j k| ≤
        p ^ 2 * r ^ 2 * ηM := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |∑ k, u j * u k * My j k - ∑ k, u j * u k * M j k|
          ≤ ∑ _j : Fin p, ∑ _k : Fin p, r * r * ηM := Finset.sum_le_sum fun j _ => by
            rw [← Finset.sum_sub_distrib]
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
            rw [← mul_sub, abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul (hu_j j) (hu_j k) (abs_nonneg _) hr0.le)
              (hM j k).le (abs_nonneg _) (by positivity)
        _ = p ^ 2 * r ^ 2 * ηM := by simp [Finset.card_univ]; ring
    have key1 : p * r * ηs = lam * r ^ 2 * p / (16 * ((p : ℝ) + 1)) := by rw [hηs]; ring
    have key2 : p ^ 2 * r ^ 2 * ηM = lam * r ^ 2 * (p ^ 2 / (2 * ((p : ℝ) ^ 2 + 1))) := by
      rw [hηM]; ring
    have hp1 : (p : ℝ) / (16 * ((p : ℝ) + 1)) ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hp2 : (p : ℝ) ^ 2 / (2 * ((p : ℝ) ^ 2 + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hlr : 0 < lam * r ^ 2 := by positivity
    have e1 : p * r * ηs ≤ lam * r ^ 2 / 16 := by
      rw [key1, mul_div_assoc]; nlinarith
    have e2 : p ^ 2 * r ^ 2 * ηM ≤ lam * r ^ 2 / 2 := by
      rw [key2]; nlinarith
    have hq' : lam * r ^ 2 ≤ ∑ j, ∑ k, u j * u k * M j k := by
      have : lam * r ^ 2 = Real.exp (-(p * (‖β₀‖ * B))) * (r * δ) ^ 2 * δ := by rw [hlam]; ring
      rw [this]; exact hquadM
    have hA := (abs_le.1 hlinb).1
    have hB2 := (abs_le.1 hquadb).1
    change resampleMean (fun z => w₀ z.1) n y < _
    linarith
  obtain ⟨hfeas, hlt⟩ := bootstrapTilt_feasible_and_norm_sub_lt φ t hn y hr0 hsep
  exact ⟨hn, hfeas, hlt.trans_le (min_le_left _ _)⟩

end PopulationAdjustment

end CausalInference
