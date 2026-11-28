/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityVariance

/-!
# The sandwich variance estimate is a measurable function of the sample

The stacked estimate `θ̂ₙ = (β̂ₙ, m̂ₙ)` contains the sample dual parameter `β̂ₙ = dualMinimizer`,
chosen by `Classical.choose`, which is not shown to be measurable. The sandwich variance estimate
is nevertheless a measurable function of the first `n` records, by **scale invariance**: every
entry of the estimating function and of its Jacobian carries exactly one factor of the tilt
`w_{β̂ₙ}(Xᵢ)`, and at the sample points the tilt is the partition function `Z > 0` times the
entropy balancing weight, `w_{β̂ₙ}(Xᵢ) = Z cᵢ` with `c = balancingWeights`. So the empirical
bread is `Z` times a matrix `Ã` built from the weights, the (cross) meat is `Z²` times a matrix
`B̃`, and `(Z Ã)⁻¹ (Z² B̃) (Z Ã)⁻ᵀ = Ã⁻¹ B̃ Ã⁻ᵀ` (with `(s A)⁻¹ = s⁻¹ A⁻¹` also for singular `A`,
`inv_smul_of_ne_zero`). The weights are measurable in the sample
(`measurable_balancingWeights_sample`), the weighted arm means as well, and the entries of a
matrix inverse are measurable functions of the entries (`measurable_inv_apply`).

## Main results

* `inv_smul_of_ne_zero`: `(s • A)⁻¹ = s⁻¹ • A⁻¹` for `s ≠ 0`, singular or not.
* `measurable_inv_apply`: the entries of the inverse of a matrix with measurable entries are
  measurable.
* `weightedEstFun_eq_smul`, `weightedEstJac_eq_smul`: the tilt factors out.
* `isSampleMeasurable_weightedInfluenceCovHat`: the cross covariance estimate, and so the
  sandwich variance estimate, is a measurable function of the sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

/-! ### Matrix inverses -/

section MatrixInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The inverse of a nonzero multiple**: `(s • A)⁻¹ = s⁻¹ • A⁻¹` for `s ≠ 0`, also when `A` is
singular (both sides are then `0`). -/
theorem inv_smul_of_ne_zero {s : ℝ} (hs : s ≠ 0) (A : Matrix ι ι ℝ) :
    (s • A)⁻¹ = s⁻¹ • A⁻¹ := by
  by_cases hA : IsUnit A.det
  · have h := Matrix.inv_smul' A (Units.mk0 s hs) hA
    rw [Units.smul_def, Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0] at h
    exact h
  · have hsA : ¬IsUnit (s • A).det := by
      rw [Matrix.det_smul, isUnit_iff_ne_zero]
      rw [isUnit_iff_ne_zero, not_not] at hA
      rw [hA, mul_zero, not_not]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hsA, Matrix.nonsing_inv_apply_not_isUnit _ hA,
      smul_zero]

/-- **The entries of a matrix inverse are measurable** in the entries:
`A⁻¹ = det(A)⁻¹ adj(A)`, the determinant and the adjugate being continuous. -/
theorem measurable_inv_apply {X : Type*} [MeasurableSpace X] {F : X → Matrix ι ι ℝ}
    (hF : ∀ i j, Measurable fun x => F x i j) (i j : ι) :
    Measurable fun x => (F x)⁻¹ i j := by
  have hF' : Measurable fun x => (fun i j => F x i j : ι → ι → ℝ) :=
    Measurable.of_eval fun i => Measurable.of_eval fun j => hF i j
  have hof : Continuous fun M : ι → ι → ℝ => (Matrix.of M : Matrix ι ι ℝ) := continuous_id
  have hdet : Measurable fun x => (F x).det :=
    hof.matrix_det.measurable.comp hF'
  have hadj : Measurable fun x => (F x).adjugate i j :=
    ((continuous_apply_apply i j).comp hof.matrix_adjugate).measurable.comp hF'
  have h : (fun x => (F x)⁻¹ i j) = fun x => ((F x).det)⁻¹ * (F x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [h]
  exact hdet.inv.mul hadj

end MatrixInverse

variable {𝒳 : Type*} {p : ℕ}

/-! ### The tilt factors out -/

/-- **The tilt factors out of the estimating function**: `ψ(z; θ)` is the tilt `w_β(x)` times
the estimating function at the untilted parameter `(0, m)`. -/
theorem weightedEstFun_eq_smul (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool)
    (z : 𝒳 × Bool × ℝ) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    weightedEstFun φ t a z θ = tiltWeight φ t 0 (stackedBalance θ) z.1 •
      weightedEstFun φ t a z (stackedParam 0 (θ (Sum.inr ()))) := by
  ext k
  rcases k with j | u
  · simp [weightedEstFun, tiltWeight_zero_param]
  · simp [weightedEstFun, tiltWeight_zero_param]; ring

/-- **The tilt factors out of the Jacobian matrix.** -/
theorem weightedEstJac_eq_smul (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool)
    (z : 𝒳 × Bool × ℝ) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    weightedEstJac φ t a z θ = tiltWeight φ t 0 (stackedBalance θ) z.1 •
      weightedEstJac φ t a z (stackedParam 0 (θ (Sum.inr ()))) := by
  ext k l
  rcases k with j | u <;> rcases l with k | v <;>
    simp [weightedEstJac, tiltWeight_zero_param] <;> ring

variable {Ω : Type*} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- At a sample point the tilt is the partition function times the entropy balancing weight. -/
theorem tiltWeight_sampleTilt_eq (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (n : ℕ) (ω : Ω) (i : Fin n) :
    tiltWeight φ t 0 (sampleTilt φ t O n ω) (O i ω).1 =
      partitionFunction (fun i : Fin n => φ (O i ω).1 - t) (sampleTilt φ t O n ω) *
        balancingWeights (fun i : Fin n => φ (O i ω).1 - t) i := by
  have : Nonempty (Fin n) := ⟨i⟩
  have hZ := (partitionFunction_pos (Δ := fun i : Fin n => φ (O i ω).1 - t)
    (sampleTilt φ t O n ω)).ne'
  simp only [sampleTilt] at hZ ⊢
  rw [balancingWeights, entropyWeights, mul_div_cancel₀ _ hZ]
  simp [tiltWeight]

/-- The empirical bread of arm `a` with the weights in place of the tilt. -/
noncomputable def weightedBreadTilde (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool) {n : ℕ}
    (x : Fin n → 𝒳 × Bool × ℝ) : Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ :=
  Matrix.of fun k l => -((n : ℝ)⁻¹ * ∑ i, balancingWeights (fun i => φ (x i).1 - t) i *
    weightedEstJac φ t a (x i) (stackedParam 0 (weightedArmMean
      (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1) (fun i => (x i).2.2) a)) k l)

/-- The cross meat of arms `a` and `b` with the weights in place of the tilt. -/
noncomputable def weightedMeatTilde (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a b : Bool) {n : ℕ}
    (x : Fin n → 𝒳 × Bool × ℝ) : Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ :=
  Matrix.of fun k l => (n : ℝ)⁻¹ * ∑ i, balancingWeights (fun i => φ (x i).1 - t) i ^ 2 *
    (weightedEstFun φ t a (x i) (stackedParam 0 (weightedArmMean
      (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1) (fun i => (x i).2.2) a)) k *
    weightedEstFun φ t b (x i) (stackedParam 0 (weightedArmMean
      (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1) (fun i => (x i).2.2) b)) l)

/-- **Scale invariance of the empirical bread**: it is the partition function times
`weightedBreadTilde`. -/
theorem breadMatrixHat_weighted_eq_smul (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) :
    breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω =
      partitionFunction (fun i : Fin n => φ (O i ω).1 - t) (sampleTilt φ t O n ω) •
        weightedBreadTilde φ t a (fun i : Fin n => O i ω) := by
  ext k l
  simp only [breadMatrixHat, weightedBreadTilde, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, sampleMean]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => weightedEstJac φ t a (O i ω) (weightedStackedEstimate φ t O a n ω) k l)]
  simp only [Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weightedEstJac_eq_smul, Matrix.smul_apply, smul_eq_mul]
  have hb : tiltWeight φ t 0 (stackedBalance (weightedStackedEstimate φ t O a n ω)) (O i ω).1 =
      partitionFunction (fun i : Fin n => φ (O i ω).1 - t) (sampleTilt φ t O n ω) *
        balancingWeights (fun i : Fin n => φ (O i ω).1 - t) i :=
    tiltWeight_sampleTilt_eq φ t O n ω i
  rw [hb]
  simp only [weightedStackedEstimate, stackedParam_inr, sampleBalancedArmMean]
  ring

/-- **Scale invariance of the cross meat**: it is the squared partition function times
`weightedMeatTilde`. -/
theorem crossMeat_weighted_eq_smul (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a b : Bool) (n : ℕ) (ω : Ω) :
    (Matrix.of fun k l => sampleMean (fun z =>
      weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω) k *
        weightedEstFun φ t b z (weightedStackedEstimate φ t O b n ω) l) O n ω) =
      partitionFunction (fun i : Fin n => φ (O i ω).1 - t) (sampleTilt φ t O n ω) ^ 2 •
        weightedMeatTilde φ t a b (fun i : Fin n => O i ω) := by
  ext k l
  simp only [weightedMeatTilde, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, sampleMean]
  rw [← Fin.sum_univ_eq_sum_range (fun i =>
    weightedEstFun φ t a (O i ω) (weightedStackedEstimate φ t O a n ω) k *
      weightedEstFun φ t b (O i ω) (weightedStackedEstimate φ t O b n ω) l)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [weightedEstFun_eq_smul φ t a _ (weightedStackedEstimate φ t O a n ω),
    weightedEstFun_eq_smul φ t b _ (weightedStackedEstimate φ t O b n ω)]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hb : ∀ c : Bool, tiltWeight φ t 0 (stackedBalance (weightedStackedEstimate φ t O c n ω))
      (O i ω).1 = partitionFunction (fun i : Fin n => φ (O i ω).1 - t) (sampleTilt φ t O n ω) *
        balancingWeights (fun i : Fin n => φ (O i ω).1 - t) i := fun c =>
    tiltWeight_sampleTilt_eq φ t O n ω i
  rw [hb a, hb b]
  simp only [weightedStackedEstimate, stackedParam_inr, sampleBalancedArmMean]
  ring

/-- **The cross covariance estimate in terms of the weights**: for `n ≥ 1` it is
`(Ã_a⁻¹ B̃ Ã_b⁻ᵀ)_{m m}` with `weightedBreadTilde` and `weightedMeatTilde`, a function of the
entropy balancing weights and the records only. -/
theorem weightedInfluenceCovHat_eq_tilde (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a b : Bool) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    weightedInfluenceCovHat φ t O a b n ω =
      ((weightedBreadTilde φ t a (fun i : Fin n => O i ω))⁻¹ *
        weightedMeatTilde φ t a b (fun i : Fin n => O i ω) *
        ((weightedBreadTilde φ t b (fun i : Fin n => O i ω))⁻¹)ᵀ) (Sum.inr ()) (Sum.inr ()) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Z := partitionFunction (fun i : Fin n => φ (O i ω).1 - t) (sampleTilt φ t O n ω)
  have hZ : Z ≠ 0 := (partitionFunction_pos (sampleTilt φ t O n ω)).ne'
  rw [weightedInfluenceCovHat, breadMatrixHat_weighted_eq_smul, breadMatrixHat_weighted_eq_smul,
    crossMeat_weighted_eq_smul, inv_smul_of_ne_zero hZ, inv_smul_of_ne_zero hZ]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_apply, smul_eq_mul]
  field_simp
  rfl

/-! ### Measurability -/

variable [MeasurableSpace 𝒳]

/-- The weighted arm mean of the sample is measurable in the sample. -/
theorem measurable_weightedArmMean_sample {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    (t : Fin p → ℝ) (a : Bool) (n : ℕ) :
    Measurable fun x : Fin n → 𝒳 × Bool × ℝ => weightedArmMean
      (balancingWeights fun i : Fin n => φ (x i).1 - t) (fun i => (x i).2.1)
        (fun i => (x i).2.2) a := by
  have hw : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      balancingWeights fun i : Fin n => φ (x i).1 - t :=
    measurable_balancingWeights_sample (φ := fun r : 𝒳 × Bool × ℝ => φ r.1)
      (hφ.comp measurable_fst) t
  have hA : ∀ i, Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      armWeights (balancingWeights fun i : Fin n => φ (x i).1 - t) (fun i => (x i).2.1) a i :=
    fun i => Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i).snd.fst
      measurable_const) ((measurable_pi_apply i).comp hw) measurable_const
  exact (Finset.measurable_sum _ fun i _ => (hA i).mul (measurable_pi_apply i).snd.snd).div
    (Finset.measurable_sum _ fun i _ => hA i)

/-- The untilted estimating function is jointly measurable in the record and the arm mean. -/
theorem measurable_weightedEstFun_stackedParam_zero {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    (t : Fin p → ℝ) (a : Bool) (k : Fin p ⊕ Unit) :
    Measurable fun q : (𝒳 × Bool × ℝ) × ℝ => weightedEstFun φ t a q.1 (stackedParam 0 q.2) k := by
  rcases k with j | u
  · simp only [weightedEstFun, PiLp.toLp_apply, Sum.elim_inl, stackedBalance_stackedParam,
      tiltWeight_zero_param, one_mul]
    exact ((measurable_pi_apply j).comp (hφ.comp measurable_fst.fst)).sub_const _
  · simp only [weightedEstFun, PiLp.toLp_apply, Sum.elim_inr, stackedBalance_stackedParam,
      tiltWeight_zero_param, mul_one, stackedParam_inr]
    exact ((measurable_armIndObs a).comp measurable_fst).mul
      (measurable_fst.snd.snd.sub measurable_snd)

/-- The untilted Jacobian matrix is jointly measurable in the record and the arm mean. -/
theorem measurable_weightedEstJac_stackedParam_zero {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    (t : Fin p → ℝ) (a : Bool) (k l : Fin p ⊕ Unit) :
    Measurable fun q : (𝒳 × Bool × ℝ) × ℝ =>
      weightedEstJac φ t a q.1 (stackedParam 0 q.2) k l := by
  have hf : ∀ j, Measurable fun q : (𝒳 × Bool × ℝ) × ℝ => φ q.1.1 j - t j := fun j =>
    ((measurable_pi_apply j).comp (hφ.comp measurable_fst.fst)).sub_const _
  have hI : Measurable fun q : (𝒳 × Bool × ℝ) × ℝ => armIndObs a q.1 :=
    (measurable_armIndObs a).comp measurable_fst
  rcases k with j | u <;> rcases l with k | v
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₁, Matrix.of_apply,
      stackedBalance_stackedParam, tiltWeight_zero_param, one_mul]
    exact (hf j).mul (hf k)
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    exact measurable_const
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₁, Matrix.of_apply,
      stackedBalance_stackedParam, tiltWeight_zero_param, mul_one, stackedParam_inr]
    exact (hI.mul (measurable_fst.snd.snd.sub measurable_snd)).mul (hf k)
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
      stackedBalance_stackedParam, tiltWeight_zero_param, mul_one]
    exact hI.neg

/-- The entries of `weightedBreadTilde` are measurable in the sample. -/
theorem measurable_weightedBreadTilde {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t : Fin p → ℝ)
    (a : Bool) (n : ℕ) (k l : Fin p ⊕ Unit) :
    Measurable fun x : Fin n → 𝒳 × Bool × ℝ => weightedBreadTilde φ t a x k l := by
  have hw : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      balancingWeights fun i : Fin n => φ (x i).1 - t :=
    measurable_balancingWeights_sample (φ := fun r : 𝒳 × Bool × ℝ => φ r.1)
      (hφ.comp measurable_fst) t
  have hm := measurable_weightedArmMean_sample hφ t a n
  have hi : ∀ i : Fin n, Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      balancingWeights (fun i => φ (x i).1 - t) i *
        weightedEstJac φ t a (x i) (stackedParam 0 (weightedArmMean
          (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1)
          (fun i => (x i).2.2) a)) k l := fun i => by
    have h1 : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
        balancingWeights (fun i => φ (x i).1 - t) i := (measurable_pi_apply i).comp hw
    have h2 : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
        weightedEstJac φ t a (x i) (stackedParam 0 (weightedArmMean
          (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1)
          (fun i => (x i).2.2) a)) k l := by
      have h := (measurable_weightedEstJac_stackedParam_zero hφ t a k l).comp
        ((measurable_pi_apply i).prodMk hm)
      exact h
    exact h1.mul h2
  exact ((Finset.measurable_sum Finset.univ fun i _ => hi i).const_mul _).neg

/-- The entries of `weightedMeatTilde` are measurable in the sample. -/
theorem measurable_weightedMeatTilde {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t : Fin p → ℝ)
    (a b : Bool) (n : ℕ) (k l : Fin p ⊕ Unit) :
    Measurable fun x : Fin n → 𝒳 × Bool × ℝ => weightedMeatTilde φ t a b x k l := by
  have hw : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      balancingWeights fun i : Fin n => φ (x i).1 - t :=
    measurable_balancingWeights_sample (φ := fun r : 𝒳 × Bool × ℝ => φ r.1)
      (hφ.comp measurable_fst) t
  have hma := measurable_weightedArmMean_sample hφ t a n
  have hmb := measurable_weightedArmMean_sample hφ t b n
  have hi : ∀ i : Fin n, Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      balancingWeights (fun i => φ (x i).1 - t) i ^ 2 *
        (weightedEstFun φ t a (x i) (stackedParam 0 (weightedArmMean
          (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1)
          (fun i => (x i).2.2) a)) k *
        weightedEstFun φ t b (x i) (stackedParam 0 (weightedArmMean
          (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1)
          (fun i => (x i).2.2) b)) l) := fun i => by
    have h1 : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
        balancingWeights (fun i => φ (x i).1 - t) i := (measurable_pi_apply i).comp hw
    have h2 : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
        weightedEstFun φ t a (x i) (stackedParam 0 (weightedArmMean
          (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1)
          (fun i => (x i).2.2) a)) k := by
      have h := (measurable_weightedEstFun_stackedParam_zero hφ t a k).comp
        ((measurable_pi_apply i).prodMk hma)
      exact h
    have h3 : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
        weightedEstFun φ t b (x i) (stackedParam 0 (weightedArmMean
          (balancingWeights fun i => φ (x i).1 - t) (fun i => (x i).2.1)
          (fun i => (x i).2.2) b)) l := by
      have h := (measurable_weightedEstFun_stackedParam_zero hφ t b l).comp
        ((measurable_pi_apply i).prodMk hmb)
      exact h
    exact (h1.pow_const 2).mul (h2.mul h3)
  exact (Finset.measurable_sum Finset.univ fun i _ => hi i).const_mul _

omit [MeasurableSpace 𝒳] in
/-- At sample size zero the cross covariance estimate is `0`. -/
theorem weightedInfluenceCovHat_zero (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a b : Bool) (ω : Ω) :
    weightedInfluenceCovHat φ t O a b 0 ω = 0 := by
  rw [weightedInfluenceCovHat_eq_sampleMean]
  simp [sampleMean]

omit [MeasurableSpace 𝒳] in
/-- **The cross covariance estimate is a measurable function of the sample** (for a measurable
feature map). In particular so is the sandwich variance estimate of one arm
(`weightedInfluenceCovHat_self`). -/
theorem isSampleMeasurable_weightedInfluenceCovHat [MeasurableSpace 𝒳] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) (t : Fin p → ℝ) (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a b : Bool) :
    IsSampleMeasurable (weightedInfluenceCovHat φ t O a b) O := fun n => by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ => 0, measurable_const, funext fun ω => weightedInfluenceCovHat_zero φ t O a b ω⟩
  refine ⟨fun x => ((weightedBreadTilde φ t a x)⁻¹ * weightedMeatTilde φ t a b x *
    ((weightedBreadTilde φ t b x)⁻¹)ᵀ) (Sum.inr ()) (Sum.inr ()), ?_,
    funext fun ω => weightedInfluenceCovHat_eq_tilde φ t O a b hn ω⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Finset.measurable_sum _ fun l _ => (Finset.measurable_sum _ fun k _ => ?_).mul ?_
  · exact (measurable_inv_apply (measurable_weightedBreadTilde hφ t a n) _ _).mul
      (measurable_weightedMeatTilde hφ t a b n k l)
  · exact measurable_inv_apply (measurable_weightedBreadTilde hφ t b n) _ _

end PopulationAdjustment

end CausalInference
