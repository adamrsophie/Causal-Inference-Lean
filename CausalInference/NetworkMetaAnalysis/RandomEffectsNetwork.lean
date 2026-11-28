/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.NetworkModel
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Random effects in a network: the one half correlation of a multi-arm study

A study with arms `K` and baseline arm `r` reports the `|K| - 1` contrasts of its other arms
against the baseline, `δ_k = Z_k - Z_r` (`baselineContrasts`, the `armContrasts` of the
star network with tail `r`).

**The arm level model.** Under the random effects model with consistency and exchangeability,
the arm effects are `Z_k = d_k + u_k`, with `u_k` square integrable, mean zero, variance `τ²/2`
and pairwise uncorrelated. Then every contrast has mean `d_k - d_r` and variance `τ²`, two
contrasts sharing the baseline have covariance `τ²/2` and correlation one half, and the
covariance matrix is `τ²/2 (I + J)` with `J` the all ones matrix
(`baselineContrasts_randomEffects`). This is the `covMatrix_armContrasts` for the star
network, which gives in general `diag(σ_k) + σ_r J` (`covMatrix_baselineContrasts`). With
independent Gaussian arm effects every contrast has the law `N(d_k - d_r, τ²)`
(`baselineContrasts_randomEffects_gaussian`). Adding within study estimation errors that are
uncorrelated with the random effects adds their covariance matrix
(`covMatrix_baselineContrasts_add_error`).

**The value one half is forced.** In a contrast level model, if every contrast of the study,
including the contrasts `δ_l - δ_k` not against the baseline, has the same variance `v`, then
two baseline contrasts have covariance exactly `v/2`; conversely covariance `v/2` gives every
contrast the variance `v` (`covariance_eq_half_iff_variance_sub`,
`covariance_eq_half_iff_forall_variance_sub`). Hence the covariance matrix is `v/2 (I + J)` and
the correlation is one half (`correlation_eq_half_of_variance_sub`).

**The spectrum of `c (I + J)`** on `m` contrasts, `c > 0`: it is positive definite; the constant
vectors form the eigenspace of the eigenvalue `c (m + 1)`, the vectors summing to zero the
eigenspace of the eigenvalue `c` (of dimension `m - 1`); the determinant is `(m + 1) c^m` and
the inverse is `c⁻¹ (I - J / (m + 1))`.

## Main definitions

* `onesMatrix`, `baselineContrasts`.

## Main results

* `covariance_eq_half_iff_variance_sub`, `covariance_eq_half_iff_forall_variance_sub`,
  `covMatrix_eq_of_variance_sub`, `correlation_eq_half_of_variance_sub`.
* `posDef_smul_one_add_onesMatrix`, `smul_one_add_onesMatrix_mulVec_const`,
  `smul_one_add_onesMatrix_mulVec_eq_iff_sum_eq_zero`,
  `smul_one_add_onesMatrix_mulVec_eq_iff_const`, `finrank_sum_eq_zero_add_one`,
  `det_smul_one_add_onesMatrix`, `inv_smul_one_add_onesMatrix`.
* `covMatrix_baselineContrasts`, `baselineContrasts_randomEffects`,
  `baselineContrasts_randomEffects_gaussian`, `covMatrix_baselineContrasts_add_error`.

## References

* J. P. T. Higgins and A. Whitehead, *Borrowing strength from external trials in a
  meta-analysis*, Statistics in Medicine 15 (1996).
* G. Lu and A. E. Ades, *Combination of direct and indirect evidence in mixed treatment
  comparisons*, Statistics in Medicine 23 (2004).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError
open scoped NNReal

/-! ### The all ones matrix and the spectrum of `c (I + J)` -/

section Spectrum

/-- The **all ones matrix** `J`. -/
def onesMatrix (m : Type*) : Matrix m m ℝ := Matrix.of fun _ _ => 1

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- `J x` is the constant vector of the sum of the coordinates of `x`. -/
theorem onesMatrix_mulVec (x : m → ℝ) : onesMatrix m *ᵥ x = fun _ => ∑ i, x i := by
  funext k
  simp [onesMatrix, mulVec, dotProduct]

omit [Fintype m] [DecidableEq m] in
/-- `J = 𝟙 𝟙ᵀ`. -/
theorem onesMatrix_eq_replicateCol_mul_replicateRow :
    onesMatrix m =
      replicateCol Unit (fun _ : m => (1 : ℝ)) * replicateRow Unit (fun _ : m => (1 : ℝ)) := by
  ext i j
  simp [onesMatrix, Matrix.mul_apply, replicateCol, replicateRow]

omit [DecidableEq m] in
/-- `J J = m J`. -/
theorem onesMatrix_mul_self :
    onesMatrix m * onesMatrix m = (Fintype.card m : ℝ) • onesMatrix m := by
  ext i j
  simp [onesMatrix, Matrix.mul_apply]

/-- `(c (I + J)) x = c (x + (∑ x) 𝟙)`. -/
theorem smul_one_add_onesMatrix_mulVec (c : ℝ) (x : m → ℝ) :
    (c • (1 + onesMatrix m)) *ᵥ x = c • (x + fun _ => ∑ i, x i) := by
  rw [smul_mulVec, add_mulVec, one_mulVec, onesMatrix_mulVec]

omit [Fintype m] in
/-- **`c (I + J)` is positive definite** for `c > 0`. -/
theorem posDef_smul_one_add_onesMatrix {c : ℝ} (hc : 0 < c) : (c • (1 + onesMatrix m)).PosDef := by
  refine Matrix.PosDef.smul ?_ hc
  refine Matrix.PosDef.add_posSemidef Matrix.PosDef.one ?_
  have := Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (_ : Unit) (_ : m) => (1 : ℝ))
  convert this using 1
  ext i j
  simp [onesMatrix, Matrix.mul_apply]

/-- **The constant vector is an eigenvector** of `c (I + J)` with eigenvalue `c (m + 1)`. -/
theorem smul_one_add_onesMatrix_mulVec_const (c : ℝ) :
    (c • (1 + onesMatrix m)) *ᵥ (fun _ => 1) = (c * (Fintype.card m + 1)) • fun _ => 1 := by
  rw [smul_one_add_onesMatrix_mulVec]
  funext k
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  ring

/-- **The eigenspace of the eigenvalue `c`** of `c (I + J)`, `c ≠ 0`, is the hyperplane of
vectors summing to zero. -/
theorem smul_one_add_onesMatrix_mulVec_eq_iff_sum_eq_zero {c : ℝ} (hc : c ≠ 0) (x : m → ℝ) :
    (c • (1 + onesMatrix m)) *ᵥ x = c • x ↔ ∑ i, x i = 0 := by
  rw [smul_one_add_onesMatrix_mulVec]
  constructor
  · intro h
    rcases isEmpty_or_nonempty m with he | ⟨⟨k⟩⟩
    · simp
    · have := congrFun h k
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
      have h3 : c * ∑ i, x i = 0 := by linarith
      exact (mul_eq_zero.1 h3).resolve_left hc
  · intro hx
    rw [hx]
    funext k
    simp

/-- **The eigenspace of the eigenvalue `c (m + 1)`** of `c (I + J)`, `c ≠ 0`, is the line of
the constant vectors. -/
theorem smul_one_add_onesMatrix_mulVec_eq_iff_const {c : ℝ} (hc : c ≠ 0) (x : m → ℝ) :
    (c • (1 + onesMatrix m)) *ᵥ x = (c * (Fintype.card m + 1)) • x ↔
      ∃ t : ℝ, x = t • fun _ => 1 := by
  rw [smul_one_add_onesMatrix_mulVec]
  constructor
  · intro h
    have hx : ∀ k, x k * Fintype.card m = ∑ i, x i := by
      intro k
      have := congrFun h k
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
      have h3 : c * (x k * Fintype.card m - ∑ i, x i) = 0 := by linarith
      linarith [(mul_eq_zero.1 h3).resolve_left hc]
    rcases isEmpty_or_nonempty m with he | ⟨⟨k₀⟩⟩
    · exact ⟨0, funext fun k => (he.false k).elim⟩
    · have hpos : (0 : ℝ) < Fintype.card m := by
        exact_mod_cast Fintype.card_pos_iff.2 ⟨k₀⟩
      refine ⟨(∑ i, x i) / Fintype.card m, funext fun k => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      rw [← hx k]
      field_simp
  · rintro ⟨t, rfl⟩
    funext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring

omit [DecidableEq m] in
/-- **The dimension of the eigenspace of `c`**: the hyperplane of vectors summing to zero has
dimension `m - 1` (stated as `dim + 1 = m` for `m ≥ 1`). -/
theorem finrank_sum_eq_zero_add_one (hm : 1 ≤ Fintype.card m) :
    Module.finrank ℝ (LinearMap.ker (Matrix.of fun (_ : Unit) (_ : m) => (1 : ℝ)).mulVecLin) + 1 =
      Fintype.card m := by
  classical
  have hsurj :
      Function.Surjective (Matrix.of fun (_ : Unit) (_ : m) => (1 : ℝ)).mulVecLin := by
    obtain ⟨k₀⟩ : Nonempty m := Fintype.card_pos_iff.1 (by omega)
    intro t
    refine ⟨Pi.single k₀ (t ()), funext fun u => ?_⟩
    simp [mulVec, dotProduct]
  have h := LinearMap.finrank_range_add_finrank_ker
    (Matrix.of fun (_ : Unit) (_ : m) => (1 : ℝ)).mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_unit] at h
  omega

/-- **The determinant of `c (I + J)`** is `(m + 1) c^m`. -/
theorem det_smul_one_add_onesMatrix (c : ℝ) :
    (c • (1 + onesMatrix m)).det = (Fintype.card m + 1) * c ^ Fintype.card m := by
  rw [det_smul, onesMatrix_eq_replicateCol_mul_replicateRow,
    det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  ring

/-- **The inverse of `c (I + J)`** is `c⁻¹ (I - J / (m + 1))`, for `c ≠ 0`. -/
theorem inv_smul_one_add_onesMatrix {c : ℝ} (hc : c ≠ 0) :
    (c • (1 + onesMatrix m))⁻¹ = c⁻¹ • (1 - ((Fintype.card m : ℝ) + 1)⁻¹ • onesMatrix m) := by
  refine inv_eq_left_inv ?_
  have hm : ((Fintype.card m : ℝ) + 1) ≠ 0 := by positivity
  have ha : ((Fintype.card m : ℝ) + 1)⁻¹ + ((Fintype.card m : ℝ) + 1)⁻¹ * Fintype.card m = 1 := by
    field_simp
    ring
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_mul,
    mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    onesMatrix_mul_self, smul_smul, ← add_smul, ha, one_smul, add_sub_cancel_right]

end Spectrum

/-! ### The one half correlation is forced -/

section Forced

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **Covariance one half of the common variance, exactly when the difference has the common
variance.** For square integrable `X`, `Y` with the same variance `v`,
`Cov(X, Y) = v/2` if and only if `Var(Y - X) = v`. -/
theorem covariance_eq_half_iff_variance_sub {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {v : ℝ} (hXv : Var[X; P] = v) (hYv : Var[Y; P] = v) :
    cov[X, Y; P] = v / 2 ↔ Var[fun ω => Y ω - X ω; P] = v := by
  rw [variance_fun_sub hY hX, hXv, hYv, covariance_comm Y X]
  constructor <;> intro h <;> linarith

/-- **The one half covariance is forced by a common contrast variance** (Higgins and Whitehead
1996). Let the baseline contrasts `δ_k` of a study be square integrable with common variance
`v`. Every derived contrast `δ_l - δ_k` (a contrast of two non-baseline arms) has the variance
`v` if and only if every two distinct baseline contrasts have covariance `v/2`. -/
theorem covariance_eq_half_iff_forall_variance_sub {ι : Type*} {δ : ι → Ω → ℝ}
    (hδ : ∀ k, MemLp (δ k) 2 P) {v : ℝ} (hvar : ∀ k, Var[δ k; P] = v) :
    (∀ k l, k ≠ l → cov[δ k, δ l; P] = v / 2) ↔
      ∀ k l, k ≠ l → Var[fun ω => δ l ω - δ k ω; P] = v :=
  forall₂_congr fun k l => imp_congr_right fun _ =>
    covariance_eq_half_iff_variance_sub (hδ k) (hδ l) (hvar k) (hvar l)

/-- **The covariance matrix of the baseline contrasts is `v/2 (I + J)`** when all contrasts of
the study, baseline and derived, have the common variance `v`. -/
theorem covMatrix_eq_of_variance_sub {ι : Type*} [DecidableEq ι] {δ : ι → Ω → ℝ}
    (hδ : ∀ k, MemLp (δ k) 2 P) {v : ℝ} (hvar : ∀ k, Var[δ k; P] = v)
    (hsub : ∀ k l, k ≠ l → Var[fun ω => δ l ω - δ k ω; P] = v) :
    covMatrix P δ = (v / 2) • (1 + onesMatrix ι) := by
  have hc := (covariance_eq_half_iff_forall_variance_sub hδ hvar).2 hsub
  ext k l
  simp only [covMatrix, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, onesMatrix,
    smul_eq_mul]
  by_cases h : k = l
  · subst h
    rw [covariance_self (hδ k).aestronglyMeasurable.aemeasurable, hvar, Matrix.one_apply_eq]
    ring
  · rw [hc k l h, Matrix.one_apply_ne h]
    ring

/-- **Correlation one half.** If all contrasts of the study, baseline and derived, have the
common variance `v > 0`, two distinct baseline contrasts have correlation `1/2`. -/
theorem correlation_eq_half_of_variance_sub {ι : Type*} {δ : ι → Ω → ℝ}
    (hδ : ∀ k, MemLp (δ k) 2 P) {v : ℝ} (hv : 0 < v) (hvar : ∀ k, Var[δ k; P] = v)
    (hsub : ∀ k l, k ≠ l → Var[fun ω => δ l ω - δ k ω; P] = v) {k l : ι} (hkl : k ≠ l) :
    cov[δ k, δ l; P] / Real.sqrt (Var[δ k; P] * Var[δ l; P]) = 1 / 2 := by
  rw [(covariance_eq_half_iff_forall_variance_sub hδ hvar).2 hsub k l hkl, hvar, hvar,
    Real.sqrt_mul_self hv.le]
  field_simp

end Forced

/-! ### The arm level random effects model -/

section RandomEffects

variable {K : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The **baseline contrasts** of a study with baseline arm `r`: `δ_k = Z_k - Z_r` for the
other arms `k`, the contrasts of the star network with tail `r`. -/
def baselineContrasts (r : K) (Z : K → Ω → ℝ) : {k // k ≠ r} → Ω → ℝ :=
  armContrasts (fun _ => r) Subtype.val Z

variable [Finite K] [DecidableEq K] {r : K}

omit [Finite K] [DecidableEq K] in
theorem memLp_baselineContrasts {Z : K → Ω → ℝ} (hZ : ∀ k, MemLp (Z k) 2 P)
    (k : {k // k ≠ r}) : MemLp (baselineContrasts r Z k) 2 P :=
  (hZ k.1).sub (hZ r)

/-- **The covariance of the baseline contrasts of uncorrelated arms** is `diag(σ_k) + σ_r J`:
the `covMatrix_armContrasts` for the star network. Each contrast has variance
`σ_k + σ_r` and two distinct contrasts have covariance `σ_r`. -/
theorem covMatrix_baselineContrasts [IsFiniteMeasure P] {Z : K → Ω → ℝ}
    (hZ : ∀ k, MemLp (Z k) 2 P) {σ : K → ℝ} (hvar : ∀ k, Var[Z k; P] = σ k)
    (hunc : ∀ k l, k ≠ l → cov[Z k, Z l; P] = 0) :
    covMatrix P (baselineContrasts r Z) =
      diagonal (fun k : {k // k ≠ r} => σ k.1) + σ r • onesMatrix {k // k ≠ r} := by
  have := Fintype.ofFinite K
  ext k l
  rw [baselineContrasts, covMatrix_armContrasts_apply _ _ hZ hvar hunc]
  have hk : k.1 ≠ r := k.2
  have hl : l.1 ≠ r := l.2
  by_cases h : k = l
  · subst h
    simp [incidenceMatrix, onesMatrix, hk, Ne.symm hk]
  · have h' : k.1 ≠ l.1 := fun e => h (Subtype.ext e)
    simp [incidenceMatrix, onesMatrix, h, h', hk, Ne.symm hl]

/-- **The arm level random effects model** (Higgins and Whitehead 1996; Lu and Ades 2004). Let
the arm effects of a study be `Z_k = d_k + u_k` with random effects `u_k` square integrable,
mean zero, variance `τ²/2` and pairwise uncorrelated. Then the baseline contrasts have means
`d_k - d_r`, covariance matrix `τ²/2 (I + J)`, variances `τ²`, and for `τ² > 0` two distinct
contrasts have correlation `1/2`. -/
theorem baselineContrasts_randomEffects [IsProbabilityMeasure P] (d : K → ℝ)
    {u : K → Ω → ℝ} {τsq : ℝ} (hu : ∀ k, MemLp (u k) 2 P) (hmean : ∀ k, ∫ ω, u k ω ∂P = 0)
    (hvar : ∀ k, Var[u k; P] = τsq / 2) (hunc : ∀ k l, k ≠ l → cov[u k, u l; P] = 0) :
    (∀ k, ∫ ω, baselineContrasts r (fun k ω => d k + u k ω) k ω ∂P = d k - d r) ∧
      covMatrix P (baselineContrasts r fun k ω => d k + u k ω) =
        (τsq / 2) • (1 + onesMatrix {k // k ≠ r}) ∧
      (∀ k, Var[baselineContrasts r (fun k ω => d k + u k ω) k; P] = τsq) ∧
      (0 < τsq → ∀ k l, k ≠ l →
        cov[baselineContrasts r (fun k ω => d k + u k ω) k,
            baselineContrasts r (fun k ω => d k + u k ω) l; P] /
          Real.sqrt (Var[baselineContrasts r (fun k ω => d k + u k ω) k; P] *
            Var[baselineContrasts r (fun k ω => d k + u k ω) l; P]) = 1 / 2) := by
  have := Fintype.ofFinite K
  set Z : K → Ω → ℝ := fun k ω => d k + u k ω with hZdef
  have hint : ∀ k, Integrable (u k) P := fun k => (hu k).integrable one_le_two
  have hZ : ∀ k, MemLp (Z k) 2 P := fun k => (memLp_const (d k)).add (hu k)
  have hZvar : ∀ k, Var[Z k; P] = τsq / 2 := fun k => by
    rw [← covariance_self (hZ k).aestronglyMeasurable.aemeasurable, hZdef,
      covariance_const_add_left (hint k), covariance_const_add_right (hint k),
      covariance_self (hu k).aestronglyMeasurable.aemeasurable, hvar]
  have hZunc : ∀ k l, k ≠ l → cov[Z k, Z l; P] = 0 := fun k l hkl => by
    rw [hZdef, covariance_const_add_left (hint k), covariance_const_add_right (hint l),
      hunc k l hkl]
  have hcov :
      covMatrix P (baselineContrasts r Z) = (τsq / 2) • (1 + onesMatrix {k // k ≠ r}) := by
    rw [covMatrix_baselineContrasts hZ hZvar hZunc]
    ext k l
    by_cases h : k = l
    · subst h; simp [onesMatrix]; ring
    · simp [onesMatrix, h]
  have hmem := memLp_baselineContrasts (r := r) hZ
  have hvarδ : ∀ k, Var[baselineContrasts r Z k; P] = τsq := fun k => by
    rw [← covariance_self (hmem k).aestronglyMeasurable.aemeasurable]
    have := congrFun (congrFun hcov k) k
    simp only [covMatrix, Matrix.of_apply] at this
    rw [this]
    simp [onesMatrix]
    ring
  refine ⟨fun k => ?_, hcov, hvarδ, fun hτ k l hkl => ?_⟩
  · change ∫ ω, (d k.1 + u k.1 ω) - (d r + u r ω) ∂P = d k - d r
    have i1 : Integrable (fun ω => d k.1 + u k.1 ω) P := (integrable_const _).add (hint _)
    have i2 : Integrable (fun ω => d r + u r ω) P := (integrable_const _).add (hint _)
    rw [integral_sub i1 i2,
      integral_add (integrable_const _) (hint _), integral_add (integrable_const _) (hint _),
      hmean, hmean]
    simp
  · have := congrFun (congrFun hcov k) l
    simp only [covMatrix, Matrix.of_apply] at this
    rw [this, hvarδ, hvarδ, Real.sqrt_mul_self hτ.le]
    simp [onesMatrix, hkl]
    field_simp

/-- **Gaussian arm level random effects.** If the random effects `u_k` are independent with law
`N(0, τ²/2)`, the conclusions of `baselineContrasts_randomEffects` hold, and each baseline
contrast has the law `N(d_k - d_r, τ²)`. -/
theorem baselineContrasts_randomEffects_gaussian [IsProbabilityMeasure P] (d : K → ℝ)
    {u : K → Ω → ℝ} {τsq : ℝ} (hτ : 0 ≤ τsq)
    (hlaw : ∀ k, HasLaw (u k) (gaussianReal 0 (τsq / 2).toNNReal) P) (hind : iIndepFun u P) :
    (∀ k, ∫ ω, baselineContrasts r (fun k ω => d k + u k ω) k ω ∂P = d k - d r) ∧
      covMatrix P (baselineContrasts r fun k ω => d k + u k ω) =
        (τsq / 2) • (1 + onesMatrix {k // k ≠ r}) ∧
      (∀ k, Var[baselineContrasts r (fun k ω => d k + u k ω) k; P] = τsq) ∧
      (0 < τsq → ∀ k l, k ≠ l →
        cov[baselineContrasts r (fun k ω => d k + u k ω) k,
            baselineContrasts r (fun k ω => d k + u k ω) l; P] /
          Real.sqrt (Var[baselineContrasts r (fun k ω => d k + u k ω) k; P] *
            Var[baselineContrasts r (fun k ω => d k + u k ω) l; P]) = 1 / 2) ∧
      ∀ k, HasLaw (baselineContrasts r (fun k ω => d k + u k ω) k)
        (gaussianReal (d k - d r) τsq.toNNReal) P := by
  have := Fintype.ofFinite K
  have hu : ∀ k, MemLp (u k) 2 P := fun k => (hlaw k).memLp (memLp_id_gaussianReal 2)
  have hmom := baselineContrasts_randomEffects (r := r) d hu
    (fun k => by rw [(hlaw k).integral_eq, integral_id_gaussianReal])
    (fun k => by
      rw [(hlaw k).variance_eq, variance_id_gaussianReal]
      exact Real.coe_toNNReal _ (by positivity))
    (fun k l hkl => (hind.indepFun hkl).covariance_eq_zero (hu k) (hu l))
  refine ⟨hmom.1, hmom.2.1, hmom.2.2.1, hmom.2.2.2, fun k => ?_⟩
  have hk : k.1 ≠ r := k.2
  have hneg : HasLaw (fun ω => -u r ω) (gaussianReal 0 (τsq / 2).toNNReal) P :=
    HasLaw.comp (X := u r) (Y := fun x => -x)
      ⟨by fun_prop, by rw [gaussianReal_map_neg, neg_zero]⟩ (hlaw r)
  have hsum : P.map (u k.1 + fun ω => -u r ω) =
      gaussianReal (0 + 0) ((τsq / 2).toNNReal + (τsq / 2).toNNReal) :=
    gaussianReal_add_gaussianReal_of_indepFun
      ((hind.indepFun hk).comp measurable_id measurable_neg) (hlaw k.1) hneg
  have hvv : (τsq / 2).toNNReal + (τsq / 2).toNNReal = τsq.toNNReal := by
    rw [← Real.toNNReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [add_zero, hvv] at hsum
  have hS : HasLaw (u k.1 + fun ω => -u r ω) (gaussianReal 0 τsq.toNNReal) P :=
    ⟨(hlaw k.1).aemeasurable.add hneg.aemeasurable, hsum⟩
  have h2 := HasLaw.comp (X := u k.1 + fun ω => -u r ω) (Y := fun x => (d k - d r) + x)
    ⟨by fun_prop, by rw [gaussianReal_map_const_add, zero_add]⟩ hS
  refine h2.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [baselineContrasts, armContrasts, Function.comp, Pi.add_apply]
  ring

/-- **Within study error.** If the reported contrasts are `δ̂_k = δ_k + ε_k`, with square
integrable within study errors `ε` uncorrelated with the random effects contrasts `δ`, the
covariance matrix of the reported contrasts is `Cov(δ) + Cov(ε)`; under the arm level random
effects model it is `τ²/2 (I + J) + Cov(ε)`. -/
theorem covMatrix_baselineContrasts_add_error [IsFiniteMeasure P] {ι : Type*}
    {δ ε : ι → Ω → ℝ} (hδ : ∀ k, MemLp (δ k) 2 P) (hε : ∀ k, MemLp (ε k) 2 P)
    (hunc : ∀ k l, cov[δ k, ε l; P] = 0) :
    covMatrix P (fun k ω => δ k ω + ε k ω) = covMatrix P δ + covMatrix P ε := by
  ext k l
  simp only [covMatrix, Matrix.of_apply, Matrix.add_apply]
  change cov[δ k + ε k, δ l + ε l; P] = _
  rw [covariance_add_left (hδ k) (hε k) ((hδ l).add (hε l)),
    covariance_add_right (hδ k) (hδ l) (hε l), covariance_add_right (hε k) (hδ l) (hε l),
    hunc k l, covariance_comm (ε k) (δ l), hunc l k]
  ring

end RandomEffects

end NetworkMetaAnalysis

end CausalInference
