/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLaplaceTotalVariation
public import CausalInference.PopulationAdjustment.BayesStandardization

/-!
# The logistic log likelihood: concavity, score and quadratic expansion

The logistic outcome model has the conditional density `logisticDens η y`, equal to `σ(η)` at
`y = 1` and to `1 - σ(η)` elsewhere, at the linear predictor `η = z(c) ⬝ ξ`. For records
`(cᵢ, yᵢ)`, `i < n`, the likelihood maximized by `glmMLE` is
`glmLikelihood logisticDens z x ξ = ∏ᵢ logisticDens (z(cᵢ) ⬝ ξ) yᵢ`; it is `e^{ℓ_n(ξ)}` with the
log likelihood `ℓ_n(ξ) = ∑ᵢ log logisticDens (z(cᵢ) ⬝ ξ) yᵢ` (`logisticLogLik`).

* The derivative of `η ↦ log logisticDens η y` is the score `s_y(η) = 1[y = 1] - σ(η)`
  (`hasDerivAt_log_logisticDens`); it is nonincreasing, so the log density is concave
  (`concaveOn_log_logisticDens`) and so is `ℓ_n` (`concaveOn_logisticLogLik`), for every value of
  the outcome.
* The second derivative is `-w(η)` with the weight `w = σ(1 - σ)` (`sigmoidWeight`), which is
  `1`-Lipschitz (`abs_sigmoidWeight_sub_le`). Two applications of the mean value inequality give
  the second order expansion of one term with remainder `(|η - η₀| + |d|) d²`
  (`abs_log_logisticDens_taylor`).
* **The quadratic expansion** (`abs_logisticLogLik_quad_le`): if every design vector is bounded
  by `B` in each coordinate, the score vanishes at `m` and the empirical information at `ξ₀`
  is within `n e` of `n M` entrywise, then
  `|ℓ_n(m + u) - ℓ_n(m) + (n/2) uᵀMu| ≤ n ((qB)³ (‖m - ξ₀‖ + ‖u‖) + q² e/2) ‖u‖²` with
  `q = card κ`, in Euclidean coordinates.
* **The score vanishes at an interior maximizer** (`logisticScoreSum_eq_zero_of_isLocalMax`),
  in particular at the maximum likelihood fit over `K` when `K` is a neighborhood of it
  (`logisticScoreSum_glmMLE_eq_zero`).

## Main definitions

* `PosteriorLimit.logisticDensScore`, `PosteriorLimit.sigmoidWeight`,
  `PosteriorLimit.logisticLogLik`, `PosteriorLimit.logisticScoreSum`,
  `PosteriorLimit.logisticEmpInfo`.

## Main results

* `hasDerivAt_log_logisticDens`, `concaveOn_log_logisticDens`, `abs_sigmoidWeight_sub_le`,
  `abs_log_logisticDens_taylor`.
* `glmLikelihood_logisticDens_eq_exp`, `concaveOn_logisticLogLik`, `abs_logisticLogLik_quad_le`.
* `logisticScoreSum_eq_zero_of_isLocalMax`, `glmMLE_isMaxOn`, `logisticScoreSum_glmMLE_eq_zero`.

## References

* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd edition, Chapman and Hall
  (1989), chapter 4.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open PopulationAdjustment PopulationAdjustment.BayesStandardization

/-! ### One term of the log likelihood -/

section OneTerm

/-- The **score** of the logistic density in the linear predictor: `1[y = 1] - σ(η)`. -/
noncomputable def logisticDensScore (η y : ℝ) : ℝ := (if y = 1 then 1 else 0) - Real.sigmoid η

/-- The **logistic weight** `w(η) = σ(η) (1 - σ(η))`, minus the second derivative of the log
density in the linear predictor. -/
noncomputable def sigmoidWeight (η : ℝ) : ℝ := Real.sigmoid η * (1 - Real.sigmoid η)

lemma sigmoidWeight_pos (η : ℝ) : 0 < sigmoidWeight η :=
  mul_pos (Real.sigmoid_pos η) (by linarith [Real.sigmoid_lt_one η])

lemma sigmoidWeight_le_one (η : ℝ) : sigmoidWeight η ≤ 1 := by
  have h0 := Real.sigmoid_pos η
  have h1 := Real.sigmoid_lt_one η
  unfold sigmoidWeight
  nlinarith

lemma continuous_sigmoidWeight : Continuous sigmoidWeight :=
  continuous_sigmoid.mul (continuous_const.sub continuous_sigmoid)

/-- The derivative of the log density in the linear predictor is the score. -/
lemma hasDerivAt_log_logisticDens (η y : ℝ) :
    HasDerivAt (fun t ↦ Real.log (logisticDens t y)) (logisticDensScore η y) η := by
  unfold logisticDens logisticDensScore
  by_cases hy : y = 1
  · simp only [hy, ite_true]
    have h := (Real.hasDerivAt_sigmoid η).log (Real.sigmoid_pos η).ne'
    refine h.congr_deriv ?_
    field_simp [(Real.sigmoid_pos η).ne']
  · simp only [hy, ite_false]
    have hne : 1 - Real.sigmoid η ≠ 0 := by linarith [Real.sigmoid_lt_one η]
    have h := ((Real.hasDerivAt_sigmoid η).const_sub 1).log hne
    refine h.congr_deriv ?_
    field_simp
    ring

/-- **The logistic log density is concave in the linear predictor**, for every value `y`: its
derivative `1[y = 1] - σ(η)` is nonincreasing. -/
lemma concaveOn_log_logisticDens (y : ℝ) :
    ConcaveOn ℝ univ fun t ↦ Real.log (logisticDens t y) := by
  refine Antitone.concaveOn_univ_of_deriv
    (fun t ↦ (hasDerivAt_log_logisticDens t y).differentiableAt) ?_
  intro a b hab
  rw [(hasDerivAt_log_logisticDens a y).deriv, (hasDerivAt_log_logisticDens b y).deriv]
  simp only [logisticDensScore]
  linarith [Real.sigmoid_le hab]

/-- The derivative of the weight: `w' = w (1 - 2σ)`. -/
lemma hasDerivAt_sigmoidWeight (η : ℝ) :
    HasDerivAt sigmoidWeight (sigmoidWeight η * (1 - 2 * Real.sigmoid η)) η := by
  have h := (Real.hasDerivAt_sigmoid η).mul ((Real.hasDerivAt_sigmoid η).const_sub 1)
  refine h.congr_deriv ?_
  simp only [sigmoidWeight]
  ring

/-- **The logistic weight is `1`-Lipschitz**: `|w'| = w |1 - 2σ| ≤ 1`. -/
lemma abs_sigmoidWeight_sub_le (a b : ℝ) : |sigmoidWeight a - sigmoidWeight b| ≤ |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (C := 1)
    (f := sigmoidWeight) (fun η _ ↦ (hasDerivAt_sigmoidWeight η).hasDerivWithinAt)
    (fun η _ ↦ by
      have h0 := (sigmoidWeight_pos η).le
      have h1 := sigmoidWeight_le_one η
      have hs0 := Real.sigmoid_pos η
      have hs1 := Real.sigmoid_lt_one η
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      have : |1 - 2 * Real.sigmoid η| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg (1 - 2 * Real.sigmoid η)])
    convex_univ (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h

lemma abs_le_abs_of_mem_uIcc {t d : ℝ} (ht : t ∈ uIcc 0 d) : |t| ≤ |d| := by
  rw [mem_uIcc] at ht
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith

/-- **Second order expansion of one term of the logistic log likelihood.** With
`φ(t) = log logisticDens t y`, score `s = φ'` and weight `w`,
`|φ(η + d) - φ(η) - s(η) d + w(η₀) d²/2| ≤ (|η - η₀| + |d|) d²`. -/
lemma abs_log_logisticDens_taylor (y η η₀ d : ℝ) :
    |Real.log (logisticDens (η + d) y) - Real.log (logisticDens η y) -
        logisticDensScore η y * d + sigmoidWeight η₀ / 2 * d ^ 2| ≤ (|η - η₀| + |d|) * d ^ 2 := by
  set C := |η - η₀| + |d| with hC
  have hC0 : 0 ≤ C := by positivity
  -- the logistic function minus its tangent of slope `w(η₀)`
  have h1 : ∀ t ∈ uIcc 0 d, |Real.sigmoid (η + t) - Real.sigmoid η - sigmoidWeight η₀ * t| ≤
      C * |t| := by
    intro t ht
    have hsub : uIcc 0 t ⊆ uIcc 0 d := uIcc_subset_uIcc_left ht
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := uIcc 0 t) (C := C)
      (f := fun τ ↦ Real.sigmoid (η + τ) - sigmoidWeight η₀ * τ)
      (f' := fun τ ↦ sigmoidWeight (η + τ) - sigmoidWeight η₀)
      (fun τ _ ↦ by
        have := ((Real.hasDerivAt_sigmoid (η + τ)).comp_const_add η τ).sub
          ((hasDerivAt_id τ).const_mul (sigmoidWeight η₀))
        simp only [mul_one] at this
        exact this.hasDerivWithinAt)
      (fun τ hτ ↦ by
        rw [Real.norm_eq_abs]
        refine (abs_sigmoidWeight_sub_le _ _).trans ?_
        have hτd : |τ| ≤ |d| := abs_le_abs_of_mem_uIcc (hsub hτ)
        calc |η + τ - η₀| = |(η - η₀) + τ| := by ring_nf
          _ ≤ |η - η₀| + |τ| := abs_add_le _ _
          _ ≤ C := by rw [hC]; linarith)
      (convex_uIcc 0 t) left_mem_uIcc right_mem_uIcc
    simp only [Real.norm_eq_abs, add_zero, mul_zero, sub_zero] at h
    calc |Real.sigmoid (η + t) - Real.sigmoid η - sigmoidWeight η₀ * t|
        = |Real.sigmoid (η + t) - sigmoidWeight η₀ * t - Real.sigmoid η| := by ring_nf
      _ ≤ C * |t| := h
  -- integrate the score
  have h2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := uIcc 0 d) (C := C * |d|)
    (f := fun t ↦ Real.log (logisticDens (η + t) y) - logisticDensScore η y * t +
      sigmoidWeight η₀ / 2 * t ^ 2)
    (f' := fun t ↦ logisticDensScore (η + t) y - logisticDensScore η y + sigmoidWeight η₀ * t)
    (fun t _ ↦ by
      have hd := (hasDerivAt_log_logisticDens (η + t) y).comp_const_add η t
      have := ((hd.sub ((hasDerivAt_id t).const_mul (logisticDensScore η y))).add
        ((hasDerivAt_pow 2 t).const_mul (sigmoidWeight η₀ / 2)))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp only [Nat.cast_ofNat]
      ring)
    (fun t ht ↦ by
      rw [Real.norm_eq_abs]
      have e : logisticDensScore (η + t) y - logisticDensScore η y + sigmoidWeight η₀ * t =
          -(Real.sigmoid (η + t) - Real.sigmoid η - sigmoidWeight η₀ * t) := by
        simp only [logisticDensScore]
        ring
      rw [e, abs_neg]
      exact (h1 t ht).trans (mul_le_mul_of_nonneg_left (abs_le_abs_of_mem_uIcc ht) hC0))
    (convex_uIcc 0 d) left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs, add_zero, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h2
  calc |Real.log (logisticDens (η + d) y) - Real.log (logisticDens η y) -
        logisticDensScore η y * d + sigmoidWeight η₀ / 2 * d ^ 2|
      = |Real.log (logisticDens (η + d) y) - logisticDensScore η y * d +
          sigmoidWeight η₀ / 2 * d ^ 2 - Real.log (logisticDens η y)| := by ring_nf
    _ ≤ C * |d| * |d| := h2
    _ = C * d ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end OneTerm

/-! ### The log likelihood of a sample of records -/

section LogLik

variable {C κ : Type*} [Fintype κ]

/-- The **logistic log likelihood** `ℓ_n(ξ) = ∑ᵢ log logisticDens (z(cᵢ) ⬝ ξ) yᵢ` of records
`x i = (cᵢ, yᵢ)`, `i < n`. -/
noncomputable def logisticLogLik (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) (ξ : κ → ℝ) : ℝ :=
  ∑ i, Real.log (logisticDens (z (x i).1 ⬝ᵥ ξ) (x i).2)

/-- The **score sum** `∑ᵢ s_{yᵢ}(z(cᵢ) ⬝ ξ) z(cᵢ)`, the gradient of the log likelihood. -/
noncomputable def logisticScoreSum (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) (ξ : κ → ℝ) :
    κ → ℝ :=
  ∑ i, logisticDensScore (z (x i).1 ⬝ᵥ ξ) (x i).2 • z (x i).1

/-- The **empirical information** at `ξ`: `∑ᵢ w(z(cᵢ) ⬝ ξ) z(cᵢ) z(cᵢ)ᵀ` (not divided by `n`). -/
noncomputable def logisticEmpInfo (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) (ξ : κ → ℝ) :
    Matrix κ κ ℝ :=
  Matrix.of fun j k ↦ ∑ i, sigmoidWeight (z (x i).1 ⬝ᵥ ξ) * z (x i).1 j * z (x i).1 k

/-- **The logistic likelihood is the exponential of the log likelihood**: every factor is
positive. -/
theorem glmLikelihood_logisticDens_eq_exp (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ)
    (ξ : κ → ℝ) : glmLikelihood logisticDens z x ξ = Real.exp (logisticLogLik z x ξ) := by
  unfold glmLikelihood logisticLogLik
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ ↦ (Real.exp_log (logisticDens_pos _ _)).symm

/-- **The logistic log likelihood is concave**: a sum of concave functions of linear functions
of `ξ`. -/
theorem concaveOn_logisticLogLik (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) :
    ConcaveOn ℝ univ (logisticLogLik z x) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst ↦ ?_⟩
  simp only [logisticLogLik, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h := (concaveOn_log_logisticDens (x i).2).2 (mem_univ (z (x i).1 ⬝ᵥ a))
    (mem_univ (z (x i).1 ⬝ᵥ b)) hs ht hst
  have e : z (x i).1 ⬝ᵥ (s • a + t • b) = s • (z (x i).1 ⬝ᵥ a) + t • (z (x i).1 ⬝ᵥ b) := by
    simp [dotProduct_add, dotProduct_smul]
  rw [e]
  simpa only [smul_eq_mul] using h

/-- The log likelihood in Euclidean coordinates is concave. -/
theorem concaveOn_logisticLogLik_ofLp (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) :
    ConcaveOn ℝ univ fun θ : EuclideanSpace ℝ κ ↦ logisticLogLik z x (WithLp.ofLp θ) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst ↦ ?_⟩
  have h := (concaveOn_logisticLogLik z x).2 (mem_univ (WithLp.ofLp a))
    (mem_univ (WithLp.ofLp b)) hs ht hst
  simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h

/-- The derivative of the log likelihood is the score sum. -/
theorem hasFDerivAt_logisticLogLik (z : C → κ → ℝ) {n : ℕ} (x : Fin n → C × ℝ) (ξ : κ → ℝ) :
    HasFDerivAt (logisticLogLik z x)
      (∑ i, logisticDensScore (z (x i).1 ⬝ᵥ ξ) (x i).2 • designCLM (z (x i).1)) ξ := by
  unfold logisticLogLik
  refine HasFDerivAt.fun_sum fun i _ ↦ ?_
  have hL : HasFDerivAt (fun ξ ↦ z (x i).1 ⬝ᵥ ξ) (designCLM (z (x i).1)) ξ := by
    have hf : (fun ξ ↦ z (x i).1 ⬝ᵥ ξ) = ⇑(designCLM (z (x i).1)) :=
      funext fun ξ ↦ (designCLM_apply _ ξ).symm
    rw [hf]
    exact (designCLM _).hasFDerivAt
  exact (hasDerivAt_log_logisticDens _ _).comp_hasFDerivAt ξ hL

/-- **The score vanishes at a local maximizer of the log likelihood.** -/
theorem logisticScoreSum_eq_zero_of_isLocalMax {z : C → κ → ℝ} {n : ℕ} {x : Fin n → C × ℝ}
    {ξ : κ → ℝ} (h : IsLocalMax (logisticLogLik z x) ξ) : logisticScoreSum z x ξ = 0 := by
  classical
  have h0 := h.hasFDerivAt_eq_zero (hasFDerivAt_logisticLogLik z x ξ)
  funext k
  have := congrArg (fun A : (κ → ℝ) →L[ℝ] ℝ ↦ A (Pi.single k 1)) h0
  simpa [logisticScoreSum, Finset.sum_apply, designCLM_apply, dotProduct_single] using this

/-- **The maximum likelihood fit maximizes the likelihood over `K`** when `K` is compact and
nonempty. -/
theorem glmMLE_isMaxOn {Ω : Type*} (z : C → κ → ℝ) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (O : ℕ → Ω → C × ℝ) (n : ℕ) (ω : Ω) :
    glmMLE logisticDens z K O n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K
        (glmMLE logisticDens z K O n ω) := by
  have h := exists_isMaxOn_glmLikelihood continuous_logisticDens z hK hne
    (fun i : Fin n ↦ O i ω)
  have hsel : glmMLE logisticDens z K O n ω = h.choose := by
    simp [glmMLE, glmMLECoef, h]
  rw [hsel]
  exact h.choose_spec

/-- **The score vanishes at the maximum likelihood fit** when `K` is compact and a neighborhood of
the fit. -/
theorem logisticScoreSum_glmMLE_eq_zero {Ω : Type*} (z : C → κ → ℝ) {K : Set (κ → ℝ)}
    (hK : IsCompact K) (O : ℕ → Ω → C × ℝ) (n : ℕ) (ω : Ω)
    (hnhds : K ∈ 𝓝 (glmMLE logisticDens z K O n ω)) :
    logisticScoreSum z (fun i : Fin n ↦ O i ω) (glmMLE logisticDens z K O n ω) = 0 := by
  obtain ⟨-, hmax⟩ := glmMLE_isMaxOn z hK ⟨_, mem_of_mem_nhds hnhds⟩ O n ω
  refine logisticScoreSum_eq_zero_of_isLocalMax ?_
  have hloc := hmax.isLocalMax hnhds
  have : logisticLogLik z (fun i : Fin n ↦ O i ω) =
      Real.log ∘ glmLikelihood logisticDens z (fun i : Fin n ↦ O i ω) := by
    funext ξ
    simp [glmLikelihood_logisticDens_eq_exp]
  rw [this]
  filter_upwards [hloc] with ξ hξ
  exact Real.log_le_log (by rw [glmLikelihood_logisticDens_eq_exp]; exact Real.exp_pos _) hξ

/-! ### The quadratic expansion -/

/-- A vector bounded by `B` in each coordinate acts on Euclidean space with norm at most
`q B`, `q = card κ`. -/
lemma abs_dotProduct_ofLp_le {a : κ → ℝ} {B : ℝ} (ha : ∀ j, |a j| ≤ B)
    (v : EuclideanSpace ℝ κ) : |a ⬝ᵥ WithLp.ofLp v| ≤ Fintype.card κ * B * ‖v‖ := by
  calc |a ⬝ᵥ WithLp.ofLp v| ≤ ∑ j, |a j * WithLp.ofLp v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, B * ‖v‖ := Finset.sum_le_sum fun j _ ↦ by
        rw [abs_mul]
        have h := PiLp.norm_apply_le v j
        rw [Real.norm_eq_abs] at h
        exact mul_le_mul (ha j) h (abs_nonneg _) ((abs_nonneg _).trans (ha j))
    _ = Fintype.card κ * B * ‖v‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **The local quadratic expansion of the logistic log likelihood.** Let every design vector of
the records be bounded by `B ≥ 0` in each coordinate, let the score vanish at `m`, and let the
empirical information at `ξ₀` be within `n e` of `n M` entrywise. Then, in Euclidean
coordinates, `|ℓ_n(m + u) - ℓ_n(m) + (n/2) uᵀMu| ≤ n ((qB)³ (‖m - ξ₀‖ + ‖u‖) + q² e/2) ‖u‖²`
with `q = card κ`. Proof: the second order expansion of each term around `z(cᵢ) ⬝ m` with the
weight taken at `z(cᵢ) ⬝ ξ₀`, the score equation, and the entrywise bound. -/
theorem abs_logisticLogLik_quad_le {z : C → κ → ℝ} {B : ℝ} (hB0 : 0 ≤ B) {n : ℕ}
    {x : Fin n → C × ℝ} (hB : ∀ i j, |z (x i).1 j| ≤ B) (ξ₀ : κ → ℝ) (M : Matrix κ κ ℝ) {e : ℝ}
    (hS : ∀ j k, |logisticEmpInfo z x ξ₀ j k - n * M j k| ≤ n * e)
    {m : EuclideanSpace ℝ κ} (hscore : logisticScoreSum z x (WithLp.ofLp m) = 0)
    (u : EuclideanSpace ℝ κ) :
    |logisticLogLik z x (WithLp.ofLp (m + u)) - logisticLogLik z x (WithLp.ofLp m) +
        n / 2 * quadForm M u| ≤
      n * ((Fintype.card κ * B) ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) +
        Fintype.card κ ^ 2 * e / 2) * ‖u‖ ^ 2 := by
  set q : ℝ := (Fintype.card κ : ℝ) with hq
  set Bq := q * B with hBq
  have hBq0 : 0 ≤ Bq := by positivity
  set η : Fin n → ℝ := fun i ↦ z (x i).1 ⬝ᵥ WithLp.ofLp m with hη
  set d : Fin n → ℝ := fun i ↦ z (x i).1 ⬝ᵥ WithLp.ofLp u with hd
  set w : Fin n → ℝ := fun i ↦ sigmoidWeight (z (x i).1 ⬝ᵥ ξ₀) with hw
  set φ : Fin n → ℝ → ℝ := fun i t ↦ Real.log (logisticDens t (x i).2) with hφ
  set T : Fin n → ℝ := fun i ↦ φ i (η i + d i) - φ i (η i) -
    logisticDensScore (η i) (x i).2 * d i + w i / 2 * d i ^ 2 with hT
  have hdB : ∀ i, |d i| ≤ Bq * ‖u‖ := fun i ↦ abs_dotProduct_ofLp_le (hB i) u
  have hTb : ∀ i, |T i| ≤ Bq ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) * ‖u‖ ^ 2 := by
    intro i
    have h := abs_log_logisticDens_taylor (x i).2 (η i) (z (x i).1 ⬝ᵥ ξ₀) (d i)
    have h1 : |η i - z (x i).1 ⬝ᵥ ξ₀| ≤ Bq * ‖m - WithLp.toLp 2 ξ₀‖ := by
      have := abs_dotProduct_ofLp_le (hB i) (m - WithLp.toLp 2 ξ₀)
      simpa [hη, dotProduct_sub] using this
    have h2 : d i ^ 2 ≤ (Bq * ‖u‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hdB i) 2
    calc |T i| ≤ (|η i - z (x i).1 ⬝ᵥ ξ₀| + |d i|) * d i ^ 2 := h
      _ ≤ (Bq * ‖m - WithLp.toLp 2 ξ₀‖ + Bq * ‖u‖) * (Bq * ‖u‖) ^ 2 :=
          mul_le_mul (add_le_add h1 (hdB i)) h2 (sq_nonneg _) (by positivity)
      _ = Bq ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) * ‖u‖ ^ 2 := by ring
  set S : κ → κ → ℝ := fun j k ↦ logisticEmpInfo z x ξ₀ j k with hSdef
  set X : ℝ := ∑ j, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k * (S j k - n * M j k) with hX
  have hsplit : logisticLogLik z x (WithLp.ofLp (m + u)) - logisticLogLik z x (WithLp.ofLp m) =
      ∑ i, (φ i (η i + d i) - φ i (η i)) := by
    simp only [logisticLogLik, ← Finset.sum_sub_distrib, hφ, hη, hd, WithLp.ofLp_add,
      dotProduct_add]
  have e1 : ∑ i, T i = ∑ i, (φ i (η i + d i) - φ i (η i)) -
      ∑ i, logisticDensScore (η i) (x i).2 * d i + 1 / 2 * ∑ i, w i * d i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [hT]; ring
  have h1 : ∑ i, logisticDensScore (η i) (x i).2 * d i = 0 := by
    have := congrArg (· ⬝ᵥ WithLp.ofLp u) hscore
    simpa [logisticScoreSum, sum_dotProduct, smul_dotProduct, hη, hd] using this
  have h2 : ∑ i, w i * d i ^ 2 = ∑ j, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k * S j k := by
    have hd2 : ∀ i, d i ^ 2 = ∑ j, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k *
        (z (x i).1 j * z (x i).1 k) := fun i ↦ by
      simp only [hd, dotProduct, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
    calc ∑ i, w i * d i ^ 2
        = ∑ i, ∑ j, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k *
            (w i * z (x i).1 j * z (x i).1 k) :=
          Finset.sum_congr rfl fun i _ ↦ by
            rw [hd2, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ = ∑ j, ∑ i, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k *
            (w i * z (x i).1 j * z (x i).1 k) := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, WithLp.ofLp u j * WithLp.ofLp u k *
            (w i * z (x i).1 j * z (x i).1 k) :=
          Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by
          simp only [hSdef, logisticEmpInfo, Matrix.of_apply, Finset.mul_sum, hw]
  have h3 : quadForm M u = ∑ j, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k * M j k := by
    simp only [quadForm, dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have h4 : X = ∑ j, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k * S j k -
      n * ∑ j, ∑ k, WithLp.ofLp u j * WithLp.ofLp u k * M j k := by
    simp only [hX, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    exact congrArg₂ _ rfl (Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring)
  have key : logisticLogLik z x (WithLp.ofLp (m + u)) - logisticLogLik z x (WithLp.ofLp m) +
      n / 2 * quadForm M u = ∑ i, T i - 1 / 2 * X := by
    linear_combination hsplit - e1 + h1 - (1 / 2) * h2 + ((n : ℝ) / 2) * h3 + (1 / 2) * h4
  have hTs : |∑ i, T i| ≤ n * (Bq ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) * ‖u‖ ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ ↦ hTb i).trans ?_
    simp
  have hXb : |X| ≤ q ^ 2 * (n * e) * ‖u‖ ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ ↦ Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hu : ∀ j, |WithLp.ofLp u j| ≤ ‖u‖ := fun j ↦ by
      have h := PiLp.norm_apply_le u j
      rwa [Real.norm_eq_abs] at h
    calc ∑ j, ∑ k, |WithLp.ofLp u j * WithLp.ofLp u k * (S j k - n * M j k)|
        ≤ ∑ _j : κ, ∑ _k : κ, ‖u‖ * ‖u‖ * (n * e) :=
          Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun k _ ↦ by
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul (hu j) (hu k) (abs_nonneg _) (norm_nonneg _))
              (hS j k) (abs_nonneg _) (by positivity)
      _ = q ^ 2 * (n * e) * ‖u‖ ^ 2 := by simp [q]; ring
  rw [key]
  calc |∑ i, T i - 1 / 2 * X|
      ≤ |∑ i, T i| + 1 / 2 * |X| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ n * (Bq ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) * ‖u‖ ^ 2) +
          1 / 2 * (q ^ 2 * (n * e) * ‖u‖ ^ 2) := by gcongr
    _ = _ := by ring

end LogLik

end PosteriorLimit

end CausalInference
