/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredConsistency
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Local envelopes for unbounded inverse links

The consistency theorems of the unanchored standardized comparison
(`tendstoInMeasure_unanchored_standardized`, `tendstoInMeasure_unanchored_marginalEffect`) ask
for a local envelope (`LocalEnvelope`) of the integrands `g⁻¹(c + xᵀβ)` under the aggregate
covariate law `F_B` and the target law `Q`. A bounded inverse link has one under every finite law
(`localEnvelope_of_bounded`). This file covers unbounded links.

* **Lipschitz links** (`localEnvelope_of_lipschitzWith`): if `g⁻¹` is `K`-Lipschitz and the
  covariates are integrable under the finite law `F`, then near `(c₀, β₀)` every integrand is
  bounded by `|g⁻¹(0)| + K ((|c₀| + 1) + ∑ᵢ |xᵢ| (|β₀ᵢ| + 1))`. A derivative bounded by `C` gives
  the Lipschitz constant `C` (`localEnvelope_of_hasDerivAt_bound`). The identity link is the
  basic case (`localEnvelope_id`).
* **The exponential link** (`localEnvelope_exp_iff`): `Real.exp` is not Lipschitz, and a local
  envelope for it holds exactly when every exponential moment `∫ exp(xᵀβ) dF` is finite. The
  envelope is a constant times the finite sum of `exp(xᵀ(β₀ + σ))` over the sign vectors `σ`.
* The consistency theorems for both kinds of links, with the covariate conditions in place of the
  envelope. The limit is the standardized comparison; for the causal estimand,
  `tendstoInMeasure_unanchored_marginalEffect` takes the same envelopes. There are two instances:
  the identity link with standard normal covariates, where neither the link nor the covariate is
  bounded, and the exponential link with one covariate equal to `0`.

## Main definitions

* `signVec`, `boolSignVec`: sign vectors used to bound `exp (xᵀβ)` by finitely many
  exponential moments.
* `stdNormalCovLaw`: the standard normal law on `ℝ¹`, used in the instance.

## Main results

* `localEnvelope_of_lipschitzWith`, `localEnvelope_of_hasDerivAt_bound`, `localEnvelope_id`.
* `localEnvelope_exp_iff`.
* `tendstoInMeasure_unanchored_standardized_of_lipschitzWith`,
  `tendstoInMeasure_unanchored_standardized_exp`.
* `tendstoInMeasure_unanchored_standardized_gaussian_instance`,
  `tendstoInMeasure_unanchored_standardized_exp_instance`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology EffectMeasure

variable {p : ℕ}

/-! ### Uniform control of the parameters near a point -/

/-- Near `(c₀, β₀)` the parameters satisfy `|c| < |c₀| + 1` and `|βᵢ| < |β₀ᵢ| + 1`. -/
theorem eventually_abs_lt_abs_add_one (c₀ : ℝ) (β₀ : Fin p → ℝ) :
    ∀ᶠ q : ℝ × (Fin p → ℝ) in 𝓝 (c₀, β₀), |q.1| < |c₀| + 1 ∧ ∀ i, |q.2 i| < |β₀ i| + 1 := by
  refine (((continuous_abs.comp continuous_fst).tendsto (c₀, β₀)).eventually
    (gt_mem_nhds (by simp : |c₀| < |c₀| + 1))).and (eventually_all.2 fun i => ?_)
  exact ((continuous_abs.comp ((continuous_apply i).comp continuous_snd)).tendsto
    (c₀, β₀)).eventually (gt_mem_nhds (by simp : |β₀ i| < |β₀ i| + 1))

/-- Near `(c₀, β₀)` the parameters satisfy `|c - c₀| < 1` and `|βᵢ - β₀ᵢ| < 1`. -/
theorem eventually_abs_sub_lt_one (c₀ : ℝ) (β₀ : Fin p → ℝ) :
    ∀ᶠ q : ℝ × (Fin p → ℝ) in 𝓝 (c₀, β₀), |q.1 - c₀| < 1 ∧ ∀ i, |q.2 i - β₀ i| < 1 := by
  refine ((((continuous_fst.sub continuous_const).abs).tendsto (c₀, β₀)).eventually
    (gt_mem_nhds (by simp : |c₀ - c₀| < 1))).and (eventually_all.2 fun i => ?_)
  exact ((((continuous_apply i).comp continuous_snd).sub continuous_const).abs.tendsto
    (c₀, β₀)).eventually (gt_mem_nhds (by simp : |β₀ i - β₀ i| < 1))

/-- `|xᵀβ| ≤ ∑ᵢ |xᵢ| |βᵢ|`. -/
theorem abs_dotProduct_le_sum (x β : Fin p → ℝ) : |x ⬝ᵥ β| ≤ ∑ i, |x i| * |β i| := by
  rw [dotProduct]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))

/-! ### Lipschitz inverse links -/

variable {F : Measure (Fin p → ℝ)} {ginv : ℝ → ℝ}

/-- **A Lipschitz inverse link has a local envelope** under every finite law with integrable
coordinates. Near `(c₀, β₀)` the integrands are bounded by
`|g⁻¹(0)| + K ((|c₀| + 1) + ∑ᵢ |xᵢ| (|β₀ᵢ| + 1))`. -/
theorem localEnvelope_of_lipschitzWith [IsFiniteMeasure F] {K : NNReal}
    (hL : LipschitzWith K ginv) (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) :
    LocalEnvelope F ginv := by
  intro c₀ β₀
  refine ⟨fun x => |ginv 0| + K * ((|c₀| + 1) + ∑ i, |x i| * (|β₀ i| + 1)),
    (integrable_const _).add (((integrable_const _).add (integrable_finsetSum _ fun i _ =>
      (hF i).abs.mul_const _)).const_mul _), ?_⟩
  filter_upwards [eventually_abs_lt_abs_add_one c₀ β₀] with q hq x
  have h1 : |ginv (q.1 + x ⬝ᵥ q.2)| ≤ |ginv 0| + K * |q.1 + x ⬝ᵥ q.2| := by
    have := hL.dist_le_mul (q.1 + x ⬝ᵥ q.2) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
    linarith [abs_sub_abs_le_abs_sub (ginv (q.1 + x ⬝ᵥ q.2)) (ginv 0)]
  have h2 : |q.1 + x ⬝ᵥ q.2| ≤ (|c₀| + 1) + ∑ i, |x i| * (|β₀ i| + 1) := by
    refine (abs_add_le _ _).trans (add_le_add hq.1.le ((abs_dotProduct_le_sum x q.2).trans ?_))
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hq.2 i).le (abs_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
  linarith

/-- **A derivative bounded by `C` gives a local envelope** under every finite law with integrable
coordinates: `g⁻¹` is then `C`-Lipschitz. -/
theorem localEnvelope_of_hasDerivAt_bound [IsFiniteMeasure F] {ginv' : ℝ → ℝ} {C : ℝ}
    (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hbd : ∀ t, |ginv' t| ≤ C)
    (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) : LocalEnvelope F ginv := by
  refine localEnvelope_of_lipschitzWith (K := C.toNNReal)
    (lipschitzWith_of_nnNorm_deriv_le (fun t => (hd t).differentiableAt) fun t => ?_) hF
  rw [(hd t).deriv, ← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, Real.coe_toNNReal']
  exact (hbd t).trans (le_max_left _ _)

/-- The identity link has a local envelope under every finite law with integrable coordinates. -/
theorem localEnvelope_id [IsFiniteMeasure F]
    (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) : LocalEnvelope F id :=
  localEnvelope_of_hasDerivAt_bound (C := 1) (fun t => hasDerivAt_id t) (fun _ => by simp) hF

/-! ### The exponential link -/

/-- The sign vector `σᵢ = 1` if `xᵢ ≥ 0` and `-1` otherwise, so that `xᵀσ = ∑ᵢ |xᵢ|`. -/
noncomputable def signVec (x : Fin p → ℝ) : Fin p → ℝ := fun i => if 0 ≤ x i then 1 else -1

theorem dotProduct_signVec (x : Fin p → ℝ) : x ⬝ᵥ signVec x = ∑ i, |x i| := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : 0 ≤ x i
  · simp [signVec, h, abs_of_nonneg h]
  · simp [signVec, h, abs_of_neg (not_le.1 h)]

/-- The sign vector of `b : Fin p → Bool`: `1` where `b` is true and `-1` elsewhere. -/
def boolSignVec (b : Fin p → Bool) : Fin p → ℝ := fun i => if b i then 1 else -1

theorem signVec_eq_boolSignVec (x : Fin p → ℝ) :
    signVec x = boolSignVec fun i => decide (0 ≤ x i) := by
  funext i
  simp [signVec, boolSignVec]

/-- **A local envelope for the exponential link is the finiteness of the exponential moments.**
Under any law `F`, the integrands `exp(c + xᵀβ)` have a local envelope exactly when
`exp(xᵀβ)` is integrable for every `β`. Near `(c₀, β₀)`,
`exp(c + xᵀβ) ≤ e^{c₀ + 1} exp(xᵀβ₀ + ∑ᵢ |xᵢ|)`, and `exp(xᵀβ₀ + ∑ᵢ |xᵢ|)` is one of the
`2^p` terms `exp(xᵀ(β₀ + σ))`, `σ ∈ {-1, 1}^p`. -/
theorem localEnvelope_exp_iff :
    LocalEnvelope F Real.exp ↔ ∀ β : Fin p → ℝ, Integrable (fun x => Real.exp (x ⬝ᵥ β)) F := by
  constructor
  · intro h β
    simpa using h.integrable Real.continuous_exp 0 β
  · intro h c₀ β₀
    refine ⟨fun x => Real.exp (c₀ + 1) * ∑ b : Fin p → Bool,
      Real.exp (x ⬝ᵥ (β₀ + boolSignVec b)),
      (integrable_finsetSum _ fun b _ => h _).const_mul _, ?_⟩
    filter_upwards [eventually_abs_sub_lt_one c₀ β₀] with q hq x
    rw [abs_of_pos (Real.exp_pos _)]
    have hdot : x ⬝ᵥ q.2 ≤ x ⬝ᵥ (β₀ + signVec x) := by
      rw [dotProduct_add, dotProduct_signVec]
      have : x ⬝ᵥ (q.2 - β₀) ≤ ∑ i, |x i| :=
        (le_abs_self _).trans ((abs_dotProduct_le_sum x _).trans (Finset.sum_le_sum fun i _ =>
          by simpa using mul_le_mul_of_nonneg_left (hq.2 i).le (abs_nonneg (x i))))
      rw [dotProduct_sub] at this
      linarith
    have hterm : Real.exp (x ⬝ᵥ (β₀ + signVec x)) ≤
        ∑ b : Fin p → Bool, Real.exp (x ⬝ᵥ (β₀ + boolSignVec b)) := by
      rw [signVec_eq_boolSignVec]
      exact Finset.single_le_sum (f := fun b => Real.exp (x ⬝ᵥ (β₀ + boolSignVec b)))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ _)
    calc Real.exp (q.1 + x ⬝ᵥ q.2)
        = Real.exp q.1 * Real.exp (x ⬝ᵥ q.2) := Real.exp_add _ _
      _ ≤ Real.exp (c₀ + 1) * Real.exp (x ⬝ᵥ (β₀ + signVec x)) := by
        refine mul_le_mul (Real.exp_le_exp.2 (by linarith [(abs_lt.1 hq.1).2]))
          (Real.exp_le_exp.2 hdot) (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le

/-! ### Consistency for unbounded links -/

section Consistency

variable {Ω J K : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Consistency of the unanchored standardized comparison for a Lipschitz inverse link.** The
statement of `tendstoInMeasure_unanchored_standardized` with the local envelopes replaced by a
`K`-Lipschitz, strictly increasing `g⁻¹` and integrable covariates under the aggregate law `F_B`
(a probability law) and the finite target law `Q`. -/
theorem tendstoInMeasure_unanchored_standardized_of_lipschitzWith {FB Q : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure FB] [IsFiniteMeasure Q] {L : NNReal} (hmono : StrictMono ginv)
    (hL : LipschitzWith L ginv) (hFB : ∀ i, Integrable (fun x : Fin p → ℝ => x i) FB)
    (hQ : ∀ i, Integrable (fun x : Fin p → ℝ => x i) Q) {g : ℝ → ℝ}
    {M : MultilevelModel J K p} {jA jB : J} {a b : K} (hM : M.SharedEffectModifiers {a, b})
    (hgA : ContinuousAt g (∫ x, M.surface ginv (M.μ jA) a x ∂Q))
    (hgB : ContinuousAt g (∫ x, M.surface ginv (M.μ jB) b x ∂Q))
    {αhat θhat : ℕ → Ω → ℝ} {βhat : ℕ → Ω → Fin p → ℝ}
    (hα : TendstoInMeasure P αhat atTop (fun _ => M.cellIntercept jA a))
    (hβ : TendstoInMeasure P βhat atTop (fun _ => M.cellSlope a))
    (hθ : TendstoInMeasure P θhat atTop (fun _ => M.armMean ginv (M.μ jB) FB b)) :
    TendstoInMeasure P
      (fun n ω => g (shiftMean Q ginv (fun x => x ⬝ᵥ βhat n ω)
          (calibratedShift FB ginv (βhat n ω) (θhat n ω))) -
        g (shiftMean Q ginv (fun x => x ⬝ᵥ βhat n ω) (αhat n ω))) atTop
      (fun _ => linkMarginal g Q (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b)) :=
  tendstoInMeasure_unanchored_standardized hmono hL.continuous
    (localEnvelope_of_lipschitzWith hL hFB) (localEnvelope_of_lipschitzWith hL hQ) hM hgA hgB hα
    hβ hθ

/-- **Consistency of the unanchored standardized comparison for the exponential link.** The
statement of `tendstoInMeasure_unanchored_standardized` for `g⁻¹ = exp` (the log link), with the
local envelopes replaced by finite exponential moments `∫ exp(xᵀβ) dF_B`, `∫ exp(xᵀβ) dQ` for
every `β`; by `localEnvelope_exp_iff` this is the same condition. -/
theorem tendstoInMeasure_unanchored_standardized_exp {FB Q : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure FB]
    (hFB : ∀ β : Fin p → ℝ, Integrable (fun x => Real.exp (x ⬝ᵥ β)) FB)
    (hQ : ∀ β : Fin p → ℝ, Integrable (fun x => Real.exp (x ⬝ᵥ β)) Q) {g : ℝ → ℝ}
    {M : MultilevelModel J K p} {jA jB : J} {a b : K} (hM : M.SharedEffectModifiers {a, b})
    (hgA : ContinuousAt g (∫ x, M.surface Real.exp (M.μ jA) a x ∂Q))
    (hgB : ContinuousAt g (∫ x, M.surface Real.exp (M.μ jB) b x ∂Q))
    {αhat θhat : ℕ → Ω → ℝ} {βhat : ℕ → Ω → Fin p → ℝ}
    (hα : TendstoInMeasure P αhat atTop (fun _ => M.cellIntercept jA a))
    (hβ : TendstoInMeasure P βhat atTop (fun _ => M.cellSlope a))
    (hθ : TendstoInMeasure P θhat atTop (fun _ => M.armMean Real.exp (M.μ jB) FB b)) :
    TendstoInMeasure P
      (fun n ω => g (shiftMean Q Real.exp (fun x => x ⬝ᵥ βhat n ω)
          (calibratedShift FB Real.exp (βhat n ω) (θhat n ω))) -
        g (shiftMean Q Real.exp (fun x => x ⬝ᵥ βhat n ω) (αhat n ω))) atTop
      (fun _ => linkMarginal g Q (M.surface Real.exp (M.μ jA) a)
        (M.surface Real.exp (M.μ jB) b)) :=
  tendstoInMeasure_unanchored_standardized Real.exp_strictMono Real.continuous_exp
    (localEnvelope_exp_iff.2 hFB) (localEnvelope_exp_iff.2 hQ) hM hgA hgB hα hβ hθ

end Consistency

/-! ### An instance with an unbounded link and unbounded covariates -/

/-- The standard normal law of one covariate: the image of `N(0, 1)` under `t ↦ (t)`. -/
noncomputable def stdNormalCovLaw : Measure (Fin 1 → ℝ) :=
  (gaussianReal 0 1).map fun t => fun _ => t

instance : IsProbabilityMeasure stdNormalCovLaw := by
  unfold stdNormalCovLaw
  infer_instance

theorem measurable_const_vec : Measurable fun t : ℝ => (fun _ : Fin 1 => t) := by fun_prop

/-- Integrals under `stdNormalCovLaw` are integrals under `N(0, 1)`. -/
theorem integral_stdNormalCovLaw {f : (Fin 1 → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂stdNormalCovLaw = ∫ t, f (fun _ => t) ∂gaussianReal 0 1 :=
  integral_map measurable_const_vec.aemeasurable hf.aestronglyMeasurable

/-- The covariate of `stdNormalCovLaw` is integrable. -/
theorem integrable_stdNormalCovLaw (i : Fin 1) :
    Integrable (fun x : Fin 1 → ℝ => x i) stdNormalCovLaw := by
  unfold stdNormalCovLaw
  rw [integrable_map_measure (continuous_apply i).aestronglyMeasurable
    measurable_const_vec.aemeasurable]
  exact (memLp_id_gaussianReal 1).integrable le_rfl

/-- `∫ (c + x) dN(0, 1)(x) = c`. -/
theorem integral_const_add_stdNormalCovLaw (c : ℝ) :
    ∫ x : Fin 1 → ℝ, c + x 0 ∂stdNormalCovLaw = c := by
  rw [integral_stdNormalCovLaw (by fun_prop)]
  change ∫ t, c + id t ∂gaussianReal 0 1 = c
  rw [integral_add (integrable_const _)
    ((memLp_id_gaussianReal 1).integrable le_rfl), integral_const]
  simp [integral_id_gaussianReal]

/-- **Instance of consistency with an unbounded link and unbounded covariates.** The identity
link, `F_B = Q = N(0, 1)` for one covariate, the scale `g = id`, the model with study intercepts
`μ_{j_A} = 0`, `μ_{j_B} = 1`, common prognostic effect `β₁ = 1` and no treatment parameters, and
the exact estimators. The aggregate mean of `b` is `1`, its calibrated shift is `1`, and the
standardized comparison converges to `1`. -/
theorem tendstoInMeasure_unanchored_standardized_gaussian_instance {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) :
    let M : MultilevelModel Bool Bool 1 := ⟨fun j => if j then 0 else 1, fun _ => 1, 0, 0⟩
    M.armMean id (M.μ false) stdNormalCovLaw false = 1 ∧
      calibratedShift stdNormalCovLaw id (M.cellSlope true)
        (M.armMean id (M.μ false) stdNormalCovLaw false) = 1 ∧
      TendstoInMeasure P
        (fun (_ : ℕ) (_ : Ω) => shiftMean stdNormalCovLaw id (fun x => x ⬝ᵥ M.cellSlope true)
            (calibratedShift stdNormalCovLaw id (M.cellSlope true)
              (M.armMean id (M.μ false) stdNormalCovLaw false)) -
          shiftMean stdNormalCovLaw id (fun x => x ⬝ᵥ M.cellSlope true)
            (M.cellIntercept true true)) atTop
        (fun _ => 1) := by
  intro M
  have hsurf : ∀ (α : ℝ) (k : Bool) (x : Fin 1 → ℝ), M.surface id α k x = α + x 0 := by
    intro α k x
    simp [M, MultilevelModel.surface, MultilevelModel.eta,
      NetworkMetaAnalysis.metaRegressionPredictor, dotProduct]
  have hmean : M.armMean id (M.μ false) stdNormalCovLaw false = 1 := by
    rw [MultilevelModel.armMean]
    simp only [hsurf]
    exact integral_const_add_stdNormalCovLaw _
  have hS : M.SharedEffectModifiers {true, false} := by
    rw [MultilevelModel.sharedEffectModifiers_iff]; intro _ _ _ _; rfl
  have hclass : M ∈ MultilevelModel.unanchoredClass id stdNormalCovLaw true false :=
    ⟨hS, fun s => (localEnvelope_id integrable_stdNormalCovLaw).integrable continuous_id s _⟩
  have hc := (MultilevelModel.unanchored_estimand_eq_calibrated (jA := true) (jB := false)
    strictMono_id hclass stdNormalCovLaw id).1
  have h := tendstoInMeasure_unanchored_standardized_of_lipschitzWith (P := P) (g := id)
    (M := M) (jA := true) (jB := false) (a := true) (b := false) strictMono_id LipschitzWith.id
    integrable_stdNormalCovLaw integrable_stdNormalCovLaw hS continuousAt_id continuousAt_id
    (tendstoInMeasure_const _) (tendstoInMeasure_const _) (tendstoInMeasure_const _)
  have hv : linkMarginal id stdNormalCovLaw (M.surface id (M.μ true) true)
      (M.surface id (M.μ false) false) = 1 := by
    rw [linkMarginal]
    simp only [hsurf, integral_const_add_stdNormalCovLaw]
    simp [M]
  rw [hv] at h
  refine ⟨hmean, ?_, by simpa using h⟩
  rw [← hc]
  simp [M, MultilevelModel.cellIntercept]

/-- **Instance of consistency for the exponential link.** The link `g⁻¹ = exp`, `F_B = Q = δ_0`
for one covariate, the scale `g = id`, the model with study intercepts `μ_{j_A} = 0`,
`μ_{j_B} = log 2` and all other parameters `0`, and the exact estimators. The exponential moments
are finite, the aggregate mean of `b` is `exp (log 2) = 2`, and the standardized comparison
converges to `2 - 1 = 1`. -/
theorem tendstoInMeasure_unanchored_standardized_exp_instance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) :
    let M : MultilevelModel Bool Bool 1 := ⟨fun j => if j then 0 else Real.log 2, 0, 0, 0⟩
    M.armMean Real.exp (M.μ false) (Measure.dirac fun _ => 0) false = 2 ∧
      TendstoInMeasure P
        (fun (_ : ℕ) (_ : Ω) => shiftMean (Measure.dirac fun _ => 0) Real.exp
            (fun x => x ⬝ᵥ M.cellSlope true)
            (calibratedShift (Measure.dirac fun _ => 0) Real.exp (M.cellSlope true)
              (M.armMean Real.exp (M.μ false) (Measure.dirac fun _ => 0) false)) -
          shiftMean (Measure.dirac fun _ => 0) Real.exp (fun x => x ⬝ᵥ M.cellSlope true)
            (M.cellIntercept true true)) atTop
        (fun _ => 1) := by
  intro M
  have hsurf : ∀ (α : ℝ) (k : Bool) (x : Fin 1 → ℝ), M.surface Real.exp α k x = Real.exp α := by
    intro α k x
    simp [M, MultilevelModel.surface, MultilevelModel.eta,
      NetworkMetaAnalysis.metaRegressionPredictor]
  have hmom : ∀ β : Fin 1 → ℝ, Integrable (fun x => Real.exp (x ⬝ᵥ β))
      (Measure.dirac fun _ : Fin 1 => (0 : ℝ)) := fun _ => integrable_dirac (by simp)
  have hmean : M.armMean Real.exp (M.μ false) (Measure.dirac fun _ => 0) false = 2 := by
    rw [MultilevelModel.armMean]
    simp only [hsurf, integral_dirac]
    simp [M, Real.exp_log]
  have h := tendstoInMeasure_unanchored_standardized_exp (P := P) (g := id) (M := M) (jA := true)
    (jB := false) (a := true) (b := false) hmom hmom
    (by rw [MultilevelModel.sharedEffectModifiers_iff]; intro _ _ _ _; rfl)
    continuousAt_id continuousAt_id (tendstoInMeasure_const _) (tendstoInMeasure_const _)
    (tendstoInMeasure_const _)
  have hv : linkMarginal id (Measure.dirac fun _ : Fin 1 => (0 : ℝ))
      (M.surface Real.exp (M.μ true) true) (M.surface Real.exp (M.μ false) false) = 1 := by
    rw [linkMarginal]
    simp only [hsurf, integral_dirac]
    simp [M, Real.exp_log]
    norm_num
  rw [hv] at h
  exact ⟨hmean, h⟩

end NetworkMetaRegression

end CausalInference
