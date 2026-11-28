/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ParametricFamily
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The score of a scalar parametric family

For a family `F : ParametricFamily ℝ S` with densities `f(x;θ)`, the score is
`s(θ;x) = ∂_θ f(x;θ) / f(x;θ)`, the derivative of the log density where the density is positive.
The score has mean zero under `P_θ` when the derivative of `θ ↦ ∫ f(x;θ) dν(x) = 1` can be taken
under the integral sign, and the derivative of the mean of a statistic `T` is the cross moment
`E_θ[T s]` when the derivative of `θ ↦ ∫ T f(·;θ) dν` can be taken under the integral sign.

The interchange of derivative and integral is a predicate (`DerivInterchange`,
`DerivInterchangeTwo`, `MeanDerivInterchange`) that includes the integrability of the
differentiated integrand, so that it never holds through the value `0` that Lean gives to the
integral of a non integrable function. The predicates follow from integrable envelopes of
the derivatives by dominated convergence (`derivInterchange_of_dominated`,
`derivInterchangeTwo_of_dominated`, `meanDerivInterchange_of_dominated`,
`meanDerivInterchange_of_bounded`); the Bernoulli family discharges these envelopes.

## Main definitions

* `CausalInference.ParametricFamily.mean`, `IsUnbiased`: the mean `E_θ[T]` of a statistic and
  unbiasedness (with integrability).
* `CausalInference.ParametricFamily.densityDeriv`, `densityDeriv2`, `score`, `logLik`,
  `hessLogLik`.
* `CausalInference.ParametricFamily.DerivInterchange`, `DerivInterchangeTwo`,
  `MeanDerivInterchange`.

## Main results

* `CausalInference.ParametricFamily.integrable_score` and `integral_score_eq_zero`: the score is
  integrable and has mean zero.
* `CausalInference.ParametricFamily.hasDerivAt_mean`: `∂_θ E_θ[T] = E_θ[T s(θ;X)]`.
* The dominated convergence constructors of the interchange predicates.

References: E. L. Lehmann and G. Casella (1998), *Theory of Point Estimation*, 2nd edition,
chapter 2; A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace CausalInference

namespace ParametricFamily

variable {P S : Type*} [MeasurableSpace S] (F : ParametricFamily P S)

/-- The mean `E_θ[T]` of a statistic `T` under `P_θ`. -/
noncomputable def mean (T : S → ℝ) (θ : P) : ℝ :=
  ∫ x, T x ∂F.law θ

/-- `T` is an unbiased estimator of `g(θ)`: for every `θ ∈ Θ`, `T` is `P_θ`-integrable and
`E_θ[T] = g(θ)`. The integrability excludes the value `0` of the integral of a non integrable
function. -/
def IsUnbiased (T : S → ℝ) (g : P → ℝ) : Prop :=
  ∀ θ ∈ F.Θ, Integrable T (F.law θ) ∧ F.mean T θ = g θ

/-- The log-likelihood `ℓ(θ;x) = log f(x;θ)` of one observation. Lean's `Real.log 0 = 0`; the
theorems that use it assume the density positive almost surely where it is evaluated. -/
noncomputable def logLik (θ : P) (x : S) : ℝ :=
  Real.log (F.density θ x)

variable (F : ParametricFamily ℝ S)

/-- The derivative `∂f(x;θ)/∂θ` of the density in the parameter. -/
noncomputable def densityDeriv (θ : ℝ) (x : S) : ℝ :=
  deriv (fun u ↦ F.density u x) θ

/-- The second derivative `∂²f(x;θ)/∂θ²` of the density in the parameter. -/
noncomputable def densityDeriv2 (θ : ℝ) (x : S) : ℝ :=
  deriv (fun u ↦ F.densityDeriv u x) θ

/-- The score `s(θ;x) = ∂_θ f(x;θ) / f(x;θ)`. Where `f(x;θ) = 0` the quotient is `0`; such
points form a `P_θ`-null set (`ParametricFamily.ae_law_pos`). By `score_eq_deriv_logLik` it is
the derivative of the log density wherever the density is positive. -/
noncomputable def score (θ : ℝ) (x : S) : ℝ :=
  F.densityDeriv θ x / F.density θ x

/-- The second derivative `∂²ℓ(θ;x)/∂θ²` of the log-likelihood. -/
noncomputable def hessLogLik (θ : ℝ) (x : S) : ℝ :=
  deriv (fun u ↦ deriv (fun v ↦ F.logLik v x) u) θ

/-- First order interchange at `θ`: `∂_θ f(·;θ)` is `ν`-integrable and the derivative of
`u ↦ ∫ f(x;u) dν(x)` at `θ` is `∫ ∂_θ f(x;θ) dν(x)`. -/
def DerivInterchange (θ : ℝ) : Prop :=
  Integrable (F.densityDeriv θ) F.ν ∧
    HasDerivAt (fun u ↦ ∫ x, F.density u x ∂F.ν) (∫ x, F.densityDeriv θ x ∂F.ν) θ

/-- Second order interchange at `θ`: `∂²_θ f(·;θ)` is `ν`-integrable and the derivative of
`u ↦ ∫ ∂_u f(x;u) dν(x)` at `θ` is `∫ ∂²_θ f(x;θ) dν(x)`. -/
def DerivInterchangeTwo (θ : ℝ) : Prop :=
  Integrable (F.densityDeriv2 θ) F.ν ∧
    HasDerivAt (fun u ↦ ∫ x, F.densityDeriv u x ∂F.ν) (∫ x, F.densityDeriv2 θ x ∂F.ν) θ

/-- Interchange for the mean of a statistic `T` at `θ`: `T ∂_θ f(·;θ)` is `ν`-integrable and the
derivative of `u ↦ ∫ T(x) f(x;u) dν(x)` at `θ` is `∫ T(x) ∂_θ f(x;θ) dν(x)`. -/
def MeanDerivInterchange (T : S → ℝ) (θ : ℝ) : Prop :=
  Integrable (fun x ↦ T x * F.densityDeriv θ x) F.ν ∧
    HasDerivAt (fun u ↦ ∫ x, T x * F.density u x ∂F.ν) (∫ x, T x * F.densityDeriv θ x ∂F.ν) θ

variable {F}

/-- `f(x;θ) s(θ;x) = ∂_θ f(x;θ)` for every `x`, at an interior point `θ` of `Θ`. Where
`f(x;θ) = 0`, `θ` is a local minimum of the nonnegative function `u ↦ f(x;u)`, so the derivative
vanishes (or does not exist, and is then `0` by definition). -/
theorem density_mul_score {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (x : S) :
    F.density θ x * F.score θ x = F.densityDeriv θ x := by
  rcases (F.density_nonneg θ (mem_of_mem_nhds hΘ) x).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, densityDeriv]
    symm
    refine IsLocalMin.deriv_eq_zero ?_
    filter_upwards [hΘ] with u hu
    rw [← h0]
    exact F.density_nonneg u hu x
  · rw [score]
    field_simp

/-- The score is the derivative of the log-likelihood where the density is positive and
differentiable in the parameter. -/
theorem score_eq_deriv_logLik {θ : ℝ} {x : S} (hpos : 0 < F.density θ x)
    (hd : DifferentiableAt ℝ (fun u ↦ F.density u x) θ) :
    F.score θ x = deriv (fun u ↦ F.logLik u x) θ := by
  simp only [score, densityDeriv, logLik]
  rw [(hd.hasDerivAt.log hpos.ne').deriv]

/-- At an interior point of `Θ`, a derivative of `u ↦ ∫ f(x;u) dν(x)` is `0`, since this function
is `1` near the point. -/
theorem hasDerivAt_integral_density_eq_zero {θ D : ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (h : HasDerivAt (fun u ↦ ∫ x, F.density u x ∂F.ν) D θ) : D = 0 := by
  have hc : HasDerivAt (fun u ↦ ∫ x, F.density u x ∂F.ν) 0 θ := by
    refine (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hΘ] with u hu
    exact F.integral_density u hu
  exact h.unique hc

/-- Under the first order interchange at an interior point, `∫ ∂_θ f(x;θ) dν(x) = 0`. -/
theorem integral_densityDeriv_eq_zero {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ) :
    ∫ x, F.densityDeriv θ x ∂F.ν = 0 :=
  hasDerivAt_integral_density_eq_zero hΘ h1.2

/-- Integrability of the score under `P_θ` is integrability of `∂_θ f(·;θ)` under `ν`. -/
theorem integrable_score_iff {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) :
    Integrable (F.score θ) (F.law θ) ↔ Integrable (F.densityDeriv θ) F.ν := by
  rw [integrable_law_iff (mem_of_mem_nhds hΘ)]
  simp_rw [density_mul_score hΘ]

/-- Under the first order interchange at an interior point, the score is `P_θ`-integrable. -/
theorem integrable_score {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ) :
    Integrable (F.score θ) (F.law θ) :=
  (integrable_score_iff hΘ).2 h1.1

/-- **The score has mean zero.** At an interior point `θ` of `Θ` where the first derivative of
`∫ f(x;θ) dν(x) = 1` can be taken under the integral sign, the score is `P_θ`-integrable
(`integrable_score`) and `E_θ[s(θ;X)] = 0`. Proof:
`E_θ[s] = ∫ f s dν = ∫ ∂_θ f dν = ∂_θ ∫ f dν = 0`. -/
theorem integral_score_eq_zero {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ) :
    ∫ x, F.score θ x ∂F.law θ = 0 := by
  rw [integral_law (mem_of_mem_nhds hΘ)]
  simp_rw [density_mul_score hΘ]
  exact integral_densityDeriv_eq_zero hΘ h1

/-- `E_θ[T s(θ;X)] = ∫ T ∂_θ f(·;θ) dν` at an interior point. -/
theorem integral_mul_score {T : S → ℝ} {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) :
    ∫ x, T x * F.score θ x ∂F.law θ = ∫ x, T x * F.densityDeriv θ x ∂F.ν := by
  rw [integral_law (mem_of_mem_nhds hΘ)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only
  rw [← density_mul_score hΘ x]
  ring

/-- `T s(θ;·)` is `P_θ`-integrable if and only if `T ∂_θ f(·;θ)` is `ν`-integrable, at an
interior point. -/
theorem integrable_mul_score_iff {T : S → ℝ} {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) :
    Integrable (fun x ↦ T x * F.score θ x) (F.law θ) ↔
      Integrable (fun x ↦ T x * F.densityDeriv θ x) F.ν := by
  rw [integrable_law_iff (mem_of_mem_nhds hΘ)]
  refine integrable_congr (Eventually.of_forall fun x ↦ ?_)
  simp only
  rw [← density_mul_score hΘ x]
  ring

/-- **The derivative of the mean of a statistic is its cross moment with the score.** If the
derivative of `u ↦ ∫ T f(·;u) dν` can be taken under the integral sign at the interior point `θ`,
then `T s(θ;·)` is `P_θ`-integrable and `∂_θ E_θ[T] = E_θ[T s(θ;X)]`. -/
theorem hasDerivAt_mean {T : S → ℝ} {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (hT : F.MeanDerivInterchange T θ) :
    Integrable (fun x ↦ T x * F.score θ x) (F.law θ) ∧
      HasDerivAt (F.mean T) (∫ x, T x * F.score θ x ∂F.law θ) θ := by
  refine ⟨(integrable_mul_score_iff hΘ).2 hT.1, ?_⟩
  rw [integral_mul_score hΘ]
  refine hT.2.congr_of_eventuallyEq ?_
  filter_upwards [hΘ] with u hu
  rw [mean, integral_law hu]
  simp_rw [mul_comm]

/-! ### Interchange of derivative and integral from integrable envelopes -/

/-- A derivative in a parameter of a family of almost everywhere strongly measurable functions is
almost everywhere strongly measurable at a point where the family is almost everywhere
differentiable: it is the almost everywhere limit of difference quotients with steps
`r / (n + 2)`. -/
theorem aestronglyMeasurable_deriv {μ : Measure S} {G : ℝ → S → ℝ} {θ r : ℝ} (hr : 0 < r)
    (hG : ∀ u ∈ ball θ r, AEStronglyMeasurable (G u) μ)
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun u ↦ G u x) θ) :
    AEStronglyMeasurable (fun x ↦ deriv (fun u ↦ G u x) θ) μ := by
  set t : ℕ → ℝ := fun n ↦ r / ((n : ℝ) + 2) with ht_def
  have ht_pos : ∀ n, 0 < t n := fun n ↦ div_pos hr (by positivity)
  have ht_lt : ∀ n, t n < r := fun n ↦ by
    rw [ht_def, div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have ht_mem : ∀ n, θ + t n ∈ ball θ r := fun n ↦ by
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (ht_pos n)]
    exact ht_lt n
  have ht : Tendsto t atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall ht_pos⟩
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x ↦ (t n)⁻¹ * (G (θ + t n) x - G θ x)) (fun n ↦ ?_) ?_
  · exact ((hG _ (ht_mem n)).sub (hG θ (mem_ball_self hr))).const_mul _
  · filter_upwards [hd] with x hx
    have := hx.hasDerivAt.tendsto_slope_zero_right.comp ht
    simpa [Function.comp_def, smul_eq_mul] using this

/-- **First order interchange from an envelope.** If `u ↦ f(x;u)` is differentiable on a ball
around `θ` contained in `Θ` for `ν`-almost every `x`, and `|∂_u f(x;u)| ≤ b(x)` there with `b`
integrable, then the first order interchange holds at every point of the ball. Proof: dominated
convergence (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). -/
theorem derivInterchange_of_dominated {θ ε : ℝ} (hball : ball θ ε ⊆ F.Θ)
    {b : S → ℝ} (hb : Integrable b F.ν)
    (hdiff : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, DifferentiableAt ℝ (fun v ↦ F.density v x) u)
    (hbound : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, |F.densityDeriv u x| ≤ b x) :
    ∀ u ∈ ball θ ε, F.DerivInterchange u := by
  intro u hu
  have hmeas : AEStronglyMeasurable (F.densityDeriv u) F.ν :=
    aestronglyMeasurable_deriv (G := F.density) one_pos
      (fun v _ ↦ (F.measurable_density v).aestronglyMeasurable)
      (hdiff.mono fun x hx ↦ hx u hu)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (isOpen_ball.mem_nhds hu)
    (Eventually.of_forall fun v ↦ (F.measurable_density v).aestronglyMeasurable)
    (F.integrable_density u (hball hu)) hmeas
    (hbound.mono fun x hx v hv ↦ by rw [Real.norm_eq_abs]; exact hx v hv) hb
    (hdiff.mono fun x hx v hv ↦ (hx v hv).hasDerivAt)

/-- **Second order interchange from envelopes.** With integrable envelopes `b₁` of `|∂_u f|` and
`b₂` of `|∂²_u f|` on a ball around `θ` contained in `Θ`, and almost everywhere differentiability
of `u ↦ f(x;u)` and `u ↦ ∂_u f(x;u)` on that ball, the second order interchange holds at `θ`. -/
theorem derivInterchangeTwo_of_dominated {θ ε : ℝ} (hε : 0 < ε) (hball : ball θ ε ⊆ F.Θ)
    {b₁ b₂ : S → ℝ} (hb₁ : Integrable b₁ F.ν) (hb₂ : Integrable b₂ F.ν)
    (hdiff : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, DifferentiableAt ℝ (fun v ↦ F.density v x) u)
    (hdiff2 : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, DifferentiableAt ℝ (fun v ↦ F.densityDeriv v x) u)
    (hbound₁ : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, |F.densityDeriv u x| ≤ b₁ x)
    (hbound₂ : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, |F.densityDeriv2 u x| ≤ b₂ x) :
    F.DerivInterchangeTwo θ := by
  have h1 := derivInterchange_of_dominated hball hb₁ hdiff hbound₁
  have hmeas1 : ∀ u ∈ ball θ ε, AEStronglyMeasurable (F.densityDeriv u) F.ν :=
    fun u hu ↦ (h1 u hu).1.aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (F.densityDeriv2 θ) F.ν :=
    aestronglyMeasurable_deriv (G := F.densityDeriv) hε hmeas1
      (hdiff2.mono fun x hx ↦ hx θ (mem_ball_self hε))
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds θ hε)
    (eventually_of_mem (ball_mem_nhds θ hε) hmeas1) (h1 θ (mem_ball_self hε)).1 hmeas2
    (hbound₂.mono fun x hx v hv ↦ by rw [Real.norm_eq_abs]; exact hx v hv) hb₂
    (hdiff2.mono fun x hx v hv ↦ (hx v hv).hasDerivAt)

/-- **Interchange for the mean of a statistic from an envelope.** If `T` is measurable and
`P_θ`-integrable, `u ↦ f(x;u)` is differentiable on a ball around `θ` contained in `Θ` for
`ν`-almost every `x`, and `|T(x) ∂_u f(x;u)| ≤ b(x)` there with `b` integrable, then the mean of
`T` can be differentiated under the integral sign at `θ`. -/
theorem meanDerivInterchange_of_dominated {T : S → ℝ} (hTm : Measurable T) {θ ε : ℝ}
    (hε : 0 < ε) (hball : ball θ ε ⊆ F.Θ) {b : S → ℝ} (hb : Integrable b F.ν)
    (hTint : Integrable T (F.law θ))
    (hdiff : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, DifferentiableAt ℝ (fun v ↦ F.density v x) u)
    (hbound : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, |T x * F.densityDeriv u x| ≤ b x) :
    F.MeanDerivInterchange T θ := by
  have hθ : θ ∈ F.Θ := hball (mem_ball_self hε)
  have hint : Integrable (fun x ↦ T x * F.density θ x) F.ν := by
    have := (integrable_law_iff hθ).1 hTint
    simpa [mul_comm] using this
  have hmeas : AEStronglyMeasurable (F.densityDeriv θ) F.ν :=
    aestronglyMeasurable_deriv (G := F.density) one_pos
      (fun v _ ↦ (F.measurable_density v).aestronglyMeasurable)
      (hdiff.mono fun x hx ↦ hx θ (mem_ball_self hε))
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds θ hε)
    (F' := fun u x ↦ T x * F.densityDeriv u x)
    (Eventually.of_forall fun v ↦ (hTm.mul (F.measurable_density v)).aestronglyMeasurable)
    hint (hTm.aestronglyMeasurable.mul hmeas)
    (hbound.mono fun x hx v hv ↦ by rw [Real.norm_eq_abs]; exact hx v hv) hb
    (hdiff.mono fun x hx v hv ↦ (hx v hv).hasDerivAt.const_mul (T x))

/-- **Interchange for the mean of a bounded statistic.** If `T` is measurable with `|T| ≤ C` and
the derivative of the density has an integrable envelope `b` on a ball around `θ` contained in
`Θ` (as in `derivInterchange_of_dominated`), then the mean of `T` can be differentiated under the
integral sign at `θ`: the envelope of `T ∂_u f` is `C b`. -/
theorem meanDerivInterchange_of_bounded {T : S → ℝ} (hTm : Measurable T) {C : ℝ}
    (hTC : ∀ x, |T x| ≤ C) {θ ε : ℝ} (hε : 0 < ε) (hball : ball θ ε ⊆ F.Θ) {b : S → ℝ}
    (hb : Integrable b F.ν)
    (hdiff : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, DifferentiableAt ℝ (fun v ↦ F.density v x) u)
    (hbound : ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, |F.densityDeriv u x| ≤ b x) :
    F.MeanDerivInterchange T θ := by
  have hθ : θ ∈ F.Θ := hball (mem_ball_self hε)
  have := isProbabilityMeasure_law hθ
  have hTint : Integrable T (F.law θ) :=
    Integrable.of_bound hTm.aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hTC x)
  refine meanDerivInterchange_of_dominated hTm hε hball (hb.const_mul C) hTint hdiff ?_
  filter_upwards [hbound] with x hx u hu
  rw [abs_mul]
  exact mul_le_mul (hTC x) (hx u hu) (abs_nonneg _) ((abs_nonneg _).trans (hTC x))

end ParametricFamily

end CausalInference
