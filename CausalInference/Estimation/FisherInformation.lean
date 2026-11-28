/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Score
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Fisher information of a scalar parametric family

The Fisher information `I(θ) = E_θ[s(θ;X)²]` of one observation, its identification with the
variance of the score, the information equality `I(θ) = -E_θ[∂²_θ log f(X;θ)]`, and additivity:
the score of `n` i.i.d. observations has variance `n I(θ)`, and the family of an i.i.d. sample
of size `n` has information `n I(θ)`.

## Main definitions

* `CausalInference.ParametricFamily.fisherInfo`: `I(θ) = E_θ[s(θ;X)²]`.
* `CausalInference.ParametricFamily.IsRegularAt`: a regular point, with conditions that a
  concrete family can check: common support near `θ`, a ball around `θ` inside `Θ` on which the
  density is almost everywhere twice continuously differentiable in the parameter with integrable
  envelopes of its first two derivatives, and a square integrable score.

## Main results

* `CausalInference.ParametricFamily.fisherInfo_eq_variance`: `I(θ) = Var_θ(s)`.
* `CausalInference.ParametricFamily.information_equality`: `I(θ) = -E_θ[∂²_θ ℓ(θ;X)]`, with the
  integrability of `∂²_θ ℓ`.
* `CausalInference.ParametricFamily.IsRegularAt.information_equality`: the same at a regular
  point.
* `CausalInference.ParametricFamily.sum_score_mean_variance_of_isIIDSample`: for i.i.d. observations
  (`CausalInference.IsIIDSample`) with law `P_θ`, `∑_{i < n} s(θ;X_i)` has mean zero and
  variance `n I(θ)`.
* `CausalInference.ParametricFamily.pi_fisherInfo`: the sample family `F.pi n` has information
  `n I(θ)`.

References: E. L. Lehmann and G. Casella (1998), *Theory of Point Estimation*, 2nd edition,
chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace CausalInference

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] (F : ParametricFamily ℝ S)

/-- The Fisher information `I(θ) = E_θ[s(θ;X)²]` of one observation. The theorems assume the
score square integrable, which excludes the value `0` of the integral of a non integrable
function. -/
noncomputable def fisherInfo (θ : ℝ) : ℝ :=
  ∫ x, F.score θ x ^ 2 ∂F.law θ

variable {F}

/-- The Fisher information is the variance of the score, at an interior point where the first
order interchange holds and the score is square integrable. -/
theorem fisherInfo_eq_variance {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hs : MemLp (F.score θ) 2 (F.law θ)) : F.fisherInfo θ = Var[F.score θ; F.law θ] := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hΘ)
  rw [variance_of_integral_eq_zero hs.aemeasurable (integral_score_eq_zero hΘ h1), fisherInfo]

/-- The Fisher information is nonnegative. -/
theorem fisherInfo_nonneg (θ : ℝ) : 0 ≤ F.fisherInfo θ :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-! ### The information equality -/

/-- If `f(x;θ) = 0` and the support does not move near `θ`, then `∂²_θ f(x;θ) = 0`. -/
theorem densityDeriv2_eq_zero_of_support {θ : ℝ} {x : S} (hΘ : F.Θ ∈ 𝓝 θ)
    (hsupp : ∀ᶠ u in 𝓝 θ, ∀ x, 0 < F.density u x ↔ 0 < F.density θ x)
    (h0 : F.density θ x = 0) : F.densityDeriv2 θ x = 0 := by
  have hz : ∀ᶠ u in 𝓝 θ, F.density u x = 0 := by
    filter_upwards [hsupp, hΘ] with u hu huΘ
    have : ¬ 0 < F.density u x := by rw [hu x, h0]; exact lt_irrefl 0
    exact le_antisymm (not_lt.1 this) (F.density_nonneg u huΘ x)
  have hz' : ∀ᶠ u in 𝓝 θ, F.densityDeriv u x = 0 := by
    filter_upwards [eventually_eventually_nhds.2 hz] with u hu
    rw [densityDeriv, Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)) hu, deriv_const]
  rw [densityDeriv2, Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)) hz', deriv_const]

/-- Pointwise form of the information equality: `f ∂²_θ log f = ∂²_θ f - f s²`, the quotient
rule for `∂_θ log f = ∂_θ f / f`, multiplied by `f`. -/
theorem density_mul_hessLogLik {θ : ℝ} {x : S} (hΘ : F.Θ ∈ 𝓝 θ)
    (hsupp : ∀ᶠ u in 𝓝 θ, ∀ x, 0 < F.density u x ↔ 0 < F.density θ x)
    (hd : ∀ᶠ u in 𝓝 θ, DifferentiableAt ℝ (fun v ↦ F.density v x) u)
    (hd2 : DifferentiableAt ℝ (fun u ↦ F.densityDeriv u x) θ) :
    F.density θ x * F.hessLogLik θ x =
      F.densityDeriv2 θ x - F.density θ x * F.score θ x ^ 2 := by
  rcases (F.density_nonneg θ (mem_of_mem_nhds hΘ) x).eq_or_lt with h0 | hpos
  · rw [← h0, densityDeriv2_eq_zero_of_support hΘ hsupp h0.symm]
    ring
  · have hdθ : DifferentiableAt ℝ (fun v ↦ F.density v x) θ := hd.self_of_nhds
    have hposn : ∀ᶠ u in 𝓝 θ, 0 < F.density u x :=
      hdθ.continuousAt.eventually (lt_mem_nhds hpos)
    have heq : (fun u ↦ deriv (fun v ↦ F.logLik v x) u) =ᶠ[𝓝 θ]
        fun u ↦ F.densityDeriv u x / F.density u x := by
      filter_upwards [hposn, hd] with u hu hdu
      rw [← score_eq_deriv_logLik hu hdu, score]
    have hder : HasDerivAt (fun u ↦ F.densityDeriv u x / F.density u x)
        ((F.densityDeriv2 θ x * F.density θ x - F.densityDeriv θ x * F.densityDeriv θ x) /
          F.density θ x ^ 2) θ :=
      hd2.hasDerivAt.div hdθ.hasDerivAt hpos.ne'
    rw [hessLogLik, heq.deriv_eq, hder.deriv, score]
    field_simp

/-- **The information equality.** At an interior point `θ` with common support near `θ`,
almost everywhere differentiability of `u ↦ f(x;u)` near `θ` and of `u ↦ ∂_u f(x;u)` at `θ`,
the first order interchange near `θ`, the second order interchange at `θ` and a square
integrable score: `∂²_θ ℓ(θ;·)` is `P_θ`-integrable and `I(θ) = -E_θ[∂²_θ ℓ(θ;X)]`. Proof:
`f ∂²ℓ = ∂²f - f s²` pointwise, and `∫ ∂²f dν = ∂_θ ∫ ∂_θ f dν = 0` because `∫ ∂_u f dν = 0`
near `θ`. -/
theorem information_equality {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (hsupp : ∀ᶠ u in 𝓝 θ, ∀ x, 0 < F.density u x ↔ 0 < F.density θ x)
    (hdiff : ∀ᵐ x ∂F.ν, (∀ᶠ u in 𝓝 θ, DifferentiableAt ℝ (fun v ↦ F.density v x) u) ∧
      DifferentiableAt ℝ (fun u ↦ F.densityDeriv u x) θ)
    (h1 : ∀ᶠ u in 𝓝 θ, F.DerivInterchange u) (h2 : F.DerivInterchangeTwo θ)
    (hs : MemLp (F.score θ) 2 (F.law θ)) :
    Integrable (F.hessLogLik θ) (F.law θ) ∧
      F.fisherInfo θ = -∫ x, F.hessLogLik θ x ∂F.law θ := by
  have hθ : θ ∈ F.Θ := mem_of_mem_nhds hΘ
  have hzero1 : ∀ᶠ u in 𝓝 θ, ∫ x, F.densityDeriv u x ∂F.ν = 0 := by
    filter_upwards [h1, eventually_mem_nhds_iff.2 hΘ] with u hu huΘ
    exact integral_densityDeriv_eq_zero huΘ hu
  have hzero2 : ∫ x, F.densityDeriv2 θ x ∂F.ν = 0 :=
    h2.2.unique ((hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq hzero1)
  have hsq : Integrable (fun x ↦ F.density θ x * F.score θ x ^ 2) F.ν :=
    (integrable_law_iff hθ).1 hs.integrable_sq
  have hpt : (fun x ↦ F.density θ x * F.hessLogLik θ x) =ᵐ[F.ν]
      fun x ↦ F.densityDeriv2 θ x - F.density θ x * F.score θ x ^ 2 :=
    hdiff.mono fun x hx ↦ density_mul_hessLogLik hΘ hsupp hx.1 hx.2
  refine ⟨(integrable_law_iff hθ).2 ((h2.1.sub hsq).congr hpt.symm), ?_⟩
  rw [integral_law hθ, integral_congr_ae hpt, integral_sub h2.1 hsq, hzero2, fisherInfo,
    integral_law hθ]
  ring

/-! ### Regular points -/

/-- A regular point `θ` of a scalar family, with conditions that a concrete family can check:
the support `{x : f(x;u) > 0}` is the same for all `u` near `θ`; on a ball around `θ` contained
in `Θ`, `u ↦ f(x;u)` is twice continuously differentiable for `ν`-almost every `x`, and
`|∂_u f|`, `|∂²_u f|` have `ν`-integrable envelopes there; the score is square integrable. -/
structure IsRegularAt (F : ParametricFamily ℝ S) (θ : ℝ) : Prop where
  /-- Common support near `θ`. -/
  support : ∀ᶠ u in 𝓝 θ, ∀ x, 0 < F.density u x ↔ 0 < F.density θ x
  /-- A ball inside `Θ` on which the density is almost everywhere `C²` in the parameter, with
  integrable envelopes of its first two derivatives. -/
  smooth_dominated : ∃ ε > 0, ball θ ε ⊆ F.Θ ∧
    (∀ᵐ x ∂F.ν, ContDiffOn ℝ 2 (fun u ↦ F.density u x) (ball θ ε)) ∧
    ∃ b₁ b₂ : S → ℝ, Integrable b₁ F.ν ∧ Integrable b₂ F.ν ∧
      ∀ᵐ x ∂F.ν, ∀ u ∈ ball θ ε, |F.densityDeriv u x| ≤ b₁ x ∧ |F.densityDeriv2 u x| ≤ b₂ x
  /-- The score is square integrable. -/
  memLp_score : MemLp (F.score θ) 2 (F.law θ)

namespace IsRegularAt

variable {θ : ℝ}

/-- A regular point is interior to `Θ`. -/
theorem mem_nhds (h : F.IsRegularAt θ) : F.Θ ∈ 𝓝 θ := by
  obtain ⟨ε, hε, hball, -⟩ := h.smooth_dominated
  exact Filter.mem_of_superset (ball_mem_nhds θ hε) hball

/-- If `u ↦ f(x;u)` is `C²` on a ball, it and its derivative are differentiable on the ball. -/
theorem differentiable_of_contDiffOn {ε : ℝ} {x : S}
    (hx : ContDiffOn ℝ 2 (fun u ↦ F.density u x) (ball θ ε)) :
    (∀ u ∈ ball θ ε, DifferentiableAt ℝ (fun v ↦ F.density v x) u) ∧
      ∀ u ∈ ball θ ε, DifferentiableAt ℝ (fun v ↦ F.densityDeriv v x) u := by
  have h2 : ContDiffOn ℝ (1 + 1) (fun u ↦ F.density u x) (ball θ ε) := hx
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_ball] at h2
  obtain ⟨hd, -, hd1⟩ := h2
  exact ⟨fun u hu ↦ hd.differentiableAt (isOpen_ball.mem_nhds hu),
    fun u hu ↦ (hd1.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hu)⟩

/-- At a regular point the first order interchange holds at every point near `θ`. -/
theorem derivInterchange (h : F.IsRegularAt θ) : ∀ᶠ u in 𝓝 θ, F.DerivInterchange u := by
  obtain ⟨ε, hε, hball, hsm, b₁, b₂, hb₁, hb₂, hbd⟩ := h.smooth_dominated
  exact eventually_of_mem (ball_mem_nhds θ hε) (derivInterchange_of_dominated hball hb₁
    (hsm.mono fun x hx ↦ (differentiable_of_contDiffOn hx).1)
    (hbd.mono fun x hx u hu ↦ (hx u hu).1))

/-- At a regular point the second order interchange holds at `θ`. -/
theorem derivInterchangeTwo (h : F.IsRegularAt θ) : F.DerivInterchangeTwo θ := by
  obtain ⟨ε, hε, hball, hsm, b₁, b₂, hb₁, hb₂, hbd⟩ := h.smooth_dominated
  exact derivInterchangeTwo_of_dominated hε hball hb₁ hb₂
    (hsm.mono fun x hx ↦ (differentiable_of_contDiffOn hx).1)
    (hsm.mono fun x hx ↦ (differentiable_of_contDiffOn hx).2)
    (hbd.mono fun x hx u hu ↦ (hx u hu).1) (hbd.mono fun x hx u hu ↦ (hx u hu).2)

/-- At a regular point, `u ↦ f(x;u)` is differentiable at `θ` for `ν`-almost every `x`. -/
theorem ae_differentiableAt (h : F.IsRegularAt θ) :
    ∀ᵐ x ∂F.ν, DifferentiableAt ℝ (fun u ↦ F.density u x) θ := by
  obtain ⟨ε, hε, -, hsm, -⟩ := h.smooth_dominated
  exact hsm.mono fun x hx ↦ (differentiable_of_contDiffOn hx).1 θ (mem_ball_self hε)

/-- **The score has mean zero at a regular point.** -/
theorem integral_score_eq_zero (h : F.IsRegularAt θ) : ∫ x, F.score θ x ∂F.law θ = 0 :=
  ParametricFamily.integral_score_eq_zero h.mem_nhds h.derivInterchange.self_of_nhds

/-- **The information equality at a regular point**: `I(θ) = Var_θ(s) = -E_θ[∂²_θ ℓ(θ;X)]`,
with `∂²_θ ℓ(θ;·)` integrable. -/
theorem information_equality (h : F.IsRegularAt θ) :
    F.fisherInfo θ = Var[F.score θ; F.law θ] ∧ Integrable (F.hessLogLik θ) (F.law θ) ∧
      F.fisherInfo θ = -∫ x, F.hessLogLik θ x ∂F.law θ := by
  refine ⟨fisherInfo_eq_variance h.mem_nhds h.derivInterchange.self_of_nhds h.memLp_score, ?_⟩
  obtain ⟨ε, hε, -, hsm, -⟩ := h.smooth_dominated
  refine ParametricFamily.information_equality h.mem_nhds h.support ?_ h.derivInterchange
    h.derivInterchangeTwo h.memLp_score
  filter_upwards [hsm] with x hx
  have hd := differentiable_of_contDiffOn hx
  exact ⟨eventually_of_mem (ball_mem_nhds θ hε) hd.1, hd.2 θ (mem_ball_self hε)⟩

end IsRegularAt

/-! ### Additivity of information -/

/-- For independent observations `X i`, each with law `P_θ`, the sum of the scores over a finite
set `t` of indices has mean zero and variance `card t · I(θ)`. -/
theorem sum_score_mean_variance {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → S} {θ : ℝ} (hind : iIndepFun X μ)
    (hlaw : ∀ i, HasLaw (X i) (F.law θ) μ) (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hs : MemLp (F.score θ) 2 (F.law θ)) (t : Finset ι) :
    μ[fun ω ↦ ∑ i ∈ t, F.score θ (X i ω)] = 0 ∧
      Var[fun ω ↦ ∑ i ∈ t, F.score θ (X i ω); μ] = t.card * F.fisherInfo θ := by
  have hX : ∀ i, AEMeasurable (X i) μ := fun i ↦ (hlaw i).aemeasurable
  have hsm : ∀ i, AEStronglyMeasurable (F.score θ) (μ.map (X i)) := fun i ↦ by
    rw [(hlaw i).map_eq]; exact hs.aestronglyMeasurable
  have hY : ∀ i, MemLp (fun ω ↦ F.score θ (X i ω)) 2 μ := fun i ↦
    (memLp_map_measure_iff (hsm i) (hX i)).1 (by rw [(hlaw i).map_eq]; exact hs)
  have := isProbabilityMeasure_law (mem_of_mem_nhds hΘ)
  have hs0 := integral_score_eq_zero hΘ h1
  have hmean : ∀ i, μ[fun ω ↦ F.score θ (X i ω)] = 0 := fun i ↦ by
    rw [← integral_map (hX i) (hsm i), (hlaw i).map_eq, hs0]
  have hvar : ∀ i, Var[fun ω ↦ F.score θ (X i ω); μ] = F.fisherInfo θ := fun i ↦ by
    rw [fisherInfo_eq_variance hΘ h1 hs, ← (hlaw i).map_eq,
      variance_map (hsm i).aemeasurable (hX i)]
    rfl
  have hfun : (fun ω ↦ ∑ i ∈ t, F.score θ (X i ω)) = ∑ i ∈ t, fun ω ↦ F.score θ (X i ω) := by
    ext ω; simp
  refine ⟨?_, ?_⟩
  · rw [integral_finsetSum _ fun i _ ↦ (hY i).integrable one_le_two]
    simp [hmean]
  · rw [hfun, IndepFun.variance_sum (fun i _ ↦ hY i)]
    · simp [hvar]
    · intro i _ j _ hij
      exact (hind.indepFun hij).comp₀ (hX i) (hX j) (hsm i).aemeasurable (hsm j).aemeasurable

/-- **Additivity of information for an i.i.d. sample.** If `O` is an i.i.d. sample
(`CausalInference.IsIIDSample`) whose observations have law `P_θ`, then the sample score
`∑_{i < n} s(θ;O_i)` has mean zero and variance `n I(θ)`. -/
theorem sum_score_mean_variance_of_isIIDSample {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → S} (hO : IsIIDSample O μ) {θ : ℝ}
    (hlaw : μ.map (O 0) = F.law θ) (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hs : MemLp (F.score θ) 2 (F.law θ)) (n : ℕ) :
    μ[fun ω ↦ ∑ i ∈ Finset.range n, F.score θ (O i ω)] = 0 ∧
      Var[fun ω ↦ ∑ i ∈ Finset.range n, F.score θ (O i ω); μ] = n * F.fisherInfo θ := by
  have hl : ∀ i, HasLaw (O i) (F.law θ) μ := fun i ↦
    ⟨hO.aemeasurable i, (hO.ident i).map_eq.trans hlaw⟩
  simpa using ParametricFamily.sum_score_mean_variance hO.indep hl hΘ h1 hs (Finset.range n)

/-! ### The information of the sample family -/

variable [SigmaFinite F.ν]

/-- The score of the sample family is the sum of the scores of the observations, where every
density is positive and differentiable at `θ`. -/
theorem pi_score {n : ℕ} {θ : ℝ} {x : Fin n → S} (hpos : ∀ i, 0 < F.density θ (x i))
    (hd : ∀ i, DifferentiableAt ℝ (fun u ↦ F.density u (x i)) θ) :
    (F.pi n).score θ x = ∑ i, F.score θ (x i) := by
  have hD : (F.pi n).densityDeriv θ x =
      ∑ i, (∏ j ∈ Finset.univ.erase i, F.density θ (x j)) * F.densityDeriv θ (x i) := by
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i u ↦ F.density u (x i))
      (fun i _ ↦ (hd i).hasDerivAt)
    rw [densityDeriv]
    change deriv (fun u ↦ ∏ i, F.density u (x i)) θ = _
    rw [this.deriv]
    simp [smul_eq_mul, densityDeriv]
  rw [score, hD, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hP : (F.pi n).density θ x =
      F.density θ (x i) * ∏ j ∈ Finset.univ.erase i, F.density θ (x j) :=
    (Finset.mul_prod_erase _ (fun j ↦ F.density θ (x j)) (Finset.mem_univ i)).symm
  have hne : ∏ j ∈ Finset.univ.erase i, F.density θ (x j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ ↦ (hpos j).ne'
  rw [hP, score]
  have := (hpos i).ne'
  field_simp

/-- The first order interchange for the sample family, from the first order interchange for one
observation and almost everywhere differentiability at `θ`. By the product rule
`∂_θ L_n = ∑_i (∏_{j ≠ i} f(x_j;θ)) ∂_θ f(x_i;θ)` almost everywhere, and Fubini turns each term
into `(∫ ∂_θ f dν) · 1 = 0`. -/
theorem pi_derivInterchange (n : ℕ) {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hdiff : ∀ᵐ x ∂F.ν, DifferentiableAt ℝ (fun u ↦ F.density u x) θ) :
    (F.pi n).DerivInterchange θ := by
  have hθ := mem_of_mem_nhds hΘ
  have h0 : ∫ x, F.densityDeriv θ x ∂F.ν = 0 := integral_densityDeriv_eq_zero hΘ h1
  set g : Fin n → Fin n → S → ℝ := fun i j ↦ if j = i then F.densityDeriv θ else F.density θ
    with hg
  have hall : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ F.ν), ∀ i,
      DifferentiableAt ℝ (fun u ↦ F.density u (x i)) θ :=
    ae_all_iff.2 fun i ↦
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ F.ν) (i := i)).eventually hdiff
  have hcongr : (F.pi n).densityDeriv θ =ᵐ[Measure.pi fun _ ↦ F.ν]
      fun x ↦ ∑ i, ∏ j, g i j (x j) := by
    filter_upwards [hall] with x hx
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i u ↦ F.density u (x i))
      (fun i _ ↦ (hx i).hasDerivAt)
    rw [densityDeriv]
    change deriv (fun u ↦ ∏ i, F.density u (x i)) θ = _
    rw [this.deriv]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_eq_mul, ← Finset.mul_prod_erase _ (fun j ↦ g i j (x j)) (Finset.mem_univ i),
      mul_comm]
    have hgi : g i i (x i) = F.densityDeriv θ (x i) := by simp [hg]
    rw [hgi]
    congr 1
    exact Finset.prod_congr rfl fun j hj ↦ by simp [hg, Finset.ne_of_mem_erase hj]
  have hgi : ∀ i j, Integrable (g i j) F.ν := fun i j ↦ by
    simp only [hg]
    split_ifs
    · exact h1.1
    · exact F.integrable_density θ hθ
  have hint : Integrable ((F.pi n).densityDeriv θ) (F.pi n).ν :=
    (integrable_finsetSum _ fun i _ ↦ Integrable.fintype_prod (hgi i)).congr hcongr.symm
  have hval : ∫ x, (F.pi n).densityDeriv θ x ∂(F.pi n).ν = 0 := by
    change ∫ x, (F.pi n).densityDeriv θ x ∂(Measure.pi fun _ ↦ F.ν) = 0
    rw [integral_congr_ae hcongr, integral_finsetSum _ fun i _ ↦
      Integrable.fintype_prod (hgi i)]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_fintype_prod_eq_prod (f := g i)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hg, h0])
  refine ⟨hint, ?_⟩
  rw [hval]
  refine (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [hΘ] with u hu
  exact (F.pi n).integral_density u hu

/-- **Information of the sample family.** If one observation satisfies the first order
interchange at the interior point `θ`, `u ↦ f(x;u)` is differentiable at `θ` for `ν`-almost every
`x`, and the score is square integrable, then the score of `F.pi n` is square integrable and
its Fisher information is `n I(θ)`. -/
theorem pi_fisherInfo (n : ℕ) {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hdiff : ∀ᵐ x ∂F.ν, DifferentiableAt ℝ (fun u ↦ F.density u x) θ)
    (hs : MemLp (F.score θ) 2 (F.law θ)) :
    MemLp ((F.pi n).score θ) 2 ((F.pi n).law θ) ∧ (F.pi n).fisherInfo θ = n * F.fisherInfo θ := by
  have hθ := mem_of_mem_nhds hΘ
  have := isProbabilityMeasure_law hθ
  have hlawn := pi_law (F := F) n hθ
  have hgood : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ F.law θ), ∀ i,
      0 < F.density θ (x i) ∧ DifferentiableAt ℝ (fun u ↦ F.density u (x i)) θ :=
    ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ F.law θ)
      (i := i)).eventually (ae_law_pos.and (ae_law_of_ae hdiff))
  have hscore : (F.pi n).score θ =ᵐ[Measure.pi fun _ ↦ F.law θ]
      fun x ↦ ∑ i, F.score θ (x i) := by
    filter_upwards [hgood] with x hx
    exact pi_score (fun i ↦ (hx i).1) (fun i ↦ (hx i).2)
  have hlaw : ∀ i, HasLaw (fun x : Fin n → S ↦ x i) (F.law θ) (Measure.pi fun _ ↦ F.law θ) :=
    fun i ↦ ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hind : iIndepFun (fun i (x : Fin n → S) ↦ x i) (Measure.pi fun _ ↦ F.law θ) :=
    iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  obtain ⟨hm0, hvar⟩ := sum_score_mean_variance hind hlaw hΘ h1 hs Finset.univ
  have hY : ∀ i, MemLp (fun x : Fin n → S ↦ F.score θ (x i)) 2
      (Measure.pi fun _ ↦ F.law θ) :=
    fun i ↦ hs.comp_measurePreserving (measurePreserving_eval _ i)
  have hsum : MemLp (fun x : Fin n → S ↦ ∑ i, F.score θ (x i)) 2
      (Measure.pi fun _ ↦ F.law θ) := memLp_finsetSum _ fun i _ ↦ hY i
  rw [hlawn]
  refine ⟨hsum.ae_eq hscore.symm, ?_⟩
  rw [fisherInfo, hlawn, integral_congr_ae (g := fun x ↦ (∑ i, F.score θ (x i)) ^ 2)
      (hscore.mono fun x hx ↦ by simp only [hx]),
    ← variance_of_integral_eq_zero hsum.aemeasurable hm0, hvar, Finset.card_univ,
    Fintype.card_fin]

end ParametricFamily

end CausalInference
