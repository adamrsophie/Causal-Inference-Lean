/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.FisherInformation
public import Mathlib.Probability.Moments.Covariance

/-!
# The Cramér-Rao bound for a scalar parameter

For a statistic `T` with finite variance whose mean `g(θ) = E_θ[T]` can be differentiated under
the integral sign, `g'(θ)² / I(θ) ≤ Var_θ(T)`, with equality if and only if `T - g(θ)` is
`P_θ`-almost surely a constant multiple of the score. The proof is the Cauchy-Schwarz inequality
for `Cov_θ(T, s) = g'(θ)`, in the form `Var(T - c s) ≥ 0` with `c = g'(θ) / I(θ)`.

## Main definitions

* `CausalInference.ParametricFamily.IsEfficient`: an unbiased estimator of `g(θ)` with finite
  variance that attains the bound at every `θ ∈ Θ`, where the information is positive.

## Main results

* `CausalInference.cramer_rao_core`: the Cauchy-Schwarz step on a probability space, with the
  equality case.
* `CausalInference.ParametricFamily.cramer_rao`: the bound and its equality case;
  `cramer_rao_of_isUnbiased`, `cramer_rao_unbiased` (`1 / I(θ)`), `cramer_rao_biased`
  (`(1 + b'(θ))² / I(θ)`).
* `CausalInference.ParametricFamily.IsRegularAt.cramer_rao_of_bounded`: at a regular point, for a
  bounded measurable statistic, with no interchange hypothesis left.
* `CausalInference.ParametricFamily.cramer_rao_pi` and `cramer_rao_of_isIIDSample`: the bound
  `g'(θ)² / (n I(θ))` for a statistic of an i.i.d. sample of size `n`.
* `CausalInference.ParametricFamily.isEfficient_iff`: an unbiased estimator is efficient if and
  only if `T - g(θ)` is almost surely a multiple of the score at every `θ`.

References: C. R. Rao (1945), *Information and the accuracy attainable in the estimation of
statistical parameters*, Bulletin of the Calcutta Mathematical Society; H. Cramér (1946),
*Mathematical Methods of Statistics*; E. L. Lehmann and G. Casella (1998), *Theory of Point
Estimation*, 2nd edition, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace CausalInference

section Core

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {T s : Ω → ℝ}

/-- The variance of `T - c s` for a mean zero `s`: `Var(T - c s) = Var T - 2 c E[T s] + c² E[s²]`
(bilinearity of covariance). -/
theorem variance_sub_const_mul_of_integral_eq_zero (hT : MemLp T 2 μ) (hs : MemLp s 2 μ)
    (hs0 : μ[s] = 0) (c : ℝ) :
    Var[fun ω ↦ T ω - c * s ω; μ] = Var[T; μ] - 2 * c * μ[T * s] + c ^ 2 * μ[s ^ 2] := by
  have hcs : MemLp (fun ω ↦ c * s ω) 2 μ := hs.const_mul c
  rw [variance_fun_sub hT hcs, covariance_const_mul_right, variance_const_mul,
    covariance_eq_sub hT hs, hs0, variance_eq_sub hs, hs0]
  ring

/-- **The Cramér-Rao inequality on a probability space.** If `s` is square integrable with mean
zero and `E[s²] > 0`, and `T` is square integrable, then `E[T s]² / E[s²] ≤ Var T`, with
equality if and only if `T - E T` is almost surely a constant multiple of `s`. Proof: the
residual `T - (E[T s] / E[s²]) s` has variance `Var T - E[T s]² / E[s²] ≥ 0`, which vanishes
exactly when the residual is almost surely constant. -/
theorem cramer_rao_core (hT : MemLp T 2 μ) (hs : MemLp s 2 μ) (hs0 : μ[s] = 0)
    (hI : 0 < μ[s ^ 2]) :
    μ[T * s] ^ 2 / μ[s ^ 2] ≤ Var[T; μ] ∧
      (Var[T; μ] = μ[T * s] ^ 2 / μ[s ^ 2] ↔ ∃ a : ℝ, ∀ᵐ ω ∂μ, T ω - μ[T] = a * s ω) := by
  set d := μ[T * s]
  set I := μ[s ^ 2]
  have hres := variance_sub_const_mul_of_integral_eq_zero hT hs hs0 (d / I)
  have key : Var[fun ω ↦ T ω - d / I * s ω; μ] = Var[T; μ] - d ^ 2 / I := by
    rw [hres]; field_simp; ring
  have hnn := variance_nonneg (fun ω ↦ T ω - d / I * s ω) μ
  refine ⟨by linarith, fun h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · refine ⟨d / I, ?_⟩
    have h0 : Var[fun ω ↦ T ω - d / I * s ω; μ] = 0 := by rw [key, h, sub_self]
    have hm : MemLp (fun ω ↦ T ω - d / I * s ω) 2 μ := hT.sub (hs.const_mul _)
    have hmean : μ[fun ω ↦ T ω - d / I * s ω] = μ[T] := by
      rw [integral_sub (hT.integrable one_le_two) ((hs.integrable one_le_two).const_mul _),
        integral_const_mul, hs0, mul_zero, sub_zero]
    filter_upwards [ae_eq_integral_of_variance_eq_zero hm h0] with ω hω
    rw [hmean] at hω
    linarith
  · have hTs : T =ᵐ[μ] fun ω ↦ a * s ω + μ[T] := by
      filter_upwards [ha] with ω hω
      linarith
    have hvar : Var[T; μ] = a ^ 2 * I := by
      rw [variance_congr hTs, variance_add_const ((hs.const_mul a).aestronglyMeasurable),
        variance_const_mul, variance_eq_sub hs, hs0]
      ring
    have hd : d = a * I := by
      have : d = μ[fun ω ↦ a * (s ω * s ω) + μ[T] * s ω] := by
        refine integral_congr_ae ?_
        filter_upwards [hTs] with ω hω
        simp only [Pi.mul_apply, hω]
        ring
      rw [this, integral_add (f := fun ω ↦ a * (s ω * s ω)) (g := fun ω ↦ μ[T] * s ω)
        ((hs.integrable_mul hs).const_mul _) ((hs.integrable one_le_two).const_mul _),
        integral_const_mul, integral_const_mul, hs0]
      simp [I, pow_two]
    rw [hvar, hd]
    field_simp

end Core

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S}

/-- **The Cramér-Rao bound.** Let `θ` be an interior point of `Θ` where the first order
interchange holds, the score is square integrable with positive information, and let `T` have
finite variance and a mean `g(θ) = E_θ[T]` that can be differentiated under the integral sign.
Then `g'(θ)² / I(θ) ≤ Var_θ(T)`, with equality if and only if `T - g(θ)` is `P_θ`-almost surely
a constant multiple of the score. -/
theorem cramer_rao {T : S → ℝ} {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hT : F.MeanDerivInterchange T θ) (hT2 : MemLp T 2 (F.law θ))
    (hs : MemLp (F.score θ) 2 (F.law θ)) (hI : 0 < F.fisherInfo θ) :
    deriv (F.mean T) θ ^ 2 / F.fisherInfo θ ≤ Var[T; F.law θ] ∧
      (Var[T; F.law θ] = deriv (F.mean T) θ ^ 2 / F.fisherInfo θ ↔
        ∃ a : ℝ, ∀ᵐ x ∂F.law θ, T x - F.mean T θ = a * F.score θ x) := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hΘ)
  have hc := cramer_rao_core hT2 hs (integral_score_eq_zero hΘ h1) hI
  rw [(hasDerivAt_mean hΘ hT).2.deriv]
  exact hc

/-- The derivative of the mean of an unbiased estimator of `g(θ)` is `g'(θ)` at an interior
point. -/
theorem deriv_mean_of_isUnbiased {T : S → ℝ} {g : ℝ → ℝ} {g' θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (hu : F.IsUnbiased T g) (hg : HasDerivAt g g' θ) : deriv (F.mean T) θ = g' := by
  refine (hg.congr_of_eventuallyEq ?_).deriv
  filter_upwards [hΘ] with u hu'
  exact (hu u hu').2

/-- **Cramér-Rao bound for an unbiased estimator of `g(θ)`**: `g'(θ)² / I(θ) ≤ Var_θ(T)`. -/
theorem cramer_rao_of_isUnbiased {T : S → ℝ} {g : ℝ → ℝ} {g' θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (hu : F.IsUnbiased T g) (hg : HasDerivAt g g' θ) (h1 : F.DerivInterchange θ)
    (hT : F.MeanDerivInterchange T θ) (hT2 : MemLp T 2 (F.law θ))
    (hs : MemLp (F.score θ) 2 (F.law θ)) (hI : 0 < F.fisherInfo θ) :
    g' ^ 2 / F.fisherInfo θ ≤ Var[T; F.law θ] := by
  simpa [deriv_mean_of_isUnbiased hΘ hu hg] using (cramer_rao hΘ h1 hT hT2 hs hI).1

/-- **Cramér-Rao bound for an unbiased estimator of `θ`**: `1 / I(θ) ≤ Var_θ(T)`. -/
theorem cramer_rao_unbiased {T : S → ℝ} {θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ) (hu : F.IsUnbiased T id)
    (h1 : F.DerivInterchange θ) (hT : F.MeanDerivInterchange T θ) (hT2 : MemLp T 2 (F.law θ))
    (hs : MemLp (F.score θ) 2 (F.law θ)) (hI : 0 < F.fisherInfo θ) :
    1 / F.fisherInfo θ ≤ Var[T; F.law θ] := by
  simpa using cramer_rao_of_isUnbiased hΘ hu (hasDerivAt_id θ) h1 hT hT2 hs hI

/-- **Cramér-Rao bound for a biased estimator of `θ`.** If `E_u[T] = u + b(u)` on `Θ` and the
bias `b` has derivative `b'` at `θ`, then `(1 + b')² / I(θ) ≤ Var_θ(T)`. -/
theorem cramer_rao_biased {T : S → ℝ} {b : ℝ → ℝ} {b' θ : ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (hu : F.IsUnbiased T fun u ↦ u + b u) (hb : HasDerivAt b b' θ) (h1 : F.DerivInterchange θ)
    (hT : F.MeanDerivInterchange T θ) (hT2 : MemLp T 2 (F.law θ))
    (hs : MemLp (F.score θ) 2 (F.law θ)) (hI : 0 < F.fisherInfo θ) :
    (1 + b') ^ 2 / F.fisherInfo θ ≤ Var[T; F.law θ] :=
  cramer_rao_of_isUnbiased hΘ hu ((hasDerivAt_id θ).add hb) h1 hT hT2 hs hI

/-- **The Cramér-Rao bound at a regular point**, for a statistic with finite variance whose mean
can be differentiated under the integral sign, with the equality case. -/
theorem IsRegularAt.cramer_rao {θ : ℝ} (h : F.IsRegularAt θ) (hI : 0 < F.fisherInfo θ)
    {T : S → ℝ} (hT : F.MeanDerivInterchange T θ) (hT2 : MemLp T 2 (F.law θ)) :
    deriv (F.mean T) θ ^ 2 / F.fisherInfo θ ≤ Var[T; F.law θ] ∧
      (Var[T; F.law θ] = deriv (F.mean T) θ ^ 2 / F.fisherInfo θ ↔
        ∃ a : ℝ, ∀ᵐ x ∂F.law θ, T x - F.mean T θ = a * F.score θ x) :=
  ParametricFamily.cramer_rao h.mem_nhds h.derivInterchange.self_of_nhds hT hT2 h.memLp_score hI

/-- The mean of a bounded measurable statistic can be differentiated under the integral sign at
a regular point. -/
theorem IsRegularAt.meanDerivInterchange_of_bounded {θ : ℝ} (h : F.IsRegularAt θ)
    {T : S → ℝ} (hTm : Measurable T) {C : ℝ} (hTC : ∀ x, |T x| ≤ C) :
    F.MeanDerivInterchange T θ := by
  obtain ⟨ε, hε, hball, hsm, b₁, b₂, hb₁, hb₂, hbd⟩ := h.smooth_dominated
  exact ParametricFamily.meanDerivInterchange_of_bounded hTm hTC hε hball hb₁
    (hsm.mono fun x hx ↦ (IsRegularAt.differentiable_of_contDiffOn hx).1)
    (hbd.mono fun x hx u hu ↦ (hx u hu).1)

/-- **The Cramér-Rao bound for a bounded statistic at a regular point**, with no interchange
hypothesis: for measurable `T` with `|T| ≤ C`, `g'(θ)² / I(θ) ≤ Var_θ(T)`, where
`g(θ) = E_θ[T]`, with the equality case. -/
theorem IsRegularAt.cramer_rao_of_bounded {θ : ℝ} (h : F.IsRegularAt θ)
    (hI : 0 < F.fisherInfo θ) {T : S → ℝ} (hTm : Measurable T) {C : ℝ} (hTC : ∀ x, |T x| ≤ C) :
    deriv (F.mean T) θ ^ 2 / F.fisherInfo θ ≤ Var[T; F.law θ] ∧
      (Var[T; F.law θ] = deriv (F.mean T) θ ^ 2 / F.fisherInfo θ ↔
        ∃ a : ℝ, ∀ᵐ x ∂F.law θ, T x - F.mean T θ = a * F.score θ x) := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds h.mem_nhds)
  exact h.cramer_rao hI (h.meanDerivInterchange_of_bounded hTm hTC)
    (MemLp.of_bound hTm.aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hTC x))

/-! ### The bound for an i.i.d. sample of size `n` -/

section Sample

variable [SigmaFinite F.ν]

/-- **The Cramér-Rao bound for the sample family.** Let `T` be a statistic of a sample of size
`n ≥ 1` with finite variance under the product law, whose mean can be differentiated under the
integral sign against the likelihood. If one observation satisfies the first order interchange
at the interior point `θ`, `u ↦ f(x;u)` is differentiable at `θ` for `ν`-almost every `x`, and
the score is square integrable with `I(θ) > 0`, then `g'(θ)² / (n I(θ)) ≤ Var_θ(T)`. -/
theorem cramer_rao_pi {n : ℕ} (hn : 0 < n) {T : (Fin n → S) → ℝ} {θ : ℝ}
    (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hdiff : ∀ᵐ x ∂F.ν, DifferentiableAt ℝ (fun u ↦ F.density u x) θ)
    (hT : (F.pi n).MeanDerivInterchange T θ) (hT2 : MemLp T 2 (Measure.pi fun _ ↦ F.law θ))
    (hs : MemLp (F.score θ) 2 (F.law θ)) (hI : 0 < F.fisherInfo θ) :
    deriv ((F.pi n).mean T) θ ^ 2 / (n * F.fisherInfo θ) ≤
      Var[T; Measure.pi fun _ ↦ F.law θ] := by
  have hlawn := pi_law (F := F) n (mem_of_mem_nhds hΘ)
  obtain ⟨hsn, hIn⟩ := pi_fisherInfo n hΘ h1 hdiff hs
  have hpos : 0 < (F.pi n).fisherInfo θ := by
    rw [hIn]; exact mul_pos (Nat.cast_pos.2 hn) hI
  have := (cramer_rao (F := F.pi n) hΘ (pi_derivInterchange n hΘ h1 hdiff) hT
    (by rw [hlawn]; exact hT2) hsn hpos).1
  rwa [hIn, hlawn] at this

/-- **The Cramér-Rao bound for an i.i.d. sample.** Let `O` be an i.i.d. sample
(`CausalInference.IsIIDSample`) whose observations have law `P_θ`, and `T` a statistic of the
first `n ≥ 1` observations, under the hypotheses of `cramer_rao_pi`. Then
`g'(θ)² / (n I(θ)) ≤ Var(T(O_0, …, O_{n-1}))`, where `g(u)` is the mean of `T` under `n`
i.i.d. observations with law `P_u`. -/
theorem cramer_rao_of_isIIDSample {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → S} (hO : IsIIDSample O μ) {θ : ℝ}
    (hlaw : μ.map (O 0) = F.law θ) {n : ℕ} (hn : 0 < n) {T : (Fin n → S) → ℝ}
    (hΘ : F.Θ ∈ 𝓝 θ) (h1 : F.DerivInterchange θ)
    (hdiff : ∀ᵐ x ∂F.ν, DifferentiableAt ℝ (fun u ↦ F.density u x) θ)
    (hT : (F.pi n).MeanDerivInterchange T θ) (hT2 : MemLp T 2 (Measure.pi fun _ ↦ F.law θ))
    (hs : MemLp (F.score θ) 2 (F.law θ)) (hI : 0 < F.fisherInfo θ) :
    deriv ((F.pi n).mean T) θ ^ 2 / (n * F.fisherInfo θ) ≤
      Var[fun ω ↦ T (fun i ↦ O i ω); μ] := by
  have hY : AEMeasurable (fun ω (i : Fin n) ↦ O i ω) μ :=
    AEMeasurable.of_eval fun i ↦ hO.aemeasurable i
  have hmap : μ.map (fun ω (i : Fin n) ↦ O i ω) = Measure.pi fun _ ↦ F.law θ := by
    rw [hO.map_fin_eq_pi n, hlaw]
  have hvar : Var[fun ω ↦ T (fun i ↦ O i ω); μ] = Var[T; Measure.pi fun _ ↦ F.law θ] := by
    rw [← hmap, variance_map (hmap ▸ hT2.aestronglyMeasurable.aemeasurable) hY]
    rfl
  rw [hvar]
  exact cramer_rao_pi hn hΘ h1 hdiff hT hT2 hs hI

end Sample

/-! ### Efficiency -/

variable (F) in
/-- **Efficiency.** `T` is an efficient estimator of `g(θ)` if it is unbiased for `g`, and at
every `θ ∈ Θ` it has finite variance, the information is positive, and the variance equals the
bound `g'(θ)² / I(θ)`. -/
def IsEfficient (T : S → ℝ) (g : ℝ → ℝ) : Prop :=
  F.IsUnbiased T g ∧ ∀ θ ∈ F.Θ, MemLp T 2 (F.law θ) ∧ 0 < F.fisherInfo θ ∧
    Var[T; F.law θ] = deriv g θ ^ 2 / F.fisherInfo θ

/-- **Characterization of efficiency.** On an open parameter set where, at every point, the first
order interchange holds, the score is square integrable with positive information, and `T` has
finite variance with a mean that can be differentiated under the integral sign, an unbiased
estimator of `g(θ)` is efficient if and only if at every `θ`, `T - g(θ)` is `P_θ`-almost surely a
constant multiple of the score. -/
theorem isEfficient_iff {T : S → ℝ} {g : ℝ → ℝ} (hΘ : IsOpen F.Θ) (hu : F.IsUnbiased T g)
    (h1 : ∀ θ ∈ F.Θ, F.DerivInterchange θ) (hT : ∀ θ ∈ F.Θ, F.MeanDerivInterchange T θ)
    (hT2 : ∀ θ ∈ F.Θ, MemLp T 2 (F.law θ)) (hs : ∀ θ ∈ F.Θ, MemLp (F.score θ) 2 (F.law θ))
    (hI : ∀ θ ∈ F.Θ, 0 < F.fisherInfo θ) :
    F.IsEfficient T g ↔
      ∀ θ ∈ F.Θ, ∃ a : ℝ, ∀ᵐ x ∂F.law θ, T x - g θ = a * F.score θ x := by
  have key : ∀ θ ∈ F.Θ, (Var[T; F.law θ] = deriv g θ ^ 2 / F.fisherInfo θ ↔
      ∃ a : ℝ, ∀ᵐ x ∂F.law θ, T x - g θ = a * F.score θ x) := fun θ hθ ↦ by
    have hn := hΘ.mem_nhds hθ
    have hmean : F.mean T =ᶠ[𝓝 θ] g := by
      filter_upwards [hn] with u hu'
      exact (hu u hu').2
    have := (cramer_rao hn (h1 θ hθ) (hT θ hθ) (hT2 θ hθ) (hs θ hθ) (hI θ hθ)).2
    rwa [hmean.deriv_eq, (hu θ hθ).2] at this
  exact ⟨fun h θ hθ ↦ (key θ hθ).1 (h.2 θ hθ).2.2,
    fun h ↦ ⟨hu, fun θ hθ ↦ ⟨hT2 θ hθ, hI θ hθ, (key θ hθ).2 (h θ hθ)⟩⟩⟩

end ParametricFamily

end CausalInference
