/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LineSubmodel
public import CausalInference.Estimation.HajekConvolution
public import CausalInference.Estimation.GaussianLinearImage
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The Hájek convolution bound, vector parameter

An estimator sequence `T_n` of `θ ∈ ℝ^p` is regular at `θ₀` with limit law `L` when, for every
local parameter `h ∈ ℝ^p`, under the product law of `θ_n = θ₀ + h/√n` the law of
`√n (T_n - θ_n)` converges weakly to `L`. An estimator `T_n` of a real functional `ψ(θ)` is
regular when the law of `√n (T_n - ψ(θ_n))` converges to a fixed `L`. The bounds reduce to the
scalar bound `CausalInference.ParametricFamily.hajek_convolution_bound` along one dimensional
submodels (`CausalInference.ParametricFamily.line`): for a functional with gradient `g` at `θ₀`,
the statistic `(T_n - ψ(θ₀)) / (gᵀ I⁻¹ g)` is regular in the submodel through `θ₀` in the
direction `I⁻¹ g`, whose information is `gᵀ I⁻¹ g`.

## Main definitions

* `CausalInference.ParametricFamily.IsHajekRegularVec F T θ₀ L`: regularity of an estimator of
  the vector parameter, with limit law `L` on `EuclideanSpace ℝ (Fin p)`.
* `CausalInference.ParametricFamily.IsHajekRegularFunctional F T ψ θ₀ L`: regularity of an
  estimator of a real functional `ψ`.

## Main results

* `CausalInference.tendsto_integral_iff_tendsto_charFun`: Lévy's continuity theorem for a
  sequence of measures that are probability measures for all large indices, and
  `CausalInference.tendsto_integral_of_forall_inner` (the Cramér-Wold device) and
  `CausalInference.tendsto_integral_add_of_tendsto` (a vanishing deterministic shift) in the same
  setting.
* `CausalInference.ParametricFamily.IsHajekRegularFunctional.isHajekRegular_line`: a regular
  estimator of a functional gives a regular estimator in every line along which the functional
  has a nonzero derivative.
* `CausalInference.ParametricFamily.hajek_convolution_bound_functional`: for a regular
  estimator of `ψ` with limit `N(0, W)`, `∇ψᵀ I(θ₀)⁻¹ ∇ψ ≤ W`.
* `CausalInference.ParametricFamily.hajek_convolution_bound_vec`: for a regular estimator of `θ`
  with limit `N(0, V)`, `V - I(θ₀)⁻¹` is positive semidefinite.

The equality case, asymptotically linear estimators and the maximum likelihood estimator are in
`CausalInference.Estimation.HajekRegularLinearVector`.

The hypotheses on the family are those of the vector theory (`IsRegularAtVec`,
`IsScoreRegularVec`, positive definite information) and the measurability of the score and of
the second derivatives of the log density along the line used (`LineMeasurable`), automatic on
a discrete sample space.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; A. W. van der
Vaart (1998), *Asymptotic Statistics*, chapter 8; P. J. Bickel, C. A. J. Klaassen, Y. Ritov and
J. A. Wellner (1993), *Efficient and Adaptive Estimation for Semiparametric Models*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix Complex
open scoped Topology ENNReal NNReal BoundedContinuousFunction RealInnerProductSpace

namespace CausalInference

/-! ### Weak convergence of measures that are eventually probability measures -/

section WeakConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Lévy's continuity theorem for measures that are eventually probability measures.** If
`ν n` is a probability measure for all large `n` and `L` is a probability measure, then
`∫ f dν n → ∫ f dL` for every bounded continuous `f` if and only if the characteristic functions
converge pointwise. -/
theorem tendsto_integral_iff_tendsto_charFun {ν : ℕ → Measure E}
    (hν : ∀ᶠ n in atTop, IsProbabilityMeasure (ν n)) {L : Measure E} [IsProbabilityMeasure L] :
    (∀ f : E →ᵇ ℝ, Tendsto (fun n ↦ ∫ x, f x ∂ν n) atTop (𝓝 (∫ x, f x ∂L))) ↔
      ∀ t, Tendsto (fun n ↦ charFun (ν n) t) atTop (𝓝 (charFun L t)) := by
  classical
  let μ' : ℕ → ProbabilityMeasure E := fun n ↦
    if h : IsProbabilityMeasure (ν n) then ⟨ν n, h⟩ else ⟨L, inferInstance⟩
  have hμ' : ∀ᶠ n in atTop, (μ' n : Measure E) = ν n := hν.mono fun n hn ↦ by simp [μ', hn]
  let L' : ProbabilityMeasure E := ⟨L, inferInstance⟩
  have h1 : (∀ f : E →ᵇ ℝ, Tendsto (fun n ↦ ∫ x, f x ∂ν n) atTop (𝓝 (∫ x, f x ∂L))) ↔
      Tendsto μ' atTop (𝓝 L') := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    refine forall_congr' fun f ↦ tendsto_congr' ?_
    filter_upwards [hμ'] with n hn
    rw [hn]
  have h2 : (∀ t, Tendsto (fun n ↦ charFun (ν n) t) atTop (𝓝 (charFun L t))) ↔
      ∀ t, Tendsto (fun n ↦ charFun (μ' n : Measure E) t) atTop
        (𝓝 (charFun (L' : Measure E) t)) := by
    refine forall_congr' fun t ↦ tendsto_congr' ?_
    filter_upwards [hμ'] with n hn
    rw [hn]
  rw [h1, h2, ProbabilityMeasure.tendsto_iff_tendsto_charFun]

/-- **The Cramér-Wold device for measures that are eventually probability measures.** If for
every direction `t` and every bounded continuous `g` on `ℝ`, `∫ g(⟪x, t⟫) dν n → ∫ g(⟪x, t⟫) dL`,
then `∫ f dν n → ∫ f dL` for every bounded continuous `f` on `E`. -/
theorem tendsto_integral_of_forall_inner {ν : ℕ → Measure E}
    (hν : ∀ᶠ n in atTop, IsProbabilityMeasure (ν n)) {L : Measure E} [IsProbabilityMeasure L]
    (h : ∀ t : E, ∀ g : ℝ →ᵇ ℝ,
      Tendsto (fun n ↦ ∫ x, g ⟪x, t⟫ ∂ν n) atTop (𝓝 (∫ x, g ⟪x, t⟫ ∂L))) (f : E →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂ν n) atTop (𝓝 (∫ x, f x ∂L)) := by
  refine (tendsto_integral_iff_tendsto_charFun hν).2 (fun t ↦ ?_) f
  have hc : Continuous fun x : E ↦ ⟪x, t⟫ := continuous_id.inner continuous_const
  have hmap : ∀ μ : Measure E, charFun μ t = charFun (μ.map fun x ↦ ⟪x, t⟫) (1 : ℝ) := by
    intro μ
    have := charFun_map_eq_charFun_map_inner_one (μ := μ) (Y := id) aemeasurable_id t
    simpa using this
  have hν' : ∀ᶠ n in atTop, IsProbabilityMeasure ((ν n).map fun x ↦ ⟪x, t⟫) :=
    hν.mono fun n hn ↦ by infer_instance
  simp_rw [hmap]
  refine (tendsto_integral_iff_tendsto_charFun hν').1 (fun g ↦ ?_) 1
  rw [integral_map hc.aemeasurable g.continuous.aestronglyMeasurable]
  refine (h t g).congr fun n ↦ ?_
  rw [integral_map hc.aemeasurable g.continuous.aestronglyMeasurable]

/-- **A vanishing deterministic shift does not change a weak limit.** If `ν n` is eventually a
probability measure, `∫ f dν n → ∫ f dL` for every bounded continuous `f` and `a n → 0`, then
`∫ f(x + a n) dν n → ∫ f dL`. -/
theorem tendsto_integral_add_of_tendsto {ν : ℕ → Measure E}
    (hν : ∀ᶠ n in atTop, IsProbabilityMeasure (ν n)) {L : Measure E} [IsProbabilityMeasure L]
    (h : ∀ f : E →ᵇ ℝ, Tendsto (fun n ↦ ∫ x, f x ∂ν n) atTop (𝓝 (∫ x, f x ∂L)))
    {a : ℕ → E} (ha : Tendsto a atTop (𝓝 0)) (f : E →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f (x + a n) ∂ν n) atTop (𝓝 (∫ x, f x ∂L)) := by
  have hν' : ∀ᶠ n in atTop, IsProbabilityMeasure ((ν n).map fun x ↦ x + a n) :=
    hν.mono fun n hn ↦ by infer_instance
  have hc := (tendsto_integral_iff_tendsto_charFun hν).1 h
  have key := (tendsto_integral_iff_tendsto_charFun hν' (L := L)).2 (fun t ↦ ?_) f
  · refine key.congr fun n ↦ ?_
    rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
  · simp_rw [charFun_map_add_const]
    have he : Tendsto (fun n ↦ cexp (⟪a n, t⟫ * I)) atTop (𝓝 1) := by
      have hi : Continuous fun x : E ↦ ⟪x, t⟫ := continuous_id.inner continuous_const
      have h1 : Tendsto (fun n ↦ ⟪a n, t⟫) atTop (𝓝 0) := by
        have := (hi.tendsto (0 : E)).comp ha
        rw [inner_zero_left] at this
        exact this
      have h0 : Tendsto (fun n ↦ (⟪a n, t⟫ : ℂ) * I) atTop (𝓝 0) := by
        have := ((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const I
        rw [Complex.ofReal_zero, zero_mul] at this
        exact this
      have h2 := (Complex.continuous_exp.tendsto 0).comp h0
      rw [Complex.exp_zero] at h2
      exact h2
    simpa using (hc t).mul he

end WeakConvergence

/-! ### Local alternatives -/

section LocalAlternatives

variable {p : ℕ}

/-- `1 / √n → 0`. -/
theorem tendsto_inv_sqrt_natCast : Tendsto (fun n : ℕ ↦ (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Local alternatives `θ₀ + k / √n` converge to `θ₀`. -/
theorem tendsto_localAlternative (θ₀ k : Fin p → ℝ) :
    Tendsto (fun n : ℕ ↦ θ₀ + (√(n : ℝ))⁻¹ • k) atTop (𝓝 θ₀) := by
  have h := (tendsto_const_nhds (x := θ₀)).add (tendsto_inv_sqrt_natCast.smul_const k)
  simpa using h

/-- **The drift of a differentiable functional along local alternatives.** If `ψ` has derivative
`ψ'` at `θ₀`, then `√n (ψ(θ₀ + k / √n) - ψ(θ₀)) → ψ' k`. -/
theorem tendsto_sqrt_mul_sub_of_hasFDerivAt {ψ : (Fin p → ℝ) → ℝ}
    {ψ' : (Fin p → ℝ) →L[ℝ] ℝ} {θ₀ : Fin p → ℝ} (hψ : HasFDerivAt ψ ψ' θ₀) (k : Fin p → ℝ) :
    Tendsto (fun n : ℕ ↦ √(n : ℝ) * (ψ (θ₀ + (√(n : ℝ))⁻¹ • k) - ψ θ₀)) atTop
      (𝓝 (ψ' k)) := by
  have hpath : HasDerivAt (fun t : ℝ ↦ θ₀ + t • k) k 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add θ₀
    rwa [one_smul] at this
  have hψ' : HasFDerivAt ψ ψ' (θ₀ + (0 : ℝ) • k) := by rwa [zero_smul, add_zero]
  have hd : HasDerivAt (fun t : ℝ ↦ ψ (θ₀ + t • k)) (ψ' k) 0 := hψ'.comp_hasDerivAt 0 hpath
  have hs := hd.tendsto_slope_zero_right
  have ht : Tendsto (fun n : ℕ ↦ (√(n : ℝ))⁻¹) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_sqrt_natCast, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact inv_pos.2 (Real.sqrt_pos.2 this)
  refine (hs.comp ht).congr fun n ↦ ?_
  simp [smul_eq_mul]

end LocalAlternatives

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {p : ℕ}

/-- The measurability conditions of `line_isScoreRegular` along the line through `θ₀` in the
direction `u`: the score of the line at `0` and the second derivatives of its log density near
`0` are measurable. -/
def LineMeasurable (F : ParametricFamily (Fin p → ℝ) S) (θ₀ u : Fin p → ℝ) : Prop :=
  Measurable ((F.line θ₀ u).score 0) ∧ ∀ᶠ t in 𝓝 (0 : ℝ), Measurable ((F.line θ₀ u).hessLogLik t)

/-- On a discrete sample space every line is measurable. -/
theorem lineMeasurable_of_discrete [DiscreteMeasurableSpace S]
    (F : ParametricFamily (Fin p → ℝ) S) (θ₀ u : Fin p → ℝ) : F.LineMeasurable θ₀ u :=
  ⟨.of_discrete, Eventually.of_forall fun _ ↦ .of_discrete⟩

variable {F : ParametricFamily (Fin p → ℝ) S} {θ₀ : Fin p → ℝ}

/-- **The scalar hypotheses along a line.** At a regular point with regular score and positive
definite information, the line in a direction `u ≠ 0` with the measurability conditions is a
regular scalar family at `0` with positive information `uᵀ I(θ₀) u`, regular score on a closed
ball, and log density with derivative the score. -/
theorem line_hypotheses (hreg : F.IsRegularAtVec θ₀) {r : ℝ} (hs : F.IsScoreRegularVec θ₀ r)
    (hI : (F.fisherInfoMatrix θ₀).PosDef) {u : Fin p → ℝ} (hu : u ≠ 0)
    (hm : F.LineMeasurable θ₀ u) :
    (F.line θ₀ u).IsRegularAt 0 ∧ 0 < (F.line θ₀ u).fisherInfo 0 ∧
      ∃ r' > 0, (F.line θ₀ u).IsScoreRegular 0 r' ∧
        ∀ᵐ z ∂(F.line θ₀ u).law 0, ∀ t ∈ closedBall (0 : ℝ) r',
          HasDerivAt (fun s ↦ (F.line θ₀ u).logLik s z) ((F.line θ₀ u).score t z) t :=
  ⟨hreg.line_isRegularAt u, line_fisherInfo_pos hreg hI hu,
    line_isScoreRegular hreg hs u hm.1 hm.2⟩

/-! ### Regular estimators of a vector parameter and of a functional -/

variable [SigmaFinite F.ν]

variable (F) in
/-- **Regularity of an estimator of a vector parameter.** The estimator `T n`, a measurable
function of a sample of size `n` with values in `ℝ^p`, is regular at `θ₀` with limit law `L` on
`EuclideanSpace ℝ (Fin p)` if for every local parameter `h ∈ ℝ^p`, under the law
`(F.pi n).law θ_n` of an i.i.d. sample of size `n` from `P_{θ_n}`, `θ_n = θ₀ + h / √n`, the law
of `√n (T_n - θ_n)` converges weakly to `L`. -/
structure IsHajekRegularVec (T : ∀ n, (Fin n → S) → Fin p → ℝ) (θ₀ : Fin p → ℝ)
    (L : Measure (EuclideanSpace ℝ (Fin p))) : Prop where
  /-- Each `T n` is measurable. -/
  measurable : ∀ n, Measurable (T n)
  /-- Weak convergence of `√n (T_n - θ_n)` under every local alternative. -/
  tendsto : ∀ h : Fin p → ℝ, ∀ f : EuclideanSpace ℝ (Fin p) →ᵇ ℝ, Tendsto (fun n : ℕ ↦
    ∫ x, f (√(n : ℝ) • (WithLp.toLp 2 (T n x) - WithLp.toLp 2 (θ₀ + (√(n : ℝ))⁻¹ • h)))
      ∂(F.pi n).law (θ₀ + (√(n : ℝ))⁻¹ • h)) atTop (𝓝 (∫ y, f y ∂L))

variable (F) in
/-- **Regularity of an estimator of a real functional.** The estimator `T n` of `ψ(θ)`, a
measurable real function of a sample of size `n`, is regular at `θ₀` with limit law `L` on `ℝ`
if for every local parameter `h ∈ ℝ^p`, under the law of an i.i.d. sample of size `n` from
`P_{θ_n}`, `θ_n = θ₀ + h / √n`, the law of `√n (T_n - ψ(θ_n))` converges weakly to `L`. -/
structure IsHajekRegularFunctional (T : ∀ n, (Fin n → S) → ℝ) (ψ : (Fin p → ℝ) → ℝ)
    (θ₀ : Fin p → ℝ) (L : Measure ℝ) : Prop where
  /-- Each `T n` is measurable. -/
  measurable : ∀ n, Measurable (T n)
  /-- Weak convergence of `√n (T_n - ψ(θ_n))` under every local alternative. -/
  tendsto : ∀ h : Fin p → ℝ, ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ ↦
    ∫ x, f (√(n : ℝ) * (T n x - ψ (θ₀ + (√(n : ℝ))⁻¹ • h)))
      ∂(F.pi n).law (θ₀ + (√(n : ℝ))⁻¹ • h)) atTop (𝓝 (∫ y, f y ∂L))

/-- Under local alternatives at an interior point, the sample laws are eventually probability
measures. -/
theorem eventually_isProbabilityMeasure_pi_law (hΘ : F.Θ ∈ 𝓝 θ₀) (k : Fin p → ℝ) :
    ∀ᶠ n : ℕ in atTop, IsProbabilityMeasure ((F.pi n).law (θ₀ + (√(n : ℝ))⁻¹ • k)) := by
  filter_upwards [tendsto_localAlternative θ₀ k hΘ] with n hn
  exact isProbabilityMeasure_law (F := F.pi n) hn

/-- **A regular estimator of a functional is regular along a line.** Let `T` be regular at `θ₀`
for `ψ` with limit `L`, at an interior point `θ₀` of `Θ`, and let `ψ` have derivative `ψ'` at
`θ₀`. For a direction `v` with `ψ' v ≠ 0`, the statistic `(T_n - ψ(θ₀)) / ψ' v` is regular at `0`
in the line through `θ₀` in the direction `v`, with limit the image of `L` under `y ↦ y / ψ' v`.
Indeed `√n ((T_n - ψ(θ₀)) / c - h / √n) = (√n (T_n - ψ(θ_n)) + a_n) / c` with `c = ψ' v`,
`θ_n = θ₀ + (h / √n) v` and `a_n = √n (ψ(θ_n) - ψ(θ₀)) - h c → 0`. -/
theorem IsHajekRegularFunctional.isHajekRegular_line (hΘ : F.Θ ∈ 𝓝 θ₀)
    {T : ∀ n, (Fin n → S) → ℝ} {ψ : (Fin p → ℝ) → ℝ} {L : Measure ℝ} [IsProbabilityMeasure L]
    (hT : F.IsHajekRegularFunctional T ψ θ₀ L) {ψ' : (Fin p → ℝ) →L[ℝ] ℝ}
    (hψ : HasFDerivAt ψ ψ' θ₀) {v : Fin p → ℝ} (hv : ψ' v ≠ 0) :
    (F.line θ₀ v).IsHajekRegular (fun n x ↦ (T n x - ψ θ₀) / ψ' v) 0
      (L.map fun y ↦ y / ψ' v) := by
  refine ⟨fun n ↦ ((hT.measurable n).sub_const _).div_const _, fun h f ↦ ?_⟩
  set c := ψ' v with hc
  set k : Fin p → ℝ := h • v with hk
  let θn : ℕ → Fin p → ℝ := fun n ↦ θ₀ + (√(n : ℝ))⁻¹ • k
  let X : ∀ n : ℕ, (Fin n → S) → ℝ := fun n x ↦ √(n : ℝ) * (T n x - ψ (θn n))
  have hX : ∀ n, Measurable (X n) := fun n ↦
    measurable_const.mul ((hT.measurable n).sub_const _)
  let ν : ℕ → Measure ℝ := fun n ↦ ((F.pi n).law (θn n)).map (X n)
  have hν : ∀ᶠ n in atTop, IsProbabilityMeasure (ν n) :=
    (eventually_isProbabilityMeasure_pi_law hΘ k).mono fun n hn ↦ by infer_instance
  have hconv : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n ↦ ∫ x, g x ∂ν n) atTop (𝓝 (∫ x, g x ∂L)) := by
    intro g
    refine (hT.tendsto k g).congr fun n ↦ ?_
    rw [integral_map (hX n).aemeasurable g.continuous.aestronglyMeasurable]
  let a : ℕ → ℝ := fun n ↦ √(n : ℝ) * (ψ (θn n) - ψ θ₀) - h * c
  have ha : Tendsto a atTop (𝓝 0) := by
    have h1 := tendsto_sqrt_mul_sub_of_hasFDerivAt hψ k
    have h2 : ψ' k = h * c := by rw [hk, map_smul, smul_eq_mul]
    rw [h2] at h1
    simpa using h1.sub_const (h * c)
  have hcont : Continuous fun y : ℝ ↦ y / c := continuous_id.div_const c
  let g : ℝ →ᵇ ℝ := f.compContinuous ⟨fun y ↦ y / c, hcont⟩
  have key := tendsto_integral_add_of_tendsto hν hconv ha g
  rw [integral_map hcont.aemeasurable f.continuous.aestronglyMeasurable]
  refine (key.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hθ : θ₀ + ((0 : ℝ) + h / √(n : ℝ)) • v = θn n := by
    simp only [θn, hk, zero_add, smul_smul, div_eq_mul_inv, mul_comm]
  have hgc : Continuous fun x ↦ g (x + a n) :=
    g.continuous.comp (continuous_id.add continuous_const)
  rw [integral_map (hX n).aemeasurable hgc.aestronglyMeasurable, pi_line_law, hθ]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [g, X, a, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
  congr 1
  field_simp
  ring

/-! ### The bounds -/

/-- `⟪x, a⟫ = a ⬝ᵥ x` in `EuclideanSpace ℝ (Fin p)`. -/
theorem inner_toLp_toLp (x a : Fin p → ℝ) :
    ⟪WithLp.toLp 2 x, WithLp.toLp 2 a⟫ = a ⬝ᵥ x := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- `I (I⁻¹ g) = g` for an invertible information matrix. -/
theorem mulVec_inv_mulVec {M : Matrix (Fin p) (Fin p) ℝ} (hM : M.PosDef) (g : Fin p → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ g) = g := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM.isUnit), one_mulVec]

/-- **The Hájek convolution bound for a functional.** In a family regular at `θ₀`
(`IsRegularAtVec`), with score regular on a closed ball (`IsScoreRegularVec`) and positive
definite information `I(θ₀)`, let `ψ` have gradient `g` at `θ₀` and let the line through `θ₀` in
the direction `I(θ₀)⁻¹ g` be measurable (`LineMeasurable`). Every estimator of `ψ` regular at
`θ₀` with limit `N(0, W)` has `gᵀ I(θ₀)⁻¹ g ≤ W`. For `g ≠ 0` the bound is the scalar bound in the
line through `θ₀` in the direction `v = I⁻¹ g`, whose information is `vᵀ I v = gᵀ I⁻¹ g = c`,
applied to the statistic `(T_n - ψ(θ₀)) / c` with limit `N(0, W / c²)`. -/
theorem hajek_convolution_bound_functional (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    {ψ : (Fin p → ℝ) → ℝ} {g : Fin p → ℝ} (hψ : HasFDerivAt ψ (gradCLM g) θ₀)
    (hm : F.LineMeasurable θ₀ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ g))
    {T : ∀ n, (Fin n → S) → ℝ} {W : ℝ≥0}
    (hT : F.IsHajekRegularFunctional T ψ θ₀ (gaussianReal 0 W)) :
    g ⬝ᵥ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ g) ≤ W := by
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨ε, hε, hball, -⟩ := hreg.exists_ball_pos
  have hΘ : F.Θ ∈ 𝓝 θ₀ := Filter.mem_of_superset (ball_mem_nhds θ₀ hε) hball
  set v := (F.fisherInfoMatrix θ₀)⁻¹ *ᵥ g with hvdef
  set c := g ⬝ᵥ v with hcdef
  have hc : 0 < c := by simpa using hI.inv.dotProduct_mulVec_pos hg
  have hv : v ≠ 0 := fun h0 ↦ by rw [hcdef, h0, dotProduct_zero] at hc; exact lt_irrefl _ hc
  have hψv : gradCLM g v ≠ 0 := by rw [gradCLM_apply]; exact hc.ne'
  obtain ⟨hR, hIpos, r', -, hsr, hdl⟩ := line_hypotheses hreg hs hI hv hm
  have hTl := hT.isHajekRegular_line hΘ hψ hψv
  have hdiv : (fun y : ℝ ↦ y / gradCLM g v) = (c⁻¹ * ·) := by
    funext y
    rw [gradCLM_apply, div_eq_inv_mul]
  rw [hdiv, gaussianReal_map_const_mul, mul_zero] at hTl
  have hb := hajek_convolution_bound hR hsr hdl hIpos hTl
  have hq : v ⬝ᵥ (F.fisherInfoMatrix θ₀ *ᵥ v) = c := by
    rw [hvdef, mulVec_inv_mulVec hI, dotProduct_comm]
  rw [line_fisherInfo hreg v, hq, NNReal.coe_mul, NNReal.coe_mk] at hb
  calc c = c ^ 2 * c⁻¹ := by field_simp
    _ ≤ c ^ 2 * (c⁻¹ ^ 2 * W) := mul_le_mul_of_nonneg_left hb (sq_nonneg c)
    _ = W := by field_simp

/-- **Linear functionals of a regular estimator.** If `T` is regular at `θ₀` with limit `L`, then
`aᵀ T` is a regular estimator of `aᵀ θ` with limit the image of `L` under `y ↦ ⟪y, a⟫`. -/
theorem IsHajekRegularVec.dotProduct {T : ∀ n, (Fin n → S) → Fin p → ℝ}
    {L : Measure (EuclideanSpace ℝ (Fin p))} (hT : F.IsHajekRegularVec T θ₀ L)
    (a : Fin p → ℝ) :
    F.IsHajekRegularFunctional (fun n x ↦ a ⬝ᵥ T n x) (fun θ ↦ a ⬝ᵥ θ) θ₀
      (L.map fun y ↦ ⟪y, WithLp.toLp 2 a⟫) := by
  have hca : Continuous fun y : Fin p → ℝ ↦ a ⬝ᵥ y := by
    simpa [← gradCLM_apply] using (gradCLM a).continuous
  have hci : Continuous fun y : EuclideanSpace ℝ (Fin p) ↦ ⟪y, WithLp.toLp 2 a⟫ :=
    continuous_id.inner continuous_const
  refine ⟨fun n ↦ hca.measurable.comp (hT.measurable n), fun h f ↦ ?_⟩
  let g : EuclideanSpace ℝ (Fin p) →ᵇ ℝ := f.compContinuous ⟨_, hci⟩
  rw [integral_map hci.aemeasurable f.continuous.aestronglyMeasurable]
  refine (hT.tendsto h g).congr fun n ↦ integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [g, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
  rw [← WithLp.toLp_sub, ← WithLp.toLp_smul, inner_toLp_toLp, dotProduct_smul, dotProduct_sub,
    smul_eq_mul]

/-- **The Hájek convolution bound, vector parameter.** In a family regular at `θ₀`
(`IsRegularAtVec`), with score regular on a closed ball (`IsScoreRegularVec`), positive definite
information `I(θ₀)` and measurable lines through `θ₀` (`LineMeasurable`) in the directions
`I(θ₀)⁻¹ a`, every estimator regular at `θ₀` with limit `N(0, V)` has `aᵀ I(θ₀)⁻¹ a ≤ aᵀ V a`
for every `a`, that is `V - I(θ₀)⁻¹` is positive semidefinite. The covariance `V` is assumed
positive semidefinite, as every covariance matrix is (`multivariateGaussian 0 V` is the
Gaussian law with covariance `V` only then). -/
theorem hajek_convolution_bound_vec (hreg : F.IsRegularAtVec θ₀) {r : ℝ}
    (hs : F.IsScoreRegularVec θ₀ r) (hI : (F.fisherInfoMatrix θ₀).PosDef)
    (hm : ∀ a, F.LineMeasurable θ₀ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a))
    {T : ∀ n, (Fin n → S) → Fin p → ℝ} {V : Matrix (Fin p) (Fin p) ℝ} (hV : V.PosSemidef)
    (hT : F.IsHajekRegularVec T θ₀ (multivariateGaussian 0 V)) :
    (∀ a : Fin p → ℝ, a ⬝ᵥ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ≤ a ⬝ᵥ (V *ᵥ a)) ∧
      (V - (F.fisherInfoMatrix θ₀)⁻¹).PosSemidef := by
  have hquad : ∀ a : Fin p → ℝ, a ⬝ᵥ ((F.fisherInfoMatrix θ₀)⁻¹ *ᵥ a) ≤ a ⬝ᵥ (V *ᵥ a) := by
    intro a
    have ha := hT.dotProduct a
    rw [multivariateGaussian_map_inner hV, WithLp.ofLp_toLp] at ha
    have hb := hajek_convolution_bound_functional hreg hs hI
      (by simpa [← gradCLM_apply] using (gradCLM a).hasFDerivAt) (hm a) ha
    have hnn : 0 ≤ a ⬝ᵥ (V *ᵥ a) := by simpa using hV.dotProduct_mulVec_nonneg a
    rwa [Real.coe_toNNReal _ hnn] at hb
  refine ⟨hquad, posSemidef_iff_dotProduct_mulVec.2 ⟨hV.isHermitian.sub hI.isHermitian.inv,
    fun a ↦ ?_⟩⟩
  rw [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg]
  exact hquad a

end ParametricFamily

end CausalInference
