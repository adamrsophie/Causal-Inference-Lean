/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.EfficiencyBound
public import CausalInference.Estimation.CramerRao
public import CausalInference.Estimation.LocalAsymptoticNormality

/-!
# The information of a score submodel

For a law `Q` of the observed data and a bounded measurable score `s` with `E_Q[s] = 0`, the
tilted laws `(1 + t s) dQ` form a dominated parametric family in the sense of
`CausalInference.ParametricFamily` (`tiltFamily`), with dominating measure `Q`, density
`1 + t s` and parameter set the open interval on which the density is positive. Its score at
`t` is `s / (1 + t s)`; in particular its score at `0` is `s` and its Fisher information at `0`
is `E_Q[s²]`. The family is regular at `0` (`ParametricFamily.IsRegularAt`) and its score is
smooth on a closed ball around `0` (`ParametricFamily.IsScoreRegular`), so the local asymptotic
normality of `CausalInference.Estimation.LocalAsymptoticNormality` and the Cramér-Rao bound of
`CausalInference.Estimation.CramerRao` apply to it.

Consequently the denominators `E[s(O)²]` of the submodel bounds `d² / E[s(O)²]`, whose least
upper bound is the efficiency bound (`isLUB_submodelBounds_arm`), are the Fisher informations
`I_s(0)` of the one dimensional submodels, so the submodel bounds are the Cramér-Rao expressions
`ψ'(0)² / I_s(0)` (`isLUB_cramerRaoBounds_arm`). The Cramér-Rao inequality itself is stated for
the mean of a bounded statistic along a submodel (`tiltFamily_cramer_rao_of_bounded`).

## Main definitions

* `tiltFamily Q hs`: the score submodel through `Q` in the direction `s` as a parametric family.

## Main results

* `map_scoreTilt`: the law of the observed data under the tilt `(1 + t s(O)) dμ` of the
  population is the tilt `(1 + t s) d(μ.map O)` of the law of the observed data.
* `score_tiltFamily`, `fisherInfo_tiltFamily_zero`: the score `s / (1 + t s)` and the
  information `I_s(0) = E_Q[s²]`.
* `isRegularAt_tiltFamily`, `isScoreRegular_tiltFamily`, `hasDerivAt_logLik_tiltFamily`: the
  regularity conditions at `0`.
* `logLikRatio_tiltFamily_sub_tendstoInMeasure`: local asymptotic normality of the tilt.
* `tiltFamily_cramer_rao_of_bounded`: the Cramér-Rao bound along a submodel.
* `isLUB_cramerRaoBounds_arm`: the efficiency bound of an arm mean is the supremum of the
  Cramér-Rao bounds of the score submodels.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov and J. A. Wellner, *Efficient and Adaptive
  Estimation for Semiparametric Models*, Johns Hopkins University Press (1993).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Topology Metric MissingData PointTreatment
open scoped ENNReal

section Map

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]

/-- **The tilt passes to the observed data.** Under the tilt `(1 + t s(O)) dμ` of the population,
the observed data `O` has the law `(1 + t s) d(μ.map O)`, the tilt of the law of the observed
data. -/
theorem map_scoreTilt {μ : Measure Ω} {O : Ω → 𝒪} (hO : Measurable O) {s : 𝒪 → ℝ}
    (hs : Measurable s) (t : ℝ) :
    (scoreTilt μ (fun ω ↦ s (O ω)) t).map O = scoreTilt (μ.map O) s t := by
  ext B hB
  rw [Measure.map_apply hO hB, scoreTilt, scoreTilt, withDensity_apply _ (hO hB),
    withDensity_apply _ hB, setLIntegral_map (f := fun z ↦ ENNReal.ofReal (1 + t * s z)) hB
      (measurable_const.add (measurable_const.mul hs)).ennreal_ofReal hO]

/-- The tilt at `t = 0` is the law itself. -/
@[simp]
theorem scoreTilt_zero (μ : Measure Ω) (S : Ω → ℝ) : scoreTilt μ S 0 = μ := by
  simp [scoreTilt]

/-- A bounded score of the observed data `O` under `μ` is the same as a bounded score of the law
`μ.map O` of the observed data. -/
theorem isBoundedScore_map_iff {μ : Measure Ω} {O : Ω → 𝒪} (hO : Measurable O) {s : 𝒪 → ℝ} :
    IsBoundedScore (μ.map O) id s ↔ IsBoundedScore μ O s := by
  constructor
  · rintro ⟨hs, hC, h0⟩
    refine ⟨hs, hC, ?_⟩
    rw [← integral_map hO.aemeasurable hs.aestronglyMeasurable]
    exact h0
  · rintro ⟨hs, hC, h0⟩
    refine ⟨hs, hC, ?_⟩
    rw [← h0]
    exact integral_map hO.aemeasurable hs.aestronglyMeasurable

end Map

section Family

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {Q : Measure 𝒪} [IsProbabilityMeasure Q]
  {s : 𝒪 → ℝ}

/-- A positive bound `|s| ≤ K` of a bounded score, chosen from the bound in `IsBoundedScore`. -/
noncomputable def IsBoundedScore.bound (hs : IsBoundedScore Q id s) : ℝ :=
  |hs.2.1.choose| + 1

omit [IsProbabilityMeasure Q] in
theorem IsBoundedScore.bound_pos (hs : IsBoundedScore Q id s) : 0 < hs.bound := by
  unfold IsBoundedScore.bound; positivity

omit [IsProbabilityMeasure Q] in
theorem IsBoundedScore.abs_le_bound (hs : IsBoundedScore Q id s) (z : 𝒪) :
    |s z| ≤ hs.bound :=
  (hs.2.1.choose_spec z).trans ((le_abs_self _).trans (by unfold IsBoundedScore.bound; linarith))

omit [IsProbabilityMeasure Q] in
theorem IsBoundedScore.integral_eq_zero (hs : IsBoundedScore Q id s) : ∫ z, s z ∂Q = 0 :=
  hs.2.2

theorem IsBoundedScore.integrable (hs : IsBoundedScore Q id s) : Integrable s Q :=
  Integrable.of_bound hs.1.aestronglyMeasurable hs.bound
    (Eventually.of_forall fun z ↦ by rw [Real.norm_eq_abs]; exact hs.abs_le_bound z)

theorem IsBoundedScore.memLp_id (hs : IsBoundedScore Q id s) (p : ℝ≥0∞) : MemLp s p Q :=
  MemLp.of_bound hs.1.aestronglyMeasurable hs.bound
    (Eventually.of_forall fun z ↦ by rw [Real.norm_eq_abs]; exact hs.abs_le_bound z)

omit [IsProbabilityMeasure Q] in
/-- `1 + t s > 0` when `|t| K < 1`. -/
theorem IsBoundedScore.one_add_mul_pos (hs : IsBoundedScore Q id s) {t : ℝ}
    (ht : |t| * hs.bound < 1) (z : 𝒪) : 0 < 1 + t * s z := by
  have : |t * s z| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hs.abs_le_bound z) (abs_nonneg t)).trans_lt ht
  linarith [neg_abs_le (t * s z)]

omit [IsProbabilityMeasure Q] in
/-- `1 + t s ≥ 1/2` when `|t| K ≤ 1/2`. -/
theorem IsBoundedScore.half_le_one_add_mul (hs : IsBoundedScore Q id s) {t : ℝ}
    (ht : |t| * hs.bound ≤ 1 / 2) (z : 𝒪) : 1 / 2 ≤ 1 + t * s z := by
  have : |t * s z| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hs.abs_le_bound z) (abs_nonneg t)).trans ht
  linarith [neg_abs_le (t * s z)]

variable (Q) in
/-- **The score submodel as a parametric family.** For a bounded measurable score `s` with
`E_Q[s] = 0` and the bound `|s| ≤ K` of `IsBoundedScore.bound`, the family with dominating
measure `Q`, density `f(z; t) = 1 + t s(z)` and parameter set `{t : |t| K < 1}`, on which the
density is positive. Its law at `t` is the tilt `scoreTilt Q s t` (`law_tiltFamily`). -/
noncomputable def tiltFamily (hs : IsBoundedScore Q id s) : ParametricFamily ℝ 𝒪 where
  ν := Q
  Θ := {t | |t| * hs.bound < 1}
  density t z := 1 + t * s z
  measurable_density _ := measurable_const.add (measurable_const.mul hs.1)
  density_nonneg _ ht z := (hs.one_add_mul_pos ht z).le
  integrable_density t _ := (integrable_const 1).add (hs.integrable.const_mul t)
  integral_density t _ := by
    rw [integral_add (integrable_const 1) (hs.integrable.const_mul t), integral_const_mul,
      hs.integral_eq_zero]
    simp

variable (hs : IsBoundedScore Q id s)

instance isProbabilityMeasure_tiltFamily_ν : IsProbabilityMeasure (tiltFamily Q hs).ν := by
  change IsProbabilityMeasure Q; infer_instance

theorem law_tiltFamily (t : ℝ) : (tiltFamily Q hs).law t = scoreTilt Q s t := rfl

theorem law_tiltFamily_zero : (tiltFamily Q hs).law 0 = Q := by
  rw [law_tiltFamily, scoreTilt_zero]

theorem density_tiltFamily (t : ℝ) (z : 𝒪) : (tiltFamily Q hs).density t z = 1 + t * s z := rfl

theorem mem_tiltFamily_Θ {t : ℝ} : t ∈ (tiltFamily Q hs).Θ ↔ |t| * hs.bound < 1 := Iff.rfl

theorem tiltFamily_Θ_mem_nhds : (tiltFamily Q hs).Θ ∈ 𝓝 (0 : ℝ) :=
  (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds (by simp)

theorem densityDeriv_tiltFamily (t : ℝ) (z : 𝒪) : (tiltFamily Q hs).densityDeriv t z = s z := by
  have h : HasDerivAt (fun u ↦ 1 + u * s z) (1 * s z) t :=
    ((hasDerivAt_id t).mul_const (s z)).const_add 1
  rw [ParametricFamily.densityDeriv]
  change deriv (fun u ↦ 1 + u * s z) t = s z
  rw [h.deriv, one_mul]

theorem densityDeriv2_tiltFamily (t : ℝ) (z : 𝒪) : (tiltFamily Q hs).densityDeriv2 t z = 0 := by
  rw [ParametricFamily.densityDeriv2]
  simp only [densityDeriv_tiltFamily, deriv_const]

/-- **The score of the tilt** at `t` is `s / (1 + t s)`. -/
theorem score_tiltFamily (t : ℝ) (z : 𝒪) :
    (tiltFamily Q hs).score t z = s z / (1 + t * s z) := by
  rw [ParametricFamily.score, densityDeriv_tiltFamily, density_tiltFamily]

/-- **The score of the tilt at `0` is `s`.** -/
theorem score_tiltFamily_zero : (tiltFamily Q hs).score 0 = s := by
  funext z; rw [score_tiltFamily]; simp

/-- **The information of the tilt at `0` is `E_Q[s²]`.** -/
theorem fisherInfo_tiltFamily_zero : (tiltFamily Q hs).fisherInfo 0 = ∫ z, s z ^ 2 ∂Q := by
  rw [ParametricFamily.fisherInfo, score_tiltFamily_zero, law_tiltFamily_zero]

/-- **The tilt is regular at `0`**: common positive support near `0`, an affine density with
bounded derivatives, and a bounded score. -/
theorem isRegularAt_tiltFamily : (tiltFamily Q hs).IsRegularAt 0 where
  support := by
    filter_upwards [tiltFamily_Θ_mem_nhds hs] with u hu x
    simp only [density_tiltFamily, zero_mul, add_zero, zero_lt_one, iff_true]
    exact hs.one_add_mul_pos hu x
  smooth_dominated := by
    refine ⟨1 / hs.bound, by have := hs.bound_pos; positivity, fun u hu ↦ ?_,
      Eventually.of_forall fun x ↦ ?_, fun _ ↦ hs.bound, fun _ ↦ 0, integrable_const _,
      integrable_const _, Eventually.of_forall fun x u _ ↦ ?_⟩
    · rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hu
      rw [mem_tiltFamily_Θ]
      have := hs.bound_pos
      rwa [lt_div_iff₀ this] at hu
    · exact (contDiff_const.add (contDiff_id.mul contDiff_const)).contDiffOn
    · rw [densityDeriv_tiltFamily, densityDeriv2_tiltFamily]
      exact ⟨hs.abs_le_bound x, by simp⟩
  memLp_score := by
    rw [score_tiltFamily_zero, law_tiltFamily_zero]
    exact hs.memLp_id 2

/-- On the parameter set, `t ↦ log (1 + t s(z))` has derivative `s(z) / (1 + t s(z))`. -/
theorem hasDerivAt_logLik_tiltFamily {t : ℝ} (ht : |t| * hs.bound < 1) (z : 𝒪) :
    HasDerivAt (fun u ↦ (tiltFamily Q hs).logLik u z) (s z / (1 + t * s z)) t := by
  have h := (((hasDerivAt_id t).mul_const (s z)).const_add 1).log (hs.one_add_mul_pos ht z).ne'
  refine h.congr_deriv ?_
  simp

omit [IsProbabilityMeasure Q] in
theorem hasDerivAt_div_one_add_mul {t : ℝ} (ht : |t| * hs.bound < 1) (z : 𝒪) :
    HasDerivAt (fun u ↦ s z / (1 + u * s z)) (-(s z ^ 2) / (1 + t * s z) ^ 2) t := by
  have h := (hasDerivAt_const t (s z)).div (((hasDerivAt_id t).mul_const (s z)).const_add 1)
    (hs.one_add_mul_pos ht z).ne'
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- The second derivative of the log density of the tilt: `-s² / (1 + t s)²`. -/
theorem hessLogLik_tiltFamily {t : ℝ} (ht : |t| * hs.bound < 1) (z : 𝒪) :
    (tiltFamily Q hs).hessLogLik t z = -(s z ^ 2) / (1 + t * s z) ^ 2 := by
  have hopen : IsOpen {u : ℝ | |u| * hs.bound < 1} :=
    isOpen_lt (continuous_abs.mul continuous_const) continuous_const
  have hev : (fun u ↦ deriv (fun v ↦ (tiltFamily Q hs).logLik v z) u) =ᶠ[𝓝 t]
      fun u ↦ s z / (1 + u * s z) := by
    filter_upwards [hopen.mem_nhds ht] with u hu
    exact (hasDerivAt_logLik_tiltFamily hs hu z).deriv
  rw [ParametricFamily.hessLogLik, hev.deriv_eq, (hasDerivAt_div_one_add_mul hs ht z).deriv]

omit [IsProbabilityMeasure Q] in
theorem abs_mul_bound_le_of_mem_closedBall {t : ℝ}
    (ht : t ∈ closedBall (0 : ℝ) (1 / (2 * hs.bound))) : |t| * hs.bound ≤ 1 / 2 := by
  have hK := hs.bound_pos
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, le_div_iff₀ (by positivity)] at ht
  linarith

/-- **The score of the tilt is smooth on the closed ball of radius `1 / (2 K)`**, where the
density is at least `1/2`: the second derivative `-s² / (1 + t s)²` of the log density is
continuous in `t` and bounded by `4 K²`. -/
theorem isScoreRegular_tiltFamily : (tiltFamily Q hs).IsScoreRegular 0 (1 / (2 * hs.bound)) where
  pos := by have := hs.bound_pos; positivity
  measurable_score := by rw [score_tiltFamily_zero]; exact hs.1
  measurable_hessLogLik θ hθ := by
    have hθ' : |θ| * hs.bound < 1 :=
      (abs_mul_bound_le_of_mem_closedBall hs hθ).trans_lt (by norm_num)
    have e : (tiltFamily Q hs).hessLogLik θ = fun z ↦ -(s z ^ 2) / (1 + θ * s z) ^ 2 :=
      funext (hessLogLik_tiltFamily hs hθ')
    rw [e]
    exact (hs.1.pow_const 2).neg.div
      ((measurable_const.add (measurable_const.mul hs.1)).pow_const 2)
  hasDerivAt_score := Eventually.of_forall fun z θ hθ ↦ by
    have hθ' : |θ| * hs.bound < 1 :=
      (abs_mul_bound_le_of_mem_closedBall hs hθ).trans_lt (by norm_num)
    have e : (fun u ↦ (tiltFamily Q hs).score u z) = fun u ↦ s z / (1 + u * s z) :=
      funext fun u ↦ score_tiltFamily hs u z
    rw [e, hessLogLik_tiltFamily hs hθ']
    exact hasDerivAt_div_one_add_mul hs hθ' z
  continuousOn_hessLogLik := Eventually.of_forall fun z ↦ by
    refine ContinuousOn.congr (f := fun u ↦ -(s z ^ 2) / (1 + u * s z) ^ 2) ?_ fun u hu ↦
      hessLogLik_tiltFamily hs ((abs_mul_bound_le_of_mem_closedBall hs hu).trans_lt
        (by norm_num)) z
    refine continuousOn_const.div (by fun_prop) fun u hu ↦ ?_
    exact pow_ne_zero 2 (hs.one_add_mul_pos ((abs_mul_bound_le_of_mem_closedBall hs hu).trans_lt
      (by norm_num)) z).ne'
  dominated := ⟨fun _ ↦ 4 * hs.bound ^ 2, by rw [law_tiltFamily_zero]; exact integrable_const _,
    Eventually.of_forall fun z θ hθ ↦ by
    have hθ2 := abs_mul_bound_le_of_mem_closedBall hs hθ
    have h1 := hs.half_le_one_add_mul hθ2 z
    have h2 : s z ^ 2 ≤ hs.bound ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hs.abs_le_bound z) 2
    have h3 : 1 / 4 ≤ (1 + θ * s z) ^ 2 := by nlinarith
    have h4 : 4 * hs.bound ^ 2 * (1 / 4) ≤ 4 * hs.bound ^ 2 * (1 + θ * s z) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [hessLogLik_tiltFamily hs (hθ2.trans_lt (by norm_num)), abs_div, abs_neg,
      abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    change s z ^ 2 ≤ 4 * hs.bound ^ 2 * (1 + θ * s z) ^ 2
    linarith⟩

/-- The derivative of the log density on the closed ball is the score. -/
theorem hasDerivAt_logLik_tiltFamily_ae :
    ∀ᵐ z ∂(tiltFamily Q hs).law 0, ∀ θ ∈ closedBall (0 : ℝ) (1 / (2 * hs.bound)),
      HasDerivAt (fun u ↦ (tiltFamily Q hs).logLik u z) ((tiltFamily Q hs).score θ z) θ :=
  Eventually.of_forall fun z θ hθ ↦ by
    rw [score_tiltFamily]
    exact hasDerivAt_logLik_tiltFamily hs
      ((abs_mul_bound_le_of_mem_closedBall hs hθ).trans_lt (by norm_num)) z

/-- **Local asymptotic normality of the tilt.** For an i.i.d. sample with law `Q` and every local
parameter `h`, the log likelihood ratio of the tilt at `h / √n` against `Q` is
`h S_n - h² E_Q[s²] / 2 + o_P(1)`, with `S_n = n^{-1/2} ∑_{i < n} s(O_i)`. This is
`ParametricFamily.logLikRatio_sub_tendstoInMeasure` for `tiltFamily`, whose hypotheses are
`isRegularAt_tiltFamily`, `isScoreRegular_tiltFamily` and `hasDerivAt_logLik_tiltFamily_ae`. -/
theorem logLikRatio_tiltFamily_sub_tendstoInMeasure {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω'} [IsProbabilityMeasure P] {Os : ℕ → Ω' → 𝒪} (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = Q) (h : ℝ) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (tiltFamily Q hs).logLikRatio Os 0 (h / √(n : ℝ)) n ω -
      (h * ((√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, s (Os i ω)) -
        h ^ 2 * (∫ z, s z ^ 2 ∂Q) / 2)) atTop 0 := by
  have := ParametricFamily.logLikRatio_sub_tendstoInMeasure hOs
    (hlaw.trans (law_tiltFamily_zero hs).symm) (isRegularAt_tiltFamily hs)
    (isScoreRegular_tiltFamily hs) (hasDerivAt_logLik_tiltFamily_ae hs) h
  simpa only [zero_add, score_tiltFamily_zero, fisherInfo_tiltFamily_zero] using this

include hs in
/-- **The Cramér-Rao bound along a score submodel.** For a bounded measurable statistic `T` of one
observation, the derivative at `0` of its mean `t ↦ E_t[T]` under the tilted laws satisfies
`(d/dt E_t[T])² / E_Q[s²] ≤ Var_Q(T)`: the Cramér-Rao bound of
`ParametricFamily.IsRegularAt.cramer_rao_of_bounded` for `tiltFamily`, whose information at `0`
is `E_Q[s²]`. -/
theorem tiltFamily_cramer_rao_of_bounded (hI : 0 < ∫ z, s z ^ 2 ∂Q) {T : 𝒪 → ℝ}
    (hTm : Measurable T) {C : ℝ} (hTC : ∀ z, |T z| ≤ C) :
    deriv (fun t ↦ ∫ z, T z ∂scoreTilt Q s t) 0 ^ 2 / ∫ z, s z ^ 2 ∂Q ≤ Var[T; Q] := by
  have h := (isRegularAt_tiltFamily hs).cramer_rao_of_bounded
    (by rwa [fisherInfo_tiltFamily_zero]) hTm hTC
  rw [fisherInfo_tiltFamily_zero, law_tiltFamily_zero] at h
  exact h.1

end Family

section Arm

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The information `E[s(O)²]` of a score of the observed data is the Fisher information at `0`
of its submodel. -/
theorem fisherInfo_tiltFamily_map {𝒪 : Type*} [MeasurableSpace 𝒪] {O : Ω → 𝒪}
    (hO : Measurable O) {s : 𝒪 → ℝ} (hs : IsBoundedScore μ O s) :
    (tiltFamily (μ.map O) ((isBoundedScore_map_iff hO).2 hs)).fisherInfo 0 =
      ∫ ω, s (O ω) ^ 2 ∂μ := by
  rw [fisherInfo_tiltFamily_zero, integral_map hO.aemeasurable
    (hs.1.pow_const 2).aestronglyMeasurable]

/-- **The efficiency bound of an arm mean is the supremum of the Cramér-Rao bounds of the score
submodels.** Under the hypotheses of `isLUB_submodelBounds_arm`, `V_a = E[φ_a(O)²]` is the least
upper bound of `ψ'(0)² / I_s(0)` over bounded scores `s` with positive information, where
`I_s(0)` is the Fisher information at `0` of the submodel `tiltFamily` through the law of the
observed data (`fisherInfo_tiltFamily_map`) and `ψ'(0)` the derivative of the arm mean along it.
The content beyond `isLUB_submodelBounds_arm` is the identity `I_s(0) = E[s(O)²]`. -/
theorem isLUB_cramerRaoBounds_arm (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω))
    (hV : 0 < ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ) :
    IsLUB {r | ∃ s, ∃ hs : IsBoundedScore μ (obsData A Y W) s,
        0 < (tiltFamily (μ.map (obsData A Y W))
          ((isBoundedScore_map_iff (measurable_obsData hW hA hY)).2 hs)).fisherInfo 0 ∧
        ∃ d, HasDerivAt (fun t ↦ regressionFunctional
          (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t) (arm A a) W (obsOutcome A Y)) d 0 ∧
        r = d ^ 2 / (tiltFamily (μ.map (obsData A Y W))
          ((isBoundedScore_map_iff (measurable_obsData hW hA hY)).2 hs)).fisherInfo 0}
      (∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ) := by
  have hO := measurable_obsData hW hA hY
  convert isLUB_submodelBounds_arm hW hA hY hY2 hps hreg a hmi hε hpos hV using 1
  ext r
  constructor
  · rintro ⟨s, hs, hI, d, hd, rfl⟩
    rw [fisherInfo_tiltFamily_map hO hs] at hI ⊢
    exact ⟨s, hs, hI, d, hd, rfl⟩
  · rintro ⟨s, hs, hI, d, hd, rfl⟩
    refine ⟨s, hs, ?_, d, hd, ?_⟩ <;> rw [fisherInfo_tiltFamily_map hO hs]
    exact hI

end Arm

end Efficiency
end CausalInference
