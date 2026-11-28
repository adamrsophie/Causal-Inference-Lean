/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapEstimator
public import CausalInference.Estimation.PosteriorLimitDelta

/-!
# The conditional limit law of the bootstrapped weighted arm mean

Let `O` be an i.i.d. sample and `T_n` a measurable statistic of `n` records. Write
`T̂ₙ = T_n(O_0, …, O_{n-1})` for the data estimate and `T*ₙ = T_n(y)` for its value at a resample
`y` drawn from the empirical law of the first `n` observations. For a measurable `ψ` the
**bootstrap remainder** is
`R_n(ω, y) = √n (T*ₙ - T̂ₙ) - √n (n⁻¹ ∑ᵢ ψ(yᵢ) - n⁻¹ ∑_{k < n} ψ(O_k))`.

**The mode of convergence.** `IsBootstrapLinear P O T ψ` says that the remainder is small in
conditional probability, in probability: for every `ρ > 0`,
`P*(|R_n| ≥ ρ) → 0` in `P` probability, where `P*` is the resampling law given the data. The
conclusion of `IsBootstrapLinear.isBernsteinVonMisesWeak` is the weak Bernstein and von Mises
property: for every bounded continuous `f`,
`∫ f(√n (T*ₙ - T̂ₙ)) dP* → ∫ f dN(0, Var ψ(O_0))` in `P` probability.

The linear term carries the limit: the conditional central limit theorem of the bootstrap mean
(`Bootstrap.isBernsteinVonMisesWeak_resampleMean`) is transferred along a remainder that is small
in conditional probability. The transfer (`isBernsteinVonMisesWeak_bootstrapLaw_of_remainder`)
uses the tightness of the linear term, read off from the limit law with a continuous cutoff, and
the uniform continuity of `f` on compact intervals.

For the weighted arm mean `T_n = bootstrapArmMean φ t a n` the influence function is
`ψ = weightedArmInfluence`, of mean zero, and the limit is `N(0, σ²)` with
`σ² = weightedArmVariance` (`isBernsteinVonMisesWeak_bootstrapArmMean`).

## Main definitions

* `bootstrapRemainder T ψ O n ω y`: the remainder `R_n(ω, y)` of the bootstrap expansion.
* `IsBootstrapLinear P O T ψ`: the remainder is small in conditional probability, in probability.

## Main results

* `isBernsteinVonMisesWeak_bootstrapLaw_of_remainder`: the transfer of the weak Bernstein and von
  Mises property along a remainder small in conditional probability.
* `IsBootstrapLinear.isBernsteinVonMisesWeak`: the conditional limit law of a bootstrap linear
  statistic.
* `IsBootstrapLinear.linearCombination`: bootstrap linearity is closed under linear combinations.
* `isBernsteinVonMisesWeak_bootstrapArmMean`: the conditional limit law of the bootstrapped
  weighted arm mean.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, Cambridge University Press, chapter 23.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap PosteriorLimit

section Transfer

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {P : Measure Ω}

/-- An integral against a bootstrap law is an integral against the resampling law. -/
theorem integral_bootstrapLaw_comp {U : (n : ℕ) → (Fin n → 𝒪) → ℝ} (hU : ∀ n, Measurable (U n))
    {f : ℝ → ℝ} (hf : Continuous f) (O : ℕ → Ω → 𝒪) (θ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ x, f (√(n : ℝ) • (x - θ n ω)) ∂bootstrapLaw U O n ω =
      ∫ y, f (√(n : ℝ) * (U n y - θ n ω)) ∂resampleLaw O n ω := by
  rw [bootstrapLaw, integral_map (hU n).aemeasurable (by fun_prop : Continuous fun x : ℝ =>
    f (√(n : ℝ) • (x - θ n ω))).aestronglyMeasurable]
  simp only [smul_eq_mul]

/-- **Transfer of the weak Bernstein and von Mises property along a small remainder.** Let `S`
and `T` be measurable statistics. If the bootstrap laws of `S` satisfy the weak Bernstein and von
Mises property with centering `θS` and limit `N`, and for every `ρ > 0` the conditional
probability `P*(|√n (T*ₙ - θTₙ) - √n (S*ₙ - θSₙ)| ≥ ρ)` tends to zero in probability, then the
bootstrap laws of `T` satisfy it with centering `θT` and the same limit `N`. -/
theorem isBernsteinVonMisesWeak_bootstrapLaw_of_remainder {O : ℕ → Ω → 𝒪}
    {S T : (n : ℕ) → (Fin n → 𝒪) → ℝ} (hS : ∀ n, Measurable (S n)) (hT : ∀ n, Measurable (T n))
    {θS θT : ℕ → Ω → ℝ} {N : Measure ℝ} (h : IsBernsteinVonMisesWeak P (bootstrapLaw S O) θS N)
    (hrem : ∀ ρ : ℝ, 0 < ρ → TendstoInMeasure P (fun n ω => (resampleLaw O n ω).real
      {y | ρ ≤ |√(n : ℝ) * (T n y - θT n ω) - √(n : ℝ) * (S n y - θS n ω)|}) atTop
      (fun _ => 0)) :
    IsBernsteinVonMisesWeak P (bootstrapLaw T O) θT N := by
  have := h.isProbabilityMeasure_limit
  refine ⟨fun n ω => inferInstance, inferInstance, fun φ hφ hφb => ?_⟩
  simp only [integral_bootstrapLaw_comp hT hφ O θT]
  have hB := h.tendsto φ hφ hφb
  simp only [integral_bootstrapLaw_comp hS hφ O θS] at hB
  obtain ⟨C, hC⟩ := hφb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine TendstoInMeasure.of_perturb hB (tendstoInMeasure_const (1 : ℝ)) fun ε hε => ?_
  simp only [mul_one]
  set η := ε / (16 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hdom : Tendsto (fun m : ℕ => ∫ z, normCutoff (m : ℝ) z ∂N) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := N) (fun _ => (1 : ℝ))
      (F := fun (m : ℕ) (z : ℝ) => normCutoff (m : ℝ) z) (f := fun _ => 0)
      (fun m => (continuous_normCutoff _).aestronglyMeasurable) (integrable_const 1)
      (fun m => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (normCutoff_mem_Icc _ z).1]
        exact (normCutoff_mem_Icc _ z).2)
      (ae_of_all _ fun z => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with m hm
        have : ‖z‖ ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
        simp only [normCutoff]
        rw [max_eq_left (by linarith), min_eq_right zero_le_one])
    simpa using this
  obtain ⟨m, hm⟩ := (hdom.eventually (gt_mem_nhds hη0)).exists
  set K : ℝ := m + 1 with hK
  have hK0 : 0 < K := by positivity
  set R := K + 1 with hR
  obtain ⟨ρ, hρ, hφu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := -R) (b := R)).uniformContinuousOn_of_continuous hφ.continuousOn)
    (ε / 2) (by positivity)
  set ρ' := min ρ 1 with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ zero_lt_one
  have hcut := h.tendsto _ (continuous_normCutoff (m : ℝ)) ⟨1, fun z => by
    rw [abs_of_nonneg (normCutoff_mem_Icc _ z).1]; exact (normCutoff_mem_Icc _ z).2⟩
  simp only [integral_bootstrapLaw_comp hS (continuous_normCutoff (m : ℝ)) O θS] at hcut
  have hG := (hcut.withProbTendingToOne_dist_lt hη0).inter
    ((hrem ρ' hρ'0).withProbTendingToOne_dist_lt hη0)
  refine withProbTendingToOne_of_eventually_subset hG (Eventually.of_forall fun n => ?_)
  rintro ω ⟨hω1, hω2⟩
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω1 hω2 ⊢
  set D := {y | ρ' ≤ |√(n : ℝ) * (T n y - θT n ω) - √(n : ℝ) * (S n y - θS n ω)|} with hD
  have hsm : Measurable fun y => √(n : ℝ) * (S n y - θS n ω) :=
    ((hS n).sub_const _).const_mul _
  have htm : Measurable fun y => √(n : ℝ) * (T n y - θT n ω) :=
    ((hT n).sub_const _).const_mul _
  have hDm : MeasurableSet D :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (htm.sub hsm))
  have hpt : ∀ y, |φ (√(n : ℝ) * (T n y - θT n ω)) - φ (√(n : ℝ) * (S n y - θS n ω))| ≤
      ε / 2 + 2 * C * normCutoff m (√(n : ℝ) * (S n y - θS n ω)) +
        2 * C * D.indicator 1 y := by
    intro y
    set a := √(n : ℝ) * (S n y - θS n ω) with ha
    set b := √(n : ℝ) * (T n y - θT n ω) with hb
    have h2C : |φ b - φ a| ≤ 2 * C := by
      have := abs_sub (φ b) (φ a)
      linarith [hC b, hC a]
    have hc0 := (normCutoff_mem_Icc m a).1
    have hi0 : 0 ≤ D.indicator (1 : (Fin n → 𝒪) → ℝ) y :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) y
    by_cases haK : K ≤ |a|
    · have : normCutoff m a = 1 := by
        simp only [normCutoff, Real.norm_eq_abs]
        rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      rw [this]
      nlinarith
    by_cases hyD : y ∈ D
    · rw [Set.indicator_of_mem hyD, Pi.one_apply]
      nlinarith
    push Not at haK
    have hba : |b - a| < ρ' := by
      simpa [hD, Set.mem_ofPred_eq, not_le, ha, hb] using hyD
    have h1 : a ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc, ← abs_le]; linarith
    have h2 : b ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc, ← abs_le]
      have := abs_sub_abs_le_abs_sub b a
      linarith [min_le_right ρ 1]
    have hdist : dist b a < ρ := by
      rw [Real.dist_eq]; linarith [min_le_left ρ 1]
    have := hφu _ h2 _ h1 hdist
    rw [Real.dist_eq] at this
    nlinarith
  have hfi : Integrable (fun y => φ (√(n : ℝ) * (T n y - θT n ω))) (resampleLaw O n ω) :=
    Integrable.of_bound (hφ.measurable.comp htm).aestronglyMeasurable C
      (ae_of_all _ fun y => hC _)
  have hgi : Integrable (fun y => φ (√(n : ℝ) * (S n y - θS n ω))) (resampleLaw O n ω) :=
    Integrable.of_bound (hφ.measurable.comp hsm).aestronglyMeasurable C
      (ae_of_all _ fun y => hC _)
  have hχi : Integrable (fun y => normCutoff m (√(n : ℝ) * (S n y - θS n ω)))
      (resampleLaw O n ω) :=
    Integrable.of_bound ((continuous_normCutoff _).measurable.comp hsm).aestronglyMeasurable 1
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (normCutoff_mem_Icc _ _).1]
        exact (normCutoff_mem_Icc _ _).2)
  have hIi : Integrable (D.indicator (1 : (Fin n → 𝒪) → ℝ)) (resampleLaw O n ω) :=
    (integrable_const (1 : ℝ)).indicator hDm
  have hχN : ∫ z, normCutoff (m : ℝ) z ∂N < η := hm
  have hχP : ∫ y, normCutoff m (√(n : ℝ) * (S n y - θS n ω)) ∂resampleLaw O n ω < 2 * η := by
    have := (abs_lt.1 hω1).2
    linarith
  have hDP : (resampleLaw O n ω).real D < η := by
    have := (abs_lt.1 hω2).2
    linarith
  rw [← integral_sub hfi hgi]
  calc |∫ y, φ (√(n : ℝ) * (T n y - θT n ω)) - φ (√(n : ℝ) * (S n y - θS n ω))
        ∂resampleLaw O n ω|
      ≤ ∫ y, |φ (√(n : ℝ) * (T n y - θT n ω)) - φ (√(n : ℝ) * (S n y - θS n ω))|
        ∂resampleLaw O n ω := abs_integral_le_integral_abs
    _ ≤ ∫ y, (ε / 2 + 2 * C * normCutoff m (√(n : ℝ) * (S n y - θS n ω)) +
          2 * C * D.indicator 1 y) ∂resampleLaw O n ω :=
        integral_mono (hfi.sub hgi).abs
          (((integrable_const _).add (hχi.const_mul _)).add (hIi.const_mul _)) hpt
    _ = ε / 2 + 2 * C * ∫ y, normCutoff m (√(n : ℝ) * (S n y - θS n ω)) ∂resampleLaw O n ω +
          2 * C * (resampleLaw O n ω).real D := by
        rw [integral_add
            (f := fun y => ε / 2 + 2 * C * normCutoff m (√(n : ℝ) * (S n y - θS n ω)))
            (g := fun y => 2 * C * D.indicator 1 y)
            ((integrable_const _).add (hχi.const_mul _)) (hIi.const_mul _),
          integral_add (f := fun _ => ε / 2)
            (g := fun y => 2 * C * normCutoff m (√(n : ℝ) * (S n y - θS n ω)))
            (integrable_const _) (hχi.const_mul _), integral_const_mul,
          integral_const_mul, integral_indicator_one hDm, integral_const, probReal_univ,
          one_smul]
    _ ≤ ε := by
        have h3 : 2 * C * ∫ y, normCutoff m (√(n : ℝ) * (S n y - θS n ω))
            ∂resampleLaw O n ω ≤ 2 * C * (2 * η) :=
          mul_le_mul_of_nonneg_left hχP.le (by positivity)
        have h4 : 2 * C * (resampleLaw O n ω).real D ≤ 2 * C * η :=
          mul_le_mul_of_nonneg_left hDP.le (by positivity)
        have h5 : 2 * C * (2 * η) + 2 * C * η ≤ ε / 2 := by
          rw [hη]
          field_simp
          nlinarith
        linarith

/-- The **bootstrap remainder**
`R_n(ω, y) = √n (T_n(y) - T̂ₙ(ω)) - √n (n⁻¹ ∑ᵢ ψ(yᵢ) - n⁻¹ ∑_{k < n} ψ(O_k(ω)))`, where
`T̂ₙ(ω) = T_n(O_0(ω), …, O_{n-1}(ω))`. -/
noncomputable def bootstrapRemainder (T : (n : ℕ) → (Fin n → 𝒪) → ℝ) (ψ : 𝒪 → ℝ)
    (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) (y : Fin n → 𝒪) : ℝ :=
  √(n : ℝ) * (T n y - T n (dataPrefix O n ω)) -
    √(n : ℝ) * (resampleMean ψ n y - sampleMean ψ O n ω)

/-- **Bootstrap linearity**: the bootstrap remainder of `T` with influence function `ψ` is small
in conditional probability, in probability. For every `ρ > 0`,
`P*(|R_n| ≥ ρ) → 0` in `P` probability, where `P*` is the resampling law given the data. -/
def IsBootstrapLinear (P : Measure Ω) (O : ℕ → Ω → 𝒪) (T : (n : ℕ) → (Fin n → 𝒪) → ℝ)
    (ψ : 𝒪 → ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → TendstoInMeasure P (fun n ω => (resampleLaw O n ω).real
    {y | ρ ≤ |bootstrapRemainder T ψ O n ω y|}) atTop (fun _ => 0)

/-- **The conditional limit law of a bootstrap linear statistic.** Let `O` be an i.i.d. sample,
`T` a measurable statistic and `ψ` measurable with `E[ψ(O_0)²] < ∞`. If `T` is bootstrap linear
with influence function `ψ`, then the bootstrap laws of `T` satisfy the weak Bernstein and von
Mises property with centering `T̂ₙ` and limit `N(0, Var ψ(O_0))`. -/
theorem IsBootstrapLinear.isBernsteinVonMisesWeak [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O P) {T : (n : ℕ) → (Fin n → 𝒪) → ℝ} (hT : ∀ n, Measurable (T n))
    {ψ : 𝒪 → ℝ} (hψ : Measurable ψ) (hψ2 : MemLp (fun ω => ψ (O 0 ω)) 2 P)
    (h : IsBootstrapLinear P O T ψ) :
    IsBernsteinVonMisesWeak P (bootstrapLaw T O) (fun n ω => T n (dataPrefix O n ω))
      (gaussianReal 0 (Var[fun ω => ψ (O 0 ω); P]).toNNReal) :=
  isBernsteinVonMisesWeak_bootstrapLaw_of_remainder (measurable_resampleMean hψ) hT
    (isBernsteinVonMisesWeak_resampleMean hO hψ hψ2) h

/-- If `0 ≤ f ≤ g + h` and `g, h → 0` in probability, then `f → 0` in probability. -/
theorem tendstoInMeasure_zero_of_le_add {f g h : ℕ → Ω → ℝ} (hf : ∀ n ω, 0 ≤ f n ω)
    (hle : ∀ n ω, f n ω ≤ g n ω + h n ω) (hg : TendstoInMeasure P g atTop (fun _ => 0))
    (hh : TendstoInMeasure P h atTop (fun _ => 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ => ?_
  have hA := (hg.withProbTendingToOne_dist_lt (half_pos hε)).inter
    (hh.withProbTendingToOne_dist_lt (half_pos hε))
  refine ⟨_, hA.eventually_le hκ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨h1, h2⟩ := hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h1 h2 ⊢
  rw [abs_of_nonneg (hf n ω)]
  linarith [le_abs_self (g n ω), le_abs_self (h n ω), hle n ω]

/-- **Bootstrap linearity is closed under linear combinations**: if `T₁` and `T₂` are bootstrap
linear with influence functions `ψ₁` and `ψ₂`, then `c₁ T₁ + c₂ T₂` is bootstrap linear with
influence function `c₁ ψ₁ + c₂ ψ₂`. -/
theorem IsBootstrapLinear.linearCombination {O : ℕ → Ω → 𝒪}
    {T₁ T₂ : (n : ℕ) → (Fin n → 𝒪) → ℝ} {ψ₁ ψ₂ : 𝒪 → ℝ} (h₁ : IsBootstrapLinear P O T₁ ψ₁)
    (h₂ : IsBootstrapLinear P O T₂ ψ₂) (c₁ c₂ : ℝ) :
    IsBootstrapLinear P O (fun n y => c₁ * T₁ n y + c₂ * T₂ n y)
      (fun z => c₁ * ψ₁ z + c₂ * ψ₂ z) := by
  intro ρ hρ
  have hrem : ∀ n ω y, bootstrapRemainder (fun n y => c₁ * T₁ n y + c₂ * T₂ n y)
      (fun z => c₁ * ψ₁ z + c₂ * ψ₂ z) O n ω y =
        c₁ * bootstrapRemainder T₁ ψ₁ O n ω y + c₂ * bootstrapRemainder T₂ ψ₂ O n ω y := by
    intro n ω y
    simp only [bootstrapRemainder, resampleMean, sampleMean, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  set ρ₁ := ρ / (2 * (|c₁| + 1)) with hρ₁
  set ρ₂ := ρ / (2 * (|c₂| + 1)) with hρ₂
  refine tendstoInMeasure_zero_of_le_add (fun _ _ => measureReal_nonneg) (fun n ω => ?_)
    (h₁ ρ₁ (by positivity)) (h₂ ρ₂ (by positivity))
  refine (measureReal_mono fun y hy => ?_).trans (measureReal_union_le _ _)
  simp only [Set.mem_ofPred_eq, hrem] at hy
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hc
  obtain ⟨hc₁, hc₂⟩ := hc
  have key : ∀ c r ρc : ℝ, ρc = ρ / (2 * (|c| + 1)) → |r| < ρc → |c| * |r| < ρ / 2 := by
    intro c r ρc hρc hr
    have hc1 : |c| + 1 ≠ 0 := by positivity
    have hpos : 0 < ρc := by rw [hρc]; positivity
    have e : (|c| + 1) * ρc = ρ / 2 := by rw [hρc]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hr.le (abs_nonneg c)]
  have := abs_add_le (c₁ * bootstrapRemainder T₁ ψ₁ O n ω y)
    (c₂ * bootstrapRemainder T₂ ψ₂ O n ω y)
  rw [abs_mul, abs_mul] at this
  linarith [key c₁ _ ρ₁ rfl hc₁, key c₂ _ ρ₂ rfl hc₂]

end Transfer

/-! ### The weighted arm mean -/

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **The conditional limit law of the bootstrapped weighted arm mean.** Let `O` be an i.i.d.
sample of records under a probability measure, `φ` a measurable feature with
`‖φ(x) - t‖ ≤ B` for all `x`, the margin condition
`P(vᵀ(φ(X) - t) ≥ δ) ≥ δ` for unit `v`, `P(A = a) > 0` and `E Y² < ∞`. If the bootstrapped weighted
arm mean is bootstrap linear with the influence function `weightedArmInfluence`, then its
bootstrap laws satisfy the weak Bernstein and von Mises property with centering `m̂ₙ` and limit
`N(0, σ²)`, `σ² = weightedArmVariance`: for every bounded continuous `f`,
`∫ f(√n (m*ₙ - m̂ₙ)) dP* → ∫ f dN(0, σ²)` in probability. -/
theorem isBernsteinVonMisesWeak_bootstrapArmMean [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (hlin : IsBootstrapLinear P O (bootstrapArmMean φ t a)
      (weightedArmInfluence (P.map (O 0)) φ t a)) :
    IsBernsteinVonMisesWeak P (bootstrapLaw (bootstrapArmMean φ t a) O)
      (sampleBalancedArmMean φ t O a)
      (gaussianReal 0 (weightedArmVariance (P.map (O 0)) φ t a).toNNReal) := by
  have hAL := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin a hq hy
  have hvar : Var[fun ω => weightedArmInfluence (P.map (O 0)) φ t a (O 0 ω); P] =
      weightedArmVariance (P.map (O 0)) φ t a := by
    have hm : AEMeasurable (fun ω => weightedArmInfluence (P.map (O 0)) φ t a (O 0 ω)) P :=
      hAL.measurable.comp_aemeasurable (hO.aemeasurable 0)
    rw [variance_of_integral_eq_zero hm hAL.integral_eq_zero, weightedArmVariance,
      integral_map (hO.aemeasurable 0) (hAL.measurable.pow_const 2).aestronglyMeasurable]
  have h := hlin.isBernsteinVonMisesWeak hO (measurable_bootstrapArmMean hφ t a) hAL.measurable
    hAL.memLp
  rw [hvar] at h
  exact h

end PopulationAdjustment

end CausalInference
