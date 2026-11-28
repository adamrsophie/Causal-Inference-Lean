/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityPopulation

/-!
# Consistency and the sample root of the stacked equations

The sample dual parameter of entropy balancing, `β̂ₙ = dualMinimizer (φ(Xᵢ) - t)ᵢ`, is the
minimizer of the convex sample objective `Fₙ(β) = n⁻¹ ∑ᵢ exp(βᵀ(φ(Xᵢ) - t))`. Under bounded
features and the margin condition it converges in probability to the population tilt
`β₀ = tiltMinimizer` (`dualMinimizer_tendstoInMeasure`): the uniform law of large numbers on a
small ball around `β₀`, the quadratic separation of the population objective and the convexity of
the sample objective trap `β̂ₙ` in the ball. The weighted arm mean then converges to the weighted
mean `m₀` of the arm under the population tilt (`sampleBalancedArmMean_tendstoInMeasure`); no
randomization, independence or outcome model is needed. The stacked estimate
`θ̂ₙ = (β̂ₙ, m̂ₙ)` is consistent for `θ₀ = (β₀, m₀)` and solves the stacked equations exactly with
probability tending to one (`weightedStackedEstimate_root`).

## Main definitions

* `sampleTilt`: the sample dual parameter `β̂ₙ`.
* `tiltArmMean`: the weighted mean `m₀` of the arm under the population tilt.
* `weightedStackedParam`, `weightedStackedEstimate`: `θ₀` and `θ̂ₙ`.

## Main results

* `dualMinimizer_tendstoInMeasure`: `β̂ₙ → β₀` in probability.
* `sampleBalancedArmMean_tendstoInMeasure`: `m̂ₙ → m₀` in probability.
* `weightedStackedEstimate_tendstoInMeasure`: `θ̂ₙ → θ₀` in probability.
* `sum_weightedEstFun_weightedStackedEstimate_eq_zero`: `θ̂ₙ` solves the sample equations on the
  feasibility event.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- The **sample dual parameter** `β̂ₙ`: the dual minimizer of entropy balancing on the first `n`
records. -/
noncomputable def sampleTilt (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (O : ℕ → Ω → 𝒳 × Bool × ℝ)
    (n : ℕ) (ω : Ω) : Fin p → ℝ :=
  dualMinimizer fun i : Fin n => φ (O i ω).1 - t

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω] in
/-- The partition function of the sample is `n` times the sample mean of the tilt. -/
theorem partitionFunction_eq_sampleMean (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (n : ℕ) (ω : Ω) (β : Fin p → ℝ) :
    partitionFunction (fun i : Fin n => φ (O i ω).1 - t) β =
      n * sampleMean (fun z => tiltWeight φ t 0 β z.1) O n ω := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [partitionFunction]
  rw [sampleMean, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul,
    partitionFunction, ← Fin.sum_univ_eq_sum_range (fun i => tiltWeight φ t 0 β (O i ω).1)]
  simp [tiltWeight]

/-- **Consistency of the sample dual parameter.** Under bounded features and the margin condition,
`β̂ₙ → β₀ = tiltMinimizer` in probability. -/
theorem dualMinimizer_tendstoInMeasure [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) :
    TendstoInMeasure P (sampleTilt φ t O) atTop (fun _ => tiltMinimizer (P.map (O 0)) φ t) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set β₀ := tiltMinimizer ν φ t with hβ₀
  have hbal := integral_tiltWeight_tiltMinimizer_mul_sub (ν := ν) hφ hB hδ hmargin
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ => ?_
  set r := min (ε / 2) 1 with hr
  have hr0 : 0 < r := lt_min (by positivity) one_pos
  set c := Real.exp (-(p * (‖β₀‖ * B))) * (r * δ) ^ 2 / 2 * δ with hc
  have hc0 : 0 < c := by positivity
  set K := Metric.closedBall β₀ r with hK
  obtain ⟨-, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall β₀ r)
    (ψ := fun z β => tiltWeight φ t 0 β z.1) (fun β _ => measurable_tiltWeight_fst hφ t β)
    (ae_of_all _ fun z => (continuous_tiltWeight_param φ t z.1).continuousOn)
    (H := fun _ => Real.exp (p * ((‖β₀‖ + r) * B))) (integrable_const _)
    (ae_of_all _ fun z β hβ => by
      rw [abs_of_pos (tiltWeight_pos _ _ _ _ _)]
      refine (tiltWeight_mem_Icc (hB z.1) ?_).2
      have := norm_le_of_mem_closedBall hβ
      linarith)
  have hev := ((withProbTendingToOne_balancingWeights_fst hO hφ hB hδ hmargin).inter
    (hunif (c / 2) (by positivity))).eventually_le hκ
  refine ⟨_, hev, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨hn, hfeas, -⟩, hω2⟩ := hω
  simp only [Set.mem_ofPred_eq] at hω2
  set Δ := fun i : Fin n => φ (O i ω).1 - t with hΔ
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i :=
    ⟨_, hfeas, fun i => entropyWeights_pos _ i⟩
  have hmin := isMinOn_dualMinimizer hpos
  set βh := dualMinimizer Δ
  change dist βh β₀ < ε
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (b := r) ?_ (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
  by_contra hfar
  replace hfar := not_le.1 hfar
  set d := ‖βh - β₀‖ with hd
  have hd0 : 0 < d := hr0.trans hfar
  set s := r / d with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := (div_le_one hd0).2 hfar.le
  set b := (1 - s) • β₀ + s • βh with hb
  have hbsub : b - β₀ = s • (βh - β₀) := by rw [hb, sub_smul, one_smul, smul_sub]; abel
  have hbn : ‖b - β₀‖ = r := by
    rw [hbsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hs, div_mul_cancel₀ _ hd0.ne']
  have hbK : b ∈ K := by rw [hK, Metric.mem_closedBall, dist_eq_norm, hbn]
  have hβ₀K : β₀ ∈ K := Metric.mem_closedBall_self hr0.le
  have hsep := tiltObjective_sub_ge (ν := ν) hφ hB hδ hmargin (hbal ·) (b - β₀)
  rw [add_sub_cancel, hbn] at hsep
  have h1 := hω2 b hbK
  have h2 := hω2 β₀ hβ₀K
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hlt : sampleMean (fun z => tiltWeight φ t 0 β₀ z.1) O n ω <
      sampleMean (fun z => tiltWeight φ t 0 b z.1) O n ω := by
    rw [← hc] at hsep
    simp only [tiltObjective] at hsep
    linarith [h1.1, h2.2]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : logPartition Δ β₀ < logPartition Δ b := by
    refine Real.log_lt_log (partitionFunction_pos β₀) ?_
    rw [partitionFunction_eq_sampleMean, partitionFunction_eq_sampleMean]
    exact mul_lt_mul_of_pos_left hlt hnR
  have hconv := (convexOn_logPartition (Δ := Δ)).2 (Set.mem_univ β₀) (Set.mem_univ βh)
    (sub_nonneg.2 hs1) hs0 (by ring)
  have hm : logPartition Δ βh ≤ logPartition Δ β₀ := hmin (Set.mem_univ β₀)
  simp only [smul_eq_mul] at hconv
  rw [← hb] at hconv
  nlinarith

/-! ### The weighted arm mean -/

/-- The **weighted mean of arm `a` under the tilt `β`**:
`E[1{A = a} w_β(X) Y] / E[1{A = a} w_β(X)]`. -/
noncomputable def tiltArmMean (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (a : Bool) (β : Fin p → ℝ) : ℝ :=
  (∫ z, armIndObs a z * tiltWeight φ t 0 β z.1 * z.2.2 ∂ν) /
    ∫ z, armIndObs a z * tiltWeight φ t 0 β z.1 ∂ν

/-- The weighted mean under the tilt is the law weighted arm mean of the tilt. -/
theorem tiltArmMean_eq_lawWeightedArmMean (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (β : Fin p → ℝ) :
    tiltArmMean ν φ t a β = lawWeightedArmMean ν (tiltWeight φ t 0 β) a := by
  have h1 : ∀ z : 𝒳 × Bool × ℝ, armIndObs a z * tiltWeight φ t 0 β z.1 =
      if z.2.1 = a then tiltWeight φ t 0 β z.1 else 0 := fun z => by
    unfold armIndObs; split_ifs <;> simp
  simp only [tiltArmMean, lawWeightedArmMean, h1]

/-- The **stacked population parameter** `θ₀ = (β₀, m₀)` of arm `a`. -/
noncomputable def weightedStackedParam (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) : EuclideanSpace ℝ (Fin p ⊕ Unit) :=
  stackedParam (tiltMinimizer ν φ t) (tiltArmMean ν φ t a (tiltMinimizer ν φ t))

/-- The **stacked estimate** `θ̂ₙ = (β̂ₙ, m̂ₙ)` of arm `a`, whose last coordinate is the weighted
arm mean `sampleBalancedArmMean`. -/
noncomputable def weightedStackedEstimate (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin p ⊕ Unit) :=
  stackedParam (sampleTilt φ t O n ω) (sampleBalancedArmMean φ t O a n ω)

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω] in
/-- The weighted arm mean is the ratio of the sample means of `1{A = a} w Y` and `1{A = a} w`
at the sample tilt `w = w_{β̂ₙ}`. -/
theorem sampleBalancedArmMean_eq_div (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) :
    sampleBalancedArmMean φ t O a n ω =
      sampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1 * z.2.2)
        O n ω /
      sampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1) O n ω := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sampleBalancedArmMean, weightedArmMean, weightedMean, sampleMean]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Δ := fun i : Fin n => φ (O i ω).1 - t
  have hw : balancingWeights Δ = fun i : Fin n => (partitionFunction Δ (sampleTilt φ t O n ω))⁻¹ *
      tiltWeight φ t 0 (sampleTilt φ t O n ω) (O i ω).1 := by
    funext i
    simp [balancingWeights, entropyWeights, tiltWeight, sampleTilt, Δ, div_eq_inv_mul]
  rw [sampleBalancedArmMean, hw,
    weightedArmMean_smul (inv_ne_zero (partitionFunction_pos _).ne'),
    weightedArmMean_eq_div_sampleMean (tiltWeight φ t 0 (sampleTilt φ t O n ω))]

/-- **Consistency of the weighted arm mean.** Under bounded features, the margin condition,
`P(A = a) > 0` and an integrable outcome, the weighted arm mean converges in probability to the
weighted mean `m₀ = tiltArmMean` of the arm under the population tilt. No randomization,
independence or outcome model is assumed. -/
theorem sampleBalancedArmMean_tendstoInMeasure [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) (P.map (O 0))) :
    TendstoInMeasure P (sampleBalancedArmMean φ t O a) atTop
      (fun _ => tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t)) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set β₀ := tiltMinimizer ν φ t with hβ₀
  have hβ := dualMinimizer_tendstoInMeasure hO hφ hB hδ hmargin
  set E := Real.exp (p * ((‖β₀‖ + 1) * B)) with hE
  have hK := Metric.closedBall_mem_nhds β₀ one_pos
  have hw : ∀ z : 𝒳 × Bool × ℝ, ∀ β ∈ Metric.closedBall β₀ 1,
      |armIndObs a z * tiltWeight φ t 0 β z.1| ≤ E := fun z β hβ => by
    have hI : armIndObs a z = 0 ∨ armIndObs a z = 1 := armIndObs_eq_zero_or_one a z
    have ht := (tiltWeight_mem_Icc (β := β) (hB z.1) (R := ‖β₀‖ + 1) (by
      have := norm_le_of_mem_closedBall hβ; linarith)).2
    rcases hI with h | h
    · rw [h, zero_mul, abs_zero]; positivity
    · rw [h, one_mul, abs_of_pos (tiltWeight_pos φ t 0 β z.1)]; exact ht
  obtain ⟨hcN, hunifN⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall β₀ 1)
    (ψ := fun z β => armIndObs a z * tiltWeight φ t 0 β z.1 * z.2.2)
    (fun β _ => ((measurable_armIndObs a).mul (measurable_tiltWeight_fst hφ t β)).mul
      measurable_snd.snd)
    (ae_of_all _ fun z => ((continuous_const.mul (continuous_tiltWeight_param φ t z.1)).mul
      continuous_const).continuousOn)
    (H := fun z => E * |z.2.2|) (hy.abs.const_mul E)
    (ae_of_all _ fun z β hβ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hw z β hβ) (abs_nonneg _))
  obtain ⟨hcD, hunifD⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall β₀ 1)
    (ψ := fun z β => armIndObs a z * tiltWeight φ t 0 β z.1)
    (fun β _ => (measurable_armIndObs a).mul (measurable_tiltWeight_fst hφ t β))
    (ae_of_all _ fun z => (continuous_const.mul
      (continuous_tiltWeight_param φ t z.1)).continuousOn)
    (H := fun _ => E) (integrable_const _) (ae_of_all _ fun z β hβ => hw z β hβ)
  have hN := hunifN.comp_tendstoInMeasure hK (hcN.continuousAt hK) hβ
  have hD := hunifD.comp_tendstoInMeasure hK (hcD.continuousAt hK) hβ
  have hD0 : (∫ z, armIndObs a z * tiltWeight φ t 0 β₀ z.1 ∂ν) ≠ 0 :=
    (integral_armIndObs_mul_tiltWeight_pos hφ hB β₀ hq).ne'
  have h := (hN.prodMk hD).comp_continuousAt (g := fun q : ℝ × ℝ => q.1 / q.2)
    (continuousAt_fst.div continuousAt_snd hD0)
  have heq : sampleBalancedArmMean φ t O a = fun n ω =>
      sampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1 * z.2.2)
        O n ω /
      sampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (sampleTilt φ t O n ω) z.1) O n ω := by
    funext n ω; exact sampleBalancedArmMean_eq_div φ t O a n ω
  rw [heq]
  exact h

/-! ### The stacked estimate -/

/-- **Consistency of the stacked estimate**: `θ̂ₙ → θ₀` in probability. -/
theorem weightedStackedEstimate_tendstoInMeasure [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) (P.map (O 0))) :
    TendstoInMeasure P (weightedStackedEstimate φ t O a) atTop
      (fun _ => weightedStackedParam (P.map (O 0)) φ t a) := by
  have hβ := dualMinimizer_tendstoInMeasure hO hφ hB hδ hmargin
  have hm := sampleBalancedArmMean_tendstoInMeasure hO hφ hB hδ hmargin a hq hy
  set X : Fin p ⊕ Unit → ℕ → Ω → ℝ := fun k => Sum.elim
    (fun j n ω => sampleTilt φ t O n ω j) (fun _ => sampleBalancedArmMean φ t O a) k with hX
  set c : Fin p ⊕ Unit → ℝ := Sum.elim (tiltMinimizer (P.map (O 0)) φ t)
    (fun _ => tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t)) with hc
  have hXc : ∀ k, TendstoInMeasure P (X k) atTop (fun _ => c k) := by
    rintro (j | u)
    · exact hβ.comp_continuousAt (g := fun β : Fin p → ℝ => β j)
        (continuous_apply j).continuousAt
    · exact hm
  have h := (tendstoInMeasure_pi hXc).comp_continuousAt (g := WithLp.toLp 2)
    (PiLp.continuous_toLp 2 _).continuousAt
  have e1 : weightedStackedEstimate φ t O a = fun n ω => WithLp.toLp 2 (fun k => X k n ω) := by
    funext n ω
    simp only [weightedStackedEstimate, stackedParam]
    congr 1
    funext k
    rcases k with j | u <;> rfl
  have e2 : weightedStackedParam (P.map (O 0)) φ t a = WithLp.toLp 2 c := by
    simp only [weightedStackedParam, stackedParam, hc]
  rw [e1, e2]
  exact h

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω] in
/-- **The stacked estimate solves the sample equations** whenever a strictly positive feasible
weight vector exists: `∑ᵢ ψ(Zᵢ; θ̂ₙ) = 0`. -/
theorem sum_weightedEstFun_weightedStackedEstimate_eq_zero (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) {n : ℕ} {ω : Ω} (hn : 0 < n)
    (hfeas : balancingWeights (fun i : Fin n => φ (O i ω).1 - t) ∈
      balancingSet (fun i : Fin n => φ (O i ω).1 - t)) :
    ∑ i ∈ range n, weightedEstFun φ t a (O i ω) (weightedStackedEstimate φ t O a n ω) = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Δ := fun i : Fin n => φ (O i ω).1 - t with hΔ
  set βh := sampleTilt φ t O n ω with hβh
  have hpos : ∃ q ∈ balancingSet Δ, ∀ i, 0 < q i := ⟨_, hfeas, fun i => entropyWeights_pos _ i⟩
  have hbal := momentBalanced_dualMinimizer hpos
  have htilt : ∀ x, tiltWeight φ t 0 (stackedBalance (weightedStackedEstimate φ t O a n ω)) x =
      tiltWeight φ t 0 βh x := fun x => rfl
  ext k
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [weightedEstFun, htilt, WithLp.ofLp_zero, Pi.zero_apply]
  rcases k with j | u
  · simp only [Sum.elim_inl]
    have h := congrFun hbal j
    simp only [sub_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => tiltWeight φ t 0 βh (O i ω).1 * (φ (O i ω).1 j - t j))]
    simpa [tiltWeight, hΔ, hβh, sampleTilt] using h
  · simp only [Sum.elim_inr]
    set m := weightedStackedEstimate φ t O a n ω (Sum.inr ())
    have hm : m = sampleBalancedArmMean φ t O a n ω := rfl
    rw [sampleBalancedArmMean_eq_div, sampleMean, sampleMean] at hm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    set SD := ∑ i ∈ range n, armIndObs a (O i ω) * tiltWeight φ t 0 βh (O i ω).1
    set SN := ∑ i ∈ range n, armIndObs a (O i ω) * tiltWeight φ t 0 βh (O i ω).1 * (O i ω).2.2
    have hsum : ∑ i ∈ range n, armIndObs a (O i ω) * tiltWeight φ t 0 βh (O i ω).1 *
        ((O i ω).2.2 - m) = SN - m * SD := by
      simp only [SN, SD, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    by_cases hSD : SD = 0
    · have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg
        (by unfold armIndObs; split_ifs <;> norm_num) (tiltWeight_pos _ _ _ _ _).le).1 hSD
      have hSN : SN = 0 := Finset.sum_eq_zero fun i hi => by rw [hall i hi, zero_mul]
      rw [hSN, hSD, mul_zero, sub_zero]
    · rw [hm, mul_div_mul_left _ _ (inv_ne_zero hnR), div_mul_cancel₀ _ hSD, sub_self]

/-- **The stacked estimate is an approximate root**: `√n (n⁻¹ ∑ᵢ ψ(Zᵢ; θ̂ₙ)) → 0` in probability,
because the sum vanishes with probability tending to one. -/
theorem weightedStackedEstimate_root [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool) :
    TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) • ((n : ℝ)⁻¹ •
      ∑ i ∈ range n, weightedEstFun φ t a (O i ω) (weightedStackedEstimate φ t O a n ω)))
      atTop (fun _ => 0) := by
  refine (tendstoInMeasure_const (μ := P)
    (0 : EuclideanSpace ℝ (Fin p ⊕ Unit))).congr_withProbTendingToOne
    (withProbTendingToOne_balancingWeights_fst hO hφ hB hδ hmargin) fun n ω hω => ?_
  obtain ⟨hn, hfeas, -⟩ := hω
  rw [sum_weightedEstFun_weightedStackedEstimate_eq_zero φ t O a hn hfeas, smul_zero, smul_zero]

end PopulationAdjustment

end CausalInference
