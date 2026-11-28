/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderInstances
public import CausalInference.PopulationAdjustment.EffectiveSampleSize

/-!
# Weights with an infinite second moment: the effective sample size fraction vanishes

When the population weight `w*(X) = exp(β*ᵀ(φ(X) - t))` has `E[w*] < ∞` but `E[w*²] = ∞`, the
effective sample size of i.i.d. weights is a vanishing fraction of the sample:
`ess(w(O₁), …, w(Oₙ)) / n = (n⁻¹ ∑ wᵢ)² / (n⁻¹ ∑ wᵢ²) → 0` in probability
(`tendstoInMeasure_ess_div_zero`). The numerator converges to `(E w)²` by the law of large
numbers; the denominator exceeds the sample mean of the truncation `min(w², M)`, which converges
to `E[min(w², M)]`, and these means are unbounded in `M` by monotone convergence.

**The exponential law at `t = 2`.** For the standard exponential law with the feature `x` and the
target `t = 2`, the population dual minimizer is `β* = 1/2` and `E[w*²] = E[exp(X - 2)] = ∞`
(`integrable_sq_tilt_expMeasure_iff`); the order condition of the consistency theorems fails
(`exists_order_expMeasure_iff`). For an i.i.d. sample of the coin trial over this law the
effective sample size fraction of the population weights tends to zero in probability
(`momentOrderInst_ess_div_tendsto_zero`).

## Main results

* `iSup_ofReal_min_natCast`, `tendstoInMeasure_ess_div_zero`.
* `integrable_fst_ipdLaw_iff`, `momentOrderInst_ess_div_tendsto_zero`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

/-- `⨆ M, min(x, M) = x` in `[0, ∞]` for real `x`, over natural `M`. -/
theorem iSup_ofReal_min_natCast (x : ℝ) :
    ⨆ M : ℕ, ENNReal.ofReal (min x M) = ENNReal.ofReal x := by
  refine le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  obtain ⟨M, hM⟩ := exists_nat_ge x
  exact (le_of_eq (by rw [min_eq_left hM])).trans (le_iSup (fun M : ℕ =>
    ENNReal.ofReal (min x M)) M)

section ESS

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪] {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}

/-- **The effective sample size fraction vanishes for weights of infinite second moment.** Let
`O` be a measurable i.i.d. sample and `w` a measurable, strictly positive weight with `E[w] < ∞`
and `E[w²] = ∞`. Then `ess(w(O₁), …, w(Oₙ)) / n → 0` in probability. -/
theorem tendstoInMeasure_ess_div_zero (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {w : 𝒪 → ℝ} (hw : Measurable w) (hpos : ∀ z, 0 < w z) (hi : Integrable w (P.map (O 0)))
    (hni : ¬ Integrable (fun z => w z ^ 2) (P.map (O 0))) :
    TendstoInMeasure P (fun n ω => ess (fun i : Fin n => w (O i ω)) / n) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  have hmap : ∀ F : 𝒪 → ℝ, Measurable F → ∫ ω, F (O 0 ω) ∂P = ∫ z, F z ∂ν := fun F hF =>
    (integral_map (hO.aemeasurable 0) hF.aestronglyMeasurable).symm
  -- the mean of the weight
  have hiP := integrable_comp_of_isIIDSample hO hOm hi 0
  set a : ℝ := ∫ ω, w (O 0 ω) ∂P with ha
  have ha0 : 0 < a := by
    rw [ha, integral_pos_iff_support_of_nonneg (fun ω => (hpos _).le) hiP]
    have : Function.support (fun ω => w (O 0 ω)) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (hpos _).ne'
    rw [this, measure_univ]; exact one_pos
  -- the truncated second moments are unbounded
  have hw2 : Measurable fun z => w z ^ 2 := hw.pow_const 2
  have hlin : ∫⁻ z, ENNReal.ofReal (w z ^ 2) ∂ν = ⊤ := by
    by_contra h
    exact hni ⟨hw2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun z => sq_nonneg _)).2 (lt_top_iff_ne_top.2 h)⟩
  have hmt : ∀ M : ℕ, Measurable fun z => min (w z ^ 2) (M : ℝ) := fun M =>
    hw2.min measurable_const
  have hsup : ⨆ M : ℕ, ∫⁻ z, ENNReal.ofReal (min (w z ^ 2) (M : ℝ)) ∂ν = ⊤ := by
    rw [← lintegral_iSup (fun M => (hmt M).ennreal_ofReal) (fun M N hMN z =>
      ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hMN)))]
    simp only [iSup_ofReal_min_natCast]
    exact hlin
  refine tendstoInMeasure_of_good_events fun η hη κ hκ => ?_
  set K : ℝ := 4 * a ^ 2 / η + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ENNReal.ofReal (2 * K) <
      ∫⁻ z, ENNReal.ofReal (min (w z ^ 2) (M : ℝ)) ∂ν := by
    rw [← lt_iSup_iff, hsup]; exact ENNReal.ofReal_lt_top
  set m : 𝒪 → ℝ := fun z => min (w z ^ 2) (M : ℝ) with hm
  have hmi : Integrable m ν :=
    (integrable_const (M : ℝ)).mono' (hmt M).aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) (Nat.cast_nonneg M))]
      exact min_le_right _ _)
  set c : ℝ := ∫ ω, m (O 0 ω) ∂P with hc
  have hcK : 2 * K < c := by
    rw [hc, hmap m (hmt M), ← ofReal_integral_eq_lintegral_ofReal hmi
      (ae_of_all _ fun z => le_min (sq_nonneg _) (Nat.cast_nonneg M))] at *
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 hM
  have hmP := integrable_comp_of_isIIDSample hO hOm hmi 0
  have h1 := (sampleMean_isConsistent hO hw hiP).withProbTendingToOne_dist_lt ha0
  have h2 := (sampleMean_isConsistent hO (hmt M) hmP).withProbTendingToOne_dist_lt
    (half_pos (hK0.trans (by linarith : K < c)))
  refine ⟨_, ((withProbTendingToOne_pos (P := P)).inter (h1.inter h2)).eventually_le hκ,
    Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨hn, hd1, hd2⟩ := hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hn hd1 hd2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmean : ∀ F : 𝒪 → ℝ, ∑ i : Fin n, F (O i ω) = n * sampleMean F O n ω := by
    intro F
    rw [sampleMean, ← Fin.sum_univ_eq_sum_range (fun i => F (O i ω)) n, ← mul_assoc,
      mul_inv_cancel₀ hn'.ne', one_mul]
  set m1 := sampleMean w O n ω with hm1
  set q := sampleMean (fun z => w z ^ 2) O n ω with hq
  set m2 := sampleMean m O n ω with hm2
  have hqm : m2 ≤ q := by
    rw [hm2, hq, sampleMean, sampleMean]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => min_le_left _ _)
      (inv_nonneg.2 hn'.le)
  have hm1pos : 0 < m1 := by
    rw [hm1, sampleMean]
    exact mul_pos (inv_pos.2 hn') (Finset.sum_pos (fun i _ => hpos _)
      (Finset.nonempty_range_iff.2 hn.ne'))
  have hm1a : m1 < 2 * a := by have := (abs_lt.1 hd1).2; linarith
  have hm2K : K < m2 := by have := (abs_lt.1 hd2).1; linarith
  have hqpos : 0 < q := hK0.trans (hm2K.trans_le hqm)
  have hess : ess (fun i : Fin n => w (O i ω)) / n = m1 ^ 2 / q := by
    rw [ess, hmean w, hmean (fun z => w z ^ 2), ← hm1, ← hq]
    field_simp
  rw [hess, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_lt_iff₀ hqpos]
  have h4 : m1 ^ 2 < 4 * a ^ 2 := by nlinarith
  have h5 : η * K = 4 * a ^ 2 + η := by rw [hK]; field_simp
  nlinarith

end ESS

/-! ### The exponential law at `t = 2` -/

section Exponential

variable {Ω₁ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳]

/-- A function of the covariate is integrable under the individual data law of a trial exactly
when it is integrable under the covariate law. -/
theorem integrable_fst_ipdLaw_iff [MeasurableSpace ι] {T : Trial Ω₁ 𝒳 ι} (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) {F : 𝒳 → ℝ} (hF : Measurable F) :
    Integrable (fun z : 𝒳 × ι × ℝ => F z.1) T.ipdLaw ↔ Integrable F T.covLaw := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hm2 : Measurable fun z : 𝒳 × ι × ℝ => F z.1 := hF.comp measurable_fst
  rw [Trial.ipdLaw, Population.covLaw,
    integrable_map_measure hm2.aestronglyMeasurable hf.aemeasurable,
    integrable_map_measure hF.aestronglyMeasurable hX.aemeasurable]
  rfl

/-- **The effective sample size fraction vanishes at `t = 2` for the exponential law.** In the
coin trial over the standard exponential law, the population weight at the target `t = 2` is
`w*(X) = exp((X - 2) / 2)` (`β* = 1/2`), with `E[w*] < ∞` and `E[w*²] = ∞`; the effective sample
size fraction `ess(w*(X₁), …, w*(Xₙ)) / n` of an i.i.d. sample of records tends to zero in
probability. -/
theorem momentOrderInst_ess_div_tendsto_zero :
    TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
      (fun n ω => ess (fun i : Fin n => Real.exp (featureLineVec (1 - 1 / 2) ⬝ᵥ
        ((sharpInstSample momentOrderExpLaw sharpInstOutcome i ω).1 - featureLineVec 2))) / n)
      atTop (fun _ => 0) := by
  have hf := measurable_sharpInstOutcome
  have hκ0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hexp := (integrable_exp_momentOrderExpLaw_iff 2 (1 / 2)).2 (by norm_num)
  have hfi : Integrable (sharpInstOutcome true) momentOrderExpLaw := by
    rw [show sharpInstOutcome true = fun x => 1 + featureLineVec 2 ⬝ᵥ x from
      funext sharpInstOutcome_true]
    exact integrable_affine_of_integrable_exp_pos hκ0 hexp 1 _
  obtain ⟨hX, hA, hYo, -⟩ := sharpInstTrial_hypotheses hf true hfi
  have hcov := sharpInstTrial_covLaw (lam := momentOrderExpLaw) (f := sharpInstOutcome)
  set F : (Fin 1 → ℝ) → ℝ := fun y =>
    Real.exp (featureLineVec (1 - 1 / 2) ⬝ᵥ (y - featureLineVec 2)) with hF
  have hFm : Measurable F := by fun_prop
  have hlawF : ∀ G : (Fin 1 → ℝ) → ℝ, Measurable G →
      (Integrable G momentOrderExpLaw ↔ Integrable (G ∘ featureLineVec) (expMeasure 1)) :=
    fun G hG => by
      rw [momentOrderExpLaw, integrable_map_measure hG.aestronglyMeasurable
        measurable_featureLineVec.aemeasurable]
  have hrec : ∀ G : (Fin 1 → ℝ) → ℝ, Measurable G →
      (Integrable (fun z : (Fin 1 → ℝ) × Bool × ℝ => G z.1)
        ((sharpInstLaw momentOrderExpLaw sharpInstOutcome).map
          (sharpInstSample momentOrderExpLaw sharpInstOutcome 0)) ↔
        Integrable (G ∘ featureLineVec) (expMeasure 1)) := fun G hG => by
    rw [map_sharpInstSample hf 0, integrable_fst_ipdLaw_iff hX hA hYo hG, hcov, hlawF G hG]
  have hFe : F ∘ featureLineVec = fun x => Real.exp (-1) * Real.exp ((1 / 2) * x) := by
    funext x
    simp only [hF, Function.comp_apply, dotProduct_featureLineVec_sub, featureLineVec]
    rw [← Real.exp_add]; ring_nf
  have hF2e : (fun y => F y ^ 2) ∘ featureLineVec =
      fun x => Real.exp (-2) * Real.exp (1 * x) := by
    funext x
    simp only [hF, Function.comp_apply, dotProduct_featureLineVec_sub, featureLineVec]
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have hi : Integrable (fun z : (Fin 1 → ℝ) × Bool × ℝ => F z.1)
      ((sharpInstLaw momentOrderExpLaw sharpInstOutcome).map
        (sharpInstSample momentOrderExpLaw sharpInstOutcome 0)) := by
    rw [hrec F hFm, hFe]
    exact ((integrable_exp_mul_expMeasure_iff).2 (by norm_num)).const_mul _
  have hni : ¬ Integrable (fun z : (Fin 1 → ℝ) × Bool × ℝ => F z.1 ^ 2)
      ((sharpInstLaw momentOrderExpLaw sharpInstOutcome).map
        (sharpInstSample momentOrderExpLaw sharpInstOutcome 0)) := by
    rw [hrec (fun y => F y ^ 2) (hFm.pow_const 2), hF2e,
      integrable_const_mul_iff (isUnit_iff_ne_zero.2 (Real.exp_pos _).ne'),
      integrable_exp_mul_expMeasure_iff]
    exact lt_irrefl _
  have hpos : ∀ z : (Fin 1 → ℝ) × Bool × ℝ, 0 < F z.1 := fun z => by
    rw [hF]; exact Real.exp_pos _
  exact tendstoInMeasure_ess_div_zero (w := fun z : (Fin 1 → ℝ) × Bool × ℝ => F z.1)
    (isIIDSample_sharpInstSample hf) (measurable_sharpInstSample hf) (hFm.comp measurable_fst)
    hpos hi hni

end Exponential

end PopulationAdjustment

end CausalInference
