/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNoise

/-!
# Weighted noise with coefficients that also depend on independent data

`tendstoInMeasure_weighted_noise` is the weighted law of large numbers behind the consistency of
the weighted (matching adjusted) estimator: for coefficients `aₙᵢ` that are measurable functions
of the features `(C(O k))_{k < n}` of the sample, `∑ᵢ aₙᵢ e(O i) → 0` in probability as soon as
`∑ᵢ aₙᵢ² v(C(O i)) → 0`. When the reported target moments are themselves random (the aggregate
summary of a second sample), the coefficients depend on the features and on data `W`
independent of the sample. This file extends the law of large numbers to that case
(`tendstoInMeasure_weighted_noise_of_indepFun`).

**The argument.** For a fixed value `w` of the outside data the second moment bound
`integral_sq_weighted_noise_le` applies to the coefficients `aₙᵢ(·, w)` truncated where the
dispersion exceeds `η`. Independence of `W` and the sample turns the joint law of the pair into a
product measure, so integrating the frozen bound over the law of `W` bounds the Lebesgue integral
of the squared truncated sum by `η`; Markov's inequality finishes as in the case without outside
data.

The file also gives the noise moments of the residual of a single arm from hypotheses on that arm
only (`armResidual_noise_moments`): the regression of the other arm plays no role in the weighted
mean of arm `a`.

## Main results

* `tendstoInMeasure_weighted_noise_of_indepFun`.
* `armResidual_noise_moments`.

## References

* D. Williams, *Probability with Martingales*, Cambridge University Press (1991).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

section OutsideData

variable {Ω D 𝒞 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace 𝒞]
  [MeasurableSpace 𝒲] {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → D}
  {C : D → 𝒞} {e : D → ℝ} {v : 𝒞 → ℝ} {W : Ω → 𝒲}

/-- **A weighted law of large numbers for conditionally centered noise, with outside data.** Let
`O` be an i.i.d. sample, `C` a feature map and `e` a noise with `E[e | C] = 0` and
`E[e² | C] ≤ v(C)` under the law of a record, and let `W` be data independent of the whole
sample. Let the coefficients `aₙᵢ` be measurable functions of the feature vector
`(C(O k))_{k < n}` and of `W`, with `|aₙᵢ| ≤ 1`. If `∑ᵢ aₙᵢ² v(C(O i)) → 0` in probability, then
`∑ᵢ aₙᵢ e(O i) → 0` in probability. -/
theorem tendstoInMeasure_weighted_noise_of_indepFun (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    (hC : Measurable C) (he : Measurable e) (he2 : Integrable (fun z => e z ^ 2) (P.map (O 0)))
    (hmean : (P.map (O 0))[e | MeasurableSpace.comap C inferInstance] =ᵐ[P.map (O 0)] 0)
    (hv : Measurable v) (hv0 : ∀ c, 0 ≤ v c) (hvi : Integrable (fun z => v (C z)) (P.map (O 0)))
    (hvar : (P.map (O 0))[fun z => e z ^ 2 | MeasurableSpace.comap C inferInstance]
      ≤ᵐ[P.map (O 0)] fun z => v (C z))
    (a : (n : ℕ) → Fin n → (Fin n → 𝒞) × 𝒲 → ℝ) (ha : ∀ n i, Measurable (a n i))
    (ha1 : ∀ n i c, |a n i c| ≤ 1)
    (hD : TendstoInMeasure P
      (fun n ω => ∑ i : Fin n, a n i ((fun k => C (O k ω)), W ω) ^ 2 * v (C (O i ω))) atTop
        (fun _ => 0)) :
    TendstoInMeasure P
      (fun n ω => ∑ i : Fin n, a n i ((fun k => C (O k ω)), W ω) * e (O i ω)) atTop
        (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hD ⊢
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun _ => htop ▸ le_top
  set r := (ε / 2).toReal with hr
  have hε2 : ε / 2 ≠ ⊤ := ENNReal.div_ne_top htop (by norm_num)
  have hr0 : 0 < r := ENNReal.toReal_pos (ENNReal.half_pos hε.ne').ne' hε2
  have hrε : ENNReal.ofReal r = ε / 2 := ENNReal.ofReal_toReal hε2
  set η := r * δ ^ 2 with hη
  have hη0 : 0 < η := by positivity
  have hD' := ENNReal.tendsto_nhds_zero.1 (hD η hη0) (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [hD'] with n hn
  set Dn : (Fin n → 𝒞) × 𝒲 → ℝ := fun q => ∑ j, a n j q ^ 2 * v (q.1 j) with hDn
  have hDm : Measurable Dn :=
    Finset.measurable_sum _ fun j _ => ((ha n j).pow_const 2).mul
      (hv.comp ((measurable_pi_apply j).comp measurable_fst))
  have hD0 : ∀ q, 0 ≤ Dn q := fun q =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hv0 _)
  set b : Fin n → (Fin n → 𝒞) × 𝒲 → ℝ := fun i q => if Dn q < η then a n i q else 0 with hbdef
  have hb : ∀ i, Measurable (b i) := fun i =>
    Measurable.ite (measurableSet_lt hDm measurable_const) (ha n i) measurable_const
  have hb1 : ∀ i q, |b i q| ≤ 1 := fun i q => by
    simp only [hbdef]; split_ifs
    · exact ha1 n i q
    · simp
  have hbη : ∀ q, ∑ i, b i q ^ 2 * v (q.1 i) ≤ η := fun q => by
    by_cases hlt : Dn q < η
    · simp only [hbdef, hlt, ite_true]; exact hlt.le
    · simp only [hbdef, hlt, ite_false]; simp [hη0.le]
  set c : Ω → Fin n → 𝒞 := fun ω k => C (O k ω) with hc
  set S' : Ω → ℝ := fun ω => (∑ i, b i (c ω, W ω) * e (O i ω)) ^ 2 with hS'
  have hsub : {ω | δ ≤ dist (∑ i : Fin n, a n i (c ω, W ω) * e (O i ω)) 0} ⊆
      {ω | η ≤ dist (∑ i : Fin n, a n i (c ω, W ω) ^ 2 * v (C (O i ω))) 0} ∪
        {ω | δ ^ 2 ≤ S' ω} := by
    intro ω hω
    change δ ≤ dist (∑ i : Fin n, a n i (c ω, W ω) * e (O i ω)) 0 at hω
    rw [Real.dist_eq, sub_zero] at hω
    by_cases hlt : Dn (c ω, W ω) < η
    · right
      have : ∑ i, b i (c ω, W ω) * e (O i ω) = ∑ i, a n i (c ω, W ω) * e (O i ω) :=
        Finset.sum_congr rfl fun i _ => by simp only [hbdef, hlt, ite_true]
      change δ ^ 2 ≤ (∑ i, b i (c ω, W ω) * e (O i ω)) ^ 2
      rw [this]
      exact (pow_le_pow_left₀ hδ.le hω 2).trans (sq_abs _).le
    · left
      change η ≤ dist (Dn (c ω, W ω)) 0
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hD0 _)]
      exact not_lt.1 hlt
  -- the frozen second moment bound, integrated over the law of `W`
  set Sₐ : Ω → ℕ → D := fun ω k => O k ω with hSa
  have hSam : Measurable Sₐ := Measurable.of_eval hOm
  set H : (ℕ → D) × 𝒲 → ℝ := fun q =>
    (∑ i : Fin n, b i ((fun k : Fin n => C (q.1 k)), q.2) * e (q.1 i)) ^ 2 with hH
  have hHm : Measurable H := by
    refine (Finset.measurable_sum _ fun i _ => ((hb i).comp ?_).mul
      (he.comp ((measurable_pi_apply (i : ℕ)).comp measurable_fst))).pow_const 2
    exact (Measurable.of_eval fun k : Fin n => hC.comp ((measurable_pi_apply (k : ℕ)).comp
      measurable_fst)).prodMk measurable_snd
  have hfrozen : ∀ w : 𝒲, ∫⁻ s, ENNReal.ofReal (H (s, w)) ∂(P.map Sₐ) ≤ ENNReal.ofReal η := by
    intro w
    have hbw : ∀ i, Measurable fun x : Fin n → 𝒞 => b i (x, w) := fun i =>
      (hb i).comp (measurable_id.prodMk measurable_const)
    have hint := integrable_sq_weighted_noise hO hOm hC he he2 (fun i x => b i (x, w)) hbw
      (fun i x => hb1 i _)
    have hmom := integral_sq_weighted_noise_le hO hOm hC he he2 hmean hvi hvar
      (fun i x => b i (x, w)) hbw (fun i x => hb1 i _)
    have hbd : ∫ ω, ∑ i, b i ((fun k => C (O k ω)), w) ^ 2 * v (C (O i ω)) ∂P ≤ η :=
      (integral_mono_of_nonneg (Eventually.of_forall fun ω => Finset.sum_nonneg fun i _ =>
        mul_nonneg (sq_nonneg _) (hv0 _)) (integrable_const η)
        (Eventually.of_forall fun ω => hbη ((fun k => C (O k ω)), w))).trans (by simp)
    rw [lintegral_map (f := fun s => ENNReal.ofReal (H (s, w))) (ENNReal.measurable_ofReal.comp
      (hHm.comp (measurable_id.prodMk measurable_const))) hSam]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hmom.trans hbd)
  have hjoint : P.map (fun ω => (Sₐ ω, W ω)) = (P.map Sₐ).prod (P.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map hSam.aemeasurable hW.aemeasurable).1 hWO.symm
  have hlint : ∫⁻ ω, ENNReal.ofReal (S' ω) ∂P ≤ ENNReal.ofReal η := by
    have h1 : ∫⁻ ω, ENNReal.ofReal (S' ω) ∂P =
        ∫⁻ q, ENNReal.ofReal (H q) ∂(P.map fun ω => (Sₐ ω, W ω)) := by
      rw [lintegral_map (f := fun q => ENNReal.ofReal (H q)) (ENNReal.measurable_ofReal.comp hHm)
        (hSam.prodMk hW)]
    rw [h1, hjoint, lintegral_prod_symm (fun q => ENNReal.ofReal (H q))
      (ENNReal.measurable_ofReal.comp hHm).aemeasurable]
    calc ∫⁻ w, ∫⁻ s, ENNReal.ofReal (H (s, w)) ∂(P.map Sₐ) ∂(P.map W)
        ≤ ∫⁻ _w, ENNReal.ofReal η ∂(P.map W) := lintegral_mono fun w => hfrozen w
      _ = ENNReal.ofReal η := by
          rw [lintegral_const, measure_univ, mul_one]
  have hS'm : Measurable S' :=
    (Finset.measurable_sum _ fun i _ => ((hb i).comp ((Measurable.of_eval fun k : Fin n =>
      hC.comp (hOm k)).prodMk hW)).mul (he.comp (hOm i))).pow_const 2
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := P) (f := fun ω => ENNReal.ofReal (S' ω))
    (ENNReal.measurable_ofReal.comp hS'm).aemeasurable (ENNReal.ofReal (δ ^ 2))
  have hsub2 : {ω | δ ^ 2 ≤ S' ω} ⊆ {ω | ENNReal.ofReal (δ ^ 2) ≤ ENNReal.ofReal (S' ω)} :=
    fun ω hω => ENNReal.ofReal_le_ofReal hω
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hbound : P {ω | δ ^ 2 ≤ S' ω} ≤ ε / 2 := by
    have h2 : ENNReal.ofReal (δ ^ 2) * P {ω | δ ^ 2 ≤ S' ω} ≤ ENNReal.ofReal η :=
      (mul_le_mul_right (measure_mono hsub2) _).trans (hmarkov.trans hlint)
    rw [hη, ENNReal.ofReal_mul hr0.le, mul_comm (ENNReal.ofReal r)] at h2
    have hne : ENNReal.ofReal (δ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hδ2).ne'
    rw [← hrε]
    exact (ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).1 h2
  calc P {ω | δ ≤ dist (∑ i : Fin n, a n i (c ω, W ω) * e (O i ω)) 0}
      ≤ P ({ω | η ≤ dist (∑ i : Fin n, a n i (c ω, W ω) ^ 2 * v (C (O i ω))) 0} ∪
          {ω | δ ^ 2 ≤ S' ω}) := measure_mono hsub
    _ ≤ P {ω | η ≤ dist (∑ i : Fin n, a n i (c ω, W ω) ^ 2 * v (C (O i ω))) 0} +
          P {ω | δ ^ 2 ≤ S' ω} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hbound
    _ = ε := ENNReal.add_halves ε

end OutsideData

/-! ### The residual of a single arm -/

section ArmResidual

open PointTreatment

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)} [IsProbabilityMeasure ν]

omit [MeasurableSpace 𝒳] in
theorem armIndObs_mul_sq (a : Bool) (z : 𝒳 × Bool × ℝ) (r : ℝ) :
    (armIndObs a z * r) ^ 2 = armIndObs a z * r ^ 2 := by
  rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> ring

/-- **Noise moments of the residual of one arm.** Let `m` be measurable and assume, under the
record law, that the residual of arm `a` is square integrable on the arm,
`E[1{A = a}(Y - m(X))²] < ∞`, that `E[1{A = a} Y | X, A] = 1{A = a} m(X)` (the regression of
arm `a`) and `E[1{A = a}(Y - m(X))² | X, A] ≤ σ²`. Then the residual `1{A = a}(Y - m(X))` has
`E[· | X, A] = 0` and `E[(·)² | X, A] ≤ max σ² 0`. Nothing is assumed about the other arm. The
outcome on the arm is integrable: otherwise its conditional expectation is `0`, so
`1{A = a} m(X) = 0` and the outcome equals the integrable residual. -/
theorem armResidual_noise_moments (a : Bool) {m : 𝒳 → ℝ} (hm : Measurable m)
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2) ν)
    (hreg : ν[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν]
        fun z => armIndObs a z * m z.1) {σ2 : ℝ}
    (hvar : ν[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[ν] fun _ => σ2) :
    ν[fun z => armIndObs a z * (z.2.2 - m z.1) | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] 0 ∧
    ν[fun z => (armIndObs a z * (z.2.2 - m z.1)) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[ν] fun _ => max σ2 0 := by
  have hpair : Measurable fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have hm𝓜 : MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
      (inferInstance : MeasurableSpace (𝒳 × Bool)) ≤
        (inferInstance : MeasurableSpace (𝒳 × Bool × ℝ)) :=
    hpair.comap_le
  have hsq : (fun z : 𝒳 × Bool × ℝ => (armIndObs a z * (z.2.2 - m z.1)) ^ 2) =
      fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 := funext fun z => armIndObs_mul_sq a z _
  have hA := measurable_armIndObs (𝒲 := 𝒳) a
  have he : Measurable fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) :=
    hA.mul (measurable_snd.snd.sub (hm.comp measurable_fst))
  have he2 : Integrable (fun z : 𝒳 × Bool × ℝ => (armIndObs a z * (z.2.2 - m z.1)) ^ 2) ν := by
    rw [hsq]; exact hres2
  have heI : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1)) ν :=
    ((memLp_two_iff_integrable_sq he.aestronglyMeasurable).2 he2).integrable one_le_two
  have hIY : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * z.2.2) ν := by
    by_contra hY
    have h0 : ν[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
        (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] = 0 := condExp_of_not_integrable hY
    have hm0 : (fun z : 𝒳 × Bool × ℝ => armIndObs a z * m z.1) =ᵐ[ν] 0 :=
      hreg.symm.trans (by rw [h0])
    refine hY (heI.congr (hm0.mono fun z hz => ?_))
    simp only [Pi.zero_apply] at hz
    simp only [mul_sub, hz, sub_zero]
  have hIm : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * m z.1) ν :=
    (hIY.sub heI).congr (ae_of_all _ fun z => by simp only [Pi.sub_apply]; ring)
  have hsm : StronglyMeasurable[MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
      (inferInstance : MeasurableSpace (𝒳 × Bool))]
        fun z : 𝒳 × Bool × ℝ => armIndObs a z * m z.1 := by
    have hq : Measurable fun q : 𝒳 × Bool => (if q.2 = a then (1 : ℝ) else 0) * m q.1 :=
      (Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
        measurable_const).mul (hm.comp measurable_fst)
    exact (hq.comp (comap_measurable _)).stronglyMeasurable
  refine ⟨?_, ?_⟩
  · have hsplit : (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1)) =
        (fun z => armIndObs a z * z.2.2) - fun z => armIndObs a z * m z.1 :=
      funext fun z => by simp only [Pi.sub_apply]; ring
    rw [hsplit]
    filter_upwards [condExp_sub hIY hIm (MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance), hreg] with z h1 h2
    rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable hm𝓜 hsm hIm]
    simp
  · rw [hsq]
    exact hvar.mono fun z hz => hz.trans (le_max_left _ _)

end ArmResidual

end PopulationAdjustment

end CausalInference
