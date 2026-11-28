/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.CrossFitting
public import CausalInference.Efficiency.ProductBias
public import CausalInference.Estimation.Consistency
public import Mathlib.Topology.EMetricSpace.Weak

/-!
# The remainder of the cross fitted augmented estimator

The fold remainder `R_{n,k} = n⁻¹ ∑_{i ∈ I_{n,k}} (aipwScore ê m̂ a - aipwScore e m a)(O_i)` of
the cross fitted estimator (`CausalInference.Efficiency.CrossFitting`) is `o_P(n^{-1/2})` as soon
as the out of fold `L²(P_W)` errors of the two learners tend to zero in probability and the
product of the two errors is `o_P(n^{-1/2})` (`tendstoInMeasure_sqrt_mul_foldRemainder`).
Nothing else is assumed about the remainder.

The proof conditions on the training data of the fold. Given the training data `t`, the summands
of the fold are i.i.d. with mean `E[aipwScore ê_t m̂_t a] - E[Y(a)]`, so the remainder splits into

* a centered term, controlled by the conditional Chebyshev inequality
  `measure_le_abs_sum_sub_integral_le`: its conditional variance is at most `n⁻¹` times the
  squared `L²` norm of the summand difference, and that norm tends to zero in probability by
  `eLpNorm_aipwScore_sub_le`. The bound uses only square integrability of the outcome: the part
  of the residual above a truncation level is uniformly small in `L²`, and below it the error of
  the score enters linearly;
* a bias term, at most `ε'⁻¹ √n ‖ê - e‖₂ ‖m̂(a, ·) - m(a, ·)‖₂` by the product bias bound
  (`ofReal_abs_integral_aipwScore_sub_le`, from `abs_integral_aipwScore_sub_armMean_le`).

The `L²` errors take values in `[0, ∞]` (`fitError`), so a learner whose output is not square
integrable has infinite error and no rate hypothesis can hold for it by convention.

## Main definitions

* None: the file bounds the fold remainder `foldRemainder` of
  `CausalInference.Efficiency.CrossFitting`.

## Main results

* `MemLp.eLpNorm_two_eq_ofReal_sqrt`: the `L²` norm as `√(∫ f²)`.
* `tendstoInMeasure_zero_iff_ofReal`, `tendstoInMeasure_add_ennreal`: convergence in probability
  of `[0, ∞]`-valued errors.
* `measure_le_abs_sum_sub_integral_le`: the conditional Chebyshev inequality for a fold.
* `eLpNorm_aipwScore_sub_le`: the `L²` error of the fitted summand.
* `ofReal_abs_integral_aipwScore_sub_le`: the bias of the fitted summand.
* `tendstoInMeasure_sqrt_mul_foldRemainder`: the fold remainder is `o_P(n^{-1/2})`.

## References

* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, The Econometrics
  Journal 21 (2018).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory MissingData PointTreatment Filter Finset
open scoped ENNReal Topology

variable {Ω' 𝒪 : Type*} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace 𝒪]

section Tools

omit [MeasurableSpace 𝒪] in
/-- The `L²` norm of a square integrable real function is `√(∫ f²)`. -/
theorem MemLp.eLpNorm_two_eq_ofReal_sqrt {μ : Measure Ω'} {f : Ω' → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal √(∫ ω, f ω ^ 2 ∂μ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow]
  congr 2
  · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    rw [Real.rpow_two, sq_abs]
  · norm_num

omit [MeasurableSpace 𝒪] in
/-- Convergence in probability to `0` of `[0, ∞]`-valued variables, tested on finite levels. -/
theorem tendstoInMeasure_zero_iff_ofReal {P : Measure Ω'} {f : ℕ → Ω' → ℝ≥0∞} :
    TendstoInMeasure P f atTop 0 ↔
      ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | ENNReal.ofReal δ ≤ f n ω}) atTop (𝓝 0) := by
  simp only [TendstoInMeasure, Pi.zero_apply, ENNReal.edist_zero_right]
  refine ⟨fun h δ hδ => h _ (ENNReal.ofReal_pos.2 hδ), fun h δ hδ => ?_⟩
  rcases eq_or_ne δ ∞ with rfl | hδt
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h 1 one_pos)
      (fun n => bot_le) fun n => measure_mono fun ω (hω : ∞ ≤ f n ω) => le_top.trans hω
  · have h' := h δ.toReal (ENNReal.toReal_pos hδ.ne' hδt)
    rwa [ENNReal.ofReal_toReal hδt] at h'

omit [MeasurableSpace 𝒪] in
/-- A sum `a f_n + b g_n` of `[0, ∞]`-valued variables tending to `0` in probability, with finite
coefficients, tends to `0` in probability. -/
theorem tendstoInMeasure_add_ennreal {P : Measure Ω'} {f g : ℕ → Ω' → ℝ≥0∞}
    (hf : TendstoInMeasure P f atTop 0) (hg : TendstoInMeasure P g atTop 0) {a b : ℝ} :
    TendstoInMeasure P (fun n ω => ENNReal.ofReal a * f n ω + ENNReal.ofReal b * g n ω)
      atTop 0 := by
  rw [tendstoInMeasure_zero_iff_ofReal] at hf hg ⊢
  intro δ hδ
  set a' := max a 1
  set b' := max b 1
  have ha' : 0 < a' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb' : 0 < b' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have key : ∀ n, P {ω | ENNReal.ofReal δ ≤ ENNReal.ofReal a * f n ω + ENNReal.ofReal b * g n ω}
      ≤ P {ω | ENNReal.ofReal (δ / 2 / a') ≤ f n ω} +
        P {ω | ENNReal.ofReal (δ / 2 / b') ≤ g n ω} := by
    intro n
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    have h1 : ENNReal.ofReal a * f n ω < ENNReal.ofReal (δ / 2) := by
      calc ENNReal.ofReal a * f n ω ≤ ENNReal.ofReal a' * f n ω := by
            gcongr; exact le_max_left _ _
        _ < ENNReal.ofReal a' * ENNReal.ofReal (δ / 2 / a') :=
            ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.2 ha').ne' ENNReal.ofReal_ne_top
              hcon.1
        _ = ENNReal.ofReal (δ / 2) := by
            rw [← ENNReal.ofReal_mul ha'.le]; congr 1; field_simp
    have h2 : ENNReal.ofReal b * g n ω < ENNReal.ofReal (δ / 2) := by
      calc ENNReal.ofReal b * g n ω ≤ ENNReal.ofReal b' * g n ω := by
            gcongr; exact le_max_left _ _
        _ < ENNReal.ofReal b' * ENNReal.ofReal (δ / 2 / b') :=
            ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.2 hb').ne' ENNReal.ofReal_ne_top
              hcon.2
        _ = ENNReal.ofReal (δ / 2) := by
            rw [← ENNReal.ofReal_mul hb'.le]; congr 1; field_simp
    have := ENNReal.add_lt_add h1 h2
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at this
    exact absurd hω (not_le.2 this)
  have hsum := (hf (δ / 2 / a') (by positivity)).add (hg (δ / 2 / b') (by positivity))
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => bot_le)
    key

/-- A sequence in `[0, ∞]` tends to `0` when, for every `r > 0`, it is eventually bounded by a
sequence tending to `0` plus `r`. -/
theorem tendsto_zero_of_le_add_ofReal {g : ℕ → ℝ≥0∞}
    (h : ∀ r : ℝ, 0 < r → ∃ b : ℕ → ℝ≥0∞, Tendsto b atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, g n ≤ b n + ENNReal.ofReal r) :
    Tendsto g atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  rcases eq_or_ne δ ⊤ with hδt | hδt
  · exact Eventually.of_forall fun n => by rw [hδt]; exact le_top
  have hδr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  obtain ⟨b, hb, hgb⟩ := h (δ.toReal / 2) (by positivity)
  have hb' := ENNReal.tendsto_nhds_zero.1 hb (ENNReal.ofReal (δ.toReal / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  filter_upwards [hgb, hb'] with n h1 h2
  calc g n ≤ b n + ENNReal.ofReal (δ.toReal / 2) := h1
    _ ≤ ENNReal.ofReal (δ.toReal / 2) + ENNReal.ofReal (δ.toReal / 2) := by gcongr
    _ = δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
          ENNReal.ofReal_toReal hδt]

end Tools

section Chebyshev

variable {𝒯 : Type*} [MeasurableSpace 𝒯]

/-- **Conditional Chebyshev inequality for a cross fitted fold.** Let `O` be an i.i.d. sample
with law `ν = P_{O_0}`, `I` a finite set of evaluation units, and `T` a training statistic
independent of `(O_i)_{i ∈ I}`. For a jointly measurable `F(t, z)` and `|I| ≤ r²`,
`P(η ≤ |r⁻¹ ∑_{i ∈ I} (F(T, O_i) - ν F(T, ·))|) ≤ P(c ≤ ‖F(T, ·)‖_{L²(ν)}) + c² / η²`.
By independence the law of `(T, (O_i)_{i ∈ I})` is a product, so the probability is an integral
over the training value `t` of the probability for fixed `t`; where `‖F(t, ·)‖_{L²(ν)} < c`,
Chebyshev's inequality and the additivity of the variance over independent terms bound it by
`c² / η²`. -/
theorem measure_le_abs_sum_sub_integral_le {P : Measure Ω'}
    [IsProbabilityMeasure P] {O : ℕ → Ω' → 𝒪} (hO : IsIIDSample O P) {I : Finset ℕ}
    {T : Ω' → 𝒯} (hT : AEMeasurable T P) (hind : IndepFun T (fun ω (i : I) => O i ω) P)
    {F : 𝒯 × 𝒪 → ℝ} (hF : Measurable F) {r η c : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hI : (I.card : ℝ) ≤ r ^ 2) :
    P {ω | η ≤ |r⁻¹ * ∑ i ∈ I, (F (T ω, O i ω) - ∫ z, F (T ω, z) ∂(P.map (O 0)))|} ≤
      P {ω | ENNReal.ofReal c ≤ eLpNorm (fun z => F (T ω, z)) 2 (P.map (O 0))} +
        ENNReal.ofReal (c ^ 2 / η ^ 2) := by
  set ν := P.map (O 0) with hν
  set Pf : 𝒯 → ℝ := fun t => ∫ z, F (t, z) ∂ν with hPfdef
  have hPf : Measurable Pf := hF.stronglyMeasurable.integral_prod_right'.measurable
  set D : 𝒯 → ℝ≥0∞ := fun t => eLpNorm (fun z => F (t, z)) 2 ν with hDdef
  have hD : Measurable D := measurable_eLpNorm_two hF ν
  set V : Ω' → (I → 𝒪) := fun ω i => O i ω with hVdef
  have hV : AEMeasurable V P := AEMeasurable.of_eval fun i => hO.aemeasurable i
  set H : 𝒯 × (I → 𝒪) → ℝ := fun p => r⁻¹ * ∑ i : I, (F (p.1, p.2 i) - Pf p.1) with hHdef
  have hH : Measurable H := measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (hF.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).sub
      (hPf.comp measurable_fst))
  set B : Set (𝒯 × (I → 𝒪)) := {p | η ≤ |H p|} with hBdef
  have hB : MeasurableSet B := measurableSet_le measurable_const (continuous_abs.measurable.comp hH)
  have hev : {ω | η ≤ |r⁻¹ * ∑ i ∈ I, (F (T ω, O i ω) - ∫ z, F (T ω, z) ∂ν)|} =
      (fun ω => (T ω, V ω)) ⁻¹' B := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hBdef, hHdef, hVdef, hPfdef]
    rw [Finset.sum_coe_sort I (fun i => F (T ω, O i ω) - ∫ z, F (T ω, z) ∂ν)]
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hT hV).mp hind
  -- the bound for a fixed training value
  have hinner : ∀ t, (P.map V) (Prod.mk t ⁻¹' B) ≤
      {t | ENNReal.ofReal c ≤ D t}.indicator 1 t + ENNReal.ofReal (c ^ 2 / η ^ 2) := by
    intro t
    by_cases ht : ENNReal.ofReal c ≤ D t
    · rw [Set.indicator_of_mem (show t ∈ {t | ENNReal.ofReal c ≤ D t} from ht), Pi.one_apply]
      exact prob_le_one.trans le_self_add
    rw [Set.indicator_of_notMem (show t ∉ {t | ENNReal.ofReal c ≤ D t} from ht), zero_add]
    rw [not_le] at ht
    rw [Measure.map_apply_of_aemeasurable hV (measurable_prodMk_left hB)]
    have hft : Measurable fun z => F (t, z) := hF.comp measurable_prodMk_left
    have hF2 : MemLp (fun z => F (t, z)) 2 ν := ht.trans ENNReal.ofReal_lt_top
    have hsq : ∫ z, F (t, z) ^ 2 ∂ν ≤ c ^ 2 := by
      have hc : √(∫ z, F (t, z) ^ 2 ∂ν) < c := by
        have h : eLpNorm (fun z => F (t, z)) 2 ν < ENNReal.ofReal c := ht
        rw [MemLp.eLpNorm_two_eq_ofReal_sqrt hF2] at h
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).1 h
      have h0 : 0 ≤ ∫ z, F (t, z) ^ 2 ∂ν := integral_nonneg fun z => sq_nonneg _
      calc ∫ z, F (t, z) ^ 2 ∂ν = √(∫ z, F (t, z) ^ 2 ∂ν) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ c ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc.le 2
    set Xt : Ω' → ℝ := fun ω => ∑ i ∈ I, (F (t, O i ω) - Pf t) with hXtdef
    have hcomp : ∀ i, MemLp (fun ω => F (t, O i ω) - Pf t) 2 P := fun i => by
      have h := (memLp_map_measure_iff hft.aestronglyMeasurable (hO.aemeasurable i)).mp
        (by rw [(hO.ident i).map_eq]; exact hF2)
      exact h.sub (memLp_const _)
    have hXt2 : MemLp Xt 2 P := memLp_finsetSum I fun i _ => hcomp i
    have hmean : ∀ i, ∫ ω, F (t, O i ω) ∂P = Pf t := fun i => by
      rw [← integral_map (hO.aemeasurable i) hft.aestronglyMeasurable, (hO.ident i).map_eq]
    have hXt0 : ∫ ω, Xt ω ∂P = 0 := by
      simp only [hXtdef]
      rw [integral_finsetSum I fun i _ => (hcomp i).integrable one_le_two]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_sub ((hcomp i).integrable one_le_two |>.add (integrable_const (Pf t)) |>.congr
        (Eventually.of_forall fun ω => by simp)) (integrable_const _), hmean]
      simp
    have hvar : Var[Xt; P] ≤ r ^ 2 * c ^ 2 := by
      rw [hXtdef, show (fun ω => ∑ i ∈ I, (F (t, O i ω) - Pf t)) =
          ∑ i ∈ I, fun ω => F (t, O i ω) - Pf t from (Finset.sum_fn _ _).symm,
        IndepFun.variance_sum (fun i _ => hcomp i) (fun i _ j _ hij =>
          ((hO.indep.indepFun hij).comp (hft.sub_const (Pf t)) (hft.sub_const (Pf t))))]
      have hone : ∀ i, Var[fun ω => F (t, O i ω) - Pf t; P] ≤ c ^ 2 := fun i => by
        have hfi : AEStronglyMeasurable (fun ω => F (t, O i ω)) P :=
          hft.aestronglyMeasurable.comp_aemeasurable (hO.aemeasurable i)
        rw [variance_sub_const hfi]
        refine (variance_le_expectation_sq hfi).trans (le_of_eq_of_le ?_ hsq)
        simp only [Pi.pow_apply]
        rw [← integral_map (hO.aemeasurable i) (hft.pow_const 2).aestronglyMeasurable,
          (hO.ident i).map_eq]
      calc ∑ i ∈ I, Var[fun ω => F (t, O i ω) - Pf t; P] ≤ ∑ i ∈ I, c ^ 2 :=
            Finset.sum_le_sum fun i _ => hone i
        _ = I.card * c ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ r ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_right hI (sq_nonneg c)
    have hsub : V ⁻¹' (Prod.mk t ⁻¹' B) ⊆ {ω | r * η ≤ |Xt ω - ∫ ω, Xt ω ∂P|} := by
      intro ω hω
      simp only [Set.mem_preimage, hBdef, hHdef, Set.mem_ofPred_eq, hVdef] at hω
      rw [Finset.sum_coe_sort I (fun i => F (t, O i ω) - Pf t)] at hω
      simp only [Set.mem_ofPred_eq, hXt0, sub_zero]
      rw [abs_mul, abs_inv, abs_of_pos hr] at hω
      exact (mul_le_mul_of_nonneg_left hω hr.le).trans_eq
        (by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul])
    calc P (V ⁻¹' (Prod.mk t ⁻¹' B)) ≤ P {ω | r * η ≤ |Xt ω - ∫ ω, Xt ω ∂P|} :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (Var[Xt; P] / (r * η) ^ 2) :=
          meas_ge_le_variance_div_sq hXt2 (mul_pos hr hη)
      _ ≤ ENNReal.ofReal (c ^ 2 / η ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
          have : Var[Xt; P] * η ^ 2 ≤ r ^ 2 * c ^ 2 * η ^ 2 :=
            mul_le_mul_of_nonneg_right hvar (by positivity)
          nlinarith [sq_nonneg η, sq_nonneg r]
  rw [hev, ← Measure.map_apply_of_aemeasurable (hT.prodMk hV) hB, hprod, Measure.prod_apply hB]
  calc ∫⁻ t, (P.map V) (Prod.mk t ⁻¹' B) ∂(P.map T)
      ≤ ∫⁻ t, ({t | ENNReal.ofReal c ≤ D t}.indicator 1 t + ENNReal.ofReal (c ^ 2 / η ^ 2))
          ∂(P.map T) := lintegral_mono hinner
    _ = P {ω | ENNReal.ofReal c ≤ D (T ω)} + ENNReal.ofReal (c ^ 2 / η ^ 2) := by
        have hS : MeasurableSet {t | ENNReal.ofReal c ≤ D t} :=
          measurableSet_le measurable_const hD
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hS,
          lintegral_const, measure_univ, mul_one, Measure.map_apply_of_aemeasurable hT hS]
        rfl

end Chebyshev

section SummandBounds

/-- The elementary bound behind the `L²` error of the fitted summand. For `I ∈ {0, 1}`, a fitted
probability `x ≥ ε'` and a true probability `p ≥ ε`, the difference of the augmented summands
`I y / x - (I - x) / x · u` and `I y / p - (I - p) / p · v` is at most
`ε'⁻¹ |u - v| + ε'⁻¹ ε⁻¹ (r + M |x - p|)` whenever `|y - v| |x - p| ≤ r + M |x - p|`. -/
theorem abs_aipw_sub_le_aux {I x p y u v ε ε' M r : ℝ} (hI : I = 0 ∨ I = 1) (hε : 0 < ε)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hx : ε' ≤ x) (hp : ε ≤ p)
    (hr : |y - v| * |x - p| ≤ r + M * |x - p|) :
    |(I * y / x - (I - x) / x * u) - (I * y / p - (I - p) / p * v)| ≤
      ε'⁻¹ * |u - v| + ε'⁻¹ * ε⁻¹ * (r + M * |x - p|) := by
  have hx0 : 0 < x := hε'.trans_le hx
  have hp0 : 0 < p := hε.trans_le hp
  have hrM : 0 ≤ r + M * |x - p| := (by positivity : 0 ≤ |y - v| * |x - p|).trans hr
  have hinv1 : 1 ≤ ε'⁻¹ := one_le_inv₀ hε' |>.2 hε'1
  have hC : 0 ≤ ε'⁻¹ * ε⁻¹ := by positivity
  rcases hI with rfl | rfl
  · have h : (0 * y / x - (0 - x) / x * u) - (0 * y / p - (0 - p) / p * v) = u - v := by
      field_simp; ring
    rw [h]
    nlinarith [abs_nonneg (u - v), mul_nonneg hC hrM]
  · have h : (1 * y / x - (1 - x) / x * u) - (1 * y / p - (1 - p) / p * v) =
        (u - v) * (1 - 1 / x) + (y - v) * ((p - x) / (x * p)) := by
      field_simp; ring
    rw [h]
    have h1 : |1 - 1 / x| ≤ ε'⁻¹ := by
      have hxi : 1 / x ≤ ε'⁻¹ := by rw [one_div]; exact inv_anti₀ hε' hx
      have hxi0 : 0 < 1 / x := by positivity
      rw [abs_le]; constructor <;> linarith
    have h2 : |(p - x) / (x * p)| ≤ ε'⁻¹ * ε⁻¹ * |x - p| := by
      rw [abs_div, abs_of_pos (mul_pos hx0 hp0), abs_sub_comm, div_le_iff₀ (mul_pos hx0 hp0)]
      have hxp : ε' * ε ≤ x * p := mul_le_mul hx hp hε.le hx0.le
      calc |x - p| = ε'⁻¹ * ε⁻¹ * |x - p| * (ε' * ε) := by field_simp
        _ ≤ ε'⁻¹ * ε⁻¹ * |x - p| * (x * p) :=
            mul_le_mul_of_nonneg_left hxp (by positivity)
    calc |(u - v) * (1 - 1 / x) + (y - v) * ((p - x) / (x * p))|
        ≤ |u - v| * |1 - 1 / x| + |y - v| * |(p - x) / (x * p)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |u - v| * ε'⁻¹ + |y - v| * (ε'⁻¹ * ε⁻¹ * |x - p|) := by
          gcongr
      _ = ε'⁻¹ * |u - v| + ε'⁻¹ * ε⁻¹ * (|y - v| * |x - p|) := by ring
      _ ≤ ε'⁻¹ * |u - v| + ε'⁻¹ * ε⁻¹ * (r + M * |x - p|) := by gcongr

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace 𝒪] in
/-- **The `L²` error of the fitted summand.** For a measurable working score `e'` with
`ε' ≤ e' ≤ 1 - ε'` and a measurable working regression `m'`, at a correct score with
`π_a(W) ≥ ε` almost surely, and for a truncation level `M ≥ 0` at which the tail of the residual
`R = Y - m(a, W)` has `‖R 1{|R| ≥ M}‖₂ ≤ δ`,
`‖aipwScore e' m' a - aipwScore e m a‖₂ ≤ ε'⁻¹ ‖m'(a, W) - m(a, W)‖₂ +
ε'⁻¹ ε⁻¹ (δ + M ‖e'(W) - e(W)‖₂)` in `L²(μ)`. -/
theorem eLpNorm_aipwScore_sub_le (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hps : IsPropensityScore μ A W e) {a : Bool}
    (hm : Measurable (m a)) {ε : ℝ} (hε : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω))
    {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ} (he' : Measurable e') (hm' : Measurable (m' a))
    {ε' : ℝ} (hε' : 0 < ε') (he'b : ∀ w, ε' ≤ e' w ∧ e' w ≤ 1 - ε') {M δ : ℝ} (hM : 0 ≤ M)
    (hδ : eLpNorm ({ω | M ≤ |obsOutcome A Y ω - m a (W ω)|}.indicator
      fun ω => obsOutcome A Y ω - m a (W ω)) 2 μ ≤ ENNReal.ofReal δ) :
    eLpNorm (fun ω => aipwScore e' m' a (obsData A Y W ω) - aipwScore e m a (obsData A Y W ω))
        2 μ ≤
      ENNReal.ofReal ε'⁻¹ * eLpNorm (fun ω => m' a (W ω) - m a (W ω)) 2 μ +
        ENNReal.ofReal (ε'⁻¹ * ε⁻¹) * (ENNReal.ofReal δ +
          ENNReal.ofReal M * eLpNorm (fun ω => e' (W ω) - e (W ω)) 2 μ) := by
  set R : Ω → ℝ := fun ω => obsOutcome A Y ω - m a (W ω) with hRdef
  set S : Set Ω := {ω | M ≤ |R ω|} with hSdef
  have hYo := measurable_obsOutcome hA hY
  have hRm : Measurable R := hYo.sub (hm.comp hW)
  have hSm : MeasurableSet S :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hRm)
  have hIcc := hps.ae_mem_Icc hW hA
  have hdm : Measurable fun ω => m' a (W ω) - m a (W ω) := (hm'.comp hW).sub (hm.comp hW)
  have hde : Measurable fun ω => e' (W ω) - e (W ω) := (he'.comp hW).sub (hps.1.comp hW)
  have hfm : Measurable fun ω =>
      aipwScore e' m' a (obsData A Y W ω) - aipwScore e m a (obsData A Y W ω) :=
    ((measurable_aipwScore he' hm').comp (measurable_obsData hW hA hY)).sub
      ((measurable_aipwScore hps.1 hm).comp (measurable_obsData hW hA hY))
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂μ, ‖aipwScore e' m' a (obsData A Y W ω) - aipwScore e m a (obsData A Y W ω)‖
      ≤ ε'⁻¹ * |m' a (W ω) - m a (W ω)| +
        ε'⁻¹ * ε⁻¹ * (|S.indicator R ω| + M * |e' (W ω) - e (W ω)|) := by
    filter_upwards [hpos, hIcc] with ω hp hI01
    have hε'1 : ε' ≤ 1 := by linarith [(he'b (W ω)).1, (he'b (W ω)).2]
    have hxp : |armProb e' a (W ω) - armProb e a (W ω)| = |e' (W ω) - e (W ω)| := by
      cases a
      · simp only [armProb_false]; rw [abs_sub_comm]; congr 1; ring
      · rfl
    have hx : ε' ≤ armProb e' a (W ω) := by
      cases a
      · simp only [armProb_false]; linarith [(he'b (W ω)).2]
      · exact (he'b (W ω)).1
    have hd1 : |e' (W ω) - e (W ω)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [(he'b (W ω)).1, (he'b (W ω)).2, hI01.1, hI01.2]
    have hr : |obsOutcome A Y ω - m a (W ω)| * |armProb e' a (W ω) - armProb e a (W ω)| ≤
        |S.indicator R ω| + M * |armProb e' a (W ω) - armProb e a (W ω)| := by
      rw [hxp]
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω]
        have : |R ω| * |e' (W ω) - e (W ω)| ≤ |R ω| :=
          mul_le_of_le_one_right (abs_nonneg _) hd1
        nlinarith [abs_nonneg (e' (W ω) - e (W ω))]
      · rw [Set.indicator_of_notMem hω, abs_zero, zero_add]
        have hlt : |R ω| < M := not_le.1 hω
        exact mul_le_mul_of_nonneg_right hlt.le (abs_nonneg _)
    have hI : armIndicator a (obsData A Y W ω) = 0 ∨ armIndicator a (obsData A Y W ω) = 1 := by
      unfold armIndicator; split_ifs <;> simp
    have h := abs_aipw_sub_le_aux (y := obsOutcome A Y ω) (u := m' a (W ω)) (v := m a (W ω)) hI
      hε hε' hε'1 hx hp hr
    rw [hxp] at h
    rw [Real.norm_eq_abs]
    exact h
  have hC0 : 0 ≤ ε'⁻¹ * ε⁻¹ := by positivity
  have habs : ∀ {f : Ω → ℝ}, AEStronglyMeasurable f μ →
      eLpNorm (fun ω => |f ω|) 2 μ = eLpNorm f 2 μ := fun hf => by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm (p := 2) _ hf
  have hsmul : ∀ {c : ℝ} (f : Ω → ℝ), 0 ≤ c →
      eLpNorm (fun ω => c * f ω) 2 μ = ENNReal.ofReal c * eLpNorm f 2 μ := by
    intro c f hc
    rw [show (fun ω => c * f ω) = c • f from rfl, eLpNorm_const_smul, Real.eNorm_eq_ofReal hc]
  have hind : AEStronglyMeasurable (S.indicator R) μ :=
    (hRm.indicator hSm).aestronglyMeasurable
  calc eLpNorm (fun ω => aipwScore e' m' a (obsData A Y W ω) -
        aipwScore e m a (obsData A Y W ω)) 2 μ
      ≤ eLpNorm (fun ω => ε'⁻¹ * |m' a (W ω) - m a (W ω)| +
          ε'⁻¹ * ε⁻¹ * (|S.indicator R ω| + M * |e' (W ω) - e (W ω)|)) 2 μ :=
        eLpNorm_mono_ae_real hfm.aestronglyMeasurable hpt
    _ ≤ eLpNorm (fun ω => ε'⁻¹ * |m' a (W ω) - m a (W ω)|) 2 μ +
          eLpNorm (fun ω => ε'⁻¹ * ε⁻¹ * (|S.indicator R ω| + M * |e' (W ω) - e (W ω)|)) 2 μ :=
        eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal ε'⁻¹ * eLpNorm (fun ω => m' a (W ω) - m a (W ω)) 2 μ +
          ENNReal.ofReal (ε'⁻¹ * ε⁻¹) * (eLpNorm (S.indicator R) 2 μ +
            ENNReal.ofReal M * eLpNorm (fun ω => e' (W ω) - e (W ω)) 2 μ) := by
        rw [hsmul _ (inv_nonneg.2 hε'.le), habs hdm.aestronglyMeasurable,
          hsmul _ hC0]
        gcongr
        calc eLpNorm (fun ω => |S.indicator R ω| + M * |e' (W ω) - e (W ω)|) 2 μ
            ≤ eLpNorm (fun ω => |S.indicator R ω|) 2 μ +
                eLpNorm (fun ω => M * |e' (W ω) - e (W ω)|) 2 μ := eLpNorm_add_le (by norm_num)
          _ = _ := by rw [habs hind, hsmul _ hM, habs hde.aestronglyMeasurable]
    _ ≤ _ := by gcongr

/-- **The bias of the fitted summand, in `L²` errors.** Under the hypotheses of the product bias
bound `abs_integral_aipwScore_sub_armMean_le`, for a working score with `ε' ≤ e' ≤ 1 - ε'` and a
working regression whose `L²` error `‖m'(a, W) - m(a, W)‖₂` is finite,
`|E[aipwScore e' m' a - aipwScore e m a]| ≤ ε'⁻¹ ‖e'(W) - e(W)‖₂ ‖m'(a, W) - m(a, W)‖₂`. -/
theorem ofReal_abs_integral_aipwScore_sub_le (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ}
    (he' : Measurable e') (hm' : Measurable (m' a)) {ε' : ℝ} (hε' : 0 < ε')
    (he'b : ∀ w, ε' ≤ e' w ∧ e' w ≤ 1 - ε')
    (hfin : eLpNorm (fun ω => m' a (W ω) - m a (W ω)) 2 μ ≠ ∞) :
    ENNReal.ofReal |∫ ω, (aipwScore e' m' a (obsData A Y W ω) -
        aipwScore e m a (obsData A Y W ω)) ∂μ| ≤
      ENNReal.ofReal ε'⁻¹ * (eLpNorm (fun ω => e' (W ω) - e (W ω)) 2 μ *
        eLpNorm (fun ω => m' a (W ω) - m a (W ω)) 2 μ) := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h => hε.trans_le h
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
  have hm2 : MemLp (fun ω => m a (W ω)) 2 μ := ((hY2 a).condExp one_le_two).ae_eq hid.symm
  have hd2 : MemLp (fun ω => m' a (W ω) - m a (W ω)) 2 μ := lt_top_iff_ne_top.2 hfin
  have hm'2 : MemLp (fun ω => m' a (W ω)) 2 μ :=
    (hd2.add hm2).ae_eq (Eventually.of_forall fun ω => by simp)
  have hIcc := hps.ae_mem_Icc hW hA
  have hde : Measurable fun ω => e' (W ω) - e (W ω) := (he'.comp hW).sub (hps.1.comp hW)
  have hd1 : MemLp (fun ω => e' (W ω) - e (W ω)) 2 μ := by
    refine MemLp.of_bound hde.aestronglyMeasurable 1 (hIcc.mono fun ω h => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(he'b (W ω)).1, (he'b (W ω)).2, h.1, h.2]
  have hx : ∀ w, ε' ≤ armProb e' a w ∧ armProb e' a w ≤ 1 := fun w => by
    have := he'b w
    cases a <;> simp only [armProb_false, armProb_true] <;> constructor <;>
      linarith [this.1, this.2]
  have hpos'' : ∀ᵐ ω ∂μ, ε' ≤ armProb e' a (W ω) := Eventually.of_forall fun ω => (hx _).1
  have hYo2 := memLp_obsOutcome hA hY hY2
  have h2' : MemLp (fun ω => aipwScore e' m' a (obsData A Y W ω)) 2 μ := by
    refine ((memLp_weightedResidual hA hW he' hm' hYo2 hm'2 hε' hpos'').add hm'2).ae_eq
      (Eventually.of_forall fun ω => ?_)
    have hne : armProb e' a (W ω) ≠ 0 := (hε'.trans_le (hx _).1).ne'
    simp only [Pi.add_apply]
    rw [aipwScore_eq a (z := obsData A Y W ω) hne, armIndicator_obsData]
    simp only [obsData, weightedResidual]
    ring
  have h2 : MemLp (fun ω => aipwScore e m a (obsData A Y W ω)) 2 μ :=
    ((memLp_armEIF hW hA hY hY2 hps hreg a hmi hε hpos 0).add (memLp_const 0)).ae_eq
      (Eventually.of_forall fun ω => by simp [armEIF])
  have hmean : ∫ ω, aipwScore e m a (obsData A Y W ω) ∂μ = armMean μ Y a := by
    have h0 := integral_armEIF_eq_zero hW hA hYi hps hreg a hmi hε hpos
    simp only [armEIF] at h0
    rw [integral_sub (h2.integrable one_le_two) (integrable_const _), integral_const] at h0
    simpa [sub_eq_zero] using h0
  have hb := abs_integral_aipwScore_sub_armMean_le hW hA hY2 hps hreg a hmi hpos' he' hm' hε' hx
    hm'2
  have hsq1 : √(∫ ω, (armProb e' a (W ω) - armProb e a (W ω)) ^ 2 ∂μ) =
      (eLpNorm (fun ω => e' (W ω) - e (W ω)) 2 μ).toReal := by
    rw [MemLp.eLpNorm_two_eq_ofReal_sqrt hd1, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    cases a
    · simp only [armProb_false]; ring
    · rfl
  have hsq2 : √(∫ ω, (m' a (W ω) - m a (W ω)) ^ 2 ∂μ) =
      (eLpNorm (fun ω => m' a (W ω) - m a (W ω)) 2 μ).toReal := by
    rw [MemLp.eLpNorm_two_eq_ofReal_sqrt hd2, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rw [integral_sub (h2'.integrable one_le_two) (h2.integrable one_le_two), hmean]
  rw [hsq1, hsq2] at hb
  calc ENNReal.ofReal |∫ ω, aipwScore e' m' a (obsData A Y W ω) ∂μ - armMean μ Y a|
      ≤ ENNReal.ofReal (ε'⁻¹ * ((eLpNorm (fun ω => e' (W ω) - e (W ω)) 2 μ).toReal *
          (eLpNorm (fun ω => m' a (W ω) - m a (W ω)) 2 μ).toReal)) :=
        ENNReal.ofReal_le_ofReal hb
    _ = _ := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hε'.le), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hd1.ne, ENNReal.ofReal_toReal hfin]

end SummandBounds

section FoldRate

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {K : ℕ} {P : Measure Ω'} [IsProbabilityMeasure P]

omit [MeasurableSpace 𝒪] in
/-- **The fold remainder is `o_P(n^{-1/2})` under product rates of the learners.** Let `O` be an
i.i.d. sample with the law of the observed data, under mean ignorability of the arm `a`, a
correct score and regression, square integrable potential outcomes and `π_a(W) ≥ ε > 0`. Let the
learners of the fold `k` be jointly measurable in the training data and the covariate, with the
fitted score in `[ε', 1 - ε']`. If the out of fold `L²(P_W)` errors `‖ê_{n,k} - e‖₂` and
`‖m̂_{n,k}(a, ·) - m(a, ·)‖₂` tend to `0` in probability and
`√n ‖ê_{n,k} - e‖₂ ‖m̂_{n,k}(a, ·) - m(a, ·)‖₂ → 0` in probability, then
`√n R_{n,k} → 0` in probability.

Given the training data, the fold remainder splits into a centered term, whose conditional
variance is at most `‖aipwScore ê m̂ a - aipwScore e m a‖₂² / n`, so that it vanishes by the
conditional Chebyshev inequality `measure_le_abs_sum_sub_integral_le` (the `L²` norm of the
summand difference is controlled by `eLpNorm_aipwScore_sub_le`), and a bias term, at most
`ε'⁻¹ √n ‖ê - e‖₂ ‖m̂(a, ·) - m(a, ·)‖₂` by the product bias bound
(`ofReal_abs_integral_aipwScore_sub_le`). No condition on the fold sizes is needed. -/
theorem tendstoInMeasure_sqrt_mul_foldRemainder (fold : ℕ → ℕ → Fin K)
    {eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ}
    {mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ}
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) {O : ℕ → Ω' → 𝒲 × Bool × ℝ}
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    (hE : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 => eHat n k p.1 p.2)
    (hM : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 =>
      mHat n k p.1 a p.2)
    {ε' : ℝ} (hε' : 0 < ε') (hEb : ∀ n k t w, ε' ≤ eHat n k t w ∧ eHat n k t w ≤ 1 - ε')
    (k : Fin K)
    (herrE : TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω)) atTop 0)
    (herrM : TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (fun t => mHat n k t a) (m a) (trainingData fold O n k ω)) atTop 0)
    (hprod : TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) *
      (fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω) *
        fitError (μ.map W) (fun t => mHat n k t a) (m a) (trainingData fold O n k ω))) atTop 0) :
    TendstoInMeasure P (fun (n : ℕ) ω => √n * foldRemainder fold eHat mHat e m a O k n ω)
      atTop 0 := by
  set F : (n : ℕ) → (cvTrain fold n k → 𝒲 × Bool × ℝ) × (𝒲 × Bool × ℝ) → ℝ :=
    fun n p => aipwScore (eHat n k p.1) (mHat n k p.1) a p.2 - aipwScore e m a p.2 with hFdef
  have hF : ∀ n, Measurable (F n) := fun n =>
    (measurable_aipwScore_fitted (hE n k) (hM n k)).sub
      ((measurable_aipwScore hps.1 (hreg.1 a)).comp measurable_snd)
  set T : (n : ℕ) → Ω' → cvTrain fold n k → 𝒲 × Bool × ℝ := fun n => trainingData fold O n k
    with hTdef
  have hT : ∀ n, AEMeasurable (T n) P := fun n =>
    aemeasurable_trainingData fold hO.aemeasurable n k
  have hobs := measurable_obsData hW hA hY
  have hEt : ∀ n t, Measurable (eHat n k t) := fun n t => (hE n k).comp measurable_prodMk_left
  have hMt : ∀ n t, Measurable (mHat n k t a) := fun n t =>
    (hM n k).comp measurable_prodMk_left
  have herrE_eq : ∀ n t, fitError (μ.map W) (eHat n k) e t =
      eLpNorm (fun ω => eHat n k t (W ω) - e (W ω)) 2 μ := fun n t =>
    fitError_map hW (hEt n t) hps.1
  have herrM_eq : ∀ n t, fitError (μ.map W) (fun t => mHat n k t a) (m a) t =
      eLpNorm (fun ω => mHat n k t a (W ω) - m a (W ω)) 2 μ := fun n t =>
    fitError_map hW (hMt n t) (hreg.1 a)
  have hDt : ∀ n t, eLpNorm (fun z => F n (t, z)) 2 (P.map (O 0)) = eLpNorm (fun ω =>
      aipwScore (eHat n k t) (mHat n k t) a (obsData A Y W ω) -
        aipwScore e m a (obsData A Y W ω)) 2 μ := fun n t => by
    rw [hlaw]
    exact eLpNorm_map_measure (g := fun z => F n (t, z))
      ((hF n).comp measurable_prodMk_left).aestronglyMeasurable hobs.aemeasurable
  -- the `L²` norm of the summand difference at the training data tends to zero
  have hD : TendstoInMeasure P (fun n ω => eLpNorm (fun z => F n (T n ω, z)) 2 (P.map (O 0)))
      atTop 0 := by
    rw [tendstoInMeasure_zero_iff_ofReal]
    intro c hc
    set C := ε'⁻¹ * ε⁻¹ with hCdef
    have hC : 0 < C := by positivity
    have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
    have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h => hε.trans_le h
    have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
    have hm2 : MemLp (fun ω => m a (W ω)) 2 μ := ((hY2 a).condExp one_le_two).ae_eq hid.symm
    have hR2 : MemLp (fun ω => obsOutcome A Y ω - m a (W ω)) 2 μ :=
      (memLp_obsOutcome hA hY hY2).sub hm2
    obtain ⟨M₀, hM₀⟩ := hR2.eLpNorm_indicator_norm_ge_le
      (ENNReal.ofReal_pos.2 (by positivity : 0 < c / 2 / C))
    set M := max M₀ 0 with hMdef
    have hset : {x | M₀ ≤ (‖obsOutcome A Y x - m a (W x)‖₊ : ℝ)} =
        {ω | M ≤ |obsOutcome A Y ω - m a (W ω)|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, coe_nnNorm, Real.norm_eq_abs, hMdef, max_le_iff,
        abs_nonneg, and_true]
    rw [hset] at hM₀
    have hbound : ∀ n ω, eLpNorm (fun z => F n (T n ω, z)) 2 (P.map (O 0)) ≤
        (ENNReal.ofReal ε'⁻¹ * fitError (μ.map W) (fun t => mHat n k t a) (m a) (T n ω) +
          ENNReal.ofReal (C * M) * fitError (μ.map W) (eHat n k) e (T n ω)) +
            ENNReal.ofReal (c / 2) := by
      intro n ω
      rw [hDt, herrE_eq, herrM_eq]
      refine (eLpNorm_aipwScore_sub_le hW hA hY hps (hreg.1 a) hε hpos (hEt n _) (hMt n _) hε'
        (hEb n k _) (le_max_right _ _) hM₀).trans (le_of_eq ?_)
      rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul hC.le,
        show C * (c / 2 / C) = c / 2 by field_simp]
      ring
    have hlim := tendstoInMeasure_zero_iff_ofReal.1
      (tendstoInMeasure_add_ennreal herrM herrE (a := ε'⁻¹) (b := C * M)) (c / 2) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le)
      fun n => measure_mono fun ω hω => ?_
    have h1 := le_trans hω (hbound n ω)
    rw [show ENNReal.ofReal c = ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
  -- the centered term
  set G : ℕ → Ω' → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ∑ i ∈ cvFold fold n k,
    (F n (T n ω, O i ω) - ∫ z, F n (T n ω, z) ∂(P.map (O 0))) with hGdef
  have hG : TendstoInMeasure P G atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro η hη
    refine tendsto_zero_of_le_add_ofReal fun r hr => ?_
    have hc : 0 < η * √r := mul_pos hη (Real.sqrt_pos.2 hr)
    refine ⟨fun n => P {ω | ENNReal.ofReal (η * √r) ≤
      eLpNorm (fun z => F n (T n ω, z)) 2 (P.map (O 0))},
      tendstoInMeasure_zero_iff_ofReal.1 hD _ hc, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hcard : ((cvFold fold n k).card : ℝ) ≤ √(n : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      exact_mod_cast card_cvFold_le fold n k
    have hind : IndepFun (T n) (fun ω (i : cvFold fold n k) => O i ω) P :=
      hO.indep.indepFun_finset₀ _ _ (disjoint_cvFold_cvTrain fold n k).symm hO.aemeasurable
    have hch := measure_le_abs_sum_sub_integral_le hO (hT n) hind (hF n) hnpos hη hcard
      (c := η * √r)
    have hcr : (η * √r) ^ 2 / η ^ 2 = r := by
      rw [mul_pow, Real.sq_sqrt hr.le]
      field_simp
    rw [hcr] at hch
    refine le_trans (measure_mono fun ω hω => ?_) hch
    simpa only [hGdef, Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] using hω
  -- the bias term
  set H : ℕ → Ω' → ℝ := fun n ω => (√(n : ℝ))⁻¹ * ((cvFold fold n k).card *
    ∫ z, F n (T n ω, z) ∂(P.map (O 0))) with hHdef
  have hH : TendstoInMeasure P H atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro η hη
    have hfin := tendstoInMeasure_zero_iff_ofReal.1 herrM 1 one_pos
    have hpr := tendstoInMeasure_zero_iff_ofReal.1
      (tendstoInMeasure_add_ennreal hprod hprod (a := ε'⁻¹) (b := 0)) η hη
    have hsum := hfin.add hpr
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => bot_le)
      fun n => (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.zero_apply, sub_zero] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hfin' : eLpNorm (fun ω' => mHat n k (T n ω) a (W ω') - m a (W ω')) 2 μ ≠ ∞ := by
      rw [← herrM_eq]; exact (h1.trans ENNReal.ofReal_lt_top).ne
    have hb := ofReal_abs_integral_aipwScore_sub_le hW hA hY hY2 hps hreg a hmi hε hpos
      (hEt n (T n ω)) (hMt n (T n ω)) hε' (hEb n k _) hfin'
    rw [← herrE_eq, ← herrM_eq] at hb
    have hint : ∫ z, F n (T n ω, z) ∂(P.map (O 0)) = ∫ ω', (aipwScore (eHat n k (T n ω))
        (mHat n k (T n ω)) a (obsData A Y W ω') - aipwScore e m a (obsData A Y W ω')) ∂μ := by
      rw [hlaw]
      exact integral_map (f := fun z => F n (T n ω, z)) hobs.aemeasurable
        ((hF n).comp measurable_prodMk_left).aestronglyMeasurable
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hHle : ‖H n ω‖ ≤ √(n : ℝ) * |∫ z, F n (T n ω, z) ∂(P.map (O 0))| := by
      have hcn : ((cvFold fold n k).card : ℝ) ≤ n := by exact_mod_cast card_cvFold_le fold n k
      rw [Real.norm_eq_abs, hHdef, abs_mul, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
        Nat.abs_cast]
      calc (√(n : ℝ))⁻¹ * ((cvFold fold n k).card * |∫ z, F n (T n ω, z) ∂(P.map (O 0))|)
          ≤ (√(n : ℝ))⁻¹ * (n * |∫ z, F n (T n ω, z) ∂(P.map (O 0))|) := by gcongr
        _ = √(n : ℝ) * |∫ z, F n (T n ω, z) ∂(P.map (O 0))| := by
          rw [← mul_assoc, inv_sqrt_mul_self _ hn0]
    have h3 : ENNReal.ofReal η ≤ ENNReal.ofReal ε'⁻¹ * (ENNReal.ofReal √(n : ℝ) *
        (fitError (μ.map W) (eHat n k) e (T n ω) *
          fitError (μ.map W) (fun t => mHat n k t a) (m a) (T n ω))) := by
      calc ENNReal.ofReal η ≤ ENNReal.ofReal (√(n : ℝ) * |∫ z, F n (T n ω, z) ∂(P.map (O 0))|) :=
            ENNReal.ofReal_le_ofReal (hω.trans hHle)
        _ = ENNReal.ofReal √(n : ℝ) * ENNReal.ofReal |∫ z, F n (T n ω, z) ∂(P.map (O 0))| :=
            ENNReal.ofReal_mul (Real.sqrt_nonneg _)
        _ ≤ ENNReal.ofReal √(n : ℝ) * (ENNReal.ofReal ε'⁻¹ *
            (fitError (μ.map W) (eHat n k) e (T n ω) *
              fitError (μ.map W) (fun t => mHat n k t a) (m a) (T n ω))) := by
            rw [hint]; gcongr
        _ = _ := by ring
    refine absurd ?_ (not_le.2 h2)
    simpa only [ENNReal.ofReal_zero, zero_mul, add_zero] using h3
  -- the decomposition
  have hsplit : (fun (n : ℕ) ω => √n * foldRemainder fold eHat mHat e m a O k n ω) =
      fun n ω => G n ω + H n ω := by
    funext n ω
    simp only [foldRemainder, hGdef, hHdef, hFdef, hTdef]
    rw [← mul_assoc, sqrt_mul_inv_self]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsplit]
  have h := hG.add hH
  rw [add_zero] at h
  exact h

end FoldRate

end Efficiency
end CausalInference
