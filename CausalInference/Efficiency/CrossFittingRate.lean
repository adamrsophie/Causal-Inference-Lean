/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.CrossFittingRemainder

/-!
# Rates for the nuisance errors of cross fitting

The product condition of `CausalInference.Efficiency.CrossFittingNormality` asks that
`√n ‖ê - e‖₂ ‖m̂ - m‖₂ → 0` in probability, a statement about `[0, ∞]`-valued errors
(`fitError`). This file gives the usual ways to verify it.

**Bounded in probability in `[0, ∞]`.** A sequence `X n` of `[0, ∞]`-valued variables is bounded
in probability when for every `η > 0` there is a finite level `M` with eventually
`P(M ≤ X n) ≤ η` (`BoundedInProbabilityENNReal`). For `X n = |Z n|` with `Z n` real this is the
real notion `BoundedInProbability` (`boundedInProbabilityENNReal_ofReal_abs_iff`).

**Bounded times vanishing.** A bounded in probability sequence times a sequence tending to `0` in
probability tends to `0` in probability (`BoundedInProbabilityENNReal.mul_tendstoInMeasure`).
Hence the product condition holds when `√n ‖ê - e‖₂` is bounded in probability and
`‖m̂ - m‖₂ → 0` in probability, or symmetrically
(`tendstoInMeasure_sqrt_mul_mul_of_bounded_left`, `..._right`), and when both errors are
`o_P(n^{-1/4})` (`tendstoInMeasure_sqrt_mul_mul_of_quarter`). An error with `√n` times it
bounded in probability tends to `0` in probability (`tendstoInMeasure_of_bounded_sqrt_mul`).

**Clipping.** The projection `max lo (min x hi)` onto an interval containing the target is a
contraction toward the target, so clipping a learner to an interval containing the true
function does not increase its `L²` error (`fitError_clipInterval_le`).

**The `√N` rate of means.** For an i.i.d. sample, a square integrable `f(O_0)` with mean `0`
and finite sets `S_n` of units, `√|S_n| · |S_n|⁻¹ ∑_{i ∈ S_n} f(O_i)` is bounded in probability:
its variance is `Var f(O_0)`, and Chebyshev's inequality applies
(`boundedInProbability_sqrt_card_mul_finsetMean`).

## Main definitions

* `BoundedInProbabilityENNReal`: boundedness in probability of `[0, ∞]`-valued variables.
* `clipInterval`: the projection onto an interval.

## Main results

* `boundedInProbabilityENNReal_ofReal_abs_iff`, `BoundedInProbabilityENNReal.mul_tendstoInMeasure`.
* `tendstoInMeasure_sqrt_mul_mul_of_bounded_left`, `tendstoInMeasure_sqrt_mul_mul_of_bounded_right`,
  `tendstoInMeasure_sqrt_mul_mul_of_quarter`, `tendstoInMeasure_of_bounded_sqrt_mul`.
* `abs_clipInterval_sub_le`, `fitError_clipInterval_le`.
* `BoundedInProbability.finset_sum`, `boundedInProbability_sqrt_card_mul_finsetMean`.

## References

* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, The Econometrics
  Journal 21 (2018).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology

variable {Ω' 𝒪 : Type*} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace 𝒪] {P : Measure Ω'}

/-! ### Bounded in probability in `[0, ∞]` -/

/-- **Bounded in probability** for `[0, ∞]`-valued variables: for every `η > 0` there is a finite
level `M > 0` with eventually `P(M ≤ X n) ≤ η`. -/
def BoundedInProbabilityENNReal (P : Measure Ω') (X : ℕ → Ω' → ℝ≥0∞) : Prop :=
  ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, P {ω | ENNReal.ofReal M ≤ X n ω} ≤ η

/-- For real variables, boundedness in probability of `|Z n|` in `[0, ∞]` is the real notion. -/
theorem boundedInProbabilityENNReal_ofReal_abs_iff {Z : ℕ → Ω' → ℝ} :
    BoundedInProbabilityENNReal P (fun n ω => ENNReal.ofReal |Z n ω|) ↔
      BoundedInProbability P Z := by
  have h : ∀ (M : ℝ) (n : ℕ), {ω | ENNReal.ofReal M ≤ ENNReal.ofReal |Z n ω|} =
      {ω | M ≤ |Z n ω|} := fun M n => by
    ext ω
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  constructor
  · intro hZ η hη
    obtain ⟨M, hM, hev⟩ := hZ η hη
    exact ⟨M, hM, hev.mono fun n hn => by rwa [h M n] at hn⟩
  · intro hZ η hη
    obtain ⟨M, hM, hev⟩ := hZ η hη
    exact ⟨M, hM, hev.mono fun n hn => by rwa [h M n]⟩

/-- A sequence below a bounded in probability sequence is bounded in probability. -/
theorem BoundedInProbabilityENNReal.mono {X Y : ℕ → Ω' → ℝ≥0∞}
    (hY : BoundedInProbabilityENNReal P Y) (hle : ∀ n ω, X n ω ≤ Y n ω) :
    BoundedInProbabilityENNReal P X := by
  intro η hη
  obtain ⟨M, hM, hev⟩ := hY η hη
  exact ⟨M, hM, hev.mono fun n hn => (measure_mono fun ω hω => le_trans hω (hle n ω)).trans hn⟩

/-- A sequence tending to `0` in probability is bounded in probability. -/
theorem _root_.MeasureTheory.TendstoInMeasure.boundedInProbabilityENNReal {X : ℕ → Ω' → ℝ≥0∞}
    (hX : TendstoInMeasure P X atTop 0) : BoundedInProbabilityENNReal P X := by
  intro η hη
  rw [tendstoInMeasure_zero_iff_ofReal] at hX
  exact ⟨1, one_pos, (ENNReal.tendsto_nhds_zero.1 (hX 1 one_pos)) η hη⟩

/-- **Bounded times vanishing.** A bounded in probability sequence times a sequence tending to
`0` in probability tends to `0` in probability. -/
theorem BoundedInProbabilityENNReal.mul_tendstoInMeasure {X Y : ℕ → Ω' → ℝ≥0∞}
    (hX : BoundedInProbabilityENNReal P X) (hY : TendstoInMeasure P Y atTop 0) :
    TendstoInMeasure P (fun n ω => X n ω * Y n ω) atTop 0 := by
  rw [tendstoInMeasure_zero_iff_ofReal] at hY ⊢
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨M, hM, hXM⟩ := hX (κ / 2) (ENNReal.half_pos hκ.ne')
  have hYe := (ENNReal.tendsto_nhds_zero.1 (hY (δ / M) (div_pos hδ hM))) (κ / 2)
    (ENNReal.half_pos hκ.ne')
  filter_upwards [hXM, hYe] with n h1 h2
  calc P {ω | ENNReal.ofReal δ ≤ X n ω * Y n ω}
      ≤ P ({ω | ENNReal.ofReal M ≤ X n ω} ∪ {ω | ENNReal.ofReal (δ / M) ≤ Y n ω}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        by_contra! hlt
        have hmul : X n ω * Y n ω < ENNReal.ofReal M * ENNReal.ofReal (δ / M) :=
          ENNReal.mul_lt_mul hlt.1 hlt.2
        rw [← ENNReal.ofReal_mul hM.le, mul_div_cancel₀ _ hM.ne'] at hmul
        exact absurd hω (not_le.2 hmul)
    _ ≤ κ / 2 + κ / 2 := (measure_union_le _ _).trans (add_le_add h1 h2)
    _ = κ := ENNReal.add_halves κ

/-! ### The product condition -/

/-- **The product condition from a `√n` rate of the first error.** If `√n f_n` is bounded in
probability and `g_n → 0` in probability, then `√n f_n g_n → 0` in probability. -/
theorem tendstoInMeasure_sqrt_mul_mul_of_bounded_left {f g : ℕ → Ω' → ℝ≥0∞}
    (hf : BoundedInProbabilityENNReal P (fun n ω => ENNReal.ofReal √(n : ℝ) * f n ω))
    (hg : TendstoInMeasure P g atTop 0) :
    TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) * (f n ω * g n ω)) atTop 0 := by
  have h := hf.mul_tendstoInMeasure hg
  convert h using 1
  funext n ω
  ring

/-- **The product condition from a `√n` rate of the second error.** If `f_n → 0` in
probability and `√n g_n` is bounded in probability, then `√n f_n g_n → 0` in probability. -/
theorem tendstoInMeasure_sqrt_mul_mul_of_bounded_right {f g : ℕ → Ω' → ℝ≥0∞}
    (hf : TendstoInMeasure P f atTop 0)
    (hg : BoundedInProbabilityENNReal P (fun n ω => ENNReal.ofReal √(n : ℝ) * g n ω)) :
    TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) * (f n ω * g n ω)) atTop 0 := by
  have h := hg.mul_tendstoInMeasure hf
  convert h using 1
  funext n ω
  ring

/-- **The product condition from `o_P(n^{-1/4})` rates.** If `n^{1/4} f_n → 0` and
`n^{1/4} g_n → 0` in probability, then `√n f_n g_n → 0` in probability. -/
theorem tendstoInMeasure_sqrt_mul_mul_of_quarter {f g : ℕ → Ω' → ℝ≥0∞}
    (hf : TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ)) * f n ω)
      atTop 0)
    (hg : TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ)) * g n ω)
      atTop 0) :
    TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) * (f n ω * g n ω)) atTop 0 := by
  have key : ∀ n : ℕ, ENNReal.ofReal √(n : ℝ) =
      ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ)) * ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ)) := by
    intro n
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),
      Real.sqrt_eq_rpow]
    norm_num
  have h := hf.boundedInProbabilityENNReal.mul_tendstoInMeasure hg
  convert h using 1
  funext n ω
  rw [key]
  ring

/-- **An error with a `√n` rate tends to `0`.** If `√n f_n` is bounded in probability, then
`f_n → 0` in probability. -/
theorem tendstoInMeasure_of_bounded_sqrt_mul {f : ℕ → Ω' → ℝ≥0∞}
    (hf : BoundedInProbabilityENNReal P (fun n ω => ENNReal.ofReal √(n : ℝ) * f n ω)) :
    TendstoInMeasure P f atTop 0 := by
  rw [tendstoInMeasure_zero_iff_ofReal]
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨M, hM, hev⟩ := hf κ hκ
  filter_upwards [hev, eventually_ge_atTop ⌈(M / δ) ^ 2⌉₊] with n h1 h2
  have hsq : M / δ ≤ √(n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (Nat.cast_nonneg _)]
    exact (Nat.le_ceil _).trans (by exact_mod_cast h2)
  have hMle : M ≤ √(n : ℝ) * δ := (div_le_iff₀ hδ).1 hsq
  refine (measure_mono fun ω hω => ?_).trans h1
  simp only [Set.mem_ofPred_eq] at hω ⊢
  calc ENNReal.ofReal M ≤ ENNReal.ofReal (√(n : ℝ) * δ) := ENNReal.ofReal_le_ofReal hMle
    _ = ENNReal.ofReal √(n : ℝ) * ENNReal.ofReal δ := ENNReal.ofReal_mul (Real.sqrt_nonneg _)
    _ ≤ ENNReal.ofReal √(n : ℝ) * f n ω := by gcongr

/-! ### Clipping -/

/-- The projection `max lo (min x hi)` of `x` onto the interval `[lo, hi]`. -/
def clipInterval (lo hi x : ℝ) : ℝ := max lo (min x hi)

theorem clipInterval_mem {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) :
    lo ≤ clipInterval lo hi x ∧ clipInterval lo hi x ≤ hi :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

theorem continuous_clipInterval (lo hi : ℝ) : Continuous (clipInterval lo hi) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- **Clipping moves toward every point of the interval**: for `y ∈ [lo, hi]`,
`|clip(x) - y| ≤ |x - y|`. -/
theorem abs_clipInterval_sub_le {lo hi x y : ℝ} (hy : lo ≤ y) (hy' : y ≤ hi) :
    |clipInterval lo hi x - y| ≤ |x - y| := by
  have h1 := le_abs_self (x - y)
  have h2 := neg_abs_le (x - y)
  have h0 := abs_nonneg (x - y)
  rw [abs_le]
  constructor
  · have h3 : y - |x - y| ≤ min x hi := le_min (by linarith) (by linarith)
    have h4 := h3.trans (le_max_right lo (min x hi))
    unfold clipInterval
    linarith
  · have h3 : max lo (min x hi) ≤ |x - y| + y :=
      max_le (by linarith) ((min_le_left x hi).trans (by linarith))
    unfold clipInterval
    linarith

/-- **Clipping does not increase the `L²` error** when the target takes values in the
interval. -/
theorem fitError_clipInterval_le {𝒯 𝒲 : Type*} [MeasurableSpace 𝒲] (ν : Measure 𝒲)
    {hHat : 𝒯 → 𝒲 → ℝ} {h : 𝒲 → ℝ} {lo hi : ℝ} (hh : ∀ w, lo ≤ h w ∧ h w ≤ hi) (t : 𝒯)
    (hHt : Measurable (hHat t)) (hm : Measurable h) :
    fitError ν (fun t w => clipInterval lo hi (hHat t w)) h t ≤ fitError ν hHat h t :=
  eLpNorm_mono ((((continuous_clipInterval lo hi).measurable.comp hHt).sub
    hm).aestronglyMeasurable) fun w => by
    simp only [Real.norm_eq_abs]
    exact abs_clipInterval_sub_le (hh w).1 (hh w).2

/-! ### The `√N` rate of means -/

/-- A finite sum of sequences bounded in probability is bounded in probability. -/
theorem BoundedInProbability.finset_sum {ι : Type*} (s : Finset ι) {X : ι → ℕ → Ω' → ℝ}
    (h : ∀ i ∈ s, BoundedInProbability P (X i)) :
    BoundedInProbability P (fun n ω => ∑ i ∈ s, X i n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun η _ => ⟨1, one_pos, Eventually.of_forall fun n => by norm_num⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- **The `√N` rate of means.** For an i.i.d. sample, a measurable `f` with `f(O_0)` square
integrable of mean `0`, and finite sets `S_n` of units, `√|S_n| · |S_n|⁻¹ ∑_{i ∈ S_n} f(O_i)` is
bounded in probability. -/
theorem boundedInProbability_sqrt_card_mul_finsetMean [IsProbabilityMeasure P]
    {O : ℕ → Ω' → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω => f (O 0 ω)) 2 P) (hf0 : ∫ ω, f (O 0 ω) ∂P = 0) (S : ℕ → Finset ℕ) :
    BoundedInProbability P (fun n ω => √((S n).card : ℝ) *
      (((S n).card : ℝ)⁻¹ * ∑ i ∈ S n, f (O i ω))) := by
  have hid := (hO.comp hf).ident
  have hi2 : ∀ i, MemLp (fun ω => f (O i ω)) 2 P := fun i => (hid i).memLp_iff.2 hf2
  have hmean : ∀ i, ∫ ω, f (O i ω) ∂P = 0 := fun i => (hid i).integral_eq.trans hf0
  have hvar : ∀ i, Var[fun ω => f (O i ω); P] = Var[fun ω => f (O 0 ω); P] := fun i =>
    (hid i).variance_eq
  set σ2 := Var[fun ω => f (O 0 ω); P]
  have hσ : 0 ≤ σ2 := variance_nonneg _ _
  have hbound : ∀ (n : ℕ) (M : ℝ), 0 < M → P {ω | M ≤ |√((S n).card : ℝ) *
      (((S n).card : ℝ)⁻¹ * ∑ i ∈ S n, f (O i ω))|} ≤ ENNReal.ofReal (σ2 / M ^ 2) := by
    intro n M hM
    rcases Nat.eq_zero_or_pos (S n).card with h0 | hpos
    · have hempty : S n = ∅ := Finset.card_eq_zero.1 h0
      have hset : {ω | M ≤ |√((S n).card : ℝ) *
          (((S n).card : ℝ)⁻¹ * ∑ i ∈ S n, f (O i ω))|} = ∅ := by
        ext ω
        simp only [hempty, Finset.sum_empty, mul_zero, abs_zero, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_le]
        exact hM
      rw [hset, measure_empty]
      exact bot_le
    have hN : (0 : ℝ) < (S n).card := by exact_mod_cast hpos
    set a : ℝ := √((S n).card : ℝ) * ((S n).card : ℝ)⁻¹ with ha
    have hX2 : MemLp (fun ω => a * ∑ i ∈ S n, f (O i ω)) 2 P :=
      (memLp_finsetSum (S n) fun i _ => hi2 i).const_mul _
    have hEX : ∫ ω, a * ∑ i ∈ S n, f (O i ω) ∂P = 0 := by
      rw [integral_const_mul, integral_finsetSum _ fun i _ => (hi2 i).integrable one_le_two]
      simp [hmean]
    have hVX : Var[fun ω => a * ∑ i ∈ S n, f (O i ω); P] = σ2 := by
      rw [variance_const_mul, show (fun ω => ∑ i ∈ S n, f (O i ω)) =
          ∑ i ∈ S n, fun ω => f (O i ω) from (Finset.sum_fn _ _).symm,
        IndepFun.variance_sum (fun i _ => hi2 i) (fun i _ j _ hij =>
          hO.pairwise_indepFun hf hij)]
      simp only [hvar, Finset.sum_const, nsmul_eq_mul, ha, mul_pow,
        Real.sq_sqrt hN.le, inv_pow]
      field_simp
    have hcheb := meas_ge_le_variance_div_sq hX2 hM
    rw [hEX, hVX] at hcheb
    refine (measure_mono fun ω hω => ?_).trans hcheb
    simp only [Set.mem_ofPred_eq, sub_zero] at hω ⊢
    rwa [ha, mul_assoc]
  intro η hη
  set η' : ℝ := (min η 1).toReal
  have hmin_top : min η 1 ≠ ⊤ := ((min_le_right η 1).trans_lt ENNReal.one_lt_top).ne
  have hη' : 0 < η' := ENNReal.toReal_pos (lt_min hη one_pos).ne' hmin_top
  set M : ℝ := √(σ2 / η') + 1
  have hM : 0 < M := by positivity
  refine ⟨M, hM, Eventually.of_forall fun n => (hbound n M hM).trans ?_⟩
  have hle : σ2 / M ^ 2 ≤ η' := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : σ2 / η' ≤ M ^ 2 := by
      have h2 : √(σ2 / η') ≤ M := by linarith
      calc σ2 / η' = √(σ2 / η') ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rwa [div_le_iff₀ hη', mul_comm] at h1
  calc ENNReal.ofReal (σ2 / M ^ 2) ≤ ENNReal.ofReal η' := ENNReal.ofReal_le_ofReal hle
    _ = min η 1 := ENNReal.ofReal_toReal hmin_top
    _ ≤ η := min_le_left _ _

end Efficiency
end CausalInference
