/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredEnvelope
public import CausalInference.Efficiency.CrossFittingRate
public import CausalInference.PopulationAdjustment.StandardizationInstancesTargetSample

/-!
# The rate of the target average of a fitted surface

The unanchored standardized comparison evaluates the fitted surface of an arm,
`x ↦ g⁻¹(α̂ + xᵀβ̂)`, on a target population. When the target integral is replaced by the average
over `S` target draws `X_1, …, X_S` (sampled or simulated), the estimate
`T = S⁻¹ ∑ᵢ h(ψ̂, Xᵢ)` of `T₀ = E h(ψ₀, X)` has two errors: the fit error of `ψ̂` and the
sampling error of the target average. This file shows that the error is of order
`a + S^{-1/2}` when the fit has rate `a`.

* **Domination** (`BoundedInProbability.of_abs_le_ae`, `BoundedInProbability.of_abs_le`): a
  sequence dominated in absolute value, almost surely and for all large `n`, by a sequence
  bounded in probability is bounded in probability. Products of sequences bounded in
  probability are bounded in probability (`BoundedInProbability.mul`).
* **Averages of a nonnegative integrable function** of an i.i.d. sample are bounded in
  probability, uniformly in the number of terms, by Markov's inequality
  (`boundedInProbability_sampleMean_of_nonneg`).
* **The decomposition** (`abs_sampleMean_sub_le`, `abs_sampleMean_sub_le_rate`): if
  `|h(ψ, x) - h(ψ₀, x)| ≤ L(x) ‖ψ - ψ₀‖`, then
  `|T - T₀| ≤ C₁ a + C₂ S^{-1/2}` with `C₁ = (S⁻¹ ∑ᵢ L(Xᵢ)) ‖ψ̂ - ψ₀‖ / a` and
  `C₂ = |√S (S⁻¹ ∑ᵢ h(ψ₀, Xᵢ) - T₀)|`.
* **The rate** (`boundedInProbability_sampleMean_sub_div_rate`): for an i.i.d. target sample,
  `h(ψ₀, X)` square integrable, `L(X)` integrable, sizes `S_n > 0`, rates `a_n > 0` and
  `‖ψ̂_n - ψ₀‖ / a_n` bounded in probability, the ratio `|T_n - T₀| / (a_n + S_n^{-1/2})` is
  bounded in probability. The sampling part is bounded by Chebyshev's inequality
  (`boundedInProbability_sqrt_card_mul_finsetMean`).
* **The target mean of an arm** (`boundedInProbability_targetArmMean_div_rate`): for a
  `K`-Lipschitz inverse link and square integrable target covariates, the target average of the
  fitted surface `g⁻¹(α̂ + xᵀβ̂)` estimates the target arm mean `∫ g⁻¹(α + xᵀβ) dQ` at the rate
  `a_n + S_n^{-1/2}`, where `a_n` is the rate of the fitted cell parameters `(α̂, β̂)`.
* An instance with every hypothesis verified (`targetArmMean_rate_instance`).

## Main definitions

* `rateInstLaw`, `rateInstDraw`, `rateInstFit`: the sample, draws and fitted intercept of the
  instance.

## Main results

* `BoundedInProbability.of_abs_le_ae`, `BoundedInProbability.of_abs_le`,
  `BoundedInProbability.abs`, `BoundedInProbability.mul`.
* `boundedInProbability_sampleMean_of_nonneg`, `abs_sampleMean_sub_le`,
  `abs_sampleMean_sub_le_rate`, `boundedInProbability_sampleMean_sub_div_rate`.
* `boundedInProbability_targetArmMean_div_rate`, `targetArmMean_rate_instance`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Domination -/

/-- **Domination preserves boundedness in probability, almost surely.** If for all large `n`,
almost surely `|X n| ≤ Y n`, and `Y` is bounded in probability, then so is `X`. -/
theorem BoundedInProbability.of_abs_le_ae {X Y : ℕ → Ω → ℝ} (hY : BoundedInProbability μ Y)
    (h : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, |X n ω| ≤ Y n ω) : BoundedInProbability μ X := by
  intro η hη
  obtain ⟨M, hM, hMY⟩ := hY η hη
  refine ⟨M, hM, ?_⟩
  filter_upwards [hMY, h] with n hn hle
  refine le_trans (measure_mono_ae ?_) hn
  filter_upwards [hle] with ω hω hMω
  change M ≤ |X n ω| at hMω
  exact hMω.trans (hω.trans (le_abs_self _))

/-- **Domination preserves boundedness in probability.** If `|X n ω| ≤ Y n ω` for all `ω` and
all large `n`, and `Y` is bounded in probability, then so is `X`. -/
theorem BoundedInProbability.of_abs_le {X Y : ℕ → Ω → ℝ} (hY : BoundedInProbability μ Y)
    (h : ∀ᶠ n in atTop, ∀ ω, |X n ω| ≤ Y n ω) : BoundedInProbability μ X :=
  hY.of_abs_le_ae (h.mono fun _ hn => ae_of_all _ hn)

/-- The absolute value of a sequence bounded in probability is bounded in probability. -/
theorem BoundedInProbability.abs {X : ℕ → Ω → ℝ} (hX : BoundedInProbability μ X) :
    BoundedInProbability μ (fun n ω => |X n ω|) := by
  intro η hη
  obtain ⟨M, hM, h⟩ := hX η hη
  exact ⟨M, hM, h.mono fun n hn => by simpa only [abs_abs] using hn⟩

/-- **The product of two sequences bounded in probability is bounded in probability.** -/
theorem BoundedInProbability.mul {X Y : ℕ → Ω → ℝ} (hX : BoundedInProbability μ X)
    (hY : BoundedInProbability μ Y) : BoundedInProbability μ (fun n ω => X n ω * Y n ω) := by
  intro η hη
  obtain ⟨M₁, hM₁, h₁⟩ := hX (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨M₂, hM₂, h₂⟩ := hY (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨M₁ * M₂, by positivity, ?_⟩
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  calc μ {ω | M₁ * M₂ ≤ |X n ω * Y n ω|}
      ≤ μ ({ω | M₁ ≤ |X n ω|} ∪ {ω | M₂ ≤ |Y n ω|}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        by_contra! hlt
        rw [abs_mul] at hω
        have := mul_lt_mul'' hlt.1 hlt.2 (abs_nonneg _) (abs_nonneg _)
        linarith
    _ ≤ μ {ω | M₁ ≤ |X n ω|} + μ {ω | M₂ ≤ |Y n ω|} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hn₁ hn₂
    _ = η := ENNReal.add_halves η

/-! ### Averages of a nonnegative integrable function -/

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **Averages of a nonnegative integrable function of an i.i.d. sample are bounded in
probability**, for any numbers of terms `S n`: by Markov's inequality,
`P(S⁻¹ ∑ᵢ L(Xᵢ) ≥ M) ≤ E L(X₀) / M`. -/
theorem boundedInProbability_sampleMean_of_nonneg [IsProbabilityMeasure μ] {X : ℕ → Ω → 𝒳}
    (hX : IsIIDSample X μ) {L : 𝒳 → ℝ} (hL : Measurable L) (hL0 : ∀ x, 0 ≤ L x)
    (hLi : Integrable (fun ω => L (X 0 ω)) μ) (S : ℕ → ℕ) :
    BoundedInProbability μ (fun n ω => sampleMean L X (S n) ω) := by
  have hid := (hX.comp hL).ident
  have hint : ∀ i, Integrable (fun ω => L (X i ω)) μ := fun i => (hid i).integrable_iff.2 hLi
  set m := ∫ ω, L (X 0 ω) ∂μ
  have hm0 : 0 ≤ m := integral_nonneg fun ω => hL0 _
  have hmean : ∀ k, ∫ ω, sampleMean L X k ω ∂μ ≤ m := by
    intro k
    rw [show ∫ ω, sampleMean L X k ω ∂μ = ∫ ω, (k : ℝ)⁻¹ * ∑ i ∈ range k, L (X i ω) ∂μ from rfl,
      integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    simp only [fun i => (hid i).integral_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h, hm0]
    · rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast h.ne'), one_mul]
  have hnn : ∀ k ω, 0 ≤ sampleMean L X k ω := fun k ω =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hL0 _)
  have hintk : ∀ k, Integrable (fun ω => sampleMean L X k ω) μ := fun k =>
    (integrable_finsetSum _ fun i _ => hint i).const_mul _
  intro η hη
  have hmin0 : min η 1 ≠ 0 := (lt_min hη one_pos).ne'
  have hmintop : min η 1 ≠ ⊤ := ((min_le_right η 1).trans_lt ENNReal.one_lt_top).ne
  set η' : ℝ := (min η 1).toReal with hη'def
  have hη'pos : 0 < η' := ENNReal.toReal_pos hmin0 hmintop
  have hη'le : ENNReal.ofReal η' ≤ η := by
    rw [hη'def, ENNReal.ofReal_toReal hmintop]
    exact min_le_left _ _
  refine ⟨m / η' + 1, by positivity, Eventually.of_forall fun n => ?_⟩
  set M := m / η' + 1
  have hM : 0 < M := by positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (hnn (S n))) (hintk (S n)) M
  have hreal : μ.real {ω | M ≤ sampleMean L X (S n) ω} ≤ η' := by
    have h1 : M * μ.real {ω | M ≤ sampleMean L X (S n) ω} ≤ m := hmk.trans (hmean _)
    have h2 : m ≤ M * η' := by
      have : m = m / η' * η' := by field_simp
      nlinarith
    exact le_of_mul_le_mul_left (h1.trans h2) hM
  refine le_trans ?_ hη'le
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine (ENNReal.ofReal_le_ofReal hreal).trans' (le_of_eq ?_)
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, abs_of_nonneg (hnn _ ω)]

/-! ### The decomposition of the target error -/

variable {E : Type*} [SeminormedAddCommGroup E]

omit [MeasurableSpace 𝒳] in
/-- **The target error splits into a fit part and a sampling part.** If
`|h(ψ, x) - h(ψ₀, x)| ≤ L(x) ‖ψ - ψ₀‖` for every `x`, then for every sample `x₀, x₁, …` and every
`k`, `|k⁻¹ ∑_{i<k} h(ψ, xᵢ) - T₀| ≤ (k⁻¹ ∑_{i<k} L(xᵢ)) ‖ψ - ψ₀‖ + |k⁻¹ ∑_{i<k} h(ψ₀, xᵢ) - T₀|`. -/
theorem abs_sampleMean_sub_le {h : E → 𝒳 → ℝ} {L : 𝒳 → ℝ} {ψ₀ : E}
    (hLip : ∀ ψ x, |h ψ x - h ψ₀ x| ≤ L x * ‖ψ - ψ₀‖) (ψ : E) (X : ℕ → Ω → 𝒳) (k : ℕ)
    (ω : Ω) (T₀ : ℝ) :
    |sampleMean (h ψ) X k ω - T₀| ≤
      sampleMean L X k ω * ‖ψ - ψ₀‖ + |sampleMean (h ψ₀) X k ω - T₀| := by
  have hsplit : sampleMean (h ψ) X k ω - T₀ =
      (k : ℝ)⁻¹ * ∑ i ∈ range k, (h ψ (X i ω) - h ψ₀ (X i ω)) +
        (sampleMean (h ψ₀) X k ω - T₀) := by
    simp only [sampleMean, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
  rw [abs_mul, abs_of_nonneg (by positivity), sampleMean, mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hLip _ _)) (by positivity)

omit [MeasurableSpace 𝒳] in
/-- **The error bound `|T - T₀| ≤ C₁ a + C₂ S^{-1/2}`**, with `C₁ = L̄ ‖ψ - ψ₀‖ / a`,
`L̄ = S⁻¹ ∑_{i<S} L(xᵢ)`, and `C₂ = |√S (S⁻¹ ∑_{i<S} h(ψ₀, xᵢ) - T₀)|`, for `a > 0` and `S > 0`;
dividing, `|T - T₀| / (a + S^{-1/2}) ≤ |C₁| + C₂`. -/
theorem abs_sampleMean_sub_le_rate {h : E → 𝒳 → ℝ} {L : 𝒳 → ℝ} {ψ₀ : E}
    (hLip : ∀ ψ x, |h ψ x - h ψ₀ x| ≤ L x * ‖ψ - ψ₀‖) (ψ : E) (X : ℕ → Ω → 𝒳) {S : ℕ}
    (hS : 0 < S) {a : ℝ} (ha : 0 < a) (ω : Ω) (T₀ : ℝ) :
    |sampleMean (h ψ) X S ω - T₀| ≤
        sampleMean L X S ω * ‖ψ - ψ₀‖ / a * a +
          |√(S : ℝ) * (sampleMean (h ψ₀) X S ω - T₀)| * (√(S : ℝ))⁻¹ ∧
      |sampleMean (h ψ) X S ω - T₀| / (a + (√(S : ℝ))⁻¹) ≤
        |sampleMean L X S ω * ‖ψ - ψ₀‖ / a| +
          |√(S : ℝ) * (sampleMean (h ψ₀) X S ω - T₀)| := by
  have hsq : 0 < √(S : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hS)
  have hR : |√(S : ℝ) * (sampleMean (h ψ₀) X S ω - T₀)| * (√(S : ℝ))⁻¹ =
      |sampleMean (h ψ₀) X S ω - T₀| := by
    rw [abs_mul, abs_of_pos hsq, mul_comm, ← mul_assoc, inv_mul_cancel₀ hsq.ne', one_mul]
  have hA : sampleMean L X S ω * ‖ψ - ψ₀‖ / a * a = sampleMean L X S ω * ‖ψ - ψ₀‖ := by
    field_simp
  have h1 := abs_sampleMean_sub_le hLip ψ X S ω T₀
  refine ⟨by rw [hA, hR]; exact h1, ?_⟩
  set C₁ := sampleMean L X S ω * ‖ψ - ψ₀‖ / a
  set C₂ := |√(S : ℝ) * (sampleMean (h ψ₀) X S ω - T₀)|
  have hs : 0 < (√(S : ℝ))⁻¹ := inv_pos.2 hsq
  have hD : 0 < a + (√(S : ℝ))⁻¹ := by linarith
  rw [div_le_iff₀ hD]
  have hb : |sampleMean (h ψ) X S ω - T₀| ≤ C₁ * a + C₂ * (√(S : ℝ))⁻¹ := by
    rw [hA, hR]; exact h1
  have hC₁ : C₁ * a ≤ |C₁| * a := mul_le_mul_of_nonneg_right (le_abs_self _) ha.le
  nlinarith [mul_nonneg (abs_nonneg C₁) hs.le, mul_nonneg (abs_nonneg (√(S : ℝ) *
    (sampleMean (h ψ₀) X S ω - T₀))) ha.le]

/-! ### The rate -/

/-- **The target average of a fitted function has error of order `a_n + S_n^{-1/2}`.** Let
`X` be an i.i.d. sample of target draws, `h(ψ₀, ·)` measurable with `h(ψ₀, X₀)` square
integrable and mean `T₀`, and let `|h(ψ, x) - h(ψ₀, x)| ≤ L(x) ‖ψ - ψ₀‖` with `L ≥ 0` measurable
and `L(X₀)` integrable. If the sizes `S_n` and rates `a_n` are positive and the fit satisfies
`‖ψ̂_n - ψ₀‖ / a_n` bounded in probability, then
`|S_n⁻¹ ∑_{i<S_n} h(ψ̂_n, Xᵢ) - T₀| / (a_n + S_n^{-1/2})` is bounded in probability. No
independence between the fit and the target draws is used. -/
theorem boundedInProbability_sampleMean_sub_div_rate [IsProbabilityMeasure μ]
    {X : ℕ → Ω → 𝒳} (hX : IsIIDSample X μ) {h : E → 𝒳 → ℝ} {ψ₀ : E}
    (hh : Measurable (h ψ₀)) (hh2 : MemLp (fun ω => h ψ₀ (X 0 ω)) 2 μ) {L : 𝒳 → ℝ}
    (hL : Measurable L) (hL0 : ∀ x, 0 ≤ L x) (hLi : Integrable (fun ω => L (X 0 ω)) μ)
    (hLip : ∀ ψ x, |h ψ x - h ψ₀ x| ≤ L x * ‖ψ - ψ₀‖) {S : ℕ → ℕ} (hS : ∀ n, 0 < S n)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {ψhat : ℕ → Ω → E}
    (hfit : BoundedInProbability μ (fun n ω => ‖ψhat n ω - ψ₀‖ / a n)) :
    BoundedInProbability μ (fun n ω =>
      |sampleMean (h (ψhat n ω)) X (S n) ω - ∫ ω', h ψ₀ (X 0 ω') ∂μ| /
        (a n + (√(S n : ℝ))⁻¹)) := by
  set T₀ := ∫ ω', h ψ₀ (X 0 ω') ∂μ
  have hfit' := (boundedInProbability_sampleMean_of_nonneg hX hL hL0 hLi S).mul hfit
  have hsamp : BoundedInProbability μ (fun n ω =>
      √(S n : ℝ) * (sampleMean (h ψ₀) X (S n) ω - T₀)) := by
    have := Efficiency.boundedInProbability_sqrt_card_mul_finsetMean hX
      (hh.sub measurable_const) (hh2.sub (memLp_const T₀)) (by
        simp only [Pi.sub_apply]
        rw [integral_sub (hh2.integrable one_le_two) (integrable_const _), integral_const]
        simp) (fun n => Finset.range (S n))
    refine this.abs.of_abs_le (Eventually.of_forall fun n ω => le_of_eq ?_)
    rw [Finset.card_range]
    congr 2
    simp only [sampleMean, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have : (S n : ℝ) ≠ 0 := by exact_mod_cast (hS n).ne'
    field_simp
    rfl
  refine (hfit'.abs.add hsamp.abs).of_abs_le (Eventually.of_forall fun n ω => ?_)
  have hpos : 0 ≤ a n + (√(S n : ℝ))⁻¹ := by have := ha n; positivity
  rw [abs_of_nonneg (div_nonneg (abs_nonneg _) hpos)]
  have := (abs_sampleMean_sub_le_rate hLip (ψhat n ω) X (hS n) (ha n) ω T₀).2
  refine this.trans (le_of_eq ?_)
  congr 2
  ring

/-! ### The target mean of an arm of the multilevel model -/

namespace NetworkMetaRegression

variable {p : ℕ}

/-- **The fitted surface is Lipschitz in the cell parameters.** For a `K`-Lipschitz `g⁻¹`,
`|g⁻¹(α + xᵀβ) - g⁻¹(α₀ + xᵀβ₀)| ≤ K (1 + ∑ᵢ |xᵢ|) ‖(α, β) - (α₀, β₀)‖`. -/
theorem abs_inv_link_affine_sub_le {ginv : ℝ → ℝ} {K : NNReal} (hL : LipschitzWith K ginv)
    (ψ ψ₀ : ℝ × (Fin p → ℝ)) (x : Fin p → ℝ) :
    |ginv (ψ.1 + x ⬝ᵥ ψ.2) - ginv (ψ₀.1 + x ⬝ᵥ ψ₀.2)| ≤
      K * (1 + ∑ i, |x i|) * ‖ψ - ψ₀‖ := by
  have h1 := hL.dist_le_mul (ψ.1 + x ⬝ᵥ ψ.2) (ψ₀.1 + x ⬝ᵥ ψ₀.2)
  rw [Real.dist_eq, Real.dist_eq] at h1
  have hfst : |ψ.1 - ψ₀.1| ≤ ‖ψ - ψ₀‖ := by
    have := norm_fst_le (ψ - ψ₀)
    rwa [Prod.fst_sub, Real.norm_eq_abs] at this
  have hsnd : ∀ i, |ψ.2 i - ψ₀.2 i| ≤ ‖ψ - ψ₀‖ := fun i => by
    have := (norm_le_pi_norm (ψ - ψ₀).2 i).trans (norm_snd_le (ψ - ψ₀))
    rwa [Prod.snd_sub, Pi.sub_apply, Real.norm_eq_abs] at this
  have h2 : |(ψ.1 + x ⬝ᵥ ψ.2) - (ψ₀.1 + x ⬝ᵥ ψ₀.2)| ≤ (1 + ∑ i, |x i|) * ‖ψ - ψ₀‖ := by
    rw [show (ψ.1 + x ⬝ᵥ ψ.2) - (ψ₀.1 + x ⬝ᵥ ψ₀.2) = (ψ.1 - ψ₀.1) + x ⬝ᵥ (ψ.2 - ψ₀.2) by
      rw [dotProduct_sub]; ring]
    refine (abs_add_le _ _).trans ?_
    rw [add_mul, one_mul, Finset.sum_mul]
    refine add_le_add hfst ((abs_dotProduct_le_sum x _).trans (Finset.sum_le_sum fun i _ => ?_))
    exact mul_le_mul_of_nonneg_left (by simpa using hsnd i) (abs_nonneg _)
  calc _ ≤ K * |(ψ.1 + x ⬝ᵥ ψ.2) - (ψ₀.1 + x ⬝ᵥ ψ₀.2)| := h1
    _ ≤ K * ((1 + ∑ i, |x i|) * ‖ψ - ψ₀‖) := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
    _ = _ := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The target average of the fitted surface of an arm estimates its target mean at the rate
`a_n + S_n^{-1/2}`.** Let `g⁻¹` be `K`-Lipschitz, let `X` be an i.i.d. sample of target
covariates with law `Q` and square integrable coordinates, let `S_n > 0` and `a_n > 0`, and let
the fitted cell parameters `(α̂_n, β̂_n)` of arm `k` (baseline of study `j`) satisfy
`‖(α̂_n, β̂_n) - (μ_j + γ_k, β₁ + β₂,k)‖ / a_n` bounded in probability. Then
`|S_n⁻¹ ∑_{i<S_n} g⁻¹(α̂_n + Xᵢᵀβ̂_n) - ∫ m_k dQ| / (a_n + S_n^{-1/2})` is bounded in
probability, where `∫ m_k dQ` is the mean of the surface of `k` at the baseline `μ_j` under
`Q`. -/
theorem boundedInProbability_targetArmMean_div_rate {J K' : Type*} (M : MultilevelModel J K' p)
    (j : J) (k : K') {ginv : ℝ → ℝ} {K : NNReal} (hL : LipschitzWith K ginv)
    {X : ℕ → Ω → Fin p → ℝ} (hX : IsIIDSample X P) (hX2 : ∀ i, MemLp (fun ω => X 0 ω i) 2 P)
    {Q : Measure (Fin p → ℝ)} (hQ : P.map (X 0) = Q) {S : ℕ → ℕ} (hS : ∀ n, 0 < S n)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {αhat : ℕ → Ω → ℝ} {βhat : ℕ → Ω → Fin p → ℝ}
    (hfit : BoundedInProbability P (fun n ω =>
      ‖(αhat n ω, βhat n ω) - (M.cellIntercept j k, M.cellSlope k)‖ / a n)) :
    BoundedInProbability P (fun n ω =>
      |sampleMean (fun x => ginv (αhat n ω + x ⬝ᵥ βhat n ω)) X (S n) ω -
          M.armMean ginv (M.μ j) Q k| / (a n + (√(S n : ℝ))⁻¹)) := by
  set ψ₀ : ℝ × (Fin p → ℝ) := (M.cellIntercept j k, M.cellSlope k)
  set h : ℝ × (Fin p → ℝ) → (Fin p → ℝ) → ℝ := fun ψ x => ginv (ψ.1 + x ⬝ᵥ ψ.2)
  have hcont : Continuous (h ψ₀) := hL.continuous.comp (by unfold dotProduct; fun_prop)
  have hX0 : AEMeasurable (X 0) P := (hX.ident 0).aemeasurable_fst
  have hXi : ∀ i, Integrable (fun ω => X 0 ω i) P := fun i => (hX2 i).integrable one_le_two
  have hh2 : MemLp (fun ω => h ψ₀ (X 0 ω)) 2 P := by
    refine MemLp.of_le (g := fun ω => |ginv 0| + K * (|ψ₀.1| + ∑ i, |X 0 ω i| * |ψ₀.2 i|))
      ((memLp_const _).add (((memLp_const _).add (memLp_finsetSum _ fun i _ =>
        ((hX2 i).norm.mul_const |ψ₀.2 i|).congr_norm (by
          exact ((hX2 i).norm.mul_const _).aestronglyMeasurable) (ae_of_all _ fun ω => by
            simp [Real.norm_eq_abs]))).const_mul _))
      (hcont.comp_aestronglyMeasurable hX0.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    have hb := abs_inv_link_affine_sub_le hL ψ₀ (0, 0) (X 0 ω)
    have hl := hL.dist_le_mul (ψ₀.1 + X 0 ω ⬝ᵥ ψ₀.2) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at hl
    have hd : |ψ₀.1 + X 0 ω ⬝ᵥ ψ₀.2| ≤ |ψ₀.1| + ∑ i, |X 0 ω i| * |ψ₀.2 i| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_dotProduct_le_sum _ _))
    have hK := mul_le_mul_of_nonneg_left hd K.coe_nonneg
    have hpos : 0 ≤ |ginv 0| + K * (|ψ₀.1| + ∑ i, |X 0 ω i| * |ψ₀.2 i|) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
    simp only [h]
    linarith [abs_sub_abs_le_abs_sub (ginv (ψ₀.1 + X 0 ω ⬝ᵥ ψ₀.2)) (ginv 0)]
  have hLi : Integrable (fun ω => (K : ℝ) * (1 + ∑ i, |X 0 ω i|)) P :=
    ((integrable_const 1).add (integrable_finsetSum _ fun i _ => (hXi i).abs)).const_mul _
  have hmain := boundedInProbability_sampleMean_sub_div_rate (h := h) (ψ₀ := ψ₀)
    (L := fun x => (K : ℝ) * (1 + ∑ i, |x i|)) hX hcont.measurable hh2
    (by fun_prop) (fun x => by positivity) hLi
    (fun ψ x => abs_inv_link_affine_sub_le hL ψ ψ₀ x) hS ha hfit
  have hT₀ : ∫ ω, h ψ₀ (X 0 ω) ∂P = M.armMean ginv (M.μ j) Q k := by
    rw [MultilevelModel.armMean_eq_cell, shiftMean, ← hQ,
      integral_map hX0 hcont.aestronglyMeasurable]
  rw [hT₀] at hmain
  exact hmain

/-! ### An instance -/

/-- The law of the target draws: independent copies of `binaryLaw (1/2)`. -/
noncomputable def rateInstLaw : Measure (ℕ → Fin 1 → ℝ) :=
  Measure.infinitePi fun _ => binaryLaw (1 / 2)

instance : IsProbabilityMeasure rateInstLaw := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  unfold rateInstLaw; infer_instance

/-- The target draws: the coordinates. -/
def rateInstDraw (i : ℕ) (ω : ℕ → Fin 1 → ℝ) : Fin 1 → ℝ := id (ω i)

theorem isIIDSample_rateInstDraw : IsIIDSample rateInstDraw rateInstLaw := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  exact PopulationAdjustment.isIIDSample_infinitePi_comp _ measurable_id

theorem map_rateInstDraw : rateInstLaw.map (rateInstDraw 0) = binaryLaw (1 / 2) := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have := PopulationAdjustment.map_infinitePi_comp_eval (binaryLaw (1 / 2)) measurable_id 0
  rw [Measure.map_id] at this
  exact this

theorem memLp_rateInstDraw (f : (Fin 1 → ℝ) → ℝ) (hf : Measurable f) :
    MemLp (fun ω => f (rateInstDraw 0 ω)) 2 rateInstLaw := by
  have hm : AEMeasurable (rateInstDraw 0) rateInstLaw := (measurable_pi_apply 0).aemeasurable
  have := (memLp_map_measure_iff (μ := rateInstLaw) (p := 2) hf.aestronglyMeasurable hm).1 (by
    rw [map_rateInstDraw, memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
    exact integrable_binaryLaw _ _)
  exact this

theorem integral_rateInstDraw (f : (Fin 1 → ℝ) → ℝ) (hf : Measurable f) :
    ∫ ω, f (rateInstDraw 0 ω) ∂rateInstLaw =
      (1 / 2) * f (fun _ => 0) + (1 / 2) * f (fun _ => 1) := by
  have hm : AEMeasurable (rateInstDraw 0) rateInstLaw := (measurable_pi_apply 0).aemeasurable
  rw [← integral_map hm hf.aestronglyMeasurable, map_rateInstDraw,
    integral_binaryLaw ⟨by norm_num, by norm_num⟩]
  norm_num

/-- The fitted intercept: the true intercept `0` plus the centered sample mean of the first
`n + 1` draws, an error of order `n^{-1/2}`. -/
noncomputable def rateInstFit (n : ℕ) (ω : ℕ → Fin 1 → ℝ) : ℝ :=
  sampleMean (fun x => x 0) rateInstDraw (n + 1) ω - 1 / 2

/-- **Instance of the rate of the target arm mean.** The identity link, the model with intercepts
`0`, prognostic effect `β₁ = 1` and no treatment parameters, arm `true` in study `true`, target
draws from `binaryLaw (1/2)`, `S_n = n + 1` draws, the fitted intercept `rateInstFit` with the
true slope, and the rate `a_n = (n + 1)^{-1/2}`. The target mean is `1/2`, and
`|S_n⁻¹ ∑_{i<S_n} (α̂_n + Xᵢ) - 1/2| / (2 (n + 1)^{-1/2})` is bounded in probability. -/
theorem targetArmMean_rate_instance :
    let M : MultilevelModel Bool Bool 1 := ⟨fun _ => 0, fun _ => 1, 0, 0⟩
    M.armMean id (M.μ true) (binaryLaw (1 / 2)) true = 1 / 2 ∧
      BoundedInProbability rateInstLaw (fun n ω =>
        |sampleMean (fun x => id (rateInstFit n ω + x ⬝ᵥ M.cellSlope true)) rateInstDraw (n + 1)
            ω - 1 / 2| / ((√((n : ℝ) + 1))⁻¹ + (√((n + 1 : ℕ) : ℝ))⁻¹)) := by
  intro M
  have hmean : M.armMean id (M.μ true) (binaryLaw (1 / 2)) true = 1 / 2 := by
    rw [MultilevelModel.armMean, integral_binaryLaw ⟨by norm_num, by norm_num⟩]
    simp [M, MultilevelModel.surface, MultilevelModel.eta,
      NetworkMetaAnalysis.metaRegressionPredictor, dotProduct]
  have hci : M.cellIntercept true true = 0 := by simp [M, MultilevelModel.cellIntercept]
  have hfit : BoundedInProbability rateInstLaw (fun n ω =>
      ‖(rateInstFit n ω, M.cellSlope true) - (M.cellIntercept true true, M.cellSlope true)‖ /
        (√((n : ℝ) + 1))⁻¹) := by
    have hm : Measurable fun x : Fin 1 → ℝ => x 0 - 1 / 2 := by fun_prop
    have hb := Efficiency.boundedInProbability_sqrt_card_mul_finsetMean isIIDSample_rateInstDraw
      hm (memLp_rateInstDraw _ hm) (by rw [integral_rateInstDraw _ hm]; norm_num)
      (fun n => Finset.range (n + 1))
    refine hb.abs.of_abs_le (Eventually.of_forall fun n ω => le_of_eq ?_)
    have hnorm : ‖(rateInstFit n ω, M.cellSlope true) -
        (M.cellIntercept true true, M.cellSlope true)‖ = |rateInstFit n ω| := by
      rw [hci, Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_def]
      simp
    have hin : ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), (rateInstDraw i ω 0 - 1 / 2) =
        rateInstFit n ω := by
      simp only [rateInstFit, sampleMean, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hnorm, Finset.card_range, hin, div_inv_eq_mul, abs_mul, abs_mul, abs_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
    push_cast
    rfl
  have h := boundedInProbability_targetArmMean_div_rate M true true (ginv := id)
    LipschitzWith.id isIIDSample_rateInstDraw
    (fun i => memLp_rateInstDraw (fun x => x i) (measurable_pi_apply i))
    map_rateInstDraw (S := fun n => n + 1) (fun n => n.succ_pos)
    (a := fun n => (√((n : ℝ) + 1))⁻¹) (fun n => by positivity) hfit
  rw [hmean] at h
  exact ⟨hmean, h⟩

end NetworkMetaRegression

end CausalInference
