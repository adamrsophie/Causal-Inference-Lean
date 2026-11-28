/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderInstances

/-!
# A directional moment in place of the norm moment

The dispersion of the entropy balancing weights (`balancingDispersionVanishes_of_isMinOn`) is
proved under `E[exp(κ ‖φ - t‖)] < ∞` with `κ > 2 p ‖β*‖`. The factor `2` comes from the squared
weights in the numerator of the dispersion, `exp(2 β̂ᵀΔ)`, and only the direction of `β*` matters
there: near `β*`, `exp(2 β̂ᵀΔ) ≤ exp(2 β*ᵀΔ) exp(2 p r ‖Δ‖)`. This file splits the hypothesis
into

* a **norm moment of order `κ > p ‖β*‖`** (without the factor `2`), used for the consistency of
  the sample dual minimizer (`tendstoInMeasure_dualMinimizer_of_isMinOn`) and for a small
  envelope `exp(s ‖Δ‖)`, and
* a **one sided directional moment** `E[exp(2 (1 + ε) β*ᵀ(φ - t))] < ∞` for some `ε > 0`: the
  second moment of the population weight `w* = exp(β*ᵀ(φ - t))`, with some room.

The product `exp(2 β*ᵀΔ) exp(s ‖Δ‖)` is integrable by convexity of `exp`:
`exp(a + b) ≤ exp((1 + ε) a) + exp((1 + ε) b / ε)` (`exp_add_le_exp_add_exp`), with no Hölder
inequality. The dispersion then vanishes (`balancingDispersionVanishes_of_isMinOn_directional`)
and the weighted arm mean is consistent
(`sampleBalancedArmMean_isConsistent_of_isMinOn_directional`,
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn_directional`).

**The norm condition is a special case** (`directional_of_norm`): `κ > 2 p ‖β*‖` gives both
hypotheses. **It is a strict refinement**: for the standard exponential law at `t = 3/5`,
`β* = -2/3`, the norm condition fails for every order (`not_exists_order_expMeasure_three_fifths`)
while the directional one holds, and the weighted arm mean of the coin trial is consistent
(`momentOrderInst_directional_consistent`). The dimension factor `p` remains in the norm moment
`κ > p ‖β*‖`.

## Main results

* `sum_sq_entropyWeights_mul_le_of_bounds`, `exp_add_le_exp_add_exp`.
* `balancingDispersionVanishes_of_isMinOn_directional`,
  `sampleBalancedArmMean_isConsistent_of_isMinOn_directional`,
  `sampleBalancedArmMean_isConsistent_trial_of_isMinOn_directional`.
* `directional_of_norm`, `directional_of_norm_momentOrderExpLaw`,
  `not_exists_order_expMeasure_three_fifths`,
  `momentOrderInst_directional_consistent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-! ### Elementary bounds -/

section Bounds

variable {n p : ℕ}

/-- **The dispersion bound with separate upper and lower bounds.** If `βᵀΔᵢ ≤ uᵢ` and
`βᵀΔⱼ ≥ -hⱼ` for every unit and `wᵢ ≥ 0`, then
`∑ᵢ cᵢ² wᵢ ≤ (∑ᵢ exp(2 uᵢ) wᵢ) / (∑ⱼ exp(-hⱼ))²` for the entropy weights `c` of `β`. -/
theorem sum_sq_entropyWeights_mul_le_of_bounds [Nonempty (Fin n)] {Δ : Fin n → Fin p → ℝ}
    {β : Fin p → ℝ} {u h : Fin n → ℝ} (hu : ∀ i, β ⬝ᵥ Δ i ≤ u i)
    (hh : ∀ j, -h j ≤ β ⬝ᵥ Δ j) {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) :
    ∑ i, entropyWeights Δ β i ^ 2 * w i ≤
      (∑ i, Real.exp (2 * u i) * w i) / (∑ j, Real.exp (-h j)) ^ 2 := by
  have hD : 0 < ∑ j, Real.exp (-h j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ : ∑ j, Real.exp (-h j) ≤ partitionFunction Δ β :=
    Finset.sum_le_sum fun j _ => Real.exp_le_exp.2 (hh j)
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : entropyWeights Δ β i ≤ Real.exp (u i) / ∑ j, Real.exp (-h j) := by
    rw [entropyWeights]
    calc Real.exp (β ⬝ᵥ Δ i) / partitionFunction Δ β
        ≤ Real.exp (u i) / partitionFunction Δ β :=
          (div_le_div_iff_of_pos_right (partitionFunction_pos β)).2
            (Real.exp_le_exp.2 (hu i))
      _ ≤ Real.exp (u i) / ∑ j, Real.exp (-h j) := by gcongr
  have h0 : 0 ≤ entropyWeights Δ β i := (entropyWeights_pos β i).le
  calc entropyWeights Δ β i ^ 2 * w i ≤ (Real.exp (u i) / ∑ j, Real.exp (-h j)) ^ 2 * w i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (hw i)
    _ = Real.exp (2 * u i) * w i / (∑ j, Real.exp (-h j)) ^ 2 := by
        rw [div_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

/-- **Convexity of `exp` splits a product**: `exp(a + b) ≤ exp((1 + ε) a) + exp((1 + ε) b / ε)`
for `ε > 0`. -/
theorem exp_add_le_exp_add_exp {a b ε : ℝ} (hε : 0 < ε) :
    Real.exp (a + b) ≤ Real.exp ((1 + ε) * a) + Real.exp ((1 + ε) / ε * b) := by
  have h1 : 0 < 1 + ε := by linarith
  have hl : (0 : ℝ) ≤ 1 / (1 + ε) := by positivity
  have hm : (0 : ℝ) ≤ ε / (1 + ε) := by positivity
  have hs : 1 / (1 + ε) + ε / (1 + ε) = 1 := by field_simp
  have hc := convexOn_exp.2 (Set.mem_univ ((1 + ε) * a)) (Set.mem_univ ((1 + ε) / ε * b)) hl hm hs
  simp only [smul_eq_mul] at hc
  have he : 1 / (1 + ε) * ((1 + ε) * a) + ε / (1 + ε) * ((1 + ε) / ε * b) = a + b := by
    field_simp
  rw [he] at hc
  have hl1 : 1 / (1 + ε) ≤ 1 := (div_le_one h1).2 (by linarith)
  have hm1 : ε / (1 + ε) ≤ 1 := (div_le_one h1).2 (by linarith)
  have e1 := Real.exp_pos ((1 + ε) * a)
  have e2 := Real.exp_pos ((1 + ε) / ε * b)
  nlinarith [mul_le_mul_of_nonneg_right hl1 e1.le, mul_le_mul_of_nonneg_right hm1 e2.le]

end Bounds

/-! ### Dispersion under a directional moment -/

section Dispersion

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪] {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {p : ℕ}

/-- **The weights disperse under a norm moment of order `p ‖β*‖` and a directional moment.**
Under the margin condition at `t`, reported targets `tₙ → t` in probability, a minimizer `β*` of
the population dual objective, `E[exp(κ ‖f - t‖)] < ∞` for some `κ > p ‖β*‖`, and
`E[exp(2 (1 + ε) β*ᵀ(f - t))] < ∞` for some `ε > 0`, the dispersion
`∑ᵢ cₙᵢ² (1 + ‖f(Oᵢ) - t‖²)` of the entropy balancing weights at `tₙ` tends to zero in
probability. -/
theorem balancingDispersionVanishes_of_isMinOn_directional (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {f : 𝒪 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) f t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun z => Real.exp (κ * ‖f z - t‖)) (P.map (O 0)))
    (hκ : p * ‖βs‖ < κ) {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun z => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (f z - t)))) (P.map (O 0))) :
    BalancingDispersionVanishes P f t O tm := by
  have hpb : 0 ≤ (p : ℝ) * ‖βs‖ := by positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hpb hκ
  obtain ⟨-, hconv⟩ := tendstoInMeasure_dualMinimizer_of_isMinOn hO hf hδ hmargin htm hmin hexp hκ
  set r : ℝ := ε * κ / ((1 + ε) * (2 * p + 1)) with hr
  have hr0 : 0 < r := by positivity
  have hrκ : (1 + ε) / ε * ((2 * p + 1) * r) = κ := by rw [hr]; field_simp
  set S : ℝ := ‖βs‖ + r with hS
  have hS0 : 0 < S := by positivity
  set c0 : ℝ := p * S * r with hc0
  set g : 𝒪 → ℝ := fun z => ‖f z - t‖ with hg
  have hgm : Measurable g := (hf.sub_const t).norm
  have hdm : Measurable fun z => βs ⬝ᵥ (f z - t) :=
    (continuous_const.dotProduct continuous_id).measurable.comp (hf.sub_const t)
  set A : 𝒪 → ℝ := fun z => Real.exp (2 * (βs ⬝ᵥ (f z - t)) + 2 * p * r * g z) * (1 + g z ^ 2)
    with hA
  set B : 𝒪 → ℝ := fun z => Real.exp (-(p * S * g z)) with hB
  have hAm : Measurable A :=
    (Real.measurable_exp.comp ((measurable_const.mul hdm).add (measurable_const.mul hgm))).mul
      (measurable_const.add (hgm.pow_const 2))
  have hBm : Measurable B := Real.measurable_exp.comp (measurable_const.mul hgm).neg
  have hAi : Integrable A (P.map (O 0)) := by
    refine ((hdir.add hexp).const_mul (1 + 2 / r ^ 2)).mono' hAm.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    have hg0 : 0 ≤ g z := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hy := exp_add_le_exp_add_exp (a := 2 * (βs ⬝ᵥ (f z - t))) (b := (2 * p + 1) * r * g z) hε
    have e1 : (1 + ε) * (2 * (βs ⬝ᵥ (f z - t))) = 2 * (1 + ε) * (βs ⬝ᵥ (f z - t)) := by ring
    have e2 : (1 + ε) / ε * ((2 * p + 1) * r * g z) = κ * ‖f z - t‖ := by
      rw [← hrκ]; simp only [hg]; ring
    rw [e1, e2] at hy
    calc Real.exp (2 * (βs ⬝ᵥ (f z - t)) + 2 * p * r * g z) * (1 + g z ^ 2)
        ≤ Real.exp (2 * (βs ⬝ᵥ (f z - t)) + 2 * p * r * g z) *
            ((1 + 2 / r ^ 2) * Real.exp (r * g z)) := by
          gcongr; exact one_add_sq_le_mul_exp hg0 hr0
      _ = (1 + 2 / r ^ 2) * Real.exp (2 * (βs ⬝ᵥ (f z - t)) + (2 * p + 1) * r * g z) := by
          rw [mul_left_comm, ← Real.exp_add]; ring_nf
      _ ≤ (1 + 2 / r ^ 2) * (Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (f z - t))) +
            Real.exp (κ * ‖f z - t‖)) := by gcongr
  have hBi : Integrable B (P.map (O 0)) :=
    (integrable_const (1 : ℝ)).mono' hBm.aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (by positivity) (norm_nonneg _))
  have hAP := integrable_comp_of_isIIDSample hO hOm hAi 0
  have hBP := integrable_comp_of_isIIDSample hO hOm hBi 0
  have hEB : 0 < ∫ ω, B (O 0 ω) ∂P := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) hBP]
    have : Function.support (fun ω => B (O 0 ω)) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (Real.exp_pos _).ne'
    rw [this, measure_univ]; exact one_pos
  have hAc := sampleMean_isConsistent hO hAm hAP
  have hBc := sampleMean_isConsistent hO hBm hBP
  set G : ℝ × ℝ → ℝ := fun u => u.1 / u.2 ^ 2 with hG
  have hGc : ContinuousAt G ((∫ ω, A (O 0 ω) ∂P), (∫ ω, B (O 0 ω) ∂P)) :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hEB.ne')
  have hY := ((tendstoInMeasure_inv_natCast_mul_zero
    ((hAc.prodMk hBc).comp_continuousAt hGc)).const_mul (Real.exp (4 * c0)))
  simp only [mul_zero] at hY
  refine tendstoInMeasure_zero_of_abs_le_of_tendstoInMeasure
    (((withProbTendingToOne_balancingFeasible hO hf hδ hmargin htm).inter
      (hconv.withProbTendingToOne_dist_lt hr0)).inter
        (htm.withProbTendingToOne_dist_lt hr0)) hY fun n ω hω => ?_
  obtain ⟨⟨⟨hn, -⟩, hβ⟩, he⟩ := hω
  simp only [Set.mem_ofPred_eq, dist_eq_norm] at hβ he
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Δ : Fin n → Fin p → ℝ := fun j => f (O j ω) - tm n ω with hΔ
  set β := dualMinimizer Δ with hβdef
  have hβS : ‖β‖ ≤ S := by
    calc ‖β‖ = ‖(β - βs) + βs‖ := by rw [sub_add_cancel]
      _ ≤ ‖β - βs‖ + ‖βs‖ := norm_add_le _ _
      _ ≤ S := by rw [hS]; linarith
  have hsplit : ∀ j : Fin n, Δ j = (f (O j ω) - t) - (tm n ω - t) := fun j => by simp [hΔ]
  have hup : ∀ i : Fin n, β ⬝ᵥ Δ i ≤
      βs ⬝ᵥ (f (O i ω) - t) + p * r * g (O i ω) + c0 := fun i => by
    have h1 : β ⬝ᵥ Δ i = βs ⬝ᵥ (f (O i ω) - t) + (β - βs) ⬝ᵥ (f (O i ω) - t) -
        β ⬝ᵥ (tm n ω - t) := by
      rw [hsplit i, dotProduct_sub, sub_dotProduct]; ring
    have h2 : (β - βs) ⬝ᵥ (f (O i ω) - t) ≤ p * r * g (O i ω) := by
      refine (le_abs_self _).trans ((abs_dotProduct_le_mul_norm _ _).trans ?_)
      calc (p : ℝ) * (‖β - βs‖ * ‖f (O i ω) - t‖) ≤ p * (r * ‖f (O i ω) - t‖) := by gcongr
        _ = p * r * g (O i ω) := by simp only [hg]; ring
    have h3 : -(β ⬝ᵥ (tm n ω - t)) ≤ c0 := by
      refine (neg_le_abs _).trans ((abs_dotProduct_le_mul_norm _ _).trans ?_)
      calc (p : ℝ) * (‖β‖ * ‖tm n ω - t‖) ≤ p * (S * r) := by gcongr
        _ = c0 := by rw [hc0]; ring
    linarith
  have hlow : ∀ j : Fin n, -(p * S * g (O j ω) + c0) ≤ β ⬝ᵥ Δ j := fun j => by
    refine neg_le_of_abs_le ((abs_dotProduct_le_mul_norm β (Δ j)).trans ?_)
    have h1 : ‖Δ j‖ ≤ g (O j ω) + ‖tm n ω - t‖ := by rw [hsplit j]; exact norm_sub_le _ _
    calc (p : ℝ) * (‖β‖ * ‖Δ j‖) ≤ p * (S * (g (O j ω) + r)) := by
          gcongr; exact h1.trans (by linarith)
      _ = p * S * g (O j ω) + c0 := by rw [hc0]; ring
  have hsum := sum_sq_entropyWeights_mul_le_of_bounds hup hlow
    (w := fun i => 1 + g (O i ω) ^ 2) (fun i => by positivity)
  have hnonneg : 0 ≤ ∑ i : Fin n, balancingWeights Δ i ^ 2 * (1 + g (O i ω) ^ 2) :=
    Finset.sum_nonneg fun i _ => by positivity
  change |∑ i : Fin n, balancingWeights Δ i ^ 2 * (1 + g (O i ω) ^ 2)| ≤ _
  rw [abs_of_nonneg hnonneg]
  refine hsum.trans (le_of_eq ?_)
  have hmean : ∀ F : 𝒪 → ℝ, (n : ℝ) * sampleMean F O n ω = ∑ i : Fin n, F (O i ω) := by
    intro F
    rw [sampleMean, ← Fin.sum_univ_eq_sum_range (fun i => F (O i ω)) n, ← mul_assoc,
      mul_inv_cancel₀ hn'.ne', one_mul]
  have hAs : ∑ i : Fin n, Real.exp (2 * (βs ⬝ᵥ (f (O i ω) - t) + p * r * g (O i ω) + c0)) *
      (1 + g (O i ω) ^ 2) = Real.exp (2 * c0) * (n * sampleMean A O n ω) := by
    rw [hmean A, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA]; simp only; rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have hBs : ∑ j : Fin n, Real.exp (-(p * S * g (O j ω) + c0)) =
      Real.exp (-c0) * (n * sampleMean B O n ω) := by
    rw [hmean B, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB]; simp only; rw [← Real.exp_add]; ring_nf
  rw [hAs, hBs, hG]
  have hBpos : 0 < sampleMean B O n ω := by
    rw [sampleMean]
    exact mul_pos (inv_pos.2 hn') (Finset.sum_pos (fun i _ => Real.exp_pos _)
      (Finset.nonempty_range_iff.2 hn.ne'))
  simp only
  have he' : Real.exp (4 * c0) = Real.exp (2 * c0) / Real.exp (-c0) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]; push_cast; ring_nf
  rw [he']
  field_simp

/-- **The norm condition gives the directional one.** If `E[exp(κ ‖f - t‖)] < ∞` with
`κ > 2 p ‖β*‖`, then `κ > p ‖β*‖` and `E[exp(2 (1 + ε) β*ᵀ(f - t))] < ∞` for some `ε > 0`. -/
theorem directional_of_norm {ν : Measure 𝒪} {f : 𝒪 → Fin p → ℝ} (hf : Measurable f)
    {t βs : Fin p → ℝ} {κ : ℝ} (hexp : Integrable (fun z => Real.exp (κ * ‖f z - t‖)) ν)
    (hκ : 2 * p * ‖βs‖ < κ) :
    p * ‖βs‖ < κ ∧ ∃ ε, 0 < ε ∧
      Integrable (fun z => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (f z - t)))) ν := by
  have hpb : 0 ≤ (p : ℝ) * ‖βs‖ := by positivity
  refine ⟨by linarith, ?_⟩
  rcases eq_or_lt_of_le hpb with h0 | h0
  · refine ⟨1, one_pos, ?_⟩
    refine integrable_exp_dotProduct_of_le (β := (2 * (1 + 1) : ℝ) • βs) hf hexp ?_ |>.congr
      (ae_of_all _ fun z => by simp only [smul_dotProduct, smul_eq_mul])
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    nlinarith
  · set ε : ℝ := (κ - 2 * p * ‖βs‖) / (2 * p * ‖βs‖) with hε
    have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
    refine ⟨ε, hε0, ?_⟩
    refine integrable_exp_dotProduct_of_le (β := (2 * (1 + ε)) • βs) hf hexp ?_ |>.congr
      (ae_of_all _ fun z => by simp only [smul_dotProduct, smul_eq_mul])
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have : (p : ℝ) * (2 * (1 + ε) * ‖βs‖) = 2 * p * ‖βs‖ + ε * (2 * p * ‖βs‖) := by ring
    rw [this, hε, div_mul_cancel₀ _ (by linarith)]
    linarith

end Dispersion

/-! ### Consistency under a directional moment -/

section Consistency

variable {Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted arm mean under a directional moment.** The hypotheses of
`sampleBalancedArmMean_isConsistent_of_isMinOn`, with `E[exp(κ ‖φ(X) - t‖)] < ∞` for some
`κ > 2 p ‖β*‖` replaced by: the same moment for some `κ > p ‖β*‖`, and
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`. Then the weighted arm mean at the
reported targets `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_of_isMinOn_directional (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {βs : Fin p → ℝ}
    (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) (fun z => φ z.1) t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖))
      (P.map (O 0))) (hκ : p * ‖βs‖ < κ) {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ z.1 - t))))
      (P.map (O 0)))
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {T : ℕ → 𝒲 → Fin p → ℝ} (hT : ∀ n, Measurable (T n))
    (htm : TendstoInMeasure P (fun n ω => T n (W ω)) atTop (fun _ => t))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a}) {m : 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * (z.2.2 - m z.1) ^ 2)
      (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => armIndObs a z * z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => armIndObs a z * m z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => armIndObs a z * (z.2.2 - m z.1) ^ 2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (T n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  have hf : Measurable fun z : 𝒳 × Bool × ℝ => φ z.1 := hφ.comp measurable_fst
  have hpb : 0 ≤ (p : ℝ) * ‖βs‖ := by positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hpb hκ
  have hfeas := (tendstoInMeasure_dualMinimizer_of_isMinOn hO hf hδ hmargin htm hmin hexp hκ).1
  have hdisp := balancingDispersionVanishes_of_isMinOn_directional hO hOm hf hδ hmargin htm hmin
    hexp hκ hε hdir
  have hφ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖ ^ 2) (P.map (O 0)) :=
    integrable_sq_of_integrable_exp_pos (g := fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖)
      (hf.sub_const t).norm (fun _ => norm_nonneg _) hκ0 hexp
  exact sampleBalancedArmMean_isConsistent_of_dispersion hO hOm hφ hW hWO hT htm hfeas hdisp
    hφ2 hind a hq hres2 hreg hvar haff

end Consistency

section Trial

variable {Ω₁ Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **The weighted arm mean of a randomized trial under a directional moment.** The hypotheses of
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn`, with the moment of order
`κ > 2 p ‖β*‖` replaced by a moment `E[exp(κ ‖φ(X) - t‖)] < ∞` of order `κ > p ‖β*‖` and the
directional moment `E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`, both under the
covariate law. Then the weighted arm mean at `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_trial_of_isMinOn_directional (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hκ : p * ‖βs‖ < κ) {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hq : 0 < T.μ.real (T.A ⁻¹' {a})) {m : 𝒳 → ℝ} (hm : T.IsCondMean a m)
    (hres2 : Integrable (fun ω => (T.Y a ω - m (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 | MeasurableSpace.comap T.X inferInstance]
      ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have : IsProbabilityMeasure (T.μ.map fun ω => (T.X ω, T.A ω, T.obsOutcome ω)) := by
    change IsProbabilityMeasure T.ipdLaw
    rw [← hlaw]; infer_instance
  have : IsProbabilityMeasure T.μ := Measure.isProbabilityMeasure_of_map hf.aemeasurable
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  obtain ⟨hind, hres2', hreg', hvar'⟩ :=
    ipdLaw_arm_hypotheses hX hA hYo a hYa hrand hm hres2 hvar
  have hmapφ : (T.ipdLaw.map fun z : 𝒳 × Bool × ℝ => φ z.1) = T.covLaw.map φ := by
    rw [Trial.ipdLaw, Population.covLaw,
      Measure.map_map (g := fun z : 𝒳 × Bool × ℝ => φ z.1) (hφ.comp measurable_fst) hf,
      Measure.map_map hφ hX]
    rfl
  have hint' : t ∈ interior (closedConvexHull ℝ
      ((P.map (O 0)).map fun z : 𝒳 × Bool × ℝ => φ z.1).support) := by
    rw [hlaw, hmapφ]; exact hint
  have hlift : ∀ F : 𝒳 → ℝ, Measurable F → Integrable F T.covLaw →
      Integrable (fun z : 𝒳 × Bool × ℝ => F z.1) (P.map (O 0)) := fun F hF h1 => by
    rw [Population.covLaw, integrable_map_measure hF.aestronglyMeasurable hX.aemeasurable]
      at h1
    have hm2 : Measurable fun z : 𝒳 × Bool × ℝ => F z.1 := hF.comp measurable_fst
    rw [hlaw, Trial.ipdLaw, integrable_map_measure hm2.aestronglyMeasurable hf.aemeasurable]
    exact h1
  have hexp' := hlift _ (Real.measurable_exp.comp (measurable_const.mul (hφ.sub_const t).norm))
    hexp
  have hdir' := hlift _ (Real.measurable_exp.comp (measurable_const.mul
    ((continuous_const.dotProduct continuous_id).measurable.comp (hφ.sub_const t)))) hdir
  have hmin' : IsMinOn (sharpDualObjective (P.map (O 0)) (fun z => φ z.1) t) Set.univ βs := by
    rw [hlaw, sharpDualObjective_ipdLaw hX hA hYo hφ t]; exact hmin
  have hq' : 0 < T.ipdLaw.real {z | z.2.1 = a} := by
    rw [Trial.ipdLaw, map_measureReal_apply hf
      (measurableSet_eq_fun measurable_snd.fst measurable_const)]
    exact hq
  rw [← hlaw] at hind hres2' hreg' hvar' hq'
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint'
  exact sampleBalancedArmMean_isConsistent_of_isMinOn_directional hO hOm hφ hδ hmargin hmin'
    hexp' hκ hε hdir' hW hWO hG htm hind a hq' hres2' hreg' hvar' haff

end Trial

/-! ### A strict refinement on the exponential law -/

section Exponential

/-- **At `t = 3/5` the norm condition fails for the exponential law**: with `β* = 1 - 5/3`, no
order `κ` has `E[exp(κ |X - 3/5|)] < ∞` and `κ > 2|β*| = 4/3`. -/
theorem not_exists_order_expMeasure_three_fifths :
    ¬ ∃ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖featureLineVec x - featureLineVec (3 / 5)‖))
        (expMeasure 1) ∧ 2 * (1 : ℕ) * ‖featureLineVec (1 - 1 / (3 / 5 : ℝ))‖ < κ := by
  rw [exists_order_expMeasure_iff (by norm_num)]
  norm_num

/-- **The exponential instance at `t = 3/5` under the directional moment.** The covariate
follows the standard exponential law, the assignment is a fair coin, `Y(true) = 1 + 2X`, and the
reported targets are `tₙ = 3/5 + 1/(n + 1) → 3/5`. Here `β* = -2/3`: the norm moment of order
`κ = 3/4 > |β*|` is finite, the directional moment `E[exp(2 (1 + 1) β* (X - 3/5))]` is finite
since `β* < 0` and `X ≥ 0`, while the norm condition `κ > 2|β*|` fails
(`not_exists_order_expMeasure_three_fifths`). The weighted arm mean of arm `true` converges in
probability to `1 + 2 · 3/5 = 11/5`. -/
theorem momentOrderInst_directional_consistent :
    IsConsistent (fun n ω => sampleBalancedArmMean id
      (featureLineVec (3 / 5 + 1 / ((n : ℝ) + 1)))
      (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) (11 / 5)
      (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  have ht : (0 : ℝ) < 3 / 5 := by norm_num
  have hf := measurable_sharpInstOutcome
  have hκ0 : (0 : ℝ) < 3 / 4 := by norm_num
  have hexp := (integrable_exp_momentOrderExpLaw_iff (3 / 5) (3 / 4)).2 (by norm_num)
  have hfi : Integrable (sharpInstOutcome true) momentOrderExpLaw := by
    rw [show sharpInstOutcome true = fun x => 1 + featureLineVec 2 ⬝ᵥ x from
      funext sharpInstOutcome_true]
    exact integrable_affine_of_integrable_exp_pos hκ0 hexp 1 _
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses hf true hfi
  have hcov := sharpInstTrial_covLaw (lam := momentOrderExpLaw) (f := sharpInstOutcome)
  have hdir : Integrable (fun y => Real.exp (2 * (1 + 1) *
      (featureLineVec (1 - 1 / (3 / 5 : ℝ)) ⬝ᵥ (y - featureLineVec (3 / 5)))))
      momentOrderExpLaw := by
    have hm : Measurable fun y : Fin 1 → ℝ => Real.exp (2 * (1 + 1) *
        (featureLineVec (1 - 1 / (3 / 5 : ℝ)) ⬝ᵥ (y - featureLineVec (3 / 5)))) := by fun_prop
    rw [momentOrderExpLaw, integrable_map_measure hm.aestronglyMeasurable
      measurable_featureLineVec.aemeasurable]
    have e : (fun y : Fin 1 → ℝ => Real.exp (2 * (1 + 1) *
        (featureLineVec (1 - 1 / (3 / 5 : ℝ)) ⬝ᵥ (y - featureLineVec (3 / 5))))) ∘
        featureLineVec = fun x => Real.exp (8 / 5) * Real.exp ((-8 / 3) * x) := by
      funext x
      simp only [Function.comp_apply, dotProduct_featureLineVec_sub, featureLineVec]
      rw [← Real.exp_add]; ring_nf
    rw [e]
    exact ((integrable_exp_mul_expMeasure_iff).2 (by norm_num)).const_mul _
  have htn : Tendsto (fun n : ℕ => featureLineVec (3 / 5 + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (featureLineVec (3 / 5))) := tendsto_pi_nhds.2 fun _ => by
    simpa [featureLineVec] using
      (tendsto_const_nhds (x := (3 / 5 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hκ : ((1 : ℕ) : ℝ) * ‖featureLineVec (1 - 1 / (3 / 5 : ℝ))‖ < 3 / 4 := by
    rw [norm_featureLineVec]; norm_num [abs_of_neg]
  have h := sampleBalancedArmMean_isConsistent_trial_of_isMinOn_directional hX hA hYo true hYa
    hrand (isIIDSample_sharpInstSample hf) (measurable_sharpInstSample hf)
    (map_sharpInstSample hf 0) measurable_id (t := featureLineVec (3 / 5))
    (by rw [Measure.map_id, hcov]; exact mem_interior_momentOrderExpLaw ht)
    (by rw [hcov]; exact isMinOn_sharpDualObjective_momentOrderExpLaw ht)
    (by rw [hcov]; exact hexp) hκ one_pos (by rw [hcov]; exact hdir)
    (W := fun _ => ()) measurable_const (indepFun_const_left _ _)
    (G := fun n _ => featureLineVec (3 / 5 + 1 / ((n : ℝ) + 1))) (fun _ => measurable_const)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => htn)) hq hm hres2 hvar (a0 := 1) (b := featureLineVec 2)
    sharpInstOutcome_true
  have hv : 1 + featureLineVec 2 ⬝ᵥ featureLineVec (3 / 5) = 11 / 5 := by
    simp [featureLineVec, dotProduct]; norm_num
  rw [hv] at h
  exact h

/-- **An instance of `directional_of_norm`**: for the exponential feature law at `t = 3/2`, with
`β* = 1/3`, the moment of order `κ = 3/4 > 2 |β*|` is finite, so `κ > |β*|` and some directional
moment of `β*` is finite. -/
theorem directional_of_norm_momentOrderExpLaw :
    ((1 : ℕ) : ℝ) * ‖featureLineVec (1 - 1 / (3 / 2 : ℝ))‖ < 3 / 4 ∧ ∃ ε, 0 < ε ∧
      Integrable (fun y => Real.exp (2 * (1 + ε) *
        (featureLineVec (1 - 1 / (3 / 2 : ℝ)) ⬝ᵥ (id y - featureLineVec (3 / 2)))))
        momentOrderExpLaw :=
  directional_of_norm measurable_id
    ((integrable_exp_momentOrderExpLaw_iff (3 / 2) (3 / 4)).2 (by norm_num))
    (by rw [norm_featureLineVec]; norm_num [abs_of_pos])

end Exponential

end PopulationAdjustment

end CausalInference
