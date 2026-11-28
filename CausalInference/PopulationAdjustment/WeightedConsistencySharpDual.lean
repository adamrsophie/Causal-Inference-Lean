/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralArm
public import CausalInference.Estimation.LawOfLargeNumbers

/-!
# The population dual minimizer of entropy balancing for unbounded features

For records `z` with features `f(z)` and a target `t`, the population dual objective of entropy
balancing is `F(β) = E[exp(βᵀ(f(z) - t))]`. For unbounded features it may be infinite; it is taken
here with values in `[0, ∞]` (`sharpDualObjective`), so that a minimizer is a genuine minimizer
and no statement holds through the value of a divergent integral.

**Existence and uniqueness.** Under the margin condition at `t` with margin `δ` and a finite
exponential moment `E[exp(κ ‖f(z) - t‖)]` of order `κ = p / δ²`, the objective has exactly one
minimizer (`existsUnique_isMinOn_sharpDualObjective`): the objective is continuous on the ball of
radius `1 / δ²`, outside of it the margin forces `F(β) ≥ δ exp(δ ‖β‖) > 1 = F(0)`, and two
minimizers would contradict the strict convexity of the exponential along the margin
(`integral_exp_lt_of_isMinOn`). No bound on the features is assumed.

**The sample minimizer.** Let `β*` be the population minimizer and let the exponential moment be
finite for some order `κ > p ‖β*‖`. For reported targets `tₙ → t` in probability, the sample dual
minimizer `β̂ₙ` of the entropy balancing weights at `tₙ` converges in probability to `β*`, and the
weights are feasible with probability tending to one
(`tendstoInMeasure_dualMinimizer_of_isMinOn`). The proof is the convexity argument: on a sphere
of small radius `r` around `β*` the population objective exceeds `F(β*)` by some `c > 0`
(`exists_gap_on_sphere`), the uniform law of large numbers on the closed ball transfers the gap
to the sample objective, and convexity of the sample log partition function traps its minimizer
inside the ball.

**The order of the moment.** On `Fin p → ℝ` the norm is the sup norm, so the bound used for the
tilts is `|βᵀv| ≤ p ‖β‖ ‖v‖`; the uniform law needs `exp(p (‖β*‖ + r) ‖f - t‖)` to be integrable,
which holds for a small `r` exactly when `κ > p ‖β*‖`.

## Main definitions

* `sharpDualObjective`: the population dual objective with values in `[0, ∞]`.

## Main results

* `integral_exp_lt_of_isMinOn`: strict separation of the minimizer.
* `existsUnique_isMinOn_sharpDualObjective`: existence and uniqueness for unbounded features.
* `exists_gap_on_sphere`: the gap on a sphere around the minimizer.
* `tendstoInMeasure_dualMinimizer_of_isMinOn`: feasibility and `β̂ₙ → β*` in probability.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press (1970).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

/-! ### The population objective -/

section Population

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {p : ℕ} {ν : Measure 𝒪} {f : 𝒪 → Fin p → ℝ}
  {t : Fin p → ℝ}

/-- The **population dual objective** of entropy balancing with values in `[0, ∞]`,
`F(β) = E[exp(βᵀ(f(z) - t))]`, infinite when the exponential moment diverges. -/
noncomputable def sharpDualObjective (ν : Measure 𝒪) (f : 𝒪 → Fin p → ℝ) (t β : Fin p → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (β ⬝ᵥ (f z - t))) ∂ν

/-- The tilt `exp(βᵀ(f(z) - t))` is measurable. -/
theorem measurable_exp_dotProduct_sub (hf : Measurable f) (t β : Fin p → ℝ) :
    Measurable fun z => Real.exp (β ⬝ᵥ (f z - t)) :=
  ((continuous_const.dotProduct continuous_id).measurable.comp (hf.sub_const t)).exp

/-- The tilt is at most `exp(p ‖β‖ ‖v‖)`. -/
theorem exp_dotProduct_le (β v : Fin p → ℝ) :
    Real.exp (β ⬝ᵥ v) ≤ Real.exp (p * ‖β‖ * ‖v‖) :=
  Real.exp_le_exp.2 ((le_abs_self _).trans ((abs_dotProduct_le_mul_norm β v).trans
    (le_of_eq (by ring))))

/-- The tilt of a parameter with `p ‖β‖ ≤ κ` is integrable under `E[exp(κ ‖f - t‖)] < ∞`. -/
theorem integrable_exp_dotProduct_of_le (hf : Measurable f) {κ : ℝ}
    (hexp : Integrable (fun z => Real.exp (κ * ‖f z - t‖)) ν) {β : Fin p → ℝ}
    (hβ : p * ‖β‖ ≤ κ) : Integrable (fun z => Real.exp (β ⬝ᵥ (f z - t))) ν :=
  hexp.mono' (measurable_exp_dotProduct_sub hf t β).aestronglyMeasurable
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (exp_dotProduct_le β _).trans
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hβ (norm_nonneg _))))

/-- On integrable tilts the objective is the integral. -/
theorem sharpDualObjective_eq_ofReal {β : Fin p → ℝ}
    (hi : Integrable (fun z => Real.exp (β ⬝ᵥ (f z - t))) ν) :
    sharpDualObjective ν f t β = ENNReal.ofReal (∫ z, Real.exp (β ⬝ᵥ (f z - t)) ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm

/-- A finite objective has an integrable tilt. -/
theorem integrable_of_sharpDualObjective_ne_top (hf : Measurable f) {β : Fin p → ℝ}
    (h : sharpDualObjective ν f t β ≠ ⊤) :
    Integrable (fun z => Real.exp (β ⬝ᵥ (f z - t))) ν := by
  refine ⟨(measurable_exp_dotProduct_sub hf t β).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact h.lt_top

/-- The objective at zero is the total mass. -/
theorem sharpDualObjective_zero [IsProbabilityMeasure ν] : sharpDualObjective ν f t 0 = 1 := by
  simp [sharpDualObjective]

/-- **The margin set of a direction.** For `u ≠ 0`, the set where `(u / ‖u‖)ᵀ(f - t) ≥ δ` is
measurable and on it `uᵀ(f - t) ≥ ‖u‖ δ`. -/
theorem margin_dir_le (hf : Measurable f) {u : Fin p → ℝ} (hu : u ≠ 0) {δ : ℝ} :
    MeasurableSet {z | δ ≤ (‖u‖⁻¹ • u) ⬝ᵥ (f z - t)} ∧
      ∀ z, δ ≤ (‖u‖⁻¹ • u) ⬝ᵥ (f z - t) → ‖u‖ * δ ≤ u ⬝ᵥ (f z - t) := by
  refine ⟨measurableSet_le measurable_const
    ((continuous_const.dotProduct continuous_id).measurable.comp (hf.sub_const t)), fun z hz => ?_⟩
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [smul_dotProduct, smul_eq_mul] at hz
  have := mul_le_mul_of_nonneg_left hz hu0.le
  rwa [← mul_assoc, mul_inv_cancel₀ hu0.ne', one_mul] at this

/-- The unit direction of a nonzero vector has norm one. -/
theorem norm_inv_norm_smul {u : Fin p → ℝ} (hu : u ≠ 0) : ‖‖u‖⁻¹ • u‖ = 1 := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hu0), inv_mul_cancel₀ hu0.ne']

/-- **Strict convexity along the margin.** Under the margin condition, for integrable tilts of
two distinct parameters `b ≠ c`, the tilt of the midpoint is integrable and
`F((b + c) / 2) < (F(b) + F(c)) / 2`. -/
theorem integral_exp_midpoint_lt (hf : Measurable f) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {b c : Fin p → ℝ} (hbc : b ≠ c) (hb : Integrable (fun z => Real.exp (b ⬝ᵥ (f z - t))) ν)
    (hc : Integrable (fun z => Real.exp (c ⬝ᵥ (f z - t))) ν) :
    Integrable (fun z => Real.exp (((1 / 2 : ℝ) • (b + c)) ⬝ᵥ (f z - t))) ν ∧
      ∫ z, Real.exp (((1 / 2 : ℝ) • (b + c)) ⬝ᵥ (f z - t)) ∂ν <
        ((∫ z, Real.exp (b ⬝ᵥ (f z - t)) ∂ν) + ∫ z, Real.exp (c ⬝ᵥ (f z - t)) ∂ν) / 2 := by
  set m : Fin p → ℝ := (1 / 2 : ℝ) • (b + c) with hm
  have hsplit : ∀ z, Real.exp (m ⬝ᵥ (f z - t)) =
      Real.exp (b ⬝ᵥ (f z - t) / 2) * Real.exp (c ⬝ᵥ (f z - t) / 2) := fun z => by
    rw [← Real.exp_add, hm, smul_dotProduct, add_dotProduct, smul_eq_mul]; ring_nf
  have hsq : ∀ x : ℝ, Real.exp x = Real.exp (x / 2) ^ 2 := fun x => by
    rw [sq, ← Real.exp_add]; ring_nf
  set g : 𝒪 → ℝ := fun z => (Real.exp (b ⬝ᵥ (f z - t)) + Real.exp (c ⬝ᵥ (f z - t))) / 2 -
    Real.exp (m ⬝ᵥ (f z - t)) with hg
  have hg_eq : ∀ z, g z =
      (Real.exp (b ⬝ᵥ (f z - t) / 2) - Real.exp (c ⬝ᵥ (f z - t) / 2)) ^ 2 / 2 := fun z => by
    rw [hg]; simp only; rw [hsplit, hsq (b ⬝ᵥ (f z - t)), hsq (c ⬝ᵥ (f z - t))]; ring
  have hg0 : ∀ z, 0 ≤ g z := fun z => by rw [hg_eq]; positivity
  have hmi : Integrable (fun z => Real.exp (m ⬝ᵥ (f z - t))) ν := by
    refine ((hb.add hc).div_const 2).mono'
      (measurable_exp_dotProduct_sub hf t m).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := hg0 z
    simp only [hg] at this
    simp only [Pi.add_apply]
    linarith
  refine ⟨hmi, ?_⟩
  have hgi : Integrable g ν := ((hb.add hc).div_const 2).sub hmi
  have hpos : 0 < ∫ z, g z ∂ν := by
    rw [integral_pos_iff_support_of_nonneg hg0 hgi]
    have hu : b - c ≠ 0 := sub_ne_zero.2 hbc
    obtain ⟨hS, hSle⟩ := margin_dir_le (t := t) hf hu (δ := δ)
    have hSν := hmargin _ (norm_inv_norm_smul hu)
    have hsub : {z | δ ≤ (‖b - c‖⁻¹ • (b - c)) ⬝ᵥ (f z - t)} ⊆ Function.support g := by
      intro z hz
      have h1 := hSle z hz
      have hn : 0 < ‖b - c‖ * δ := mul_pos (norm_pos_iff.2 hu) hδ
      rw [sub_dotProduct] at h1
      rw [Function.mem_support, hg_eq]
      have hne : Real.exp (b ⬝ᵥ (f z - t) / 2) ≠ Real.exp (c ⬝ᵥ (f z - t) / 2) := by
        intro he
        have := Real.exp_injective he
        linarith
      have : (Real.exp (b ⬝ᵥ (f z - t) / 2) - Real.exp (c ⬝ᵥ (f z - t) / 2)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (sub_ne_zero.2 hne)
      positivity
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hSν
    linarith
  have hint : ∫ z, g z ∂ν = ((∫ z, Real.exp (b ⬝ᵥ (f z - t)) ∂ν) +
      ∫ z, Real.exp (c ⬝ᵥ (f z - t)) ∂ν) / 2 - ∫ z, Real.exp (m ⬝ᵥ (f z - t)) ∂ν := by
    have hadd : Integrable (fun z => (Real.exp (b ⬝ᵥ (f z - t)) +
        Real.exp (c ⬝ᵥ (f z - t))) / 2) ν := (hb.add hc).div_const 2
    rw [hg, integral_sub hadd hmi, integral_div, integral_add hb hc]
  linarith

/-- A minimizer has an integral of the tilt at most that of any integrable tilt. -/
theorem integral_exp_le_of_isMinOn {βs b : Fin p → ℝ}
    (hmin : IsMinOn (sharpDualObjective ν f t) Set.univ βs)
    (hs : Integrable (fun z => Real.exp (βs ⬝ᵥ (f z - t))) ν)
    (hb : Integrable (fun z => Real.exp (b ⬝ᵥ (f z - t))) ν) :
    ∫ z, Real.exp (βs ⬝ᵥ (f z - t)) ∂ν ≤ ∫ z, Real.exp (b ⬝ᵥ (f z - t)) ∂ν := by
  have h := hmin (Set.mem_univ b)
  simp only [Set.mem_ofPred_eq] at h
  rw [sharpDualObjective_eq_ofReal hs, sharpDualObjective_eq_ofReal hb] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => (Real.exp_pos _).le)).1 h

/-- **Strict separation of the minimizer.** Under the margin condition, if `β*` minimizes the
objective and has an integrable tilt, every other parameter `b ≠ β*` with an integrable tilt has
`F(β*) < F(b)`. -/
theorem integral_exp_lt_of_isMinOn (hf : Measurable f) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {βs b : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective ν f t) Set.univ βs)
    (hs : Integrable (fun z => Real.exp (βs ⬝ᵥ (f z - t))) ν)
    (hb : Integrable (fun z => Real.exp (b ⬝ᵥ (f z - t))) ν) (hne : b ≠ βs) :
    ∫ z, Real.exp (βs ⬝ᵥ (f z - t)) ∂ν < ∫ z, Real.exp (b ⬝ᵥ (f z - t)) ∂ν := by
  obtain ⟨hmi, hlt⟩ := integral_exp_midpoint_lt hf hδ hmargin hne hb hs
  have := integral_exp_le_of_isMinOn hmin hs hmi
  linarith

/-- **The margin bound on the objective**: `F(β) ≥ δ exp(δ ‖β‖)` for `β ≠ 0`, with values in
`[0, ∞]`. -/
theorem ofReal_le_sharpDualObjective [IsFiniteMeasure ν] (hf : Measurable f) {δ : ℝ}
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {β : Fin p → ℝ} (hβ : β ≠ 0) :
    ENNReal.ofReal (δ * Real.exp (δ * ‖β‖)) ≤ sharpDualObjective ν f t β := by
  obtain ⟨hS, hSle⟩ := margin_dir_le (t := t) hf hβ (δ := δ)
  set S := {z | δ ≤ (‖β‖⁻¹ • β) ⬝ᵥ (f z - t)} with hSdef
  have hSν := hmargin _ (norm_inv_norm_smul hβ)
  have hle : ∀ z, S.indicator (fun _ => ENNReal.ofReal (Real.exp (δ * ‖β‖))) z ≤
      ENNReal.ofReal (Real.exp (β ⬝ᵥ (f z - t))) := fun z => by
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have := hSle z hz
      linarith [mul_comm ‖β‖ δ]
    · rw [Set.indicator_of_notMem hz]; exact bot_le
  calc ENNReal.ofReal (δ * Real.exp (δ * ‖β‖))
      = ENNReal.ofReal (Real.exp (δ * ‖β‖)) * ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
    _ ≤ ENNReal.ofReal (Real.exp (δ * ‖β‖)) * ν S := by
        gcongr
        rw [← ofReal_measureReal (measure_ne_top ν S)]
        exact ENNReal.ofReal_le_ofReal hSν
    _ = ∫⁻ z, S.indicator (fun _ => ENNReal.ofReal (Real.exp (δ * ‖β‖))) z ∂ν := by
        rw [lintegral_indicator_const hS]
    _ ≤ _ := lintegral_mono hle

/-- **Existence and uniqueness of the population dual minimizer for unbounded features.** Under
the margin condition at `t` with margin `δ` and a finite exponential moment
`E[exp(κ ‖f(z) - t‖)]` of order `κ = p / δ²`, the population dual objective has exactly one
minimizer. -/
theorem existsUnique_isMinOn_sharpDualObjective [IsProbabilityMeasure ν] (hf : Measurable f)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)})
    (hexp : Integrable (fun z => Real.exp (p / δ ^ 2 * ‖f z - t‖)) ν) :
    ∃! β, IsMinOn (sharpDualObjective ν f t) Set.univ β := by
  set R : ℝ := 1 / δ ^ 2 with hR
  have hR0 : 0 < R := by positivity
  have hpR : (p : ℝ) / δ ^ 2 = p * R := by rw [hR]; ring
  have hint : ∀ β ∈ Metric.closedBall (0 : Fin p → ℝ) R,
      Integrable (fun z => Real.exp (β ⬝ᵥ (f z - t))) ν := fun β hβ =>
    integrable_exp_dotProduct_of_le hf hexp (by
      rw [hpR]; exact mul_le_mul_of_nonneg_left (by simpa using hβ) (Nat.cast_nonneg p))
  have hcont : ContinuousOn (fun β => ∫ z, Real.exp (β ⬝ᵥ (f z - t)) ∂ν)
      (Metric.closedBall (0 : Fin p → ℝ) R) := by
    refine continuousOn_of_dominated
      (fun β _ => (measurable_exp_dotProduct_sub hf t β).aestronglyMeasurable)
      (fun β hβ => ae_of_all _ fun z => ?_) hexp
      (ae_of_all _ fun z => (Continuous.continuousOn (by fun_prop)))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (exp_dotProduct_le β _).trans (Real.exp_le_exp.2 ?_)
    rw [hpR]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa using hβ) (Nat.cast_nonneg p)) (norm_nonneg _)
  obtain ⟨β₁, hβ₁K, hmin₁⟩ := (isCompact_closedBall (0 : Fin p → ℝ) R).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hR0.le⟩ hcont
  have h0K : (0 : Fin p → ℝ) ∈ Metric.closedBall (0 : Fin p → ℝ) R :=
    Metric.mem_closedBall_self hR0.le
  have hF0 : ∫ z, Real.exp ((0 : Fin p → ℝ) ⬝ᵥ (f z - t)) ∂ν = 1 := by simp
  have hβ₁1 : ∫ z, Real.exp (β₁ ⬝ᵥ (f z - t)) ∂ν ≤ 1 := hF0 ▸ hmin₁ h0K
  have hexist : IsMinOn (sharpDualObjective ν f t) Set.univ β₁ := by
    intro β _
    simp only [Set.mem_ofPred_eq]
    rw [sharpDualObjective_eq_ofReal (hint β₁ hβ₁K)]
    by_cases hβ : β ∈ Metric.closedBall (0 : Fin p → ℝ) R
    · rw [sharpDualObjective_eq_ofReal (hint β hβ)]
      exact ENNReal.ofReal_le_ofReal (hmin₁ hβ)
    · have hRβ : R < ‖β‖ := by simpa using hβ
      have hne : β ≠ 0 := by
        rintro rfl; rw [norm_zero] at hRβ; exact absurd hRβ (not_lt.2 hR0.le)
      refine le_trans ?_ (ofReal_le_sharpDualObjective hf hmargin hne)
      refine ENNReal.ofReal_le_ofReal (hβ₁1.trans ?_)
      have he : δ * R = 1 / δ := by rw [hR]; field_simp
      have h3 : Real.exp (1 / δ) ≤ Real.exp (δ * ‖β‖) := by
        rw [← he]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hRβ.le hδ.le)
      have h4 : 1 / δ + 1 < Real.exp (1 / δ) := Real.add_one_lt_exp (by positivity)
      have h5 : δ * (1 / δ + 1) = 1 + δ := by field_simp
      nlinarith
  refine ⟨β₁, hexist, fun β₂ hβ₂ => ?_⟩
  have hfin : ∀ β, IsMinOn (sharpDualObjective ν f t) Set.univ β →
      Integrable (fun z => Real.exp (β ⬝ᵥ (f z - t))) ν := fun β hβ =>
    integrable_of_sharpDualObjective_ne_top hf (ne_top_of_le_ne_top (by
      rw [sharpDualObjective_zero]; exact ENNReal.one_ne_top) (hβ (Set.mem_univ 0)))
  by_contra hne
  have h1 := integral_exp_lt_of_isMinOn hf hδ hmargin hexist (hfin β₁ hexist) (hfin β₂ hβ₂) hne
  have h2 := integral_exp_le_of_isMinOn hβ₂ (hfin β₂ hβ₂) (hfin β₁ hexist)
  linarith

/-- **The gap on a sphere around the minimizer.** Under the margin condition, let `β*` minimize
the objective and `E[exp(κ ‖f - t‖)] < ∞` with `p (‖β*‖ + r) ≤ κ` for a radius `r > 0`. Then for
some `c > 0`, every `b` with `‖b - β*‖ = r` has `F(β*) + c ≤ F(b)`. -/
theorem exists_gap_on_sphere (hf : Measurable f) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective ν f t) Set.univ βs) {κ : ℝ}
    (hexp : Integrable (fun z => Real.exp (κ * ‖f z - t‖)) ν) {r : ℝ} (hr : 0 < r)
    (hκ : p * (‖βs‖ + r) ≤ κ) :
    ∃ c, 0 < c ∧ ∀ b : Fin p → ℝ, ‖b - βs‖ = r →
      (∫ z, Real.exp (βs ⬝ᵥ (f z - t)) ∂ν) + c ≤ ∫ z, Real.exp (b ⬝ᵥ (f z - t)) ∂ν := by
  have hle : ∀ b : Fin p → ℝ, ‖b - βs‖ ≤ r → p * ‖b‖ ≤ κ := fun b hb => by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg p)) hκ
    calc ‖b‖ = ‖(b - βs) + βs‖ := by rw [sub_add_cancel]
      _ ≤ ‖b - βs‖ + ‖βs‖ := norm_add_le _ _
      _ ≤ ‖βs‖ + r := by linarith
  have hs := integrable_exp_dotProduct_of_le hf hexp
    (hle βs (by rw [sub_self, norm_zero]; exact hr.le))
  set S := Metric.sphere βs r with hSdef
  have hmemS : ∀ b, b ∈ S ↔ ‖b - βs‖ = r := fun b => mem_sphere_iff_norm
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun b hb => ?_⟩
    have : b ∈ S := (hmemS b).2 hb
    rw [hS] at this
    exact absurd this (Set.notMem_empty b)
  have hcont : ContinuousOn (fun β => ∫ z, Real.exp (β ⬝ᵥ (f z - t)) ∂ν) S := by
    refine continuousOn_of_dominated
      (fun β _ => (measurable_exp_dotProduct_sub hf t β).aestronglyMeasurable)
      (fun β hβ => ae_of_all _ fun z => ?_) hexp
      (ae_of_all _ fun z => (Continuous.continuousOn (by fun_prop)))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (exp_dotProduct_le β _).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (hle β ((hmemS β).1 hβ).le) (norm_nonneg _)))
  obtain ⟨b₀, hb₀S, hb₀⟩ := (isCompact_sphere βs r).exists_isMinOn hS hcont
  have hb₀r := (hmemS b₀).1 hb₀S
  have hne : b₀ ≠ βs := by
    rintro rfl; rw [sub_self, norm_zero] at hb₀r; exact hr.ne hb₀r
  have hlt := integral_exp_lt_of_isMinOn hf hδ hmargin hmin hs
    (integrable_exp_dotProduct_of_le hf hexp (hle b₀ hb₀r.le)) hne
  refine ⟨_, sub_pos.2 hlt, fun b hb => ?_⟩
  have := hb₀ ((hmemS b).2 hb)
  simp only [Set.mem_ofPred_eq] at this
  linarith

end Population

/-! ### The sample minimizer -/

section Sample

variable {𝒪 Ω : Type*} [MeasurableSpace 𝒪] [MeasurableSpace Ω] {p : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {f : 𝒪 → Fin p → ℝ} {t : Fin p → ℝ}

omit [MeasurableSpace 𝒪] [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The partition function at the target `s` in terms of the sample mean of the tilt at `t`:
`∑ᵢ exp(βᵀ(f(Oᵢ) - s)) = exp(-βᵀ(s - t)) n F̂ₙ(β)`. -/
theorem partitionFunction_sub_eq (f : 𝒪 → Fin p → ℝ) (t s : Fin p → ℝ) (n : ℕ) (ω : Ω)
    (β : Fin p → ℝ) :
    partitionFunction (fun i : Fin n => f (O i ω) - s) β =
      Real.exp (-(β ⬝ᵥ (s - t))) *
        (n * sampleMean (fun z => Real.exp (β ⬝ᵥ (f z - t))) O n ω) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [partitionFunction]
  rw [sampleMean, ← mul_assoc (n : ℝ), mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_mul,
    partitionFunction, ← Fin.sum_univ_eq_sum_range (fun i => Real.exp (β ⬝ᵥ (f (O i ω) - t))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Real.exp_add]
  congr 1
  simp only [dotProduct_sub]
  ring

/-- **Consistency of the sample dual minimizer for unbounded features.** Under the margin
condition at `t` for the law of the records, let `β*` minimize the population dual objective and
let `E[exp(κ ‖f - t‖)] < ∞` for some `κ > p ‖β*‖`. For reported targets `tₙ → t` in probability
(deterministic or random, no independence needed), the entropy balancing weights at `tₙ` are
feasible with probability tending to one and the sample dual minimizer
`β̂ₙ = dualMinimizer (f(Oᵢ) - tₙ)ᵢ` converges in probability to `β*`. -/
theorem tendstoInMeasure_dualMinimizer_of_isMinOn (hO : IsIIDSample O P) (hf : Measurable f)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) f t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun z => Real.exp (κ * ‖f z - t‖)) (P.map (O 0)))
    (hκ : p * ‖βs‖ < κ) :
    WithProbTendingToOne P (balancingFeasibleEvent f O tm) ∧
      TendstoInMeasure P (fun n ω => dualMinimizer fun i : Fin n => f (O i ω) - tm n ω) atTop
        (fun _ => βs) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  have hfeas := withProbTendingToOne_balancingFeasible hO hf hδ hmargin htm
  refine ⟨hfeas.mono fun n ω hω => ?_, ?_⟩
  · obtain ⟨-, -, β, -, -, hmem, -⟩ := hω
    exact hmem
  set r₀ : ℝ := (κ - p * ‖βs‖) / (p + 1) with hr₀
  have hr₀0 : 0 < r₀ := div_pos (sub_pos.2 hκ) (by positivity)
  refine tendstoInMeasure_of_good_events fun ε hε κ' hκ' => ?_
  set r := min (ε / 2) r₀ with hr
  have hr0 : 0 < r := lt_min (by positivity) hr₀0
  have hrκ : p * (‖βs‖ + r) ≤ κ := by
    have h1 : r ≤ r₀ := min_le_right _ _
    have h2 : (p : ℝ) * r₀ ≤ (p + 1) * r₀ := by nlinarith
    have h3 : (p + 1) * r₀ = κ - p * ‖βs‖ := by rw [hr₀]; field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) p]
  obtain ⟨c, hc, hsep⟩ := exists_gap_on_sphere hf hδ hmargin hmin hexp hr0 hrκ
  set K := Metric.closedBall βs r with hK
  have hKle : ∀ β ∈ K, p * ‖β‖ ≤ κ := fun β hβ => by
    have hb : ‖β - βs‖ ≤ r := by rwa [hK, Metric.mem_closedBall, dist_eq_norm] at hβ
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg p)) hrκ
    calc ‖β‖ = ‖(β - βs) + βs‖ := by rw [sub_add_cancel]
      _ ≤ ‖β - βs‖ + ‖βs‖ := norm_add_le _ _
      _ ≤ ‖βs‖ + r := by linarith
  obtain ⟨-, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall βs r)
    (ψ := fun z β => Real.exp (β ⬝ᵥ (f z - t)))
    (fun β _ => measurable_exp_dotProduct_sub hf t β)
    (ae_of_all _ fun z => Continuous.continuousOn (by fun_prop))
    (H := fun z => Real.exp (κ * ‖f z - t‖)) hexp
    (ae_of_all _ fun z β hβ => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact (exp_dotProduct_le β _).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (hKle β hβ) (norm_nonneg _))))
  set Fs := ∫ z, Real.exp (βs ⬝ᵥ (f z - t)) ∂ν with hFs
  have hFs0 : 0 ≤ Fs := integral_nonneg fun _ => (Real.exp_pos _).le
  set ρ := (Fs + 3 * c / 4) / (Fs + c / 4) with hρ
  have hd0 : 0 < Fs + c / 4 := by positivity
  have hρ1 : 1 < ρ := by rw [hρ, one_lt_div hd0]; linarith
  have hρeq : ρ * (Fs + c / 4) = Fs + 3 * c / 4 := by rw [hρ]; field_simp
  set ζ := Real.log ρ / ((p + 1) * (r + 1)) with hζ
  have hζ0 : 0 < ζ := div_pos (Real.log_pos hρ1) (by positivity)
  have hev := ((hfeas.inter (hunif (c / 4) (by positivity))).inter
    (htm.withProbTendingToOne_dist_lt hζ0)).eventually_le hκ'
  refine ⟨_, hev, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨⟨hn, -, β₁, -, hmin₁, -, -⟩, hω2⟩, hω3⟩ := hω
  simp only [Set.mem_ofPred_eq] at hω2 hω3
  set Δ := fun i : Fin n => f (O i ω) - tm n ω with hΔ
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hm := isMinOn_dualMinimizer (exists_isMinOn_logPartition_iff.1 ⟨β₁, hmin₁⟩)
  set βh := dualMinimizer Δ with hβh
  change dist βh βs < ε
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (b := r) ?_ (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
  by_contra hfar
  replace hfar := not_le.1 hfar
  set d := ‖βh - βs‖ with hd
  have hd0 : 0 < d := hr0.trans hfar
  set s := r / d with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := (div_le_one hd0).2 hfar.le
  set b := (1 - s) • βs + s • βh with hb
  have hbsub : b - βs = s • (βh - βs) := by rw [hb, sub_smul, one_smul, smul_sub]; abel
  have hbn : ‖b - βs‖ = r := by
    rw [hbsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hs, div_mul_cancel₀ _ hd0.ne']
  have hbK : b ∈ K := by rw [hK, Metric.mem_closedBall, dist_eq_norm, hbn]
  have hβsK : βs ∈ K := Metric.mem_closedBall_self hr0.le
  have hconv := (convexOn_logPartition (Δ := Δ)).2 (Set.mem_univ βs) (Set.mem_univ βh)
    (sub_nonneg.2 hs1) hs0 (by ring)
  have hmh : logPartition Δ βh ≤ logPartition Δ βs := hm (Set.mem_univ βs)
  simp only [smul_eq_mul] at hconv
  rw [← hb] at hconv
  have hL : logPartition Δ b ≤ logPartition Δ βs := by nlinarith
  have hZ : partitionFunction Δ b ≤ partitionFunction Δ βs :=
    (Real.log_le_log_iff (partitionFunction_pos b) (partitionFunction_pos βs)).1 hL
  rw [hΔ, partitionFunction_sub_eq f t (tm n ω) n ω b,
    partitionFunction_sub_eq f t (tm n ω) n ω βs] at hZ
  set e := tm n ω - t with he
  set Fb := sampleMean (fun z => Real.exp (b ⬝ᵥ (f z - t))) O n ω with hFb
  set Fh := sampleMean (fun z => Real.exp (βs ⬝ᵥ (f z - t))) O n ω with hFh
  set D := b ⬝ᵥ e - βs ⬝ᵥ e with hD
  have hsplit : Real.exp (-(βs ⬝ᵥ e)) = Real.exp (-(b ⬝ᵥ e)) * Real.exp D := by
    rw [← Real.exp_add, hD]; ring_nf
  rw [hsplit, mul_assoc] at hZ
  have hZ' := le_of_mul_le_mul_left hZ (Real.exp_pos _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hFbh : Fb ≤ Real.exp D * Fh := by
    rw [mul_left_comm] at hZ'
    exact le_of_mul_le_mul_left hZ' hnR
  have hDle : D ≤ Real.log ρ := by
    have h1 : D ≤ p * ‖b - βs‖ * ‖e‖ := by
      rw [hD, ← sub_dotProduct]
      exact (le_abs_self _).trans ((abs_dotProduct_le_mul_norm _ _).trans (le_of_eq (by ring)))
    rw [hbn] at h1
    have he' : ‖e‖ < ζ := by rw [he, ← dist_eq_norm]; exact hω3
    have h2 : (p : ℝ) * r * ‖e‖ ≤ (p + 1) * (r + 1) * ζ := by
      have h3 : (p : ℝ) * r ≤ (p + 1) * (r + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) p]
      have h4 : 0 ≤ (p : ℝ) * r := by positivity
      calc (p : ℝ) * r * ‖e‖ ≤ (p * r) * ζ := mul_le_mul_of_nonneg_left he'.le h4
        _ ≤ (p + 1) * (r + 1) * ζ := mul_le_mul_of_nonneg_right h3 hζ0.le
    have h5 : (p + 1) * (r + 1) * ζ = Real.log ρ := by rw [hζ]; field_simp
    linarith
  have hE : Real.exp D ≤ ρ := by
    calc Real.exp D ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.2 hDle
      _ = ρ := Real.exp_log (by linarith)
  have hFh0 : 0 ≤ Fh := by rw [hFh]; unfold sampleMean; positivity
  have hb1 := hω2 b hbK
  have hb2 := hω2 βs hβsK
  rw [Real.dist_eq, abs_lt] at hb1 hb2
  have hgap := hsep b hbn
  have ha : Real.exp D * Fh ≤ ρ * Fh := mul_le_mul_of_nonneg_right hE hFh0
  have hb' : ρ * Fh < ρ * (Fs + c / 4) := by
    refine mul_lt_mul_of_pos_left ?_ (by linarith)
    linarith [hb2.2]
  linarith [hb1.1]

end Sample

end PopulationAdjustment

end CausalInference
