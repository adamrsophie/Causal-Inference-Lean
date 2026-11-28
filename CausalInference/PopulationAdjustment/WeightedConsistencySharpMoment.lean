/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencySharpDual
public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralTrial
public import CausalInference.PopulationAdjustment.WeightedNormalityPopulation

/-!
# Consistency of the weighted arm mean under one exponential moment

The consistency theorems of `WeightedConsistencyGeneralArm` assume an exponential moment
`E[exp(κ ‖φ(X) - t‖)] < ∞` of order `κ = 2 p (16 / δ²) + 1` fixed by the margin `δ`, or of all
orders under the interior condition. Here the order is tied to the population dual minimizer
`β*` instead: an exponential moment of some order `κ > 2 p ‖β*‖` suffices.

**Why `2 p ‖β*‖`.** The dispersion `∑ᵢ cᵢ² (1 + ‖φ(Xᵢ) - t‖²)` of the weights
`cᵢ = exp(β̂ᵀΔᵢ) / ∑ⱼ exp(β̂ᵀΔⱼ)` is `n⁻¹` times the ratio of the sample means of
`exp(2 β̂ᵀΔ)(1 + ‖Δ‖²)` and of `exp(β̂ᵀΔ)` (squared). Since `β̂ → β*`
(`tendstoInMeasure_dualMinimizer_of_isMinOn`), with probability tending to one `β̂` lies in a ball
of radius `r` around `β*`, and the numerator is dominated by `exp(2 p (‖β*‖ + r) ‖Δ‖)(1 + ‖Δ‖²)`;
the bound `|βᵀv| ≤ p ‖β‖ ‖v‖` is the one for the sup norm of `Fin p → ℝ`. For `κ > 2 p ‖β*‖` a
radius `r` with `2 p (‖β*‖ + r) + r = κ` absorbs the polynomial factor, and the law of large numbers
makes the ratio bounded in probability. Measuring `β` in the `ℓ¹` norm instead, the bound
`|βᵀv| ≤ ‖β‖₁ ‖v‖` (sup norm on `v`) gives the order `2 ‖β*‖₁`. In both forms the condition is
the finiteness, with some room, of `E[exp(2 β*ᵀΔ)]`, which is the moment the variance of the
weighted mean involves.

**Bounded features.** For bounded features the minimizers of `sharpDualObjective` are exactly
the population tilt `tiltMinimizer` (`isMinOn_sharpDualObjective_iff_eq_tiltMinimizer`), so the
minimizer used here extends that tilt to unbounded features.

## Main results

* `sharpDualObjective_eq_ofReal_tiltObjective`,
  `isMinOn_sharpDualObjective_iff_eq_tiltMinimizer`: the bounded case.
* `balancingDispersionVanishes_of_isMinOn`: the weights disperse.
* `sampleBalancedArmMean_isConsistent_of_isMinOn`: consistency under `κ > 2 p ‖β*‖`.
* `sampleBalancedArmMean_isConsistent_of_interior_allOrders`: the interior condition with all
  exponential moments, as a corollary.
* `sampleBalancedArmMean_isConsistent_trial_of_isMinOn`: the version for a randomized trial.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-! ### Elementary bounds -/

/-- `1 + g² ≤ (1 + 2 / r²) exp(r g)` for `g ≥ 0` and `r > 0`. -/
theorem one_add_sq_le_mul_exp {g r : ℝ} (hg : 0 ≤ g) (hr : 0 < r) :
    1 + g ^ 2 ≤ (1 + 2 / r ^ 2) * Real.exp (r * g) := by
  have h1 : 1 ≤ Real.exp (r * g) := Real.one_le_exp (by positivity)
  have h2 := Real.quadratic_le_exp_of_nonneg (mul_nonneg hr.le hg)
  have h3 : g ^ 2 = 2 / r ^ 2 * ((r * g) ^ 2 / 2) := by field_simp
  have h4 : (r * g) ^ 2 / 2 ≤ Real.exp (r * g) := by nlinarith [mul_nonneg hr.le hg]
  have h5 : g ^ 2 ≤ 2 / r ^ 2 * Real.exp (r * g) := by
    rw [h3]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
  nlinarith

/-- Square integrability from an exponential moment of any positive order. -/
theorem integrable_sq_of_integrable_exp_pos {𝒟 : Type*} [MeasurableSpace 𝒟] {ν : Measure 𝒟}
    {g : 𝒟 → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) {κ : ℝ} (hκ : 0 < κ)
    (hexp : Integrable (fun z => Real.exp (κ * g z)) ν) : Integrable (fun z => g z ^ 2) ν :=
  (hexp.const_mul (1 + 2 / κ ^ 2)).mono' (hg.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := one_add_sq_le_mul_exp (hg0 z) hκ
      linarith)

/-! ### The bounded case -/

section Bounded

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {p : ℕ} {ν : Measure (𝒳 × Bool × ℝ)}
  {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

/-- For bounded features the objective with values in `[0, ∞]` is the real objective
`tiltObjective`. -/
theorem sharpDualObjective_eq_ofReal_tiltObjective [IsFiniteMeasure ν] (hφ : Measurable φ)
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ) :
    sharpDualObjective ν (fun z => φ z.1) t β = ENNReal.ofReal (tiltObjective ν φ t β) := by
  have he : ∀ z : 𝒳 × Bool × ℝ, tiltWeight φ t 0 β z.1 = Real.exp (β ⬝ᵥ (φ z.1 - t)) :=
    fun z => by simp [tiltWeight]
  have hi : Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (β ⬝ᵥ (φ z.1 - t))) ν := by
    simpa only [he] using integrable_tiltWeight_fst (ν := ν) hφ hB β
  rw [sharpDualObjective_eq_ofReal hi, tiltObjective]
  simp only [he]

/-- **The population tilt is the unique minimizer for bounded features.** Under bounded features
and the margin condition, a parameter minimizes `sharpDualObjective` exactly when it is the
population tilt `tiltMinimizer`. -/
theorem isMinOn_sharpDualObjective_iff_eq_tiltMinimizer [IsProbabilityMeasure ν]
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {β : Fin p → ℝ} :
    IsMinOn (sharpDualObjective ν (fun z => φ z.1) t) Set.univ β ↔ β = tiltMinimizer ν φ t := by
  have hmin0 : IsMinOn (sharpDualObjective ν (fun z => φ z.1) t) Set.univ
      (tiltMinimizer ν φ t) := isMinOn_iff.2 fun γ _ => by
    rw [sharpDualObjective_eq_ofReal_tiltObjective hφ hB,
      sharpDualObjective_eq_ofReal_tiltObjective hφ hB]
    exact ENNReal.ofReal_le_ofReal
      (isMinOn_iff.1 (isMinOn_tiltMinimizer hφ hB hδ hmargin) γ (Set.mem_univ _))
  have hf : Measurable fun z : 𝒳 × Bool × ℝ => φ z.1 := hφ.comp measurable_fst
  have hexp : Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (p / δ ^ 2 * ‖φ z.1 - t‖)) ν :=
    (integrable_const (Real.exp (p / δ ^ 2 * B))).mono'
      (Real.measurable_exp.comp (measurable_const.mul (hf.sub_const t).norm)).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hB z.1) (by positivity)))
  obtain ⟨β₀, -, huniq⟩ := existsUnique_isMinOn_sharpDualObjective hf hδ hmargin hexp
  exact ⟨fun h => (huniq β h).trans (huniq _ hmin0).symm, fun h => h ▸ hmin0⟩

end Bounded

/-! ### Dispersion -/

section Dispersion

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪] {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {p : ℕ}

/-- **The weights disperse under one exponential moment.** Under the margin condition at `t`,
reported targets `tₙ → t` in probability, a minimizer `β*` of the population dual objective and
`E[exp(κ ‖f - t‖)] < ∞` for some `κ > 2 p ‖β*‖`, the dispersion
`∑ᵢ cₙᵢ² (1 + ‖f(Oᵢ) - t‖²)` of the entropy balancing weights at `tₙ` tends to zero in
probability. -/
theorem balancingDispersionVanishes_of_isMinOn (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {f : 𝒪 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) f t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun z => Real.exp (κ * ‖f z - t‖)) (P.map (O 0)))
    (hκ : 2 * p * ‖βs‖ < κ) :
    BalancingDispersionVanishes P f t O tm := by
  have hpb : 0 ≤ (p : ℝ) * ‖βs‖ := by positivity
  have hκ1 : p * ‖βs‖ < κ := by linarith
  obtain ⟨-, hconv⟩ := tendstoInMeasure_dualMinimizer_of_isMinOn hO hf hδ hmargin htm hmin hexp hκ1
  set r₀ : ℝ := (κ - 2 * p * ‖βs‖) / (2 * p + 1) with hr₀
  have hr₀0 : 0 < r₀ := div_pos (sub_pos.2 hκ) (by positivity)
  set S : ℝ := ‖βs‖ + r₀ with hS
  have hS0 : 0 < S := by positivity
  set L : ℝ := p * S with hL
  have hL0 : 0 ≤ L := by positivity
  have hLκ : 2 * L + r₀ = κ := by
    have : (2 * p + 1) * r₀ = κ - 2 * p * ‖βs‖ := by rw [hr₀]; field_simp
    rw [hL, hS]; linarith
  set c0 : ℝ := p * S with hc0
  set g : 𝒪 → ℝ := fun z => ‖f z - t‖ with hg
  have hgm : Measurable g := (hf.sub_const t).norm
  set A : 𝒪 → ℝ := fun z => Real.exp (2 * L * g z) * (1 + g z ^ 2) with hA
  set B : 𝒪 → ℝ := fun z => Real.exp (-(L * g z)) with hB
  have hAm : Measurable A :=
    (Real.measurable_exp.comp (measurable_const.mul hgm)).mul
      (measurable_const.add (hgm.pow_const 2))
  have hBm : Measurable B := Real.measurable_exp.comp (measurable_const.mul hgm).neg
  have hAi : Integrable A (P.map (O 0)) := by
    refine (hexp.const_mul (1 + 2 / r₀ ^ 2)).mono' hAm.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    have hg0 : 0 ≤ g z := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (2 * L * g z) * (1 + g z ^ 2)
        ≤ Real.exp (2 * L * g z) * ((1 + 2 / r₀ ^ 2) * Real.exp (r₀ * g z)) := by
          gcongr; exact one_add_sq_le_mul_exp hg0 hr₀0
      _ = (1 + 2 / r₀ ^ 2) * Real.exp (κ * ‖f z - t‖) := by
          rw [mul_left_comm, ← Real.exp_add, ← hLκ]; simp only [hg]; ring_nf
  have hBi : Integrable B (P.map (O 0)) :=
    (integrable_const (1 : ℝ)).mono' hBm.aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg hL0 (norm_nonneg _))
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
      (hconv.withProbTendingToOne_dist_lt hr₀0)).inter
        (htm.withProbTendingToOne_dist_lt one_pos)) hY fun n ω hω => ?_
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
  have hbd : ∀ j, |β ⬝ᵥ Δ j| ≤ L * g (O j ω) + c0 := fun j => by
    have h1 : ‖Δ j‖ ≤ g (O j ω) + ‖tm n ω - t‖ := by
      have : Δ j = (f (O j ω) - t) - (tm n ω - t) := by simp [hΔ]
      rw [this]; exact norm_sub_le _ _
    refine (abs_dotProduct_le_mul_norm β (Δ j)).trans ?_
    calc (p : ℝ) * (‖β‖ * ‖Δ j‖) ≤ p * (S * (g (O j ω) + ‖tm n ω - t‖)) := by
          gcongr
      _ ≤ p * (S * (g (O j ω) + 1)) := by gcongr
      _ = L * g (O j ω) + c0 := by rw [hL, hc0]; ring
  have hsum := sum_sq_entropyWeights_mul_le hbd (w := fun i => 1 + g (O i ω) ^ 2)
    (fun i => by positivity)
  have hnonneg : 0 ≤ ∑ i : Fin n, balancingWeights Δ i ^ 2 * (1 + g (O i ω) ^ 2) :=
    Finset.sum_nonneg fun i _ => by positivity
  change |∑ i : Fin n, balancingWeights Δ i ^ 2 * (1 + g (O i ω) ^ 2)| ≤ _
  rw [abs_of_nonneg hnonneg]
  refine hsum.trans (le_of_eq ?_)
  have hmean : ∀ F : 𝒪 → ℝ, (n : ℝ) * sampleMean F O n ω = ∑ i : Fin n, F (O i ω) := by
    intro F
    rw [sampleMean, ← Fin.sum_univ_eq_sum_range (fun i => F (O i ω)) n, ← mul_assoc,
      mul_inv_cancel₀ hn'.ne', one_mul]
  have hAs : ∑ i : Fin n, Real.exp (2 * (L * g (O i ω) + c0)) * (1 + g (O i ω) ^ 2) =
      Real.exp (2 * c0) * (n * sampleMean A O n ω) := by
    rw [hmean A, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hA]; simp only; rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have hBs : ∑ j : Fin n, Real.exp (-(L * g (O j ω) + c0)) =
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

end Dispersion

/-! ### Consistency of the weighted arm mean -/

section Consistency

variable {Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted arm mean under one exponential moment.** Under the margin
condition at `t` for the law of the features, let `β*` minimize the population dual objective
`E[exp(βᵀ(φ(X) - t))]` and let `E[exp(κ ‖φ(X) - t‖)] < ∞` for some `κ > 2 p ‖β*‖`. For reported
targets `tₙ = Tₙ(W) → t` in probability computed from data `W` independent of the sample,
randomized assignment and the arm `a` hypotheses of
`sampleBalancedArmMean_isConsistent_of_dispersion`, the weighted arm mean at `tₙ` is consistent
for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_of_isMinOn (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {βs : Fin p → ℝ}
    (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) (fun z => φ z.1) t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖))
      (P.map (O 0))) (hκ : 2 * p * ‖βs‖ < κ)
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
  have hκ0 : 0 < κ := by linarith
  have hfeas := (tendstoInMeasure_dualMinimizer_of_isMinOn hO hf hδ hmargin htm hmin hexp
    (by linarith)).1
  have hdisp := balancingDispersionVanishes_of_isMinOn hO hOm hf hδ hmargin htm hmin hexp hκ
  have hφ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖ ^ 2) (P.map (O 0)) :=
    integrable_sq_of_integrable_exp_pos (g := fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖)
      (hf.sub_const t).norm (fun _ => norm_nonneg _) hκ0 hexp
  exact sampleBalancedArmMean_isConsistent_of_dispersion hO hOm hφ hW hWO hT htm hfeas hdisp
    hφ2 hind a hq hres2 hreg hvar haff

/-- **The interior condition with all exponential moments, as a corollary.** If `t` lies in the
interior of the closed convex hull of the support of the law of `φ(X)` and
`E[exp(κ ‖φ(X) - t‖)] < ∞` for every `κ`, the population dual minimizer `β*` exists
(`existsUnique_isMinOn_sharpDualObjective`) and the moment of order `2 p ‖β*‖ + 1` gives the
consistency of the weighted arm mean at reported targets `tₙ → t`. -/
theorem sampleBalancedArmMean_isConsistent_of_interior_allOrders (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    (hexp : ∀ κ : ℝ, Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖))
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
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  have hf : Measurable fun z : 𝒳 × Bool × ℝ => φ z.1 := hφ.comp measurable_fst
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin_of_mem_interior_map hf hint
  obtain ⟨βs, hmin, -⟩ := existsUnique_isMinOn_sharpDualObjective hf hδ hmargin (hexp _)
  exact sampleBalancedArmMean_isConsistent_of_isMinOn hO hOm hφ hδ hmargin hmin
    (hexp (2 * p * ‖βs‖ + 1)) (by linarith) hW hWO hT htm hind a hq hres2 hreg hvar haff

end Consistency

/-! ### The randomized trial -/

section Trial

variable {Ω₁ Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- The population dual objective of the records of a trial is that of its covariate law. -/
theorem sharpDualObjective_ipdLaw (hX : Measurable T.X) (hA : Measurable T.A)
    (hYo : Measurable T.obsOutcome) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t : Fin p → ℝ) :
    sharpDualObjective T.ipdLaw (fun z : 𝒳 × Bool × ℝ => φ z.1) t =
      sharpDualObjective T.covLaw φ t := by
  funext β
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hm : Measurable fun x => ENNReal.ofReal (Real.exp (β ⬝ᵥ (φ x - t))) :=
    ENNReal.measurable_ofReal.comp (measurable_exp_dotProduct_sub hφ t β)
  rw [sharpDualObjective, sharpDualObjective, Trial.ipdLaw, Population.covLaw,
    lintegral_map (f := fun z : 𝒳 × Bool × ℝ => ENNReal.ofReal (Real.exp (β ⬝ᵥ (φ z.1 - t))))
      (hm.comp measurable_fst) hf, lintegral_map hm hX]

/-- **The weighted arm mean of a randomized trial under one exponential moment.** Let `T` be
a trial with measurable covariates, assignment, observed outcome and potential outcome `Y(a)`,
with `A` independent of `(X, Y(a))`, and let `O` be a measurable i.i.d. sample of its records.
Assume the interior condition at `t` for the law of the features `φ(X)`, a minimizer `β*` of the
population dual objective `E[exp(βᵀ(φ(X) - t))]` and `E[exp(κ ‖φ(X) - t‖)] < ∞` for some
`κ > 2 p ‖β*‖`; reported targets `tₙ = Gₙ(W) → t` in probability from data `W` independent of the
sample; `P(A = a) > 0`, a conditional mean `m = a₀ + bᵀφ` of `Y(a)` given `X` with a square
integrable residual and conditional variance at most `σ²`. Then the weighted arm mean at `tₙ` is
consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_trial_of_isMinOn (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hκ : 2 * p * ‖βs‖ < κ)
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
  have hexp' : Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖))
      (P.map (O 0)) := by
    have hm1 : Measurable fun x : 𝒳 => Real.exp (κ * ‖φ x - t‖) :=
      Real.measurable_exp.comp (measurable_const.mul (hφ.sub_const t).norm)
    have h1 := hexp
    rw [Population.covLaw, integrable_map_measure hm1.aestronglyMeasurable hX.aemeasurable]
      at h1
    have hm2 : Measurable fun z : 𝒳 × Bool × ℝ => Real.exp (κ * ‖φ z.1 - t‖) :=
      hm1.comp measurable_fst
    rw [hlaw, Trial.ipdLaw, integrable_map_measure hm2.aestronglyMeasurable hf.aemeasurable]
    exact h1
  have hmin' : IsMinOn (sharpDualObjective (P.map (O 0)) (fun z => φ z.1) t) Set.univ βs := by
    rw [hlaw, sharpDualObjective_ipdLaw hX hA hYo hφ t]; exact hmin
  have hq' : 0 < T.ipdLaw.real {z | z.2.1 = a} := by
    rw [Trial.ipdLaw, map_measureReal_apply hf
      (measurableSet_eq_fun measurable_snd.fst measurable_const)]
    exact hq
  rw [← hlaw] at hind hres2' hreg' hvar' hq'
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint'
  exact sampleBalancedArmMean_isConsistent_of_isMinOn hO hOm hφ hδ hmargin hmin' hexp' hκ hW
    hWO hG htm hind a hq' hres2' hreg' hvar' haff

end Trial

end PopulationAdjustment

end CausalInference
