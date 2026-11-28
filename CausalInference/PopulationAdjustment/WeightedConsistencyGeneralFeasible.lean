/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyArm

/-!
# Feasibility and dispersion of entropy balancing weights at converging targets

The weighted (matching adjusted) estimator fits entropy balancing weights `cₙᵢ` to reported
target moments. Its consistency needs two properties of the weights, each with probability
tending to one: **feasibility** (the weights form a probability vector reproducing the target
moments) and **vanishing dispersion** (`∑ᵢ cₙᵢ² (1 + ‖φ(Xᵢ) - t‖²) → 0`, the scaling the weighted
law of large numbers needs for the allocation and residual noise). This file derives both from
conditions on the law of the features, for reported targets `tₙ` that converge to `t` in
probability (deterministic or random) and for features that need not be bounded.

**Feasibility, uniformly near `t`.** Under the margin condition at `t` with margin `δ`, the
uniform law of large numbers on the unit sphere gives, with probability tending to one, the
sample margin condition at `t`. A shift of the target by at most `δ / 4` along every direction
keeps a sample margin `δ / 2` (`marginClamp_le_marginClamp_half`), so on the same event the dual
problem at every target `s` with `p ‖s - t‖ ≤ δ / 4` has a minimizer of norm at most `16 / δ²`
(`exists_isMinOn_logPartition_near`). With `tₙ → t` in probability this gives feasibility at
`tₙ` with probability tending to one (`withProbTendingToOne_balancingFeasible`). No bound on the
features is used.

**Dispersion.** For a dual parameter of norm at most `S` and a target within `ρ` of `t`, with
`gᵢ = ‖φ(Xᵢ) - t‖` and `L = p S`, the weights satisfy `cᵢ ≤ e^{2 L ρ} e^{L gᵢ} / ∑ⱼ e^{-L gⱼ}`
(`entropyWeights_le_exp_div`). Hence the dispersion is at most
`e^{4 L ρ} n⁻¹ Aₙ / Bₙ²` with the sample means `Aₙ` of `e^{2 L g}(1 + g²)` and `Bₙ` of
`e^{-L g}`, which converge by the law of large numbers to a finite limit and to a positive limit.
So the dispersion vanishes as soon as `E[exp(κ ‖φ(X) - t‖)] < ∞` for `κ = 2 p (16 / δ²) + 1`
(`balancingDispersionVanishes_of_integrable_exp`). Features bounded almost surely are a special
case (`balancingDispersionVanishes_of_ae_bounded`).

The exponential moment order is tied to the margin, not to the population dual parameter. The
sharper route (convergence of the sample dual minimizer to the population dual `β*` by convexity,
under an exponential moment near `β*` only) is not carried out here.

## Main definitions

* `balancingFeasibleEvent`: the event that the weights at the target are feasible.
* `BalancingDispersionVanishes`: the dispersion of the weights tends to zero in probability.

## Main results

* `exists_isMinOn_logPartition_near`, `withProbTendingToOne_balancingFeasible`.
* `entropyWeights_le_exp_div`, `balancingDispersionVanishes_of_integrable_exp`,
  `balancingDispersionVanishes_of_ae_bounded`.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

/-! ### Shifting the target keeps a margin -/

/-- Shifting the argument down by at most `δ / 4` and halving the margin does not decrease the
clamp: `marginClamp δ u ≤ marginClamp (δ / 2) u'` when `u - δ / 4 ≤ u'`. -/
theorem marginClamp_le_marginClamp_half {δ u u' : ℝ} (hδ : 0 < δ) (h : u - δ / 4 ≤ u') :
    marginClamp δ u ≤ marginClamp (δ / 2) u' := by
  unfold marginClamp
  rcases le_or_gt (δ / 2) u with hu | hu
  · refine max_le_max le_rfl (min_le_min le_rfl ?_)
    have h2 : 2 * u' / (δ / 2) = 4 * u' / δ := by field_simp; ring
    rw [h2, sub_le_sub_iff_right, div_le_div_iff_of_pos_right hδ]
    linarith
  · refine max_le (le_max_left _ _) ((min_le_right _ _).trans ?_)
    have : 2 * u / δ - 1 < 0 := by
      rw [sub_neg, div_lt_one hδ]; linarith
    exact this.le.trans (le_max_left _ _)

section Deterministic

variable {n p : ℕ}

/-- **The dual problem has a bounded minimizer at every target near `t`.** If the sample margin
condition holds at `t` with margin `δ` (in every direction `v` of norm one the sample average of
`marginClamp δ (vᵀ(yᵢ - t))` exceeds `δ / 2`), then for every target `s` with
`p ‖s - t‖ ≤ δ / 4` the dual `Q` of the centered features `yᵢ - s` has a global minimizer of norm
at most `16 / δ²`. -/
theorem exists_isMinOn_logPartition_near (hn : 0 < n) {y : Fin n → Fin p → ℝ} {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ / 2 < (n : ℝ)⁻¹ * ∑ i, marginClamp δ (v ⬝ᵥ (y i - t)))
    {s : Fin p → ℝ} (hs : p * ‖s - t‖ ≤ δ / 4) :
    ∃ β, ‖β‖ ≤ 16 / δ ^ 2 ∧ IsMinOn (logPartition fun i => y i - s) Set.univ β := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h' : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ / 2 / 2 < (n : ℝ)⁻¹ * ∑ i, marginClamp (δ / 2) (v ⬝ᵥ (y i - s)) := by
    intro v hv
    have hle : ∑ i, marginClamp δ (v ⬝ᵥ (y i - t)) ≤
        ∑ i, marginClamp (δ / 2) (v ⬝ᵥ (y i - s)) := by
      refine Finset.sum_le_sum fun i _ => marginClamp_le_marginClamp_half hδ ?_
      have hsplit : v ⬝ᵥ (y i - s) = v ⬝ᵥ (y i - t) + v ⬝ᵥ (t - s) := by
        rw [← dotProduct_add]; congr 1; abel
      have hb : |v ⬝ᵥ (t - s)| ≤ δ / 4 := by
        refine (abs_dotProduct_le_mul_norm v (t - s)).trans ?_
        rw [hv, one_mul, norm_sub_rev]; exact hs
      rw [hsplit]; linarith [neg_abs_le (v ⬝ᵥ (t - s))]
    have := h v hv
    have h2 : (n : ℝ)⁻¹ * ∑ i, marginClamp δ (v ⬝ᵥ (y i - t)) ≤
        (n : ℝ)⁻¹ * ∑ i, marginClamp (δ / 2) (v ⬝ᵥ (y i - s)) :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hn'.le)
    linarith
  obtain ⟨β, hβ, hmin⟩ := exists_isMinOn_logPartition_of_margin hn hδ2 h'
  refine ⟨β, hβ.trans (le_of_eq ?_), hmin⟩
  field_simp; ring

end Deterministic

section Sample

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪] {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {p : ℕ}

/-- **The sample margin condition holds with probability tending to one.** Under the margin
condition at `t` for the law of the features `f(O 0)`, with probability tending to one the
sample is nonempty and in every direction `v` of norm one the sample average of
`marginClamp δ (vᵀ(f(O i) - t))` exceeds `δ / 2` (uniform law of large numbers on the unit
sphere). -/
theorem withProbTendingToOne_sample_margin (hO : IsIIDSample O P) {f : 𝒪 → Fin p → ℝ}
    (hf : Measurable f) {t : Fin p → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)}) :
    WithProbTendingToOne P (fun n => {ω | 0 < n ∧ ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ / 2 < (n : ℝ)⁻¹ * ∑ i : Fin n, marginClamp δ (v ⬝ᵥ (f (O i ω) - t))}) := by
  set ψ : 𝒪 → (Fin p → ℝ) → ℝ := fun z v => marginClamp δ (v ⬝ᵥ (f z - t)) with hψ
  set K : Set (Fin p → ℝ) := Metric.sphere 0 1 with hK
  have hKc : IsCompact K := isCompact_sphere 0 1
  have hmeas : ∀ v ∈ K, Measurable fun z => ψ z v := fun v _ =>
    (continuous_marginClamp δ).measurable.comp
      ((continuous_const.dotProduct continuous_id).measurable.comp (hf.sub_const t))
  have hcont : ∀ᵐ z ∂(P.map (O 0)), ContinuousOn (ψ z) K := ae_of_all _ fun z =>
    ((continuous_marginClamp δ).comp (continuous_id.dotProduct continuous_const)).continuousOn
  have hdom : ∀ᵐ z ∂(P.map (O 0)), ∀ v ∈ K, |ψ z v| ≤ (fun _ => (1 : ℝ)) z :=
    ae_of_all _ fun z v _ => by
      rw [abs_of_nonneg (marginClamp_nonneg _ _)]; exact marginClamp_le_one _ _
  obtain ⟨-, hunif⟩ := uniform_law_of_large_numbers_real hO hKc hmeas hcont
    (integrable_const (1 : ℝ)) hdom
  have hpop : ∀ v ∈ K, δ ≤ ∫ z, ψ z v ∂(P.map (O 0)) := by
    intro v hv
    have hv1 : ‖v‖ = 1 := by simpa [hK] using hv
    have hsm : MeasurableSet {z | δ ≤ v ⬝ᵥ (f z - t)} :=
      measurableSet_le measurable_const
        ((continuous_const.dotProduct continuous_id).measurable.comp (hf.sub_const t))
    refine (hmargin v hv1).trans ?_
    rw [← integral_indicator_one hsm]
    refine integral_mono ((integrable_const 1).indicator hsm) ?_ fun z => ?_
    · exact (integrable_const (1 : ℝ)).mono' (hmeas v hv).aestronglyMeasurable
        (ae_of_all _ fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (marginClamp_nonneg _ _)]
          exact marginClamp_le_one _ _)
    · by_cases hz : δ ≤ v ⬝ᵥ (f z - t)
      · rw [Set.indicator_of_mem hz]; exact (marginClamp_eq_one hδ hz).ge
      · rw [Set.indicator_of_notMem hz]; exact marginClamp_nonneg _ _
  refine ((hunif (δ / 2) (half_pos hδ)).inter withProbTendingToOne_pos).mono
    fun n ω hω => ?_
  obtain ⟨hω1, hn⟩ := hω
  simp only [Set.mem_ofPred_eq] at hω1 hn
  refine ⟨hn, fun v hv1 => ?_⟩
  have hvK : v ∈ K := by simpa [hK] using hv1
  have h1 := hω1 v hvK
  have h2 := hpop v hvK
  have heq : sampleMean (fun z => ψ z v) O n ω =
      (n : ℝ)⁻¹ * ∑ i : Fin n, marginClamp δ (v ⬝ᵥ (f (O i ω) - t)) := by
    rw [sampleMean, ← Fin.sum_univ_eq_sum_range (fun i => ψ (O i ω) v) n]
  rw [← heq]
  rw [Real.dist_eq] at h1
  linarith [(abs_lt.1 h1).1]

/-- The event that the entropy balancing weights of the first `n` records at the target `s` are
feasible: they form a probability vector with `∑ᵢ cᵢ f(O i) = s`. -/
def balancingFeasibleEvent (f : 𝒪 → Fin p → ℝ) (O : ℕ → Ω → 𝒪) (tm : ℕ → Ω → Fin p → ℝ)
    (n : ℕ) : Set Ω :=
  {ω | balancingWeights (fun i : Fin n => f (O i ω) - tm n ω) ∈
    balancingSet (fun i : Fin n => f (O i ω) - tm n ω)}

/-- **Feasibility at converging targets with probability tending to one.** Under the margin
condition at `t` and reported targets `tₙ → t` in probability (deterministic or random, with no
independence needed), with probability tending to one the sample is nonempty, `p ‖tₙ - t‖ ≤ δ / 4`,
and the dual at `tₙ` has a minimizer of norm at most `16 / δ²`; in particular the entropy
balancing weights at `tₙ` are feasible and are the entropy weights of that minimizer. No bound
on the features is assumed. -/
theorem withProbTendingToOne_balancingFeasible (hO : IsIIDSample O P) {f : 𝒪 → Fin p → ℝ}
    (hf : Measurable f) {t : Fin p → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t)) :
    WithProbTendingToOne P (fun n => {ω | 0 < n ∧ p * ‖tm n ω - t‖ ≤ δ / 4 ∧
      ∃ β, ‖β‖ ≤ 16 / δ ^ 2 ∧
        IsMinOn (logPartition fun i : Fin n => f (O i ω) - tm n ω) Set.univ β ∧
        balancingWeights (fun i : Fin n => f (O i ω) - tm n ω) ∈
          balancingSet (fun i : Fin n => f (O i ω) - tm n ω) ∧
        entropyWeights (fun i : Fin n => f (O i ω) - tm n ω) β =
          balancingWeights (fun i : Fin n => f (O i ω) - tm n ω)}) := by
  have hr : 0 < δ / (4 * (p + 1)) := by positivity
  refine ((withProbTendingToOne_sample_margin hO hf hδ hmargin).inter
    (htm.withProbTendingToOne_dist_lt hr)).mono fun n ω hω => ?_
  obtain ⟨⟨hn, hm⟩, hd⟩ := hω
  simp only [Set.mem_ofPred_eq, dist_eq_norm] at hd
  have hs : p * ‖tm n ω - t‖ ≤ δ / 4 := by
    have hp : (p : ℝ) ≤ p + 1 := by linarith
    calc (p : ℝ) * ‖tm n ω - t‖ ≤ (p + 1) * (δ / (4 * (p + 1))) := by
          gcongr
      _ = δ / 4 := by field_simp
  obtain ⟨β, hβ, hmin⟩ := exists_isMinOn_logPartition_near hn hδ hm hs
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpos := exists_isMinOn_logPartition_iff.1 ⟨β, hmin⟩
  exact ⟨hn, hs, β, hβ, hmin, (balancingWeights_isMinOn hpos).2.1,
    entropyWeights_eq_balancingWeights hmin⟩

end Sample

/-! ### Dispersion of the weights -/

section WeightBound

variable {n p : ℕ}

/-- **A weight bound without bounded features.** If `|βᵀΔⱼ| ≤ hⱼ` for every unit, then the
entropy weight of unit `i` is at most `exp(hᵢ) / ∑ⱼ exp(-hⱼ)`. -/
theorem entropyWeights_le_exp_div [Nonempty (Fin n)] {Δ : Fin n → Fin p → ℝ} {β : Fin p → ℝ}
    {h : Fin n → ℝ} (hb : ∀ j, |β ⬝ᵥ Δ j| ≤ h j) (i : Fin n) :
    entropyWeights Δ β i ≤ Real.exp (h i) / ∑ j, Real.exp (-h j) := by
  have hD : 0 < ∑ j, Real.exp (-h j) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ : ∑ j, Real.exp (-h j) ≤ partitionFunction Δ β :=
    Finset.sum_le_sum fun j _ => Real.exp_le_exp.2 (neg_le_of_abs_le (hb j))
  rw [entropyWeights]
  calc Real.exp (β ⬝ᵥ Δ i) / partitionFunction Δ β
      ≤ Real.exp (h i) / partitionFunction Δ β :=
        (div_le_div_iff_of_pos_right (partitionFunction_pos β)).2
          (Real.exp_le_exp.2 (le_of_abs_le (hb i)))
    _ ≤ Real.exp (h i) / ∑ j, Real.exp (-h j) := by gcongr

/-- **The dispersion bound.** If `|βᵀΔⱼ| ≤ hⱼ` for every unit and `wᵢ ≥ 0`, then
`∑ᵢ cᵢ² wᵢ ≤ (∑ᵢ exp(2 hᵢ) wᵢ) / (∑ⱼ exp(-hⱼ))²` for the entropy weights `c` of `β`. -/
theorem sum_sq_entropyWeights_mul_le [Nonempty (Fin n)] {Δ : Fin n → Fin p → ℝ}
    {β : Fin p → ℝ} {h : Fin n → ℝ} (hb : ∀ j, |β ⬝ᵥ Δ j| ≤ h j) {w : Fin n → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    ∑ i, entropyWeights Δ β i ^ 2 * w i ≤
      (∑ i, Real.exp (2 * h i) * w i) / (∑ j, Real.exp (-h j)) ^ 2 := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := entropyWeights_le_exp_div hb i
  have h0 : 0 ≤ entropyWeights Δ β i := (entropyWeights_pos β i).le
  calc entropyWeights Δ β i ^ 2 * w i ≤ (Real.exp (h i) / ∑ j, Real.exp (-h j)) ^ 2 * w i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (hw i)
    _ = Real.exp (2 * h i) * w i / (∑ j, Real.exp (-h j)) ^ 2 := by
        rw [div_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

end WeightBound

section Limits

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Domination by a sequence tending to zero in probability.** If `|Xₙ| ≤ Yₙ` on events of
probability tending to one and `Yₙ → 0` in probability, then `Xₙ → 0` in probability. -/
theorem tendstoInMeasure_zero_of_abs_le_of_tendstoInMeasure {X Y : ℕ → Ω → ℝ} {A : ℕ → Set Ω}
    (hA : WithProbTendingToOne P A) (hY : TendstoInMeasure P Y atTop (fun _ => 0))
    (h : ∀ n, ∀ ω ∈ A n, |X n ω| ≤ Y n ω) : TendstoInMeasure P X atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ =>
    ⟨fun n => A n ∩ {ω | dist (Y n ω) 0 < ε},
      (hA.inter (hY.withProbTendingToOne_dist_lt hε)).eventually_le hκ,
      Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨h1, h2⟩ := hω
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h2 ⊢
  exact (h n ω h1).trans_lt ((le_abs_self _).trans_lt h2)

/-- If `Zₙ → z` in probability, then `n⁻¹ Zₙ → 0` in probability. -/
theorem tendstoInMeasure_inv_natCast_mul_zero {Z : ℕ → Ω → ℝ} {z : ℝ}
    (hZ : TendstoInMeasure P Z atTop (fun _ => z)) :
    TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * Z n ω) atTop (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_abs_le_on (hZ.withProbTendingToOne_dist_lt one_pos)
    (tendsto_const_div_atTop_nhds_zero_nat (|z| + 1)) fun n ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω
  simp only [abs_mul, abs_inv, Nat.abs_cast]
  rw [div_eq_inv_mul]
  gcongr
  linarith [abs_sub_abs_le_abs_sub (Z n ω) z]

end Limits

section Dispersion

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪] {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {p : ℕ}

/-- **Vanishing dispersion of the balancing weights.** For records `O`, a feature map `f`, a
limit target `t` and reported targets `tₙ`, the dispersion
`∑ᵢ cₙᵢ² (1 + ‖f(O i) - t‖²)` of the entropy balancing weights `cₙ` at `tₙ` tends to zero in
probability. This is the scaling under which the weighted law of large numbers removes the
allocation noise (whose conditional variance is at most the square of an affine function of the
features) and the residual noise (bounded conditional variance). -/
def BalancingDispersionVanishes (P : Measure Ω) (f : 𝒪 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒪) (tm : ℕ → Ω → Fin p → ℝ) : Prop :=
  TendstoInMeasure P (fun n ω => ∑ i : Fin n,
    balancingWeights (fun j : Fin n => f (O j ω) - tm n ω) i ^ 2 * (1 + ‖f (O i ω) - t‖ ^ 2))
    atTop (fun _ => 0)

theorem one_add_sq_le_two_mul_exp_of_nonneg {g : ℝ} (hg : 0 ≤ g) : 1 + g ^ 2 ≤ 2 * Real.exp g := by
  nlinarith [Real.quadratic_le_exp_of_nonneg hg]

/-- **Vanishing dispersion from an exponential moment.** Under the margin condition at `t` with
margin `δ`, reported targets `tₙ → t` in probability and a finite exponential moment
`E[exp(κ ‖f(O 0) - t‖)] < ∞` of order `κ = 2 p (16 / δ²) + 1`, the dispersion of the entropy
balancing weights at `tₙ` vanishes. On the feasibility event of
`withProbTendingToOne_balancingFeasible` the dual parameter has norm at most `S = 16 / δ²`, and
with `L = p S` and `gᵢ = ‖f(O i) - t‖` the dispersion is at most
`e^{16 / δ} n⁻¹ Aₙ / Bₙ²` with the sample means `Aₙ` of `e^{2 L g}(1 + g²)` and `Bₙ` of
`e^{-L g}`; the law of large numbers finishes. -/
theorem balancingDispersionVanishes_of_integrable_exp (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {f : 𝒪 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t))
    (hexp : Integrable (fun z => Real.exp ((2 * p * (16 / δ ^ 2) + 1) * ‖f z - t‖))
      (P.map (O 0))) :
    BalancingDispersionVanishes P f t O tm := by
  set S : ℝ := 16 / δ ^ 2 with hS
  set L : ℝ := p * S with hL
  have hS0 : 0 < S := by positivity
  have hL0 : 0 ≤ L := by positivity
  set c0 : ℝ := 4 / δ with hc0
  set g : 𝒪 → ℝ := fun z => ‖f z - t‖ with hg
  have hgm : Measurable g := (hf.sub_const t).norm
  set A : 𝒪 → ℝ := fun z => Real.exp (2 * L * g z) * (1 + g z ^ 2) with hA
  set B : 𝒪 → ℝ := fun z => Real.exp (-(L * g z)) with hB
  have hAm : Measurable A :=
    (Real.measurable_exp.comp (measurable_const.mul hgm)).mul
      (measurable_const.add (hgm.pow_const 2))
  have hBm : Measurable B := Real.measurable_exp.comp (measurable_const.mul hgm).neg
  have hAi : Integrable A (P.map (O 0)) := by
    refine (hexp.const_mul 2).mono' hAm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    have hg0 : 0 ≤ g z := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (2 * L * g z) * (1 + g z ^ 2) ≤ Real.exp (2 * L * g z) * (2 * Real.exp (g z)) :=
          by gcongr; exact one_add_sq_le_two_mul_exp_of_nonneg hg0
      _ = 2 * Real.exp ((2 * p * (16 / δ ^ 2) + 1) * ‖f z - t‖) := by
          rw [mul_left_comm, ← Real.exp_add, hL, hS]; simp only [hg]; ring_nf
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
  -- the bound `Y n ω = e^{4 c0} n⁻¹ Aₙ / Bₙ²` tends to zero
  set G : ℝ × ℝ → ℝ := fun u => u.1 / u.2 ^ 2 with hG
  have hGc : ContinuousAt G ((∫ ω, A (O 0 ω) ∂P), (∫ ω, B (O 0 ω) ∂P)) :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hEB.ne')
  have hY := ((tendstoInMeasure_inv_natCast_mul_zero
    ((hAc.prodMk hBc).comp_continuousAt hGc)).const_mul (Real.exp (4 * c0)))
  simp only [mul_zero] at hY
  refine tendstoInMeasure_zero_of_abs_le_of_tendstoInMeasure
    (withProbTendingToOne_balancingFeasible hO hf hδ hmargin htm) hY fun n ω hω => ?_
  obtain ⟨hn, hs, β, hβ, -, -, hβw⟩ := hω
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Δ : Fin n → Fin p → ℝ := fun j => f (O j ω) - tm n ω with hΔ
  have hbd : ∀ j, |β ⬝ᵥ Δ j| ≤ L * g (O j ω) + c0 := fun j => by
    have h1 : ‖Δ j‖ ≤ g (O j ω) + ‖tm n ω - t‖ := by
      have : Δ j = (f (O j ω) - t) - (tm n ω - t) := by simp [hΔ]
      rw [this]; exact norm_sub_le _ _
    refine (abs_dotProduct_le_mul_norm β (Δ j)).trans ?_
    calc (p : ℝ) * (‖β‖ * ‖Δ j‖) ≤ p * (S * (g (O j ω) + ‖tm n ω - t‖)) := by
          gcongr
      _ = L * g (O j ω) + S * (p * ‖tm n ω - t‖) := by rw [hL]; ring
      _ ≤ L * g (O j ω) + S * (δ / 4) := by gcongr
      _ = L * g (O j ω) + c0 := by rw [hS, hc0]; field_simp; ring
  have hsum := sum_sq_entropyWeights_mul_le hbd (w := fun i => 1 + g (O i ω) ^ 2)
    (fun i => by positivity)
  rw [hβw] at hsum
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
  have he : Real.exp (4 * c0) = Real.exp (2 * c0) / Real.exp (-c0) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]; push_cast; ring_nf
  rw [he]
  field_simp

/-- **Features bounded almost surely.** If `‖f(O 0) - t‖ ≤ B` almost surely, the exponential
moment of `balancingDispersionVanishes_of_integrable_exp` is finite, so the dispersion of the
weights at targets `tₙ → t` vanishes under the margin condition. -/
theorem balancingDispersionVanishes_of_ae_bounded (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {f : 𝒪 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ᵐ z ∂(P.map (O 0)), ‖f z - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t)) :
    BalancingDispersionVanishes P f t O tm := by
  refine balancingDispersionVanishes_of_integrable_exp hO hOm hf hδ hmargin htm ?_
  refine (integrable_const (Real.exp ((2 * p * (16 / δ ^ 2) + 1) * B))).mono'
    (Real.measurable_exp.comp (measurable_const.mul (hf.sub_const t).norm)).aestronglyMeasurable
    (hB.mono fun z hz => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz (by positivity))

end Dispersion

end PopulationAdjustment

end CausalInference
