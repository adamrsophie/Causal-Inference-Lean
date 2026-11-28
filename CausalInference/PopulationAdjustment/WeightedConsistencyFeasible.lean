/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.EntropyExistence
public import CausalInference.Estimation.LawOfLargeNumbers

/-!
# Feasibility of the sample balancing problem with probability tending to one

The entropy balancing weights of an i.i.d. sample balance the features exactly only when the
target moments `t` are feasible for the sample: when a strictly positive probability vector
reproduces `t`, equivalently when the dual `Q(β) = log ∑ᵢ exp(βᵀ(φ(xᵢ) - t))` has a minimizer
(`exists_isMinOn_logPartition_iff`). This file derives sample feasibility, with probability
tending to one, from a condition on the law of the features, and bounds the weights by `K / n`
on the same events.

**The margin condition.** There is `δ > 0` such that, in every direction `v` of norm one (sup
norm), the centered features exceed the target by `δ` along `v` with probability at least `δ`:
`P(vᵀ(φ(X) - t) ≥ δ) ≥ δ`. It excludes target moments on the boundary of the convex hull of the
support of the features and features concentrated on a hyperplane; it says, quantitatively, that
`t` lies in the interior of the convex hull of the support. (That the interior condition implies
the margin condition for bounded features is not shown here; the instances verify the margin
condition directly.)

**The argument.** A continuous lower bound of the indicator of `{vᵀ(φ - t) ≥ δ}` is averaged
over the sample; by the uniform law of large numbers on the unit sphere, with probability tending
to one every such average exceeds `δ / 2`. On that event the partition function is larger at
every `β` with `‖β‖ = 4 / δ²` than at `0` (`logPartition_lt_of_margin`), so the minimum of the
convex dual over the closed ball is a global minimum, attained at a point of norm at most
`4 / δ²` (`exists_isMinOn_logPartition_of_margin`). With features bounded by `B`, the weights of
such a parameter are at most `exp(2 p (4 / δ²) B) / n` (`entropyWeights_le_of_norm_le`).

## Main definitions

* `marginClamp δ s = max 0 (min 1 (2 s / δ - 1))`, the continuous lower bound of `1{s ≥ δ}`.

## Main results

* `exists_isMinOn_logPartition_of_margin`: the deterministic step.
* `entropyWeights_le_of_norm_le`: the weights of a bounded parameter are at most `K / n`.
* `withProbTendingToOne_balancingWeights`: under the margin condition and bounded features, with
  probability tending to one the sample is nonempty, the entropy balancing weights are feasible
  (they form a probability vector balancing the features at `t`), and they are at most `K / n`.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

/-! ### The clamp -/

/-- The continuous lower bound `max 0 (min 1 (2 s / δ - 1))` of the indicator `1{s ≥ δ}`: it is
`0` below `δ / 2`, `1` from `δ` on, and affine in between. -/
noncomputable def marginClamp (δ s : ℝ) : ℝ := max 0 (min 1 (2 * s / δ - 1))

theorem marginClamp_nonneg (δ s : ℝ) : 0 ≤ marginClamp δ s := le_max_left _ _

theorem marginClamp_le_one (δ s : ℝ) : marginClamp δ s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem marginClamp_eq_one {δ s : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) : marginClamp δ s = 1 := by
  have h : 1 ≤ 2 * s / δ - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith
  rw [marginClamp, min_eq_left h, max_eq_right zero_le_one]

theorem lt_of_marginClamp_pos {δ s : ℝ} (hδ : 0 < δ) (h : 0 < marginClamp δ s) : δ / 2 < s := by
  by_contra hs
  push Not at hs
  have : 2 * s / δ - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hδ]; linarith
  have h0 : marginClamp δ s = 0 :=
    max_eq_left ((min_le_right _ _).trans this)
  linarith

theorem continuous_marginClamp (δ : ℝ) : Continuous (marginClamp δ) := by
  unfold marginClamp; fun_prop

/-! ### The deterministic step -/

section Deterministic

variable {n p : ℕ}

/-- A dot product is at most `p ‖β‖ ‖w‖` in absolute value (sup norms). -/
theorem abs_dotProduct_le_mul_norm (β w : Fin p → ℝ) : |β ⬝ᵥ w| ≤ p * (‖β‖ * ‖w‖) := by
  rw [dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |β k * w k| ≤ ∑ _k : Fin p, ‖β‖ * ‖w‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact mul_le_mul (norm_le_pi_norm β k) (norm_le_pi_norm w k) (norm_nonneg _)
          (norm_nonneg _)
    _ = p * (‖β‖ * ‖w‖) := by simp

/-- **The partition function grows on a sphere under the sample margin condition.** If in every
direction `v` of norm one the sample average of `marginClamp δ (vᵀΔᵢ)` exceeds `δ / 2`, then
`Q(β) > Q(0)` for every `β` with `‖β‖ = 4 / δ²`. -/
theorem logPartition_lt_of_margin (hn : 0 < n) {Δ : Fin n → Fin p → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ / 2 < (n : ℝ)⁻¹ * ∑ i, marginClamp δ (v ⬝ᵥ Δ i))
    {β : Fin p → ℝ} (hβ : ‖β‖ = 4 / δ ^ 2) :
    logPartition Δ 0 < logPartition Δ β := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set S := 4 / δ ^ 2 with hS
  have hS0 : 0 < S := by positivity
  obtain ⟨v, hv1, hβv⟩ : ∃ v : Fin p → ℝ, ‖v‖ = 1 ∧ β = S • v := by
    refine ⟨S⁻¹ • β, ?_, ?_⟩
    · rw [norm_smul, hβ, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hS0), inv_mul_cancel₀ hS0.ne']
    · rw [smul_smul, mul_inv_cancel₀ hS0.ne', one_smul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hav := h v hv1
  have hE : 2 / δ < Real.exp (S * (δ / 2)) := by
    have h1 : S * (δ / 2) = 2 / δ := by rw [hS]; field_simp; ring
    rw [h1]
    linarith [Real.add_one_le_exp (2 / δ)]
  have hterm : ∀ i, marginClamp δ (v ⬝ᵥ Δ i) * Real.exp (S * (δ / 2)) ≤
      Real.exp (β ⬝ᵥ Δ i) := fun i => by
    rcases (marginClamp_nonneg δ (v ⬝ᵥ Δ i)).lt_or_eq with hpos | h0
    · have hlt := lt_of_marginClamp_pos hδ hpos
      rw [hβv, smul_dotProduct, smul_eq_mul]
      calc marginClamp δ (v ⬝ᵥ Δ i) * Real.exp (S * (δ / 2))
          ≤ 1 * Real.exp (S * (δ / 2)) := by
            gcongr; exact marginClamp_le_one _ _
        _ ≤ Real.exp (S * (v ⬝ᵥ Δ i)) := by
            rw [one_mul]; exact Real.exp_le_exp.2 (by nlinarith)
    · rw [← h0, zero_mul]; exact (Real.exp_pos _).le
  have hsum : (n : ℝ) < partitionFunction Δ β := by
    have h1 : (∑ i, marginClamp δ (v ⬝ᵥ Δ i)) * Real.exp (S * (δ / 2)) ≤
        partitionFunction Δ β := by
      rw [Finset.sum_mul, partitionFunction]; exact Finset.sum_le_sum fun i _ => hterm i
    have h2 : n * (δ / 2) < ∑ i, marginClamp δ (v ⬝ᵥ Δ i) := by
      rw [lt_inv_mul_iff₀ hn'] at hav; linarith
    have h3 : (n : ℝ) ≤ n * (δ / 2) * (2 / δ) := by
      rw [mul_assoc, show δ / 2 * (2 / δ) = 1 by field_simp, mul_one]
    calc (n : ℝ) ≤ n * (δ / 2) * (2 / δ) := h3
      _ < (∑ i, marginClamp δ (v ⬝ᵥ Δ i)) * Real.exp (S * (δ / 2)) := by
          apply mul_lt_mul h2 hE.le (by positivity) (Finset.sum_nonneg fun i _ =>
            marginClamp_nonneg _ _)
      _ ≤ partitionFunction Δ β := h1
  have h0 : partitionFunction Δ 0 = n := by simp [partitionFunction]
  rw [logPartition, logPartition, h0]
  exact Real.log_lt_log hn' hsum

/-- **The dual has a bounded minimizer under the sample margin condition.** Under the hypothesis
of `logPartition_lt_of_margin`, `Q` has a global minimizer of norm at most `4 / δ²`: its minimum
over the closed ball is not attained on the sphere, and by convexity a point outside the ball has
a larger value than `Q(0)`. -/
theorem exists_isMinOn_logPartition_of_margin (hn : 0 < n) {Δ : Fin n → Fin p → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (h : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ / 2 < (n : ℝ)⁻¹ * ∑ i, marginClamp δ (v ⬝ᵥ Δ i)) :
    ∃ β, ‖β‖ ≤ 4 / δ ^ 2 ∧ IsMinOn (logPartition Δ) Set.univ β := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set S := 4 / δ ^ 2 with hS
  have hS0 : 0 < S := by positivity
  have hL : Continuous (logPartition Δ) := by
    have hZ : Continuous (partitionFunction Δ) := by
      unfold partitionFunction; fun_prop
    exact hZ.log fun β => (partitionFunction_pos β).ne'
  obtain ⟨β₀, hβ₀, hmin⟩ := (isCompact_closedBall (0 : Fin p → ℝ) S).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hS0.le⟩ hL.continuousOn
  have hβ₀' : ‖β₀‖ ≤ S := by simpa using hβ₀
  have h0 : logPartition Δ β₀ ≤ logPartition Δ 0 :=
    hmin (Metric.mem_closedBall_self hS0.le)
  refine ⟨β₀, hβ₀', fun u _ => ?_⟩
  change logPartition Δ β₀ ≤ logPartition Δ u
  by_cases hu : ‖u‖ ≤ S
  · exact hmin (by simpa using hu)
  · push Not at hu
    have hu0 : 0 < ‖u‖ := hS0.trans hu
    set lam := S / ‖u‖ with hlam
    have hl0 : 0 < lam := div_pos hS0 hu0
    have hl1 : lam < 1 := (div_lt_one hu0).2 hu
    have hw : ‖lam • u‖ = S := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0, hlam, div_mul_cancel₀ _ hu0.ne']
    have hgt := logPartition_lt_of_margin hn hδ h hw
    have hconv := (convexOn_logPartition (Δ := Δ)).2 (Set.mem_univ u) (Set.mem_univ 0)
      hl0.le (sub_nonneg.2 hl1.le) (add_sub_cancel lam 1)
    simp only [smul_zero, add_zero, smul_eq_mul] at hconv
    have : logPartition Δ 0 < logPartition Δ u := by nlinarith
    linarith

/-- **The weights of a bounded parameter are at most `K / n`.** If `‖β‖ ≤ S` and every
`‖Δᵢ‖ ≤ B`, then `entropyWeights Δ β i ≤ exp(2 p S B) / n`. -/
theorem entropyWeights_le_of_norm_le (hn : 0 < n) {Δ : Fin n → Fin p → ℝ} {β : Fin p → ℝ}
    {S B : ℝ} (hβ : ‖β‖ ≤ S) (hΔ : ∀ i, ‖Δ i‖ ≤ B) (i : Fin n) :
    entropyWeights Δ β i ≤ Real.exp (2 * p * S * B) / n := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set M := p * (S * B) with hM
  have hbd : ∀ j, |β ⬝ᵥ Δ j| ≤ M := fun j =>
    (abs_dotProduct_le_mul_norm β (Δ j)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hβ (hΔ j) (norm_nonneg _) ((norm_nonneg _).trans hβ)) (Nat.cast_nonneg p))
  have hup : Real.exp (β ⬝ᵥ Δ i) ≤ Real.exp M := Real.exp_le_exp.2 (le_of_abs_le (hbd i))
  have hlow : n * Real.exp (-M) ≤ partitionFunction Δ β := by
    calc (n : ℝ) * Real.exp (-M) = ∑ _j : Fin n, Real.exp (-M) := by simp
      _ ≤ partitionFunction Δ β := Finset.sum_le_sum fun j _ =>
          Real.exp_le_exp.2 (neg_le_of_abs_le (hbd j))
  rw [entropyWeights, div_le_div_iff₀ (partitionFunction_pos β) hn']
  calc Real.exp (β ⬝ᵥ Δ i) * n ≤ Real.exp M * n := by gcongr
    _ = Real.exp (2 * p * S * B) * (n * Real.exp (-M)) := by
        rw [show 2 * (p : ℝ) * S * B = M + M by rw [hM]; ring, Real.exp_add]
        rw [show Real.exp M * Real.exp M * (n * Real.exp (-M)) =
          Real.exp M * n * (Real.exp M * Real.exp (-M)) by ring, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]
    _ ≤ Real.exp (2 * p * S * B) * partitionFunction Δ β := by gcongr

end Deterministic

/-! ### The sample problem is feasible with probability tending to one -/

section Sample

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪] {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {p : ℕ}

omit [IsProbabilityMeasure P] in
/-- The sample is nonempty with probability tending to one. -/
theorem withProbTendingToOne_pos : WithProbTendingToOne P (fun n => {_ω : Ω | 0 < n}) := by
  refine tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn => ?_
  have : {_ω : Ω | 0 < n}ᶜ = ∅ := by
    ext ω; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_not]; omega
  rw [this, measure_empty]

/-- **Sample feasibility and bounded weights with probability tending to one.** Let `O` be an
i.i.d. sample of records, `f` a measurable feature map with `‖f z - t‖ ≤ B` for every record, and
assume the margin condition: for some `δ > 0` and every `v` of norm one,
`P(vᵀ(f(O 0) - t) ≥ δ) ≥ δ`. Then, with probability tending to one, the sample is nonempty, the
entropy balancing weights of the centered features `f(O i) - t` are feasible (a probability
vector balancing the features at `t`) and they are at most `exp(2 p (4 / δ²) B) / n`. -/
theorem withProbTendingToOne_balancingWeights (hO : IsIIDSample O P) {f : 𝒪 → Fin p → ℝ}
    (hf : Measurable f) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ z, ‖f z - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)}) :
    WithProbTendingToOne P (fun n => {ω | 0 < n ∧
      balancingWeights (fun i : Fin n => f (O i ω) - t) ∈
        balancingSet (fun i : Fin n => f (O i ω) - t) ∧
      ∀ i, balancingWeights (fun i : Fin n => f (O i ω) - t) i ≤
        Real.exp (2 * p * (4 / δ ^ 2) * B) / n}) := by
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
  -- the population averages of the clamp are at least `δ`
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
  set Δ : Fin n → Fin p → ℝ := fun i => f (O i ω) - t with hΔ
  have hav : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ / 2 < (n : ℝ)⁻¹ * ∑ i, marginClamp δ (v ⬝ᵥ Δ i) := by
    intro v hv1
    have hvK : v ∈ K := by simpa [hK] using hv1
    have h1 := hω1 v hvK
    have h2 := hpop v hvK
    have heq : sampleMean (fun z => ψ z v) O n ω =
        (n : ℝ)⁻¹ * ∑ i, marginClamp δ (v ⬝ᵥ Δ i) := by
      rw [sampleMean, ← Fin.sum_univ_eq_sum_range (fun i => ψ (O i ω) v) n]
    rw [← heq]
    rw [Real.dist_eq] at h1
    linarith [(abs_lt.1 h1).1]
  obtain ⟨β, hβS, hβmin⟩ := exists_isMinOn_logPartition_of_margin hn hδ hav
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpos := exists_isMinOn_logPartition_iff.1 ⟨β, hβmin⟩
  refine ⟨hn, (balancingWeights_isMinOn hpos).2.1, fun i => ?_⟩
  rw [← entropyWeights_eq_balancingWeights hβmin]
  exact entropyWeights_le_of_norm_le hn hβS (fun i => hB _) i

end Sample

end PopulationAdjustment

end CausalInference
