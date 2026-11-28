/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderDirectional

/-!
# Consistency of the weighted arm mean under one sided exponential moments

The consistency of the entropy balancing weighted arm mean under a directional moment
(`sampleBalancedArmMean_isConsistent_of_isMinOn_directional`) asks for a norm moment
`E[exp(κ ‖φ - t‖)] < ∞` of order `κ > p ‖β*‖`. The norm moment enters in three places: the gap of
the population objective on a sphere around `β*`, the uniform law of large numbers on the ball
around `β*` (both in the consistency of the sample dual minimizer), and a small envelope
`exp(s ‖Δ‖)` in the dispersion of the weights. This file shows that a norm moment of an
arbitrarily small order `s > 0` suffices, together with the directional moment.

**The envelope.** Write `c = 2 (1 + ε) β*` and `λ = 1 / (2 (1 + ε))`, so that `β* = λ c`. Every
`β` with `‖β - β*‖ ≤ ρ = (1 - λ) s / (p + 1)` is the convex combination `λ c + (1 - λ) u` with
`p ‖u‖ ≤ s`, and by convexity of `exp`
`exp(βᵀΔ) ≤ exp(cᵀΔ) + exp(s ‖Δ‖)` (`exp_dotProduct_le_envelope_oneSided`). In dimension one
this is the two point bound `exp(βΔ) ≤ exp(aΔ) + exp(bΔ)` for `a ≤ β ≤ b`.

**The steps.** With any integrable envelope of the tilts on a ball around `β*`, the gap on the
sphere (`exists_gap_on_sphere_of_envelope`) and the consistency of the sample dual minimizer
(`tendstoInMeasure_dualMinimizer_of_envelope`) hold by the arguments of the norm case. The
dispersion of the weights vanishes (`balancingDispersionVanishes_of_isMinOn_oneSided`) and the
weighted arm mean is consistent (`sampleBalancedArmMean_isConsistent_of_isMinOn_oneSided`,
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided`) under

* a norm moment `E[exp(s ‖φ - t‖)] < ∞` of some order `s > 0`, and
* the directional moment `E[exp(2 (1 + ε) β*ᵀ(φ - t))] < ∞` for some `ε > 0`.

The factor `p ‖β*‖` of the directional theorem disappears: the norm moment controls only a
neighborhood of the origin, the directional moment the direction of `β*`.

## Main results

* `exp_dotProduct_le_envelope_oneSided`, `exists_gap_on_sphere_of_envelope`,
  `tendstoInMeasure_dualMinimizer_of_envelope`.
* `exists_envelope_oneSided`, `tendstoInMeasure_dualMinimizer_of_isMinOn_oneSided`,
  `balancingDispersionVanishes_of_isMinOn_oneSided`,
  `sampleBalancedArmMean_isConsistent_of_isMinOn_oneSided`,
  `sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-! ### The convex envelope -/

section Envelope

variable {p : ℕ}

/-- **The convex envelope of the tilts near `β*`.** For `ε > 0`, `s > 0` and
`‖β - β*‖ ≤ (1 - λ) s / (p + 1)` with `λ = 1 / (2 (1 + ε))`,
`exp(βᵀv) ≤ exp(2 (1 + ε) β*ᵀv) + exp(s ‖v‖)`. -/
theorem exp_dotProduct_le_envelope_oneSided {βs β : Fin p → ℝ} {ε s : ℝ} (hε : 0 < ε)
    (hs : 0 < s)
    (hβ : ‖β - βs‖ ≤ (1 - 1 / (2 * (1 + ε))) * s / (p + 1)) (v : Fin p → ℝ) :
    Real.exp (β ⬝ᵥ v) ≤
      Real.exp (2 * (1 + ε) * (βs ⬝ᵥ v)) + Real.exp (s * ‖v‖) := by
  set l : ℝ := 1 / (2 * (1 + ε)) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l < 1 := by
    rw [hl, div_lt_one (by positivity)]; linarith
  have hm0 : 0 < 1 - l := by linarith
  set a : ℝ := 2 * (1 + ε) * (βs ⬝ᵥ v) with ha
  set b : ℝ := ((β - βs) ⬝ᵥ v) / (1 - l) with hb
  have hsplit : β ⬝ᵥ v = l * a + (1 - l) * b := by
    have e1 : l * a = βs ⬝ᵥ v := by
      rw [hl, ha]; field_simp
    have e2 : (1 - l) * b = (β - βs) ⬝ᵥ v := by
      rw [hb]; field_simp
    rw [e1, e2, sub_dotProduct]; ring
  have hbs : b ≤ s * ‖v‖ := by
    rw [hb, div_le_iff₀ hm0]
    have h1 : (β - βs) ⬝ᵥ v ≤ p * ‖β - βs‖ * ‖v‖ :=
      (le_abs_self _).trans ((abs_dotProduct_le_mul_norm _ _).trans (le_of_eq (by ring)))
    have h2 : (p : ℝ) * ‖β - βs‖ ≤ (1 - l) * s := by
      have hp : (p : ℝ) ≤ p + 1 := by linarith
      have hp0 : (0 : ℝ) < p + 1 := by positivity
      calc (p : ℝ) * ‖β - βs‖ ≤ (p + 1) * ((1 - l) * s / (p + 1)) := by
            gcongr
        _ = (1 - l) * s := by field_simp
    have h3 : (p : ℝ) * ‖β - βs‖ * ‖v‖ ≤ (1 - l) * s * ‖v‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    linarith
  have hc := convexOn_exp.2 (Set.mem_univ a) (Set.mem_univ b) hl0.le hm0.le (by ring)
  simp only [smul_eq_mul] at hc
  rw [hsplit]
  have hea := Real.exp_pos a
  have heb : Real.exp b ≤ Real.exp (s * ‖v‖) := Real.exp_le_exp.2 hbs
  have heb0 := Real.exp_pos b
  nlinarith [mul_le_mul_of_nonneg_right hl1.le hea.le, mul_le_mul_of_nonneg_left heb hm0.le]

end Envelope

/-! ### The population gap and the sample minimizer under an envelope -/

section Population

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {p : ℕ} {ν : Measure 𝒪} {f : 𝒪 → Fin p → ℝ}
  {t : Fin p → ℝ}

/-- **The gap on a sphere under an envelope.** Under the margin condition, let `β*` minimize the
objective and let an integrable `H` dominate the tilts `exp(βᵀ(f - t))` of every `β` with
`‖β - β*‖ ≤ r`, `r > 0`. Then for some `c > 0`, every `b` with `‖b - β*‖ = r` has
`F(β*) + c ≤ F(b)`. -/
theorem exists_gap_on_sphere_of_envelope (hf : Measurable f) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective ν f t) Set.univ βs) {H : 𝒪 → ℝ}
    (hH : Integrable H ν) {r : ℝ} (hr : 0 < r)
    (henv : ∀ β : Fin p → ℝ, ‖β - βs‖ ≤ r → ∀ z, Real.exp (β ⬝ᵥ (f z - t)) ≤ H z) :
    ∃ c, 0 < c ∧ ∀ b : Fin p → ℝ, ‖b - βs‖ = r →
      (∫ z, Real.exp (βs ⬝ᵥ (f z - t)) ∂ν) + c ≤ ∫ z, Real.exp (b ⬝ᵥ (f z - t)) ∂ν := by
  have hint : ∀ β : Fin p → ℝ, ‖β - βs‖ ≤ r →
      Integrable (fun z => Real.exp (β ⬝ᵥ (f z - t))) ν := fun β hβ =>
    hH.mono' (measurable_exp_dotProduct_sub hf t β).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact henv β hβ z)
  have hs := hint βs (by rw [sub_self, norm_zero]; exact hr.le)
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
      (fun β hβ => ae_of_all _ fun z => ?_) hH
      (ae_of_all _ fun z => (Continuous.continuousOn (by fun_prop)))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact henv β ((hmemS β).1 hβ).le z
  obtain ⟨b₀, hb₀S, hb₀⟩ := (isCompact_sphere βs r).exists_isMinOn hS hcont
  have hb₀r := (hmemS b₀).1 hb₀S
  have hne : b₀ ≠ βs := by
    rintro rfl; rw [sub_self, norm_zero] at hb₀r; exact hr.ne hb₀r
  have hlt := integral_exp_lt_of_isMinOn hf hδ hmargin hmin hs (hint b₀ hb₀r.le) hne
  refine ⟨_, sub_pos.2 hlt, fun b hb => ?_⟩
  have := hb₀ ((hmemS b).2 hb)
  simp only [Set.mem_ofPred_eq] at this
  linarith

end Population

section Sample

variable {𝒪 Ω : Type*} [MeasurableSpace 𝒪] [MeasurableSpace Ω] {p : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {f : 𝒪 → Fin p → ℝ} {t : Fin p → ℝ}

/-- **Consistency of the sample dual minimizer under an envelope.** Under the margin condition at
`t` for the law of the records, let `β*` minimize the population dual objective and let an
integrable `H` dominate the tilts `exp(βᵀ(f - t))` of every `β` with `‖β - β*‖ ≤ r₀`, `r₀ > 0`.
For reported targets `tₙ → t` in probability, the entropy balancing weights at `tₙ` are feasible
with probability tending to one and the sample dual minimizer converges in probability to
`β*`. -/
theorem tendstoInMeasure_dualMinimizer_of_envelope (hO : IsIIDSample O P) (hf : Measurable f)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) f t) Set.univ βs)
    {H : 𝒪 → ℝ} (hH : Integrable H (P.map (O 0))) {r₀ : ℝ} (hr₀0 : 0 < r₀)
    (henv : ∀ β : Fin p → ℝ, ‖β - βs‖ ≤ r₀ → ∀ z, Real.exp (β ⬝ᵥ (f z - t)) ≤ H z) :
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
  refine tendstoInMeasure_of_good_events fun ε hε κ' hκ' => ?_
  set r := min (ε / 2) r₀ with hr
  have hr0 : 0 < r := lt_min (by positivity) hr₀0
  have henv' : ∀ β : Fin p → ℝ, ‖β - βs‖ ≤ r → ∀ z, Real.exp (β ⬝ᵥ (f z - t)) ≤ H z :=
    fun β hβ => henv β (hβ.trans (min_le_right _ _))
  obtain ⟨c, hc, hsep⟩ := exists_gap_on_sphere_of_envelope hf hδ hmargin hmin hH hr0 henv'
  set K := Metric.closedBall βs r with hK
  have hKle : ∀ β ∈ K, ‖β - βs‖ ≤ r := fun β hβ => by
    rwa [hK, Metric.mem_closedBall, dist_eq_norm] at hβ
  obtain ⟨-, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall βs r)
    (ψ := fun z β => Real.exp (β ⬝ᵥ (f z - t)))
    (fun β _ => measurable_exp_dotProduct_sub hf t β)
    (ae_of_all _ fun z => Continuous.continuousOn (by fun_prop))
    (H := H) hH
    (ae_of_all _ fun z β hβ => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact henv' β (hKle β hβ) z)
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

/-! ### Dispersion under one sided moments -/

section Dispersion

variable {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪] {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} {p : ℕ}

/-- **The tilts near `β*` are dominated under one sided moments.** If
`E[exp(s ‖f - t‖)] < ∞` for some `s > 0` and `E[exp(2 (1 + ε) β*ᵀ(f - t))] < ∞` for some
`ε > 0`, then the integrable function `exp(2 (1 + ε) β*ᵀ(f - t)) + exp(s ‖f - t‖)` dominates
the tilts of every `β` in a ball of positive radius around `β*`. -/
theorem exists_envelope_oneSided {ν : Measure 𝒪} {f : 𝒪 → Fin p → ℝ} {t βs : Fin p → ℝ}
    {s : ℝ} (hs : 0 < s) (hexp : Integrable (fun z => Real.exp (s * ‖f z - t‖)) ν) {ε : ℝ}
    (hε : 0 < ε)
    (hdir : Integrable (fun z => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (f z - t)))) ν) :
    ∃ H : 𝒪 → ℝ, Integrable H ν ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ β : Fin p → ℝ, ‖β - βs‖ ≤ r₀ → ∀ z, Real.exp (β ⬝ᵥ (f z - t)) ≤ H z := by
  have hl : 0 < 1 - 1 / (2 * (1 + ε)) := by
    rw [sub_pos, div_lt_one (by positivity)]; linarith
  exact ⟨_, hdir.add hexp, _, by positivity, fun β hβ z =>
    exp_dotProduct_le_envelope_oneSided hε hs hβ (f z - t)⟩

/-- **Consistency of the sample dual minimizer under one sided moments.** Under the margin
condition at `t`, a minimizer `β*` of the population dual objective,
`E[exp(s ‖f - t‖)] < ∞` for some `s > 0` and `E[exp(2 (1 + ε) β*ᵀ(f - t))] < ∞` for some
`ε > 0`, the weights at reported targets `tₙ → t` are feasible with probability tending to one
and the sample dual minimizer converges in probability to `β*`. -/
theorem tendstoInMeasure_dualMinimizer_of_isMinOn_oneSided (hO : IsIIDSample O P)
    {f : 𝒪 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) f t) Set.univ βs)
    {s : ℝ} (hs : 0 < s) (hexp : Integrable (fun z => Real.exp (s * ‖f z - t‖)) (P.map (O 0)))
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun z => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (f z - t)))) (P.map (O 0))) :
    WithProbTendingToOne P (balancingFeasibleEvent f O tm) ∧
      TendstoInMeasure P (fun n ω => dualMinimizer fun i : Fin n => f (O i ω) - tm n ω) atTop
        (fun _ => βs) := by
  obtain ⟨H, hH, r₀, hr₀, henv⟩ := exists_envelope_oneSided hs hexp hε hdir
  exact tendstoInMeasure_dualMinimizer_of_envelope hO hf hδ hmargin htm hmin hH hr₀ henv

/-- **The weights disperse under one sided moments.** Under the margin condition at `t`,
reported targets `tₙ → t` in probability, a minimizer `β*` of the population dual objective,
`E[exp(s ‖f - t‖)] < ∞` for some `s > 0` and `E[exp(2 (1 + ε) β*ᵀ(f - t))] < ∞` for some
`ε > 0`, the dispersion `∑ᵢ cₙᵢ² (1 + ‖f(Oᵢ) - t‖²)` of the entropy balancing weights at `tₙ`
tends to zero in probability. -/
theorem balancingDispersionVanishes_of_isMinOn_oneSided (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {f : 𝒪 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (f z - t)})
    {tm : ℕ → Ω → Fin p → ℝ} (htm : TendstoInMeasure P tm atTop (fun _ => t))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) f t) Set.univ βs)
    {s : ℝ} (hs : 0 < s) (hexp : Integrable (fun z => Real.exp (s * ‖f z - t‖)) (P.map (O 0)))
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun z => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (f z - t)))) (P.map (O 0))) :
    BalancingDispersionVanishes P f t O tm := by
  obtain ⟨-, hconv⟩ :=
    tendstoInMeasure_dualMinimizer_of_isMinOn_oneSided hO hf hδ hmargin htm hmin hs hexp hε hdir
  set r : ℝ := ε * s / ((1 + ε) * (2 * p + 1)) with hr
  have hr0 : 0 < r := by positivity
  have hrs : (1 + ε) / ε * ((2 * p + 1) * r) = s := by rw [hr]; field_simp
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
    have e2 : (1 + ε) / ε * ((2 * p + 1) * r * g z) = s * ‖f z - t‖ := by
      rw [← hrs]; simp only [hg]; ring
    rw [e1, e2] at hy
    calc Real.exp (2 * (βs ⬝ᵥ (f z - t)) + 2 * p * r * g z) * (1 + g z ^ 2)
        ≤ Real.exp (2 * (βs ⬝ᵥ (f z - t)) + 2 * p * r * g z) *
            ((1 + 2 / r ^ 2) * Real.exp (r * g z)) := by
          gcongr; exact one_add_sq_le_mul_exp hg0 hr0
      _ = (1 + 2 / r ^ 2) * Real.exp (2 * (βs ⬝ᵥ (f z - t)) + (2 * p + 1) * r * g z) := by
          rw [mul_left_comm, ← Real.exp_add]; ring_nf
      _ ≤ (1 + 2 / r ^ 2) * (Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (f z - t))) +
            Real.exp (s * ‖f z - t‖)) := by gcongr
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

end Dispersion

/-! ### Consistency under one sided moments -/

section Consistency

variable {Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted arm mean under one sided moments.** The hypotheses of
`sampleBalancedArmMean_isConsistent_of_isMinOn_directional`, with the norm moment of order
`κ > p ‖β*‖` replaced by a norm moment `E[exp(s ‖φ(X) - t‖)] < ∞` of some order `s > 0`. With the
directional moment `E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞`, the weighted arm mean at the reported
targets `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_of_isMinOn_oneSided (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    {βs : Fin p → ℝ}
    (hmin : IsMinOn (sharpDualObjective (P.map (O 0)) (fun z => φ z.1) t) Set.univ βs)
    {s : ℝ} (hs : 0 < s) (hexp : Integrable (fun z : 𝒳 × Bool × ℝ => Real.exp (s * ‖φ z.1 - t‖))
      (P.map (O 0))) {ε : ℝ} (hε : 0 < ε)
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
  have hfeas := (tendstoInMeasure_dualMinimizer_of_isMinOn_oneSided hO hf hδ hmargin htm hmin
    hs hexp hε hdir).1
  have hdisp := balancingDispersionVanishes_of_isMinOn_oneSided hO hOm hf hδ hmargin htm hmin
    hs hexp hε hdir
  have hφ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖ ^ 2) (P.map (O 0)) :=
    integrable_sq_of_integrable_exp_pos (g := fun z : 𝒳 × Bool × ℝ => ‖φ z.1 - t‖)
      (hf.sub_const t).norm (fun _ => norm_nonneg _) hs hexp
  exact sampleBalancedArmMean_isConsistent_of_dispersion hO hOm hφ hW hWO hT htm hfeas hdisp
    hφ2 hind a hq hres2 hreg hvar haff

end Consistency

section Trial

variable {Ω₁ Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **The weighted arm mean of a randomized trial under one sided moments.** The hypotheses of
`sampleBalancedArmMean_isConsistent_trial_of_isMinOn`, with the moment of order
`κ > 2 p ‖β*‖` replaced by a norm moment `E[exp(s ‖φ(X) - t‖)] < ∞` of some order `s > 0` and
the directional moment `E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`, both under the
covariate law. Then the weighted arm mean at `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {s : ℝ} (hs : 0 < s) (hexp : Integrable (fun x => Real.exp (s * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
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
  exact sampleBalancedArmMean_isConsistent_of_isMinOn_oneSided hO hOm hφ hδ hmargin hmin'
    hs hexp' hε hdir' hW hWO hG htm hind a hq' hres2' hreg' hvar' haff

end Trial

end PopulationAdjustment

end CausalInference
