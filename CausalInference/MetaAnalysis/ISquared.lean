/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CochranQ

/-!
# Meta-analysis: the `H²` and `I²` statistics

For Cochran's `Q` from `k` studies, `H² = Q / (k - 1)` (`hSquared`) and
`I² = max(0, (Q - (k - 1)) / Q)` (`iSquared`), the share of the variability of the estimates
that is not explained by sampling error (Higgins and Thompson 2002). At `Q = 0` the quotient is
undefined; `iSquared` takes the value `0` there by an explicit convention (`iSquared_zero`), and
every other statement assumes `Q > 0` or `Q ≥ 0` explicitly.

* **Identities and range.** For `Q > 0` and `k ≥ 2`, `I² = max(0, 1 - 1 / H²)`
  (`iSquared_eq_max_one_sub_inv`); for `Q ≥ 0`, `0 ≤ I² < 1` (`iSquared_mem_Ico`); `I² = 0`
  exactly when `Q ≤ k - 1` (`iSquared_eq_zero_iff`); `I²` is monotone in `Q`
  (`iSquared_mono`).
* **Interpretation.** If the estimates have variances `vᵢ + τ²` and the weights use `vᵢ`, then
  `E[Q] = (k - 1) + τ² c` (`integral_cochranQ_of_variance_add`), and `I²` evaluated at `E[Q]` is
  `τ² / (τ² + s²)` with the typical within-study variance `s² = (k - 1) / c`
  (`typicalVariance`, `iSquared_integral_cochranQ`). As a function of `τ² ≥ 0` this share is `0`
  at `0`, strictly increasing and tends to `1` (`strictMonoOn_heterogeneityShare`,
  `tendsto_heterogeneityShare`).

## Main definitions

* `hSquared`, `iSquared`, `typicalVariance`, `heterogeneityShare`.

## Main results

* `iSquared_zero`, `iSquared_of_pos`, `iSquared_eq_max_one_sub_inv`, `iSquared_mem_Ico`,
  `iSquared_eq_zero_iff`, `iSquared_pos_iff`, `iSquared_mono`.
* `iSquared_integral_cochranQ`, `heterogeneityShare_zero`, `strictMonoOn_heterogeneityShare`,
  `tendsto_heterogeneityShare`.

## References

* J. P. T. Higgins and S. G. Thompson, *Quantifying heterogeneity in a meta-analysis*,
  Statistics in Medicine 21 (2002).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-! ### Definitions, identities and range -/

section Statistic

/-- The **`H²` statistic** `Q / (k - 1)` of Cochran's `Q` from `k` studies. The results assume
`k ≥ 2`. -/
noncomputable def hSquared (Q : ℝ) (k : ℕ) : ℝ := Q / ((k : ℝ) - 1)

/-- The **`I²` statistic** `max(0, (Q - (k - 1)) / Q)` of Cochran's `Q` from `k` studies
(Higgins and Thompson 2002), with the convention `I² = 0` when `Q = 0` (all estimates equal). -/
noncomputable def iSquared (Q : ℝ) (k : ℕ) : ℝ :=
  if Q = 0 then 0 else max 0 ((Q - ((k : ℝ) - 1)) / Q)

variable {Q Q' : ℝ} {k : ℕ}

/-- **The convention at `Q = 0`**: `I² = 0`. -/
theorem iSquared_zero (k : ℕ) : iSquared 0 k = 0 := by simp [iSquared]

/-- For `Q > 0`, `I²` is the formula `max(0, (Q - (k - 1)) / Q)`. -/
theorem iSquared_of_pos (hQ : 0 < Q) : iSquared Q k = max 0 ((Q - ((k : ℝ) - 1)) / Q) := by
  simp [iSquared, hQ.ne']

/-- **`I² = max(0, 1 - 1 / H²)`** for `Q > 0` and `k ≥ 2`. -/
theorem iSquared_eq_max_one_sub_inv (hQ : 0 < Q) (hk : 2 ≤ k) :
    iSquared Q k = max 0 (1 - 1 / hSquared Q k) := by
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [iSquared_of_pos hQ, hSquared]
  congr 1
  field_simp

/-- **The range of `I²`**: `0 ≤ I² < 1` for `Q ≥ 0` and `k ≥ 2`. -/
theorem iSquared_mem_Ico (hQ : 0 ≤ Q) (hk : 2 ≤ k) : iSquared Q k ∈ Set.Ico 0 1 := by
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rcases hQ.eq_or_lt with h | h
  · subst h
    rw [iSquared_zero]
    exact ⟨le_rfl, one_pos⟩
  · rw [iSquared_of_pos h]
    refine ⟨le_max_left _ _, max_lt one_pos ?_⟩
    rw [div_lt_one h]
    linarith

/-- **`I² = 0` exactly when `Q ≤ k - 1`**, for `Q ≥ 0` and `k ≥ 1`. -/
theorem iSquared_eq_zero_iff (hQ : 0 ≤ Q) (hk : 1 ≤ k) :
    iSquared Q k = 0 ↔ Q ≤ (k : ℝ) - 1 := by
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rcases hQ.eq_or_lt with h | h
  · subst h
    simp only [iSquared_zero, true_iff]
    exact hk1
  · rw [iSquared_of_pos h, max_eq_left_iff, div_nonpos_iff]
    constructor
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · linarith
      · linarith
    · intro h'
      exact Or.inr ⟨by linarith, h.le⟩

/-- **`I² > 0` exactly when `Q > k - 1`**, for `Q ≥ 0` and `k ≥ 1`. -/
theorem iSquared_pos_iff (hQ : 0 ≤ Q) (hk : 1 ≤ k) : 0 < iSquared Q k ↔ (k : ℝ) - 1 < Q := by
  have hnn : 0 ≤ iSquared Q k := by
    unfold iSquared
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  rw [hnn.lt_iff_ne', ne_eq, iSquared_eq_zero_iff hQ hk, not_le]

/-- **`I²` is monotone in `Q`** for `0 < Q ≤ Q'`. -/
theorem iSquared_mono (hQ : 0 < Q) (hQQ' : Q ≤ Q') (hk : 1 ≤ k) :
    iSquared Q k ≤ iSquared Q' k := by
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hQ' : 0 < Q' := hQ.trans_le hQQ'
  rw [iSquared_of_pos hQ, iSquared_of_pos hQ']
  refine max_le_max le_rfl ?_
  have e : ∀ q : ℝ, 0 < q → (q - ((k : ℝ) - 1)) / q = 1 - ((k : ℝ) - 1) / q := fun q hq => by
    field_simp
  rw [e Q hQ, e Q' hQ']
  exact sub_le_sub_left (div_le_div_of_nonneg_left hk1 hQ hQQ') 1

end Statistic

/-! ### Interpretation: the share of between study variance -/

section Interpretation

/-- The **typical within-study variance** `s² = (k - 1) / c` with
`c = ∑ wᵢ - ∑ wᵢ² / ∑ wᵢ` (Higgins and Thompson 2002). -/
noncomputable def typicalVariance {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) - 1) / cochranQSlope v

/-- The **share of between study variance** `τ² / (τ² + s²)`. -/
noncomputable def heterogeneityShare (s τ2 : ℝ) : ℝ := τ2 / (τ2 + s)

/-- With two or more studies the typical within-study variance is positive. -/
theorem typicalVariance_pos {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hk : 2 ≤ Fintype.card ι) : 0 < typicalVariance v := by
  have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
  exact div_pos (by linarith) (cochranQSlope_pos hv (by omega))

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ι → Ω → ℝ}
  {v : ι → ℝ} {θ : ℝ}

/-- **`I²` measures the share of between study variance** (Higgins and Thompson 2002). Let the
estimates be square integrable and pairwise uncorrelated with common mean `θ` and variances
`vᵢ + τ²`, `τ² ≥ 0`, the weights using the within-study variances `vᵢ > 0`, and `k ≥ 2`. Then
`I²` evaluated at `E[Q]` is `τ² / (τ² + s²)`, `s²` the typical within-study variance. -/
theorem iSquared_integral_cochranQ [IsFiniteMeasure P] (hv : ∀ i, 0 < v i)
    (hk : 2 ≤ Fintype.card ι) (hY : ∀ i, MemLp (Y i) 2 P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ)
    {τ2 : ℝ} (hτ : 0 ≤ τ2) (hvar : ∀ i, Var[Y i; P] = v i + τ2)
    (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    iSquared (∫ ω, cochranQ v (fun i => Y i ω) ∂P) (Fintype.card ι) =
      heterogeneityShare (typicalVariance v) τ2 := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hc := cochranQSlope_pos hv (by omega)
  have hk1 : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    linarith
  rw [integral_cochranQ_of_variance_add hv hY hmean hvar hunc]
  have hE : 0 < (Fintype.card ι : ℝ) - 1 + τ2 * cochranQSlope v := by positivity
  rw [iSquared_of_pos hE, add_sub_cancel_left, max_eq_right (by positivity),
    heterogeneityShare, typicalVariance]
  field_simp
  ring

/-- The share of between study variance is `0` at `τ² = 0`. -/
theorem heterogeneityShare_zero (s : ℝ) : heterogeneityShare s 0 = 0 := by
  simp [heterogeneityShare]

/-- For `s > 0` the share of between study variance is strictly increasing on `τ² ≥ 0`. -/
theorem strictMonoOn_heterogeneityShare {s : ℝ} (hs : 0 < s) :
    StrictMonoOn (heterogeneityShare s) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  rw [heterogeneityShare, heterogeneityShare, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- For `s > 0` the share of between study variance tends to `1` as `τ² → ∞`. -/
theorem tendsto_heterogeneityShare {s : ℝ} (hs : 0 < s) :
    Tendsto (heterogeneityShare s) atTop (𝓝 1) := by
  have h : heterogeneityShare s =ᶠ[atTop] fun t => 1 - s / (t + s) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [heterogeneityShare]
    field_simp
    ring
  rw [tendsto_congr' h]
  have : Tendsto (fun t : ℝ => s / (t + s)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ s tendsto_id)
  simpa using tendsto_const_nhds.sub this

end Interpretation

end MetaAnalysis

end CausalInference
