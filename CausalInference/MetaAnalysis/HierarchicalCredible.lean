/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HierarchicalPosterior
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Credible sets and the highest posterior density set

A **`(1 - α)` credible set** is a measurable set of posterior probability at least `1 - α`
(`IsCredibleSet`). Let the posterior have the density `π` with respect to a measure `vol`
(Lebesgue measure in the applications). The **highest posterior density set** at level `c` is
`{ξ | c ≤ π(ξ)}` (`hpdSet`).

**Minimal volume** (`volume_le_of_hpd`, Box and Tiao 1973). Let `c > 0` and let `C` be a
measurable set between the strict and the weak level set, `{c < π} ⊆ C ⊆ {c ≤ π}`, of finite
posterior probability. Then every measurable `D` with at least the posterior probability of `C`
has `vol(C) ≤ vol(D)`. No finiteness of the volume is assumed: `vol(C) ≤ P(C) / c < ∞` follows
(`volume_lt_top_of_hpd`). The level `c = ∞` is allowed; `c = 0` is not (then `C` may be the whole
space).

**Ties.** When `π = c` on a set of positive volume, the weak level set `{c ≤ π}` can have more
posterior probability than wanted, and there may be no level whose weak level set has posterior
probability exactly `1 - α`. The sandwich form covers this: every measurable part of the tie can be
added to `{c < π}`, and the minimal volume sets are then not unique. For the uniform posterior on
`[0, 1]` (`uniform_hpd_tie`) the weak level sets have probability `0` or `1` only, while
`[0, 1/2]` and `[1/2, 1]` are both highest density sets of probability `1/2` and volume `1/2`.

**The normal posterior** (`hpdSet_gaussianPDF`, `volume_le_of_gaussianReal_Icc`). For
`N(m, v)`, `v > 0`, the highest density set at the level `φ(m + r)`, `r ≥ 0`, is the symmetric
interval `[m - r, m + r]`; every measurable set of at least its posterior probability, in
particular every interval, has length at least `2r`.

## Main definitions

* `IsCredibleSet`, `hpdSet`.

## Main results

* `volume_lt_top_of_hpd`, `volume_le_of_hpd`, `volume_le_of_isCredibleSet`, `uniform_hpd_tie`,
  `hpdSet_gaussianPDF`, `volume_le_of_gaussianReal_Icc`.

## References

* G. E. P. Box and G. C. Tiao, *Bayesian Inference in Statistical Analysis* (1973).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- A **`(1 - α)` credible set** of the posterior `post`: a measurable set of posterior
probability at least `1 - α`. -/
def IsCredibleSet (post : Measure Ξ) (α : ℝ) (C : Set Ξ) : Prop :=
  MeasurableSet C ∧ ENNReal.ofReal (1 - α) ≤ post C

/-- The **highest posterior density set** `{ξ | c ≤ π(ξ)}` at the level `c`. -/
def hpdSet (dens : Ξ → ℝ≥0∞) (c : ℝ≥0∞) : Set Ξ := {ξ | c ≤ dens ξ}

theorem measurableSet_hpdSet {dens : Ξ → ℝ≥0∞} (hd : Measurable dens) (c : ℝ≥0∞) :
    MeasurableSet (hpdSet dens c) :=
  measurableSet_le measurable_const hd

omit [MeasurableSpace Ξ] in
/-- The strict level set lies in the weak one. -/
theorem setOf_lt_subset_hpdSet (dens : Ξ → ℝ≥0∞) (c : ℝ≥0∞) :
    {ξ | c < dens ξ} ⊆ hpdSet dens c := by
  intro x hx
  simp only [hpdSet, mem_ofPred_eq] at hx ⊢
  exact hx.le

/-- On a set where the density is at least `c`, the volume is at most `1/c` times the posterior
probability. -/
theorem mul_volume_le_of_subset_hpdSet {vol : Measure Ξ} {dens : Ξ → ℝ≥0∞} (hd : Measurable dens)
    {c : ℝ≥0∞} {A : Set Ξ} (hA : MeasurableSet A) (hAc : A ⊆ hpdSet dens c) :
    c * vol A ≤ vol.withDensity dens A := by
  rw [withDensity_apply _ hA, ← setLIntegral_const]
  exact setLIntegral_mono hd fun x hx => hAc hx

/-- **Highest density sets have finite volume**: if `c > 0`, `C ⊆ {c ≤ π}` and `C` has finite
posterior probability, then `vol(C) < ∞`. -/
theorem volume_lt_top_of_hpd {vol : Measure Ξ} {dens : Ξ → ℝ≥0∞} (hd : Measurable dens)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) {C : Set Ξ} (hC : MeasurableSet C) (hCc : C ⊆ hpdSet dens c)
    (hfin : vol.withDensity dens C ≠ ∞) :
    vol C < ∞ := by
  have h := mul_volume_le_of_subset_hpdSet (vol := vol) hd hC hCc
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.mul_top hc0, top_le_iff] at h
  exact hfin h

/-- **The highest posterior density set has minimal volume** (Box and Tiao 1973). Let the
posterior be `vol.withDensity π`, let `c ≠ 0`, and let `C` be measurable with
`{c < π} ⊆ C ⊆ {c ≤ π}` and finite posterior probability. Every measurable `D` with
`P(C) ≤ P(D)` has `vol(C) ≤ vol(D)`. Proof: `P(C \ D) ≤ P(D \ C)`, while `π ≥ c` on `C \ D` and
`π ≤ c` on `D \ C`, so `c vol(C \ D) ≤ c vol(D \ C)`; add `vol(C ∩ D)`. -/
theorem volume_le_of_hpd {vol : Measure Ξ} {dens : Ξ → ℝ≥0∞} (hd : Measurable dens)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) {C : Set Ξ} (hC : MeasurableSet C)
    (hlow : {ξ | c < dens ξ} ⊆ C) (hCc : C ⊆ hpdSet dens c)
    (hfin : vol.withDensity dens C ≠ ∞) {D : Set Ξ} (hD : MeasurableSet D)
    (hCD : vol.withDensity dens C ≤ vol.withDensity dens D) :
    vol C ≤ vol D := by
  set Pp := vol.withDensity dens
  have h1 : c * vol (C \ D) ≤ Pp (C \ D) :=
    mul_volume_le_of_subset_hpdSet hd (hC.diff hD) fun x hx => hCc hx.1
  have h2 : Pp (D \ C) ≤ c * vol (D \ C) := by
    rw [withDensity_apply _ (hD.diff hC), ← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun x hx => ?_
    by_contra h
    exact hx.2 (hlow (not_le.1 h))
  have hfinCD : Pp (C ∩ D) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  have h3 : Pp (C \ D) ≤ Pp (D \ C) := by
    have hle := hCD
    rw [← measure_inter_add_sdiff C hD, ← measure_inter_add_sdiff D hC, inter_comm D C] at hle
    exact (ENNReal.add_le_add_iff_left hfinCD).1 hle
  have h4 : vol (C \ D) ≤ vol (D \ C) := by
    by_cases hctop : c = ∞
    · have hfin' : Pp (C \ D) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)
      have h0 : vol (C \ D) = 0 := by
        by_contra hne
        rw [hctop, ENNReal.top_mul hne, top_le_iff] at h1
        exact hfin' h1
      rw [h0]
      exact zero_le
    · exact (ENNReal.mul_le_mul_iff_right hc0 hctop).1 (h1.trans (h3.trans h2))
  calc vol C = vol (C ∩ D) + vol (C \ D) := (measure_inter_add_sdiff C hD).symm
    _ ≤ vol (C ∩ D) + vol (D \ C) := by gcongr
    _ = vol D := by rw [inter_comm, measure_inter_add_sdiff D hC]

/-- **The highest density credible set is the smallest credible set**: if a highest density set
`C` (as in `volume_le_of_hpd`) has posterior probability exactly `1 - α`, then every
`(1 - α)` credible set has at least its volume. -/
theorem volume_le_of_isCredibleSet {vol : Measure Ξ} {dens : Ξ → ℝ≥0∞} (hd : Measurable dens)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) {C : Set Ξ} (hC : MeasurableSet C)
    (hlow : {ξ | c < dens ξ} ⊆ C) (hCc : C ⊆ hpdSet dens c) {α : ℝ}
    (hCα : vol.withDensity dens C = ENNReal.ofReal (1 - α)) {D : Set Ξ}
    (hD : IsCredibleSet (vol.withDensity dens) α D) :
    vol C ≤ vol D :=
  volume_le_of_hpd hd hc0 hC hlow hCc (by rw [hCα]; exact ENNReal.ofReal_ne_top) hD.1
    (hCα ▸ hD.2)

/-- **Ties: the uniform posterior on `[0, 1]`.** With the density `1` on `[0, 1]` and `0`
elsewhere, every weak level set has posterior probability `0` or `1`, so no level set is a
credible set of probability `1/2`; at the level `1` both `[0, 1/2]` and `[1/2, 1]` satisfy the
sandwich condition of `volume_le_of_hpd`, have posterior probability `1/2` and volume `1/2`: the
minimal volume credible set of probability `1/2` is not unique. -/
theorem uniform_hpd_tie :
    let dens : ℝ → ℝ≥0∞ := (Icc (0 : ℝ) 1).indicator 1
    (∀ c, (volume.withDensity dens) (hpdSet dens c) = 0 ∨
        (volume.withDensity dens) (hpdSet dens c) = 1) ∧
      ({ξ | 1 < dens ξ} ⊆ Icc 0 (1 / 2) ∧ Icc 0 (1 / 2) ⊆ hpdSet dens 1 ∧
        {ξ | 1 < dens ξ} ⊆ Icc (1 / 2) 1 ∧ Icc (1 / 2) 1 ⊆ hpdSet dens 1) ∧
      (volume.withDensity dens) (Icc 0 (1 / 2)) = ENNReal.ofReal (1 / 2) ∧
      (volume.withDensity dens) (Icc (1 / 2) 1) = ENNReal.ofReal (1 / 2) ∧
      volume (Icc (0 : ℝ) (1 / 2)) = ENNReal.ofReal (1 / 2) ∧
      volume (Icc (1 / 2 : ℝ) 1) = ENNReal.ofReal (1 / 2) := by
  intro dens
  have hdens : ∀ x, dens x = if x ∈ Icc (0 : ℝ) 1 then 1 else 0 := fun x => by
    simp only [dens, indicator, Pi.one_apply]
  have hP : ∀ A : Set ℝ, MeasurableSet A →
      (volume.withDensity dens) A = volume (A ∩ Icc 0 1) := fun A hA => by
    rw [withDensity_apply _ hA, show dens = (Icc (0 : ℝ) 1).indicator 1 from rfl,
      lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    simp [inter_comm]
  have hnot : ∀ ξ, ¬ 1 < dens ξ := fun ξ => by
    rw [hdens]; split_ifs <;> simp
  refine ⟨fun c => ?_, ⟨fun ξ h => absurd h (hnot ξ), fun ξ hξ => ?_, fun ξ h => absurd h (hnot ξ),
    fun ξ hξ => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have hm : MeasurableSet (hpdSet dens c) :=
      measurableSet_hpdSet (measurable_one.indicator measurableSet_Icc) c
    rw [hP _ hm]
    by_cases hc : c ≤ 1
    · right
      have : hpdSet dens c ∩ Icc 0 1 = Icc 0 1 := by
        refine inter_eq_right.2 fun x hx => ?_
        change c ≤ dens x
        simp only [hdens, hx, ↓reduceIte]
        exact hc
      rw [this, Real.volume_Icc]
      norm_num
    · left
      have : hpdSet dens c ∩ Icc 0 1 = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun x hx => hc ?_
        have h := hx.1
        change c ≤ dens x at h
        simpa only [hdens, hx.2, ↓reduceIte] using h
      rw [this, measure_empty]
  · change 1 ≤ dens ξ
    have : ξ ∈ Icc (0 : ℝ) 1 := ⟨hξ.1, by linarith [hξ.2]⟩
    simp only [hdens, this, ↓reduceIte, le_refl]
  · change 1 ≤ dens ξ
    have : ξ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hξ.1], hξ.2⟩
    simp only [hdens, this, ↓reduceIte, le_refl]
  · rw [hP _ measurableSet_Icc, inter_eq_left.2 (Icc_subset_Icc le_rfl (by norm_num)),
      Real.volume_Icc]
    norm_num
  · rw [hP _ measurableSet_Icc, inter_eq_left.2 (Icc_subset_Icc (by norm_num) le_rfl),
      Real.volume_Icc]
    norm_num
  · rw [Real.volume_Icc]; norm_num
  · rw [Real.volume_Icc]; norm_num

/-- **The highest density set of a normal posterior is a symmetric interval**: for `v > 0` and
`r ≥ 0`, `{x | φ(m + r; m, v) ≤ φ(x; m, v)} = [m - r, m + r]`. -/
theorem hpdSet_gaussianPDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    hpdSet (gaussianPDF m v) (gaussianPDF m v (m + r)) = Icc (m - r) (m + r) := by
  ext x
  have hvpos : (0 : ℝ) < v := by positivity
  simp only [hpdSet, mem_ofPred_eq, mem_Icc, gaussianPDF]
  rw [ENNReal.ofReal_le_ofReal_iff (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal,
    gaussianPDFReal, mul_le_mul_iff_right₀ (by positivity), Real.exp_le_exp,
    div_le_div_iff_of_pos_right (by positivity), neg_le_neg_iff, add_sub_cancel_left]
  constructor
  · intro h
    have := abs_le_of_sq_le_sq' h hr
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2⟩
    nlinarith

/-- **The symmetric interval is the shortest credible set of a normal posterior**: for
`N(m, v)`, `v > 0`, and `r ≥ 0`, every measurable set `D` with at least the posterior probability
of `[m - r, m + r]` has Lebesgue measure at least `2r`; in particular every interval of at least
that probability has length at least `2r`. -/
theorem volume_le_of_gaussianReal_Icc (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    {D : Set ℝ} (hD : MeasurableSet D)
    (hDP : gaussianReal m v (Icc (m - r) (m + r)) ≤ gaussianReal m v D) :
    ENNReal.ofReal (2 * r) ≤ volume D := by
  have hd : Measurable (gaussianPDF m v) := measurable_gaussianPDF m v
  have hset := hpdSet_gaussianPDF m hv hr
  have hc0 : gaussianPDF m v (m + r) ≠ 0 := by
    rw [gaussianPDF, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact gaussianPDFReal_pos _ _ _ hv
  have h := volume_le_of_hpd (vol := volume) hd hc0 (C := hpdSet (gaussianPDF m v)
    (gaussianPDF m v (m + r))) (measurableSet_hpdSet hd _) (setOf_lt_subset_hpdSet _ _) le_rfl
    (by rw [← gaussianReal_of_var_ne_zero m hv]; exact measure_ne_top _ _) hD
    (by rw [← gaussianReal_of_var_ne_zero m hv, hset]; exact hDP)
  rw [hset, Real.volume_Icc] at h
  convert h using 2
  ring

end MetaAnalysis

end CausalInference
