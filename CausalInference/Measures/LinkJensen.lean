/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.EffectModifier
public import Mathlib.Analysis.Convex.Deriv

/-!
# The sign of the averaging gap on a convex or concave link

Jensen's inequality on an arbitrary interval of the real line, with no closedness or
continuity hypothesis, and its strict form; Mathlib's `ConvexOn.map_integral_le` asks for a
closed domain and continuity, which excludes the log link on `(0, ∞)` and the logit link on
`(0, 1)`. Applied to the averaging gap `J_g(m) = g (∫ m) - ∫ g ∘ m` of `Measures/LinkScale.lean`:
a strictly convex link has a negative gap and a strictly concave link a positive gap, for every
mean function that is not almost surely constant (that is, for a prognostic covariate).

## Main results

* `convexOn_map_integral_le_of_ordConnected`: `φ (∫ f) ≤ ∫ φ ∘ f` for `φ` convex on an
  interval containing almost every value of `f`.
* `strictConvexOn_map_integral_eq_iff`: equality holds for a strictly convex `φ` if and only if
  `f` is almost surely constant.
* `averagingGap_neg_of_strictConvexOn`, `averagingGap_pos_of_strictConcaveOn`: the sign of the
  averaging gap.
* `averagingGap_log_pos`: on the log scale the gap of a prognostic positive mean is positive.
* `plugIn_sub_integral_eq_averagingGap`, `plugIn_lt_integral_of_strictConvexOn`,
  `integral_lt_plugIn_of_strictConcaveOn`: plugging the mean covariate into a linear predictor
  and a strictly convex (concave) inverse link gives a mean below (above) the averaged mean.

## References

* J. L. W. V. Jensen, *Sur les fonctions convexes et les inégalités entre les valeurs
  moyennes*, Acta Mathematica 30 (1906), 175 to 193.
* S. Dias, A. J. Sutton, N. J. Welton, A. E. Ades, *NICE DSU Technical Support Document 3:
  Heterogeneity: Subgroups, Meta-Regression, Bias and Bias-Adjustment* (2011, updated 2012),
  Section 1.1.5.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

/-! ### Support lines -/

/-- A convex function on a set of reals has a support line at every interior point. -/
theorem convexOn_exists_support_line {I : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ I φ) {m : ℝ}
    (hm : m ∈ interior I) : ∃ s : ℝ, ∀ y ∈ I, φ m + s * (y - m) ≤ φ y := by
  refine ⟨derivWithin φ (Set.Ioi m) m, fun y hy => ?_⟩
  rcases lt_trichotomy y m with hlt | rfl | hgt
  · have h1 := hφ.slope_le_leftDeriv_of_mem_interior hy hm hlt
    have h2 := hφ.leftDeriv_le_rightDeriv_of_mem_interior hm
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
    nlinarith
  · simp
  · have h1 := hφ.rightDeriv_le_slope_of_mem_interior hm hy hgt
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    linarith

/-- A strictly convex function on a set of reals has a strict support line at every interior
point. -/
theorem strictConvexOn_exists_strict_support_line {I : Set ℝ} {φ : ℝ → ℝ}
    (hφ : StrictConvexOn ℝ I φ) {m : ℝ} (hm : m ∈ interior I) :
    ∃ s : ℝ, ∀ y ∈ I, y ≠ m → φ m + s * (y - m) < φ y := by
  have hc := hφ.convexOn
  have hmI : m ∈ I := interior_subset hm
  have hoc := hc.1.ordConnected
  refine ⟨derivWithin φ (Set.Ioi m) m, fun y hy hne => ?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · set z := (y + m) / 2 with hz_def
    have hz : z ∈ I := hoc.out hy hmI ⟨by linarith [hz_def], by linarith [hz_def]⟩
    have h0 := hφ.slope_strict_mono_adjacent hy hmI (by linarith [hz_def])
      (by linarith [hz_def])
    have h1 := hc.slope_le_leftDeriv_of_mem_interior hz hm (by linarith [hz_def])
    have h2 := hc.leftDeriv_le_rightDeriv_of_mem_interior hm
    rw [slope_def_field] at h1
    have e1 : z - y = (m - y) / 2 := by rw [hz_def]; ring
    have e2 : m - z = (m - y) / 2 := by rw [hz_def]; ring
    rw [e1, e2] at h0
    rw [e2] at h1
    have hpos : 0 < (m - y) / 2 := by linarith
    rw [div_lt_div_iff_of_pos_right hpos] at h0
    rw [div_le_iff₀ hpos] at h1
    nlinarith
  · set z := (m + y) / 2 with hz_def
    have hz : z ∈ I := hoc.out hmI hy ⟨by linarith [hz_def], by linarith [hz_def]⟩
    have h0 := hφ.slope_strict_mono_adjacent hmI hy (by linarith [hz_def])
      (by linarith [hz_def])
    have h1 := hc.rightDeriv_le_slope_of_mem_interior hm hz (by linarith [hz_def])
    rw [slope_def_field] at h1
    have e1 : z - m = (y - m) / 2 := by rw [hz_def]; ring
    have e2 : y - z = (y - m) / 2 := by rw [hz_def]; ring
    rw [e1, e2] at h0
    rw [e1] at h1
    have hpos : 0 < (y - m) / 2 := by linarith
    rw [div_lt_div_iff_of_pos_right hpos] at h0
    rw [le_div_iff₀ hpos] at h1
    nlinarith

/-! ### Jensen's inequality on an interval -/

section Jensen

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An integrable function that is almost surely at least its mean is almost surely equal to
its mean. -/
theorem ae_eq_integral_of_ae_integral_le {f : Ω → ℝ} (hf : Integrable f μ)
    (h : ∀ᵐ ω ∂μ, ∫ x, f x ∂μ ≤ f ω) : f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  have hi : Integrable (fun ω => f ω - ∫ x, f x ∂μ) μ := hf.sub (integrable_const _)
  have h0 : ∫ ω, (f ω - ∫ x, f x ∂μ) ∂μ = 0 := by
    rw [integral_sub hf (integrable_const _)]
    simp
  have := (integral_eq_zero_iff_of_nonneg_ae (h.mono fun ω hω => by simpa using hω) hi).1 h0
  filter_upwards [this] with ω hω
  simpa [sub_eq_zero] using hω

/-- The mean of an integrable function with values almost surely in an interval `I` is an
interior point of `I`, or the function is almost surely equal to its mean. -/
theorem integral_mem_interior_or_ae_eq {I : Set ℝ} (hI : I.OrdConnected) {f : Ω → ℝ}
    (hf : Integrable f μ) (hfI : ∀ᵐ ω ∂μ, f ω ∈ I) :
    ∫ x, f x ∂μ ∈ interior I ∨ f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  set m := ∫ x, f x ∂μ
  by_cases ha : ∃ a ∈ I, a < m
  · by_cases hb : ∃ b ∈ I, m < b
    · obtain ⟨a, haI, ham⟩ := ha
      obtain ⟨b, hbI, hmb⟩ := hb
      left
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (Ioo_mem_nhds ham hmb)
        fun y hy => hI.out haI hbI ⟨hy.1.le, hy.2.le⟩
    · right
      simp only [not_exists, not_and, not_lt] at hb
      have := ae_eq_integral_of_ae_integral_le (f := fun ω => -f ω) hf.neg (by
        filter_upwards [hfI] with ω hω
        rw [integral_neg]
        exact neg_le_neg (hb _ hω))
      filter_upwards [this] with ω hω
      rw [integral_neg] at hω
      linarith
  · right
    simp only [not_exists, not_and, not_lt] at ha
    exact ae_eq_integral_of_ae_integral_le hf (hfI.mono fun ω hω => ha _ hω)

/-- **Jensen's inequality on an interval**: for `φ` convex on an interval `I` containing almost
every value of an integrable `f` with `φ ∘ f` integrable, `φ (∫ f) ≤ ∫ φ ∘ f`. -/
theorem convexOn_map_integral_le_of_ordConnected {I : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ I φ)
    {f : Ω → ℝ} (hf : Integrable f μ) (hfI : ∀ᵐ ω ∂μ, f ω ∈ I)
    (hφf : Integrable (fun ω => φ (f ω)) μ) : φ (∫ x, f x ∂μ) ≤ ∫ x, φ (f x) ∂μ := by
  rcases integral_mem_interior_or_ae_eq hφ.1.ordConnected hf hfI with hm | hconst
  · obtain ⟨s, hs⟩ := convexOn_exists_support_line hφ hm
    have i1 : Integrable (fun ω => s * (f ω - ∫ x, f x ∂μ)) μ :=
      (hf.sub (integrable_const _)).const_mul s
    have hlin : Integrable (fun ω => φ (∫ x, f x ∂μ) + s * (f ω - ∫ x, f x ∂μ)) μ :=
      (integrable_const _).add i1
    have := integral_mono_ae hlin hφf (hfI.mono fun ω hω => hs _ hω)
    rw [integral_add (integrable_const _) i1, integral_const_mul,
      integral_sub hf (integrable_const _)] at this
    simpa using this
  · have hc : (fun x => φ (f x)) =ᵐ[μ] fun _ => φ (∫ x, f x ∂μ) := hconst.fun_comp φ
    rw [integral_congr_ae hc]
    simp

/-- **Strict Jensen on an interval**: for `φ` strictly convex on an interval, equality in
Jensen's inequality holds if and only if `f` is almost surely constant. -/
theorem strictConvexOn_map_integral_eq_iff {I : Set ℝ} {φ : ℝ → ℝ} (hφ : StrictConvexOn ℝ I φ)
    {f : Ω → ℝ} (hf : Integrable f μ) (hfI : ∀ᵐ ω ∂μ, f ω ∈ I)
    (hφf : Integrable (fun ω => φ (f ω)) μ) :
    φ (∫ x, f x ∂μ) = ∫ x, φ (f x) ∂μ ↔ ∃ c, ∀ᵐ ω ∂μ, f ω = c := by
  constructor
  · intro heq
    rcases integral_mem_interior_or_ae_eq hφ.convexOn.1.ordConnected hf hfI with hm | hconst
    · obtain ⟨s, hs⟩ := strictConvexOn_exists_strict_support_line hφ hm
      set m := ∫ x, f x ∂μ
      set G : Ω → ℝ := fun ω => φ (f ω) - (φ m + s * (f ω - m))
      have i1 : Integrable (fun ω => s * (f ω - m)) μ := (hf.sub (integrable_const _)).const_mul s
      have hlin : Integrable (fun ω => φ m + s * (f ω - m)) μ := (integrable_const _).add i1
      have hG : Integrable G μ := hφf.sub hlin
      have hG0 : ∀ᵐ ω ∂μ, 0 ≤ G ω := by
        filter_upwards [hfI] with ω hω
        simp only [G, sub_nonneg]
        rcases eq_or_ne (f ω) m with h | h
        · rw [h]; simp
        · exact (hs _ hω h).le
      have hGint : ∫ ω, G ω ∂μ = 0 := by
        simp only [G]
        rw [integral_sub hφf hlin, integral_add (integrable_const _) i1, integral_const_mul,
          integral_sub hf (integrable_const _)]
        simp [← heq, m]
      have hGz := (integral_eq_zero_iff_of_nonneg_ae hG0 hG).1 hGint
      refine ⟨m, ?_⟩
      filter_upwards [hGz, hfI] with ω hω hωI
      by_contra hne
      have := hs _ hωI hne
      simp only [G, Pi.zero_apply] at hω
      linarith
    · exact ⟨_, hconst⟩
  · rintro ⟨c, hc⟩
    have hm : ∫ x, f x ∂μ = c := by rw [integral_congr_ae hc]; simp
    have hc' : (fun x => φ (f x)) =ᵐ[μ] fun _ => φ c := hc.mono fun ω h => by simp [h]
    rw [integral_congr_ae hc', hm]
    simp

end Jensen

/-! ### The sign of the averaging gap -/

namespace EffectMeasure

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- **A strictly convex link has a negative averaging gap**: if `g` is strictly convex on an
interval containing almost every value of `m`, `m` and `g ∘ m` are integrable, and the covariate
is prognostic for `m`, then `J_g(m) = g (∫ m) - ∫ g ∘ m < 0`. -/
theorem averagingGap_neg_of_strictConvexOn {g : ℝ → ℝ} {I : Set ℝ} (hg : StrictConvexOn ℝ I g)
    {m : X → ℝ} (hm : Integrable m ν) (hmI : ∀ᵐ x ∂ν, m x ∈ I)
    (hgm : Integrable (fun x => g (m x)) ν) (hnd : IsPrognostic ν m) : averagingGap g ν m < 0 := by
  have hle := convexOn_map_integral_le_of_ordConnected hg.convexOn hm hmI hgm
  have hne : g (∫ x, m x ∂ν) ≠ ∫ x, g (m x) ∂ν := fun h =>
    hnd ((strictConvexOn_map_integral_eq_iff hg hm hmI hgm).1 h)
  simp only [averagingGap]
  linarith [lt_of_le_of_ne hle hne]

/-- **A strictly concave link has a positive averaging gap**, under the hypotheses of
`averagingGap_neg_of_strictConvexOn` with `g` strictly concave. -/
theorem averagingGap_pos_of_strictConcaveOn {g : ℝ → ℝ} {I : Set ℝ}
    (hg : StrictConcaveOn ℝ I g) {m : X → ℝ} (hm : Integrable m ν) (hmI : ∀ᵐ x ∂ν, m x ∈ I)
    (hgm : Integrable (fun x => g (m x)) ν) (hnd : IsPrognostic ν m) :
    0 < averagingGap g ν m := by
  have h := averagingGap_neg_of_strictConvexOn hg.neg hm hmI hgm.neg hnd
  simp only [averagingGap, Pi.neg_apply, integral_neg] at h ⊢
  linarith

/-- **On the log scale the averaging gap of a prognostic mean is positive**: for an almost surely
positive integrable mean `m` with `log ∘ m` integrable that is not almost surely constant,
`log (∫ m) > ∫ log ∘ m`. -/
theorem averagingGap_log_pos {m : X → ℝ} (hm : Integrable m ν) (hpos : ∀ᵐ x ∂ν, 0 < m x)
    (hlm : Integrable (fun x => Real.log (m x)) ν) (hnd : IsPrognostic ν m) :
    0 < averagingGap Real.log ν m :=
  averagingGap_pos_of_strictConcaveOn strictConcaveOn_log_Ioi hm hpos hlm hnd

/-! ### Plugging the mean covariate into a linear predictor -/

section LinearPredictor

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℕ}

/-- **The plug in mean minus the averaged mean is an averaging gap.** For a linear predictor
`η(x) = a + xᵀb` and covariates `X` with integrable components, the mean `h (η (E X))` obtained
by plugging the mean covariate into the inverse link `h`, minus the averaged mean
`E h (η (X))`, is the averaging gap of `η ∘ X` on the scale `h`. -/
theorem plugIn_sub_integral_eq_averagingGap {X : Ω → Fin p → ℝ}
    (hX : ∀ j, Integrable (fun ω => X ω j) μ) (a : ℝ) (b : Fin p → ℝ) (h : ℝ → ℝ) :
    h (a + ∑ j, (∫ ω, X ω j ∂μ) * b j) - ∫ ω, h (a + ∑ j, X ω j * b j) ∂μ =
      averagingGap h μ (fun ω => a + ∑ j, X ω j * b j) := by
  have hs : ∫ ω, (a + ∑ j, X ω j * b j) ∂μ = a + ∑ j, (∫ ω, X ω j ∂μ) * b j := by
    rw [integral_add (integrable_const a)
      (integrable_finsetSum _ fun j _ => (hX j).mul_const (b j)),
      integral_finsetSum _ fun j _ => (hX j).mul_const (b j)]
    simp [integral_mul_const]
  rw [averagingGap, hs]

/-- The linear predictor of covariates with integrable components is integrable. -/
theorem integrable_linearPredictor {X : Ω → Fin p → ℝ}
    (hX : ∀ j, Integrable (fun ω => X ω j) μ) (a : ℝ) (b : Fin p → ℝ) :
    Integrable (fun ω => a + ∑ j, X ω j * b j) μ :=
  (integrable_const a).add (integrable_finsetSum _ fun j _ => (hX j).mul_const (b j))

/-- **Plugging in the mean covariate underestimates the mean for a strictly convex inverse link**,
and overestimates it for a strictly concave one, unless the linear predictor is almost surely
constant. The values of the predictor lie almost surely in an interval `I` on which the inverse
link `h` is strictly convex (respectively strictly concave). -/
theorem plugIn_lt_integral_of_strictConvexOn {X : Ω → Fin p → ℝ}
    (hX : ∀ j, Integrable (fun ω => X ω j) μ) (a : ℝ) (b : Fin p → ℝ) {h : ℝ → ℝ} {I : Set ℝ}
    (hh : StrictConvexOn ℝ I h) (hI : ∀ᵐ ω ∂μ, a + ∑ j, X ω j * b j ∈ I)
    (hhi : Integrable (fun ω => h (a + ∑ j, X ω j * b j)) μ)
    (hnd : IsPrognostic μ fun ω => a + ∑ j, X ω j * b j) :
    h (a + ∑ j, (∫ ω, X ω j ∂μ) * b j) < ∫ ω, h (a + ∑ j, X ω j * b j) ∂μ := by
  have := averagingGap_neg_of_strictConvexOn hh (integrable_linearPredictor hX a b) hI hhi hnd
  rw [← plugIn_sub_integral_eq_averagingGap hX] at this
  linarith

theorem integral_lt_plugIn_of_strictConcaveOn {X : Ω → Fin p → ℝ}
    (hX : ∀ j, Integrable (fun ω => X ω j) μ) (a : ℝ) (b : Fin p → ℝ) {h : ℝ → ℝ} {I : Set ℝ}
    (hh : StrictConcaveOn ℝ I h) (hI : ∀ᵐ ω ∂μ, a + ∑ j, X ω j * b j ∈ I)
    (hhi : Integrable (fun ω => h (a + ∑ j, X ω j * b j)) μ)
    (hnd : IsPrognostic μ fun ω => a + ∑ j, X ω j * b j) :
    ∫ ω, h (a + ∑ j, X ω j * b j) ∂μ < h (a + ∑ j, (∫ ω, X ω j ∂μ) * b j) := by
  have := averagingGap_pos_of_strictConcaveOn hh (integrable_linearPredictor hX a b) hI hhi hnd
  rw [← plugIn_sub_integral_eq_averagingGap hX] at this
  linarith

end LinearPredictor

end EffectMeasure

end CausalInference
