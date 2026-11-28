/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.ExternalAdjustment
public import Mathlib.Order.Bounds.Basic

/-!
# The E-value as a least confounding strength

For an observed risk ratio `RR`, an unmeasured confounder with risk ratio parameters `a`
(confounder to exposure) and `b` (confounder to outcome) can explain the estimate away when
`RR ≤ boundingFactor a b = a b / (a + b - 1)` (Ding and VanderWeele 2016). The library has the
E-value `eValue RR = RR + √(RR (RR - 1))` (extended to `RR < 1` by inversion), the inequality
`eValue_le_max` and the attainment `boundingFactor_eValue`. This file proves that the E-value is
the least strength that explains the estimate away, in the two senses used by VanderWeele and
Ding (2017), and adds the facts used when it is reported.

## Main results

* `le_boundingFactor_self_iff`, `isLeast_eValue`: on the diagonal `a = b = v`, the estimate is
  explained away exactly when `v ≥ eValue RR`, so the E-value is the least common strength.
* `isLeast_eValue_max`: the E-value is the least value of `max a b` over all pairs that explain
  the estimate away.
* `eValue_lt_max_of_ne`: a pair with `a ≠ b` that explains the estimate away has
  `max a b > eValue RR`; so the diagonal pair `(E, E)` is the only pair attaining the least
  maximum (`eq_eValue_of_max_eq`).
* `one_le_eValue`, `eValue_eq_one_iff`, `strictMonoOn_eValue`, `strictAntiOn_eValue`: range and
  monotonicity in `RR`.
* `isLeast_eValue_of_le_one`, `boundingFactor_eValue_inv`: the protective case by inversion.
* `eValueLimit`, `one_lt_div_of_max_lt_eValueLimit`, `div_eq_one_of_eValueLimit`,
  `eValueLimit_le_eValue`: the E-value of a confidence limit: the limit closest to the null is
  moved to the null only by a confounder whose larger parameter reaches the E-value of that
  limit, which is at most the E-value of the estimate.

## References

* P. Ding and T. J. VanderWeele, *Sensitivity analysis without assumptions*, Epidemiology 27
  (2016).
* T. J. VanderWeele and P. Ding, *Sensitivity analysis in observational research: introducing the
  E-value*, Annals of Internal Medicine 167 (2017).
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace IndirectComparisonBias

open Set BiasFormulas ExternalAdjustment

/-! ### The bounding factor -/

/-- The bounding factor is strictly increasing in its first argument on `[1, ∞)` when the second
argument exceeds one: cross multiplied, the gap is `b (b - 1) (a' - a)`. -/
theorem boundingFactor_lt_boundingFactor_left {a a' b : ℝ} (ha : 1 ≤ a) (h : a < a')
    (hb : 1 < b) : boundingFactor a b < boundingFactor a' b := by
  unfold boundingFactor
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < b) (by linarith : (0 : ℝ) < b - 1))
    (by linarith : (0 : ℝ) < a' - a)]

/-- The bounding factor is nonnegative on `[1, ∞) × [1, ∞)`. -/
theorem boundingFactor_nonneg {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 0 ≤ boundingFactor a b :=
  zero_le_one.trans (one_le_boundingFactor ha hb)

/-! ### The E-value on the diagonal and over all pairs -/

/-- The E-value of a positive risk ratio is at least one. -/
theorem one_le_eValue {RR : ℝ} (h0 : 0 < RR) : 1 ≤ eValue RR := by
  have hq : 1 ≤ max RR RR⁻¹ := by
    rcases le_total 1 RR with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_le_inv₀ h0).2 h)
  have := Real.sqrt_nonneg (max RR RR⁻¹ * (max RR RR⁻¹ - 1))
  unfold eValue
  linarith

/-- The E-value of a positive risk ratio is one exactly at the null `RR = 1`. -/
theorem eValue_eq_one_iff {RR : ℝ} (h0 : 0 < RR) : eValue RR = 1 ↔ RR = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, eValue_of_one_le le_rfl]; simp⟩
  have hs := Real.sqrt_nonneg (max RR RR⁻¹ * (max RR RR⁻¹ - 1))
  have hq : max RR RR⁻¹ ≤ 1 := by unfold eValue at h; linarith
  have h1 : RR ≤ 1 := (le_max_left _ _).trans hq
  have h2 : RR⁻¹ ≤ 1 := (le_max_right _ _).trans hq
  have h3 : 1 ≤ RR := by
    by_contra hlt
    exact absurd h2 (not_le.2 ((one_lt_inv₀ h0).2 (not_le.1 hlt)))
  linarith

/-- **The diagonal criterion.** For an observed `RR > 1` and a common strength `v ≥ 1` of the two
confounding parameters, the confounder explains the estimate away (`RR ≤ boundingFactor v v`)
exactly when `v ≥ eValue RR`. -/
theorem le_boundingFactor_self_iff {RR v : ℝ} (hRR : 1 < RR) (hv : 1 ≤ v) :
    RR ≤ boundingFactor v v ↔ eValue RR ≤ v := by
  constructor
  · intro h
    simpa using eValue_le_max hRR hv hv h
  · intro h
    have hE := one_le_eValue (zero_lt_one.trans hRR)
    calc RR = boundingFactor (eValue RR) (eValue RR) := (boundingFactor_eValue hRR.le).symm
      _ ≤ boundingFactor v v := boundingFactor_mono hE h hE h

/-- **The E-value is the least common strength** (VanderWeele and Ding 2017): for `RR ≥ 1`, it
is the least `v ≥ 1` with `RR ≤ boundingFactor v v`. -/
theorem isLeast_eValue {RR : ℝ} (hRR : 1 ≤ RR) :
    IsLeast {v | 1 ≤ v ∧ RR ≤ boundingFactor v v} (eValue RR) := by
  refine ⟨⟨one_le_eValue (zero_lt_one.trans_le hRR), (boundingFactor_eValue hRR).ge⟩,
    fun v hv => ?_⟩
  rcases hRR.lt_or_eq with h | h
  · exact (le_boundingFactor_self_iff h hv.1).1 hv.2
  · rw [← h, eValue_of_one_le le_rfl]
    simpa using hv.1

/-- **The E-value is the least larger parameter over all explaining pairs** (VanderWeele and
Ding 2017): for `RR ≥ 1` it is the least value of `max a b` over the pairs `a, b ≥ 1` with
`RR ≤ boundingFactor a b`. -/
theorem isLeast_eValue_max {RR : ℝ} (hRR : 1 ≤ RR) :
    IsLeast {M | ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ RR ≤ boundingFactor a b ∧ M = max a b}
      (eValue RR) := by
  have hE := one_le_eValue (zero_lt_one.trans_le hRR)
  refine ⟨⟨eValue RR, eValue RR, hE, hE, (boundingFactor_eValue hRR).ge, (max_self _).symm⟩,
    ?_⟩
  rintro M ⟨a, b, ha, hb, h, rfl⟩
  rcases hRR.lt_or_eq with hlt | heq
  · exact eValue_le_max hlt ha hb h
  · rw [← heq, eValue_of_one_le le_rfl]
    simpa using le_max_of_le_left ha

/-- **Unequal parameters do worse than the E-value.** For `RR > 1` and `a, b ≥ 1` with `a ≠ b`,
if the confounder explains the estimate away then `eValue RR < max a b`: lowering the larger
parameter to the smaller one keeps `boundingFactor` strictly below its diagonal value. -/
theorem eValue_lt_max_of_ne {RR a b : ℝ} (hRR : 1 < RR) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : RR ≤ boundingFactor a b) (hab : a ≠ b) : eValue RR < max a b := by
  have key : ∀ {x y : ℝ}, 1 ≤ x → x < y → RR ≤ boundingFactor x y → eValue RR < y := by
    intro x y hx hxy hxyR
    have hy : 1 < y := hx.trans_lt hxy
    have hlt : RR < boundingFactor y y :=
      hxyR.trans_lt (boundingFactor_lt_boundingFactor_left hx hxy hy)
    have hle : eValue RR ≤ y := (le_boundingFactor_self_iff hRR hy.le).1 hlt.le
    refine lt_of_le_of_ne hle fun hEy => ?_
    rw [← hEy, boundingFactor_eValue hRR.le] at hlt
    exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [max_eq_right hlt.le]; exact key ha hlt h
  · rw [max_eq_left hlt.le]
    rw [boundingFactor_comm] at h
    exact key hb hlt h

/-- **The least maximum is attained only on the diagonal.** For `RR > 1`, a pair `a, b ≥ 1` that
explains the estimate away with `max a b = eValue RR` has `a = b = eValue RR`. -/
theorem eq_eValue_of_max_eq {RR a b : ℝ} (hRR : 1 < RR) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : RR ≤ boundingFactor a b) (hmax : max a b = eValue RR) :
    a = eValue RR ∧ b = eValue RR := by
  have hab : a = b := by
    by_contra hne
    exact absurd hmax (ne_of_gt (eValue_lt_max_of_ne hRR ha hb h hne))
  subst hab
  rw [max_self] at hmax
  exact ⟨hmax, hmax⟩

/-! ### Monotonicity in the observed risk ratio -/

/-- The E-value is strictly increasing in the observed risk ratio on `[1, ∞)`. -/
theorem strictMonoOn_eValue : StrictMonoOn eValue (Ici 1) := by
  intro a (ha : 1 ≤ a) b (hb : 1 ≤ b) hab
  rw [eValue_of_one_le ha, eValue_of_one_le hb]
  have : Real.sqrt (a * (a - 1)) ≤ Real.sqrt (b * (b - 1)) := Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- The E-value is strictly decreasing in the observed risk ratio on `(0, 1]`: a protective
estimate farther from the null needs a stronger confounder. -/
theorem strictAntiOn_eValue : StrictAntiOn eValue (Ioc 0 1) := by
  intro a ha b hb hab
  rw [← eValue_inv a, ← eValue_inv b]
  exact strictMonoOn_eValue (show (1 : ℝ) ≤ b⁻¹ from (one_le_inv₀ hb.1).2 hb.2)
    (show (1 : ℝ) ≤ a⁻¹ from (one_le_inv₀ ha.1).2 ha.2) ((inv_lt_inv₀ hb.1 ha.1).2 hab)

/-! ### The protective case -/

/-- **Attainment for a protective estimate**: for `0 < RR ≤ 1` the diagonal confounder of
strength `eValue RR`, acting with the exposure recoded, has bounding factor `1 / RR`, so the
corrected estimate `RR * boundingFactor E E` is exactly the null. -/
theorem boundingFactor_eValue_inv {RR : ℝ} (h0 : 0 < RR) (h1 : RR ≤ 1) :
    RR * boundingFactor (eValue RR) (eValue RR) = 1 := by
  rw [← eValue_inv, boundingFactor_eValue ((one_le_inv₀ h0).2 h1), mul_inv_cancel₀ h0.ne']

/-- **The E-value is the least common strength for a protective estimate**: for `0 < RR ≤ 1`,
it is the least `v ≥ 1` with `1 / RR ≤ boundingFactor v v`. -/
theorem isLeast_eValue_of_le_one {RR : ℝ} (h0 : 0 < RR) (h1 : RR ≤ 1) :
    IsLeast {v | 1 ≤ v ∧ RR⁻¹ ≤ boundingFactor v v} (eValue RR) := by
  rw [← eValue_inv]
  exact isLeast_eValue ((one_le_inv₀ h0).2 h1)

/-! ### The E-value of a confidence limit -/

/-- The **E-value of a confidence interval** `[lo, hi]` for a risk ratio (VanderWeele and Ding
2017): the E-value of the limit closest to the null, `eValue lo` if `1 < lo`, `eValue hi` if
`hi < 1`, and `1` if the interval contains the null. -/
noncomputable def eValueLimit (lo hi : ℝ) : ℝ :=
  if 1 < lo then eValue lo else if hi < 1 then eValue hi else 1

/-- **A confounder below the E-value of the lower limit leaves the interval above the null.**
For `1 < lo`, a confounder with parameters `a, b ≥ 1` and `max a b < eValueLimit lo hi`, and any
bias factor `0 < B ≤ boundingFactor a b` it may produce, the corrected lower limit `lo / B` still
exceeds one. -/
theorem one_lt_div_of_max_lt_eValueLimit {lo hi a b B : ℝ} (hlo : 1 < lo) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hmax : max a b < eValueLimit lo hi) (hB0 : 0 < B)
    (hB : B ≤ boundingFactor a b) : 1 < lo / B := by
  rw [eValueLimit, ite_eq_left hlo] at hmax
  have hlt : boundingFactor a b < lo := by
    by_contra hle
    exact absurd (eValue_le_max hlo ha hb (not_lt.1 hle)) (not_le.2 hmax)
  rw [one_lt_div hB0]
  exact hB.trans_lt hlt

/-- **The diagonal confounder at the E-value of the lower limit moves that limit to the null**:
for `1 < lo`, `lo / boundingFactor E E = 1` with `E = eValueLimit lo hi`. -/
theorem div_eq_one_of_eValueLimit {lo hi : ℝ} (hlo : 1 < lo) :
    lo / boundingFactor (eValueLimit lo hi) (eValueLimit lo hi) = 1 := by
  rw [eValueLimit, ite_eq_left hlo, boundingFactor_eValue hlo.le, div_self (by linarith)]

/-- **The E-value of the interval is at most the E-value of the estimate**: for
`0 < lo ≤ RR ≤ hi`, `eValueLimit lo hi ≤ eValue RR`, with value one when `lo ≤ 1 ≤ hi`. -/
theorem eValueLimit_le_eValue {lo hi RR : ℝ} (hlo0 : 0 < lo) (hlo : lo ≤ RR) (hhi : RR ≤ hi) :
    eValueLimit lo hi ≤ eValue RR := by
  unfold eValueLimit
  split_ifs with h1 h2
  · exact strictMonoOn_eValue.monotoneOn (show (1 : ℝ) ≤ lo from h1.le)
      (show (1 : ℝ) ≤ RR from h1.le.trans hlo) hlo
  · exact strictAntiOn_eValue.antitoneOn (show RR ∈ Ioc (0 : ℝ) 1 from
      ⟨hlo0.trans_le hlo, (hhi.trans h2.le)⟩) (show hi ∈ Ioc (0 : ℝ) 1 from
      ⟨hlo0.trans_le (hlo.trans hhi), h2.le⟩) hhi
  · exact one_le_eValue (hlo0.trans_le hlo)

end IndirectComparisonBias

end BiasAnalysis

end CausalInference
