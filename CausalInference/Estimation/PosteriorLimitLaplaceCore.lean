/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLaplaceGaussian
public import Mathlib.Analysis.Convex.Continuous

/-!
# The Laplace estimate for a concave log likelihood

Let `ℓ : ℝ^p → ℝ` be concave (a log likelihood after `n` observations), `π` a prior density and
`M` a positive definite matrix with `λ ‖u‖² ≤ uᵀ M u`. Suppose that on the ball `‖u‖ ≤ δ` the
log likelihood has the quadratic expansion

  `|ℓ(m + u) - ℓ(m) + (n/2) uᵀ M u| ≤ η n ‖u‖²`, with `0 ≤ η ≤ λ/4`,

and that `π` varies by at most `o` on the ball of radius `δ` around `m`. Then
(`integral_abs_mul_exp_sub_gaussian_le`) `ℓ ≤ ℓ(m)` everywhere, and

  `∫ |π(θ) e^{ℓ(θ) - ℓ(m)} - π(θ₀) e^{-(n/2)(θ - m)ᵀ M (θ - m)}| dθ
    ≤ (o + 8 π(θ₀) η / λ) G(nλ/8) + e^{-nλδ²/4} (∫ π + π(θ₀) G(nλ/4))`,

with `G(b) = ∫ e^{-b ‖v‖²} dv` (`gaussianMass`). Inside the ball the two exponents are compared
(`abs_exp_sub_exp_le`); outside it, concavity along the segment from `m` turns the quadratic
decrease on the sphere of radius `δ` into the tail bound `ℓ(θ) - ℓ(m) ≤ -nλδ²/4`
(`sub_le_neg_mul_sq_of_concaveOn`). No smoothness of `ℓ` beyond the expansion is used, and
measurability of `ℓ` follows from concavity.

## Main results

* `exists_mul_sq_norm_le_quadForm`: a positive definite form is coercive.
* `abs_exp_sub_exp_le`, `mul_exp_neg_le`: two elementary exponential inequalities.
* `sub_le_neg_mul_sq_of_concaveOn`: the tail bound from concavity.
* `integral_abs_mul_exp_sub_gaussian_le`: the Laplace estimate.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 10.
-/

@[expose] public section

open MeasureTheory Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

variable {ι : Type*} [Fintype ι]

/-- **A positive definite form is coercive**: `λ ‖v‖² ≤ vᵀ M v` for some `λ > 0`, the minimum of
the form on the unit sphere. -/
lemma exists_mul_sq_norm_le_quadForm {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    ∃ lam > 0, ∀ v : EuclideanSpace ℝ ι, lam * ‖v‖ ^ 2 ≤ quadForm M v := by
  have hpos : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 → 0 < quadForm M v := fun v hv ↦ by
    have hv' : WithLp.ofLp v ≠ 0 := by
      intro h
      exact hv (by simpa using congrArg (WithLp.toLp 2) h)
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hM).2 hv'
    simpa [quadForm] using this
  have hsph : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 →
      ‖v‖⁻¹ • v ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := fun v hv ↦ by
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    simp [norm_smul, hn]
  rcases (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun v ↦ ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have := hsph v hv
      rw [h] at this
      exact this
    simp [hv, quadForm]
  · obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1).exists_isMinOn h
      (continuous_quadForm M).continuousOn
    have hv₀0 : v₀ ≠ 0 := by
      rintro rfl
      simp at hv₀
    refine ⟨quadForm M v₀, hpos v₀ hv₀0, fun v ↦ ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp [quadForm]
    · have h1 : quadForm M v₀ ≤ quadForm M (‖v‖⁻¹ • v) := hmin (hsph v hv)
      rw [quadForm_smul, inv_pow] at h1
      have h2 : 0 < ‖v‖ ^ 2 := by positivity
      calc quadForm M v₀ * ‖v‖ ^ 2 ≤ ((‖v‖ ^ 2)⁻¹ * quadForm M v) * ‖v‖ ^ 2 := by gcongr
        _ = quadForm M v := by field_simp

/-- `|eᵃ - eᵇ| ≤ |a - b| e^c` for `a, b ≤ c`. -/
lemma abs_exp_sub_exp_le {a b c : ℝ} (ha : a ≤ c) (hb : b ≤ c) :
    |Real.exp a - Real.exp b| ≤ |a - b| * Real.exp c := by
  have key : ∀ x y : ℝ, x ≤ y → y ≤ c → Real.exp y - Real.exp x ≤ (y - x) * Real.exp c := by
    intro x y hxy hyc
    have h1 := Real.add_one_le_exp (x - y)
    have h2 : Real.exp y - Real.exp x = Real.exp y * (1 - Real.exp (x - y)) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      ring_nf
    rw [h2]
    calc Real.exp y * (1 - Real.exp (x - y)) ≤ Real.exp y * (y - x) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos y).le
      _ ≤ Real.exp c * (y - x) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hyc) (by linarith)
      _ = (y - x) * Real.exp c := by ring
  rcases le_total a b with h | h
  · rw [abs_sub_comm (Real.exp a), abs_sub_comm a b,
      abs_of_nonneg (by linarith [Real.exp_le_exp.2 h] : 0 ≤ Real.exp b - Real.exp a),
      abs_of_nonneg (by linarith : 0 ≤ b - a)]
    exact key a b h hb
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 h] : 0 ≤ Real.exp a - Real.exp b),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    exact key b a h ha

/-- `t e^{-κt} ≤ (2/κ) e^{-κt/2}` for `κ > 0`, from `κt/2 ≤ e^{κt/2}`. -/
lemma mul_exp_neg_le {t κ : ℝ} (hκ : 0 < κ) :
    t * Real.exp (-κ * t) ≤ 2 / κ * Real.exp (-(κ / 2) * t) := by
  have h1 := Real.add_one_le_exp (κ / 2 * t)
  have h2 : Real.exp (-κ * t) = Real.exp (-(κ / 2) * t) * Real.exp (-(κ / 2) * t) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp (κ / 2 * t) * Real.exp (-(κ / 2) * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have h4 := Real.exp_pos (-(κ / 2) * t)
  rw [h2]
  have h5 : t ≤ 2 / κ * Real.exp (κ / 2 * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    linarith
  calc t * (Real.exp (-(κ / 2) * t) * Real.exp (-(κ / 2) * t))
      ≤ 2 / κ * Real.exp (κ / 2 * t) * (Real.exp (-(κ / 2) * t) * Real.exp (-(κ / 2) * t)) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = 2 / κ * (Real.exp (κ / 2 * t) * Real.exp (-(κ / 2) * t)) * Real.exp (-(κ / 2) * t) := by
        ring
    _ = 2 / κ * Real.exp (-(κ / 2) * t) := by rw [h3, mul_one]

omit [Fintype ι] in
/-- **The tail bound from concavity.** If `ℓ` is concave and `ℓ(m + u) - ℓ(m) ≤ -c ‖u‖²` for
`‖u‖ ≤ δ`, with `c ≥ 0` and `δ > 0`, then `ℓ(m + u) - ℓ(m) ≤ -c δ²` for `‖u‖ > δ`: by concavity
along the segment from `m` to `m + u`, the value at the point `m + (δ/‖u‖) u` of the sphere is
at least the corresponding convex combination. -/
lemma sub_le_neg_mul_sq_of_concaveOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ℓ : E → ℝ} (hℓ : ConcaveOn ℝ univ ℓ) {m : E} {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hin : ∀ u, ‖u‖ ≤ δ → ℓ (m + u) - ℓ m ≤ -c * ‖u‖ ^ 2) {u : E} (hu : δ < ‖u‖) :
    ℓ (m + u) - ℓ m ≤ -c * δ ^ 2 := by
  have hu0 : 0 < ‖u‖ := hδ.trans hu
  set t := δ / ‖u‖ with ht
  have ht0 : 0 < t := div_pos hδ hu0
  have ht1 : t ≤ 1 := (div_le_one hu0).2 hu.le
  have hconc := hℓ.2 (mem_univ m) (mem_univ (m + u)) (sub_nonneg.2 ht1) ht0.le
    (by ring : 1 - t + t = 1)
  have hpt : (1 - t) • m + t • (m + u) = m + t • u := by
    rw [smul_add, sub_smul, one_smul]
    abel
  rw [hpt, smul_eq_mul, smul_eq_mul] at hconc
  have hnorm : ‖t • u‖ = δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ht, div_mul_cancel₀ _ hu0.ne']
  have h1 := hin (t • u) hnorm.le
  rw [hnorm] at h1
  have h2 : t * (ℓ (m + u) - ℓ m) ≤ -c * δ ^ 2 := by linarith
  by_contra hcon
  push Not at hcon
  have h3 : 0 ≤ c * δ ^ 2 := by positivity
  nlinarith

/-- **The Laplace estimate.** Let `ℓ` be concave with
`|ℓ(m + u) - ℓ(m) + (n/2) uᵀMu| ≤ η n ‖u‖²` for `‖u‖ ≤ δ`, where `λ‖u‖² ≤ uᵀMu`, `λ > 0`,
`0 ≤ η ≤ λ/4`, `n, δ > 0`, and let the nonnegative integrable prior density `π` vary by at most
`o` on the ball of radius `δ` around `m`: `|π(θ) - π(θ₀)| ≤ o` there. Then `ℓ ≤ ℓ(m)`, and
`∫ |π(θ) e^{ℓ(θ) - ℓ(m)} - π(θ₀) e^{-(n/2)(θ - m)ᵀM(θ - m)}| dθ` is at most
`(o + 8 π(θ₀) η/λ) G(nλ/8) + e^{-nλδ²/4} (∫ π + π(θ₀) G(nλ/4))`. -/
theorem integral_abs_mul_exp_sub_gaussian_le {M : Matrix ι ι ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hQ : ∀ v, lam * ‖v‖ ^ 2 ≤ quadForm M v) {p : EuclideanSpace ℝ ι → ℝ} (hpm : Measurable p)
    (hp0 : ∀ θ, 0 ≤ p θ) (hpi : Integrable p) {ℓ : EuclideanSpace ℝ ι → ℝ}
    (hℓ : ConcaveOn ℝ univ ℓ) {m θ₀ : EuclideanSpace ℝ ι} {n η δ o : ℝ}
    (hn : 0 < n) (hη0 : 0 ≤ η) (hη : η ≤ lam / 4) (hδ : 0 < δ)
    (hquad : ∀ u, ‖u‖ ≤ δ → |ℓ (m + u) - ℓ m + n / 2 * quadForm M u| ≤ η * n * ‖u‖ ^ 2)
    (hosc : ∀ θ, ‖θ - m‖ ≤ δ → |p θ - p θ₀| ≤ o) :
    (∀ θ, ℓ θ - ℓ m ≤ 0) ∧
    ∫ θ, |p θ * Real.exp (ℓ θ - ℓ m) - p θ₀ * Real.exp (-(n / 2) * quadForm M (θ - m))| ≤
      (o + 8 * p θ₀ * η / lam) * gaussianMass ι (n * lam / 8) +
        Real.exp (-(n * lam / 4) * δ ^ 2) *
          ((∫ θ, p θ) + p θ₀ * gaussianMass ι (n * lam / 4)) := by
  have hℓm : Measurable ℓ := (continuousOn_univ.mp (hℓ.continuousOn isOpen_univ)).measurable
  have hp0' := hp0 θ₀
  have hin : ∀ u, ‖u‖ ≤ δ → ℓ (m + u) - ℓ m ≤ -(n * lam / 4) * ‖u‖ ^ 2 := by
    intro u hu
    have h1 := (abs_le.1 (hquad u hu)).2
    have h2 := hQ u
    have h3 : η * n * ‖u‖ ^ 2 ≤ lam / 4 * n * ‖u‖ ^ 2 := by gcongr
    nlinarith
  have hout : ∀ u, δ < ‖u‖ → ℓ (m + u) - ℓ m ≤ -(n * lam / 4) * δ ^ 2 :=
    fun u hu ↦ sub_le_neg_mul_sq_of_concaveOn hℓ (by positivity) hδ hin hu
  have hle0 : ∀ θ, ℓ θ - ℓ m ≤ 0 := by
    intro θ
    have e : θ = m + (θ - m) := by abel
    rw [e]
    rcases le_or_gt ‖θ - m‖ δ with h | h
    · have := hin (θ - m) h
      have : 0 ≤ n * lam / 4 * ‖θ - m‖ ^ 2 := by positivity
      linarith
    · have := hout (θ - m) h
      have : 0 ≤ n * lam / 4 * δ ^ 2 := by positivity
      linarith
  refine ⟨hle0, ?_⟩
  set C₁ := o + 8 * p θ₀ * η / lam with hC₁
  set e₀ := Real.exp (-(n * lam / 4) * δ ^ 2) with he₀
  have ho : 0 ≤ o := (abs_nonneg _).trans (hosc m (by simp [hδ.le]))
  have hC₁0 : 0 ≤ C₁ :=
    add_nonneg ho (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp0') hη0) hlam.le)
  set F : EuclideanSpace ℝ ι → ℝ := fun θ ↦ C₁ * Real.exp (-(n * lam / 8) * ‖θ - m‖ ^ 2) +
    e₀ * p θ + p θ₀ * e₀ * Real.exp (-(n * lam / 4) * ‖θ - m‖ ^ 2) with hF
  have hbound : ∀ θ, |p θ * Real.exp (ℓ θ - ℓ m) -
      p θ₀ * Real.exp (-(n / 2) * quadForm M (θ - m))| ≤ F θ := by
    intro θ
    set u := θ - m with hu
    have hθ : θ = m + u := by rw [hu]; abel
    set a := ℓ θ - ℓ m
    set b := -(n / 2) * quadForm M u
    have hb : b ≤ -(n * lam / 2) * ‖u‖ ^ 2 := by
      have := hQ u
      simp only [b]
      nlinarith
    have hF1 : 0 ≤ C₁ * Real.exp (-(n * lam / 8) * ‖u‖ ^ 2) :=
      mul_nonneg hC₁0 (Real.exp_pos _).le
    have hF2 : 0 ≤ e₀ * p θ := mul_nonneg (Real.exp_pos _).le (hp0 θ)
    have hF3 : 0 ≤ p θ₀ * e₀ * Real.exp (-(n * lam / 4) * ‖u‖ ^ 2) :=
      mul_nonneg (mul_nonneg hp0' (Real.exp_pos _).le) (Real.exp_pos _).le
    rcases le_or_gt ‖u‖ δ with h | h
    · have ha : a ≤ -(n * lam / 4) * ‖u‖ ^ 2 := by
        have := hin u h
        rw [← hθ] at this
        exact this
      have hb' : b ≤ -(n * lam / 4) * ‖u‖ ^ 2 := by
        have : 0 ≤ n * lam / 4 * ‖u‖ ^ 2 := by positivity
        linarith
      have hab : |a - b| ≤ η * n * ‖u‖ ^ 2 := by
        have := hquad u h
        rw [← hθ] at this
        simpa [a, b, sub_neg_eq_add] using this
      have hexp := abs_exp_sub_exp_le ha hb'
      have hea : Real.exp a ≤ Real.exp (-(n * lam / 8) * ‖u‖ ^ 2) := by
        refine Real.exp_le_exp.2 (ha.trans ?_)
        have : 0 ≤ n * lam / 8 * ‖u‖ ^ 2 := by positivity
        linarith
      have hmx := mul_exp_neg_le (t := n * ‖u‖ ^ 2) (κ := lam / 4) (by positivity)
      have e1 : -(n * lam / 4) * ‖u‖ ^ 2 = -(lam / 4) * (n * ‖u‖ ^ 2) := by ring
      have e2 : -(n * lam / 8) * ‖u‖ ^ 2 = -(lam / 4 / 2) * (n * ‖u‖ ^ 2) := by ring
      have hsplit : p θ * Real.exp a - p θ₀ * Real.exp b =
          (p θ - p θ₀) * Real.exp a + p θ₀ * (Real.exp a - Real.exp b) := by ring
      rw [hsplit]
      have hosc' := hosc θ (by rw [← hu]; exact h)
      calc |(p θ - p θ₀) * Real.exp a + p θ₀ * (Real.exp a - Real.exp b)|
          ≤ |p θ - p θ₀| * Real.exp a + p θ₀ * |Real.exp a - Real.exp b| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos a), abs_of_nonneg hp0']
        _ ≤ o * Real.exp (-(n * lam / 8) * ‖u‖ ^ 2) +
              p θ₀ * (η * (n * ‖u‖ ^ 2 * Real.exp (-(lam / 4) * (n * ‖u‖ ^ 2)))) := by
            refine add_le_add (mul_le_mul hosc' hea (Real.exp_pos _).le ho)
              (mul_le_mul_of_nonneg_left ?_ hp0')
            calc |Real.exp a - Real.exp b| ≤ |a - b| * Real.exp (-(n * lam / 4) * ‖u‖ ^ 2) :=
                    hexp
                _ ≤ η * n * ‖u‖ ^ 2 * Real.exp (-(n * lam / 4) * ‖u‖ ^ 2) := by gcongr
                _ = η * (n * ‖u‖ ^ 2 * Real.exp (-(lam / 4) * (n * ‖u‖ ^ 2))) := by
                    rw [e1]; ring
        _ ≤ o * Real.exp (-(n * lam / 8) * ‖u‖ ^ 2) +
              p θ₀ * (η * (2 / (lam / 4) * Real.exp (-(lam / 4 / 2) * (n * ‖u‖ ^ 2)))) := by
            gcongr
        _ = C₁ * Real.exp (-(n * lam / 8) * ‖u‖ ^ 2) := by
            rw [← e2, hC₁]
            field_simp
            ring
        _ ≤ F θ := by
            simp only [hF, ← hu]
            linarith
    · have ha : a ≤ -(n * lam / 4) * δ ^ 2 := by
        have := hout u h
        rw [← hθ] at this
        exact this
      have hb' : b ≤ -(n * lam / 4) * δ ^ 2 + -(n * lam / 4) * ‖u‖ ^ 2 := by
        have : n * lam / 4 * δ ^ 2 ≤ n * lam / 4 * ‖u‖ ^ 2 := by gcongr
        linarith
      have hg0 : 0 ≤ p θ * Real.exp a := mul_nonneg (hp0 θ) (Real.exp_pos _).le
      have hG0 : 0 ≤ p θ₀ * Real.exp b := mul_nonneg hp0' (Real.exp_pos _).le
      have h1 : p θ * Real.exp a ≤ e₀ * p θ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ha) (hp0 θ)
      have h2 : p θ₀ * Real.exp b ≤ p θ₀ * e₀ * Real.exp (-(n * lam / 4) * ‖u‖ ^ 2) := by
        rw [mul_assoc, he₀, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hb') hp0'
      rw [abs_sub_le_iff]
      simp only [hF, ← hu]
      constructor <;> linarith
  have hFi : Integrable F := by
    refine ((integrable_exp_neg_mul_sq_norm_sub (by positivity) m).const_mul C₁).add
      (hpi.const_mul e₀) |>.add ?_
    exact (integrable_exp_neg_mul_sq_norm_sub (by positivity) m).const_mul _
  have hmeas : Measurable fun θ ↦ |p θ * Real.exp (ℓ θ - ℓ m) -
      p θ₀ * Real.exp (-(n / 2) * quadForm M (θ - m))| := by
    have hq : Measurable fun θ ↦ quadForm M (θ - m) :=
      (continuous_quadForm M).measurable.comp (measurable_id.sub_const m)
    fun_prop
  calc ∫ θ, |p θ * Real.exp (ℓ θ - ℓ m) - p θ₀ * Real.exp (-(n / 2) * quadForm M (θ - m))|
      ≤ ∫ θ, F θ :=
        integral_mono (hFi.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun θ ↦ by
          rw [Real.norm_eq_abs, abs_abs]; exact hbound θ)) hFi hbound
    _ = C₁ * gaussianMass ι (n * lam / 8) +
          e₀ * ((∫ θ, p θ) + p θ₀ * gaussianMass ι (n * lam / 4)) := by
        have i1 := (integrable_exp_neg_mul_sq_norm_sub (b := n * lam / 8) (by positivity)
          m).const_mul C₁
        have i2 := hpi.const_mul e₀
        have i3 := (integrable_exp_neg_mul_sq_norm_sub (b := n * lam / 4) (by positivity)
          m).const_mul (p θ₀ * e₀)
        simp only [hF]
        rw [integral_add (f := fun θ ↦ C₁ * Real.exp (-(n * lam / 8) * ‖θ - m‖ ^ 2) + e₀ * p θ)
          (i1.add i2) i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
          integral_const_mul,
          integral_exp_neg_mul_sq_norm_sub (by positivity),
          integral_exp_neg_mul_sq_norm_sub (by positivity)]
        ring

end PosteriorLimit

end CausalInference
