/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.IndirectComparisonEValue
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.FinCases

/-!
# The bounding factor for a confounder with finitely many levels

The bound of Ding and VanderWeele (2016) for an unmeasured confounder `U` with finitely many
levels `ι`. Write `f₁ u = P(U = u | E = 1)` and `f₀ u = P(U = u | E = 0)` for the confounder laws
in the exposed and the unexposed, and `p₀ u = P(D = 1 | E = 0, U = u)` for the unexposed stratum
risks. The bias factor standardized to the exposed is `∑ p₀ f₁ / ∑ p₀ f₀`, the ratio of the
unexposed risk averaged over the confounder law of the exposed to the observed unexposed risk.
The two sensitivity parameters are `RR_EU = max_u f₁ u / f₀ u` and
`RR_UD = max_u p₀ u / min_u p₀ u`.

The second group of results is the response range bound used when the two populations of an
unanchored indirect comparison need not overlap: for any two laws of the covariate, the ratio of
the averages of a positive response is at most `max / min` of the response, attained by laws
concentrated at a maximum and at a minimum.

## Main definitions

* `exposureStrength`, `outcomeStrength`, `finiteBiasFactor`.

## Main results

* `finiteBiasFactor_le_boundingFactor`: the bias factor is at most
  `boundingFactor RR_EU RR_UD`; `finiteBiasFactor_attained`: for every `S, R ≥ 1` a two level
  confounder with `RR_EU = S`, `RR_UD = R` attains the bound.
* `finite_explainAway_le`: if the causal risk ratio standardized to the exposed is at most one,
  the observed risk ratio is at most `boundingFactor RR_EU RR_UD`; `finite_eValue_le_max`: then
  `max RR_EU RR_UD ≥ eValue RR_obs`.
* `ratio_le_outcomeStrength`, `exists_ratio_eq_outcomeStrength`,
  `ratio_eq_one_of_outcomeStrength_eq_one`: the response range bound, its attainment by disjoint
  supports, and the inert covariate.

## References

* P. Ding and T. J. VanderWeele, *Sensitivity analysis without assumptions*, Epidemiology 27
  (2016).
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace IndirectComparisonBias

open Set BiasFormulas ExternalAdjustment

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The confounder to exposure parameter `RR_EU = max_u f₁ u / f₀ u` of a confounder with laws
`f₁` among the exposed and `f₀` among the unexposed. -/
noncomputable def exposureStrength (f₁ f₀ : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun u => f₁ u / f₀ u

/-- The confounder to outcome parameter `RR_UD = max_u p₀ u / min_u p₀ u` of the stratum risks
`p₀`. -/
noncomputable def outcomeStrength (p₀ : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty p₀ / Finset.univ.inf' Finset.univ_nonempty p₀

/-- The bias factor standardized to the exposed: `∑ p₀ f₁ / ∑ p₀ f₀`. -/
noncomputable def finiteBiasFactor (p₀ f₁ f₀ : ι → ℝ) : ℝ :=
  (∑ u, p₀ u * f₁ u) / ∑ u, p₀ u * f₀ u

/-- `RR_EU ≥ 1` for two probability vectors with `f₀ > 0`. -/
theorem one_le_exposureStrength {f₁ f₀ : ι → ℝ} (hf₁ : ∑ u, f₁ u = 1) (hf₀ : ∀ u, 0 < f₀ u)
    (hf₀s : ∑ u, f₀ u = 1) : 1 ≤ exposureStrength f₁ f₀ := by
  have h : ∀ u, f₁ u ≤ exposureStrength f₁ f₀ * f₀ u := fun u =>
    (div_le_iff₀ (hf₀ u)).1 (Finset.le_sup' (fun u => f₁ u / f₀ u) (Finset.mem_univ u))
  have := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => h u
  rwa [← Finset.mul_sum, hf₁, hf₀s, mul_one] at this

/-- `RR_UD ≥ 1` for positive risks. -/
theorem one_le_outcomeStrength {p₀ : ι → ℝ} (hp₀ : ∀ u, 0 < p₀ u) : 1 ≤ outcomeStrength p₀ := by
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p₀
  rw [outcomeStrength, hu, one_le_div (hp₀ u)]
  exact Finset.le_sup' p₀ (Finset.mem_univ u)

/-- **The bounding factor for a finite confounder** (Ding and VanderWeele 2016). For a
probability vector `f₁ ≥ 0`, a positive probability vector `f₀` and positive risks `p₀`,
`∑ p₀ f₁ / ∑ p₀ f₀ ≤ boundingFactor RR_EU RR_UD`. With `m = min p₀`, `M = max p₀`, the excesses
`a = ∑ (p₀ - m) f₁` and `b = ∑ (p₀ - m) f₀` satisfy `a ≤ RR_EU b` and `a ≤ M - m`, and the claim
is a sum of nonnegative products. -/
theorem finiteBiasFactor_le_boundingFactor {p₀ f₁ f₀ : ι → ℝ} (hp₀ : ∀ u, 0 < p₀ u)
    (hf₁ : ∀ u, 0 ≤ f₁ u) (hf₁s : ∑ u, f₁ u = 1) (hf₀ : ∀ u, 0 < f₀ u)
    (hf₀s : ∑ u, f₀ u = 1) :
    finiteBiasFactor p₀ f₁ f₀ ≤ boundingFactor (exposureStrength f₁ f₀) (outcomeStrength p₀) := by
  set S := exposureStrength f₁ f₀ with hS
  set M := Finset.univ.sup' Finset.univ_nonempty p₀ with hM
  set m := Finset.univ.inf' Finset.univ_nonempty p₀ with hm
  have hS1 : 1 ≤ S := one_le_exposureStrength hf₁s hf₀ hf₀s
  obtain ⟨u0, -, hu0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p₀
  have hm0 : 0 < m := by rw [hm, hu0]; exact hp₀ u0
  have hmp : ∀ u, m ≤ p₀ u := fun u => Finset.inf'_le p₀ (Finset.mem_univ u)
  have hpM : ∀ u, p₀ u ≤ M := fun u => Finset.le_sup' p₀ (Finset.mem_univ u)
  have hmM : m ≤ M := (hmp u0).trans (hpM u0)
  have hfS : ∀ u, f₁ u ≤ S * f₀ u := fun u =>
    (div_le_iff₀ (hf₀ u)).1 (Finset.le_sup' (fun u => f₁ u / f₀ u) (Finset.mem_univ u))
  have hxa : ∑ u, p₀ u * f₁ u = m + ∑ u, (p₀ u - m) * f₁ u := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hf₁s]; ring
  have hyb : ∑ u, p₀ u * f₀ u = m + ∑ u, (p₀ u - m) * f₀ u := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hf₀s]; ring
  set a := ∑ u, (p₀ u - m) * f₁ u
  set b := ∑ u, (p₀ u - m) * f₀ u
  have hab : a ≤ S * b := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    have := mul_le_mul_of_nonneg_left (hfS u) (sub_nonneg.2 (hmp u))
    linarith
  have haM : a ≤ M - m := by
    have : a ≤ ∑ u, (M - m) * f₁ u :=
      Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right (by linarith [hpM u]) (hf₁ u)
    rwa [← Finset.mul_sum, hf₁s, mul_one] at this
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun u _ =>
    mul_nonneg (sub_nonneg.2 (hmp u)) (hf₀ u).le
  have hy0 : 0 < ∑ u, p₀ u * f₀ u := by rw [hyb]; linarith
  have hBF : boundingFactor S (M / m) = S * M / (S * m + M - m) := by
    rw [boundingFactor]
    field_simp
  have hden : 0 < S * m + M - m := by nlinarith
  rw [finiteBiasFactor, outcomeStrength, ← hM, ← hm, hBF, div_le_div_iff₀ hy0 hden, hxa, hyb]
  nlinarith [mul_nonneg hm0.le (sub_nonneg.2 hS1), mul_nonneg (mul_nonneg hm0.le
    (sub_nonneg.2 hS1)) (sub_nonneg.2 haM), mul_nonneg (hm0.le.trans hmM) (sub_nonneg.2 hab)]

/-- On `Fin 2` the maximum of two values is the larger one. -/
lemma sup'_fin_two (g : Fin 2 → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty g = max (g 0) (g 1) :=
  le_antisymm (Finset.sup'_le _ _ fun i _ => by fin_cases i <;> simp)
    (max_le (Finset.le_sup' g (Finset.mem_univ 0)) (Finset.le_sup' g (Finset.mem_univ 1)))

/-- On `Fin 2` the minimum of two values is the smaller one. -/
lemma inf'_fin_two (g : Fin 2 → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty g = min (g 0) (g 1) :=
  le_antisymm (le_min (Finset.inf'_le g (Finset.mem_univ 0)) (Finset.inf'_le g (Finset.mem_univ 1)))
    (Finset.le_inf' _ _ fun i _ => by fin_cases i <;> simp)

/-- **The finite bound is attained** (Ding and VanderWeele 2016). For every `S ≥ 1` and `R ≥ 1`
there is a two level confounder, with `f₁ ≥ 0` and positive `f₀`, `p₀`, `f₀` and `f₁`
probability vectors, whose parameters are exactly `RR_EU = S` and `RR_UD = R` and whose bias
factor equals `boundingFactor S R`: for `S > 1`, `p₀ = (1/R, 1)`, `f₁ = (0, 1)`,
`f₀ = (1 - 1/S, 1/S)`; for `S = 1`, `f₁ = f₀ = (1/2, 1/2)`. -/
theorem finiteBiasFactor_attained {S R : ℝ} (hS : 1 ≤ S) (hR : 1 ≤ R) :
    ∃ p₀ f₁ f₀ : Fin 2 → ℝ, (∀ u, 0 < p₀ u) ∧ (∀ u, 0 ≤ f₁ u) ∧ ∑ u, f₁ u = 1 ∧
      (∀ u, 0 < f₀ u) ∧ ∑ u, f₀ u = 1 ∧ exposureStrength f₁ f₀ = S ∧
      outcomeStrength p₀ = R ∧ finiteBiasFactor p₀ f₁ f₀ = boundingFactor S R := by
  have hR0 : 0 < R := by linarith
  have hRUD : outcomeStrength ![R⁻¹, 1] = R := by
    rw [outcomeStrength, sup'_fin_two, inf'_fin_two]
    have : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    simp [this]
  rcases hS.lt_or_eq with hS1 | rfl
  · have hS0 : 0 < S := by linarith
    refine ⟨![R⁻¹, 1], ![0, 1], ![1 - S⁻¹, S⁻¹], ?_, ?_, ?_, ?_, ?_, ?_, hRUD, ?_⟩
    · intro u; fin_cases u <;> simp [hR0]
    · intro u; fin_cases u <;> simp
    · simp
    · intro u; fin_cases u
      · simp [inv_lt_one_of_one_lt₀ hS1]
      · simp [hS0]
    · simp
    · rw [exposureStrength, sup'_fin_two]
      simp [hS0.le]
    · have hd : R⁻¹ * (1 - S⁻¹) + 1 * S⁻¹ = (S + R - 1) / (S * R) := by
        field_simp; ring
      simp only [finiteBiasFactor, boundingFactor, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [show R⁻¹ * 0 + 1 * 1 = (1 : ℝ) by ring, hd, one_div_div]
  · refine ⟨![R⁻¹, 1], ![2⁻¹, 2⁻¹], ![2⁻¹, 2⁻¹], ?_, ?_, ?_, ?_, ?_, ?_, hRUD, ?_⟩
    · intro u; fin_cases u <;> simp [hR0]
    · intro u; fin_cases u <;> simp
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]; norm_num
    · intro u; fin_cases u <;> simp
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]; norm_num
    · rw [exposureStrength, sup'_fin_two]
      simp
    · have hpos : 0 < R⁻¹ * 2⁻¹ + 1 * 2⁻¹ := by positivity
      simp only [finiteBiasFactor, boundingFactor, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, div_self hpos.ne']
      rw [add_sub_cancel_left, one_mul, div_self hR0.ne']

/-- **Explaining away with a finite confounder** (Ding and VanderWeele 2016). With exposed
stratum risks `p₁` and the hypotheses of `finiteBiasFactor_le_boundingFactor`, if the causal
risk ratio standardized to the exposed,
`∑ p₁ f₁ / ∑ p₀ f₁`, is at most one, then the observed risk ratio `∑ p₁ f₁ / ∑ p₀ f₀` is at most
`boundingFactor RR_EU RR_UD`. -/
theorem finite_explainAway_le {p₀ p₁ f₁ f₀ : ι → ℝ} (hp₀ : ∀ u, 0 < p₀ u)
    (hf₁ : ∀ u, 0 ≤ f₁ u) (hf₁s : ∑ u, f₁ u = 1) (hf₀ : ∀ u, 0 < f₀ u)
    (hf₀s : ∑ u, f₀ u = 1)
    (htrue : (∑ u, p₁ u * f₁ u) / (∑ u, p₀ u * f₁ u) ≤ 1) :
    (∑ u, p₁ u * f₁ u) / (∑ u, p₀ u * f₀ u) ≤
      boundingFactor (exposureStrength f₁ f₀) (outcomeStrength p₀) := by
  have hcf : 0 < ∑ u, p₀ u * f₁ u := by
    obtain ⟨u, hu⟩ : ∃ u, 0 < f₁ u := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have : ∑ u, f₁ u ≤ 0 := Finset.sum_nonpos fun u _ => h u
      linarith
    exact lt_of_lt_of_le (mul_pos (hp₀ u) hu)
      (Finset.single_le_sum (fun v _ => mul_nonneg (hp₀ v).le (hf₁ v)) (Finset.mem_univ u))
  have hden : 0 < ∑ u, p₀ u * f₀ u :=
    Finset.sum_pos (fun u _ => mul_pos (hp₀ u) (hf₀ u)) Finset.univ_nonempty
  have hle : ∑ u, p₁ u * f₁ u ≤ ∑ u, p₀ u * f₁ u := (div_le_one hcf).1 htrue
  refine le_trans ?_ (finiteBiasFactor_le_boundingFactor hp₀ hf₁ hf₁s hf₀ hf₀s)
  exact div_le_div_of_nonneg_right hle hden.le

/-- **The E-value with a finite confounder.** Under the hypotheses of `finite_explainAway_le`, if
the observed risk ratio exceeds one, then `max RR_EU RR_UD ≥ eValue RR_obs`. -/
theorem finite_eValue_le_max {p₀ p₁ f₁ f₀ : ι → ℝ} (hp₀ : ∀ u, 0 < p₀ u)
    (hf₁ : ∀ u, 0 ≤ f₁ u) (hf₁s : ∑ u, f₁ u = 1) (hf₀ : ∀ u, 0 < f₀ u)
    (hf₀s : ∑ u, f₀ u = 1)
    (htrue : (∑ u, p₁ u * f₁ u) / (∑ u, p₀ u * f₁ u) ≤ 1)
    (hRR : 1 < (∑ u, p₁ u * f₁ u) / (∑ u, p₀ u * f₀ u)) :
    eValue ((∑ u, p₁ u * f₁ u) / (∑ u, p₀ u * f₀ u)) ≤
      max (exposureStrength f₁ f₀) (outcomeStrength p₀) :=
  eValue_le_max hRR (one_le_exposureStrength hf₁s hf₀ hf₀s) (one_le_outcomeStrength hp₀)
    (finite_explainAway_le hp₀ hf₁ hf₁s hf₀ hf₀s htrue)

/-! ### The response range bound -/

/-- **The response range bound.** For a positive response `q` and any two probability vectors
`F₁, F₀ ≥ 0` (no overlap between them is required), `∑ q F₁ / ∑ q F₀ ≤ max q / min q`. -/
theorem ratio_le_outcomeStrength {q F₁ F₀ : ι → ℝ} (hq : ∀ u, 0 < q u) (hF₁ : ∀ u, 0 ≤ F₁ u)
    (hF₁s : ∑ u, F₁ u = 1) (hF₀ : ∀ u, 0 ≤ F₀ u) (hF₀s : ∑ u, F₀ u = 1) :
    (∑ u, q u * F₁ u) / (∑ u, q u * F₀ u) ≤ outcomeStrength q := by
  set M := Finset.univ.sup' Finset.univ_nonempty q
  set m := Finset.univ.inf' Finset.univ_nonempty q with hm
  obtain ⟨u0, -, hu0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty q
  have hm0 : 0 < m := by rw [hm, hu0]; exact hq u0
  have hM0 : 0 < M := hm0.trans_le ((Finset.inf'_le q (Finset.mem_univ u0)).trans
    (Finset.le_sup' q (Finset.mem_univ u0)))
  have hx : ∑ u, q u * F₁ u ≤ M := by
    have : ∑ u, q u * F₁ u ≤ ∑ u, M * F₁ u := Finset.sum_le_sum fun u _ =>
      mul_le_mul_of_nonneg_right (Finset.le_sup' q (Finset.mem_univ u)) (hF₁ u)
    rwa [← Finset.mul_sum, hF₁s, mul_one] at this
  have hy : m ≤ ∑ u, q u * F₀ u := by
    have : ∑ u, m * F₀ u ≤ ∑ u, q u * F₀ u := Finset.sum_le_sum fun u _ =>
      mul_le_mul_of_nonneg_right (Finset.inf'_le q (Finset.mem_univ u)) (hF₀ u)
    rwa [← Finset.mul_sum, hF₀s, mul_one] at this
  rw [outcomeStrength, div_le_div_iff₀ (hm0.trans_le hy) hm0]
  nlinarith [mul_le_mul_of_nonneg_right hx hm0.le, mul_le_mul_of_nonneg_left hy hM0.le]

/-- **Disjoint supports attain the response range bound**: a law concentrated at a level of
largest response and one concentrated at a level of smallest response give the ratio
`max q / min q`. -/
theorem exists_ratio_eq_outcomeStrength (q : ι → ℝ) :
    ∃ F₁ F₀ : ι → ℝ, (∀ u, 0 ≤ F₁ u) ∧ ∑ u, F₁ u = 1 ∧ (∀ u, 0 ≤ F₀ u) ∧ ∑ u, F₀ u = 1 ∧
      (∑ u, q u * F₁ u) / (∑ u, q u * F₀ u) = outcomeStrength q := by
  classical
  obtain ⟨u1, -, hu1⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty q
  obtain ⟨u0, -, hu0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty q
  refine ⟨Pi.single u1 1, Pi.single u0 1, fun u => ?_, by simp, fun u => ?_, by simp, ?_⟩
  · by_cases h : u = u1 <;> simp [h]
  · by_cases h : u = u0 <;> simp [h]
  · simp [Pi.single_apply, outcomeStrength, hu1, hu0]

/-- **An inert covariate gives ratio one**: if `max q / min q = 1` for a positive response, the
response is constant and the ratio of its averages over any two probability vectors is one. -/
theorem ratio_eq_one_of_outcomeStrength_eq_one {q F₁ F₀ : ι → ℝ} (hq : ∀ u, 0 < q u)
    (hF₁s : ∑ u, F₁ u = 1) (hF₀s : ∑ u, F₀ u = 1) (h1 : outcomeStrength q = 1) :
    (∑ u, q u * F₁ u) / (∑ u, q u * F₀ u) = 1 := by
  set M := Finset.univ.sup' Finset.univ_nonempty q
  set m := Finset.univ.inf' Finset.univ_nonempty q with hm
  obtain ⟨u0, -, hu0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty q
  have hm0 : 0 < m := by rw [hm, hu0]; exact hq u0
  have hMm : M = m := by rw [outcomeStrength, div_eq_one_iff_eq hm0.ne'] at h1; exact h1
  have hc : ∀ u, q u = m := fun u => le_antisymm
    (hMm ▸ Finset.le_sup' q (Finset.mem_univ u)) (Finset.inf'_le q (Finset.mem_univ u))
  simp only [hc, ← Finset.mul_sum, hF₁s, hF₀s, mul_one, div_self hm0.ne']

end IndirectComparisonBias

end BiasAnalysis

end CausalInference
