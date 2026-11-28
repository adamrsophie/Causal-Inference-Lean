/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedLikelihood
public import CausalInference.MetaAnalysis.Egger
public import CausalInference.MetaAnalysis.Examples
public import CausalInference.MetaAnalysis.RandomEffects

/-!
# Meta-analysis: the restricted maximum likelihood estimate of the between study variance

This file completes the first order analysis of `MetaAnalysis.RestrictedLikelihood` with the
existence of a maximizer, the uniqueness under equal within study variances, and the case of a
single study.

**Existence.** For `vᵢ > 0` and at least two studies the restricted log likelihood tends to
`-∞` as `t → ∞` (`tendsto_restrictedLogLik_atTop`): with `t ≥ max 1 vᵢ₀`,
`ℓ_R(t) ≤ -½ log t + ½ log 2`, since `log(vᵢ + t) ≥ log t`, `∑ w̃ᵢ ≥ 1 / (vᵢ₀ + t) ≥ 1 / (2t)` and
`Q ≥ 0`. It is continuous on `[0, ∞)`, so it attains its supremum there
(`exists_isMaxOn_restrictedLogLik`); a maximizer `t > 0` has restricted score `0` and a maximizer
at `0` has restricted score `≤ 0` at `0`.

**Uniqueness under equal variances.** With `vᵢ = v > 0` for all `k ≥ 2` studies,
`ℓ_R(t) = -((k-1)/2) (log(v + t) + s² / (v + t)) - ½ log k` (`restrictedLogLik_const`), with `s²`
the sample variance `∑ (yᵢ - ȳ)² / (k - 1)` of the estimates, and the restricted likelihood has
exactly one maximizer on `[0, ∞)`, the closed form `τ̂²_REML = max 0 (s² - v)`
(`isMaxOn_restrictedLogLik_const_iff`). Proof: `u ↦ log u + s² / u` has the unique minimizer
`u = s²` on `(0, ∞)`, by `log x < x - 1` for `x ≠ 1`.

Uniqueness for unequal variances is not proved here: the restricted likelihood of the between
study variance is not known to be unimodal in general, and this file makes no claim about it.

**One study.** With `k = 1`, `ℓ_R(t) = 0` for every `t ≥ 0` and every estimate
(`restrictedLogLik_of_card_eq_one`): the restricted likelihood is constant, every `t ≥ 0` is a
maximizer, and the data carry no information about `τ²`.

**Instance.** The estimates `(0, 1, 2)` have `s² = 1`: with equal variances `1/4` the unique
restricted maximum likelihood estimate is `3/4`, with equal variances `2` it is `0`
(`example_reml_const`); with the unequal variances of the example a maximizer exists
(`example_exists_reml`).

## Main results

* `tendsto_restrictedLogLik_atTop`, `exists_isMaxOn_restrictedLogLik`.
* `restrictedLogLik_const`, `isMaxOn_restrictedLogLik_const_iff`.
* `restrictedLogLik_of_card_eq_one`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Filter Topology Finset PopulationAdjustment

variable {ι : Type*} [Fintype ι]

/-! ### Existence -/

/-- **The restricted log likelihood tends to `-∞`**: for `vᵢ > 0` and at least two studies,
`ℓ_R(t) → -∞` as `t → ∞`. -/
theorem tendsto_restrictedLogLik_atTop {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hk : 2 ≤ Fintype.card ι) (y : ι → ℝ) :
    Tendsto (restrictedLogLik v y) atTop atBot := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i0⟩ := hne
  have hk' : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
  have hbound : ∀ t, max 1 (v i0) ≤ t →
      restrictedLogLik v y t ≤ -(1 / 2 * Real.log t - 1 / 2 * Real.log 2) := by
    intro t ht
    have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
    have hti : v i0 ≤ t := le_trans (le_max_right _ _) ht
    have htpos : 0 < t := by linarith
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hpos : ∀ i, 0 < v i + t := fun i => by linarith [hv i]
    have hQ : 0 ≤ cochranQ (fun i => v i + t) y := cochranQ_nonneg hpos y
    have hsum : (Fintype.card ι : ℝ) * Real.log t ≤ ∑ i, Real.log (v i + t) := by
      have : ∑ _i : ι, Real.log t ≤ ∑ i, Real.log (v i + t) :=
        Finset.sum_le_sum fun i _ => Real.log_le_log htpos (by linarith [hv i])
      simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
    have hw0 : 0 < ivWeight (fun i => v i + t) i0 := one_div_pos.2 (hpos i0)
    have hW : ivWeight (fun i => v i + t) i0 ≤ ∑ i, ivWeight (fun i => v i + t) i :=
      Finset.single_le_sum (fun i _ => (one_div_pos.2 (hpos i)).le) (Finset.mem_univ i0)
    have hlogW : -Real.log 2 - Real.log t ≤ Real.log (∑ i, ivWeight (fun i => v i + t) i) := by
      have h1 : Real.log (ivWeight (fun i => v i + t) i0) ≤
          Real.log (∑ i, ivWeight (fun i => v i + t) i) := Real.log_le_log hw0 hW
      have h2 : Real.log (ivWeight (fun i => v i + t) i0) = -Real.log (v i0 + t) := by
        simp only [ivWeight, one_div, Real.log_inv]
      have h3 : Real.log (v i0 + t) ≤ Real.log 2 + Real.log t := by
        rw [← Real.log_mul (by norm_num) htpos.ne']
        exact Real.log_le_log (hpos i0) (by linarith)
      linarith
    have hmul : Real.log t ≤ ((Fintype.card ι : ℝ) - 1) * Real.log t := by nlinarith
    simp only [restrictedLogLik]
    nlinarith
  have h1 : Tendsto (fun t => 1 / 2 * Real.log t - 1 / 2 * Real.log 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Real.tendsto_log_atTop.const_mul_atTop (by norm_num))
  refine tendsto_atBot_mono' atTop ?_ (tendsto_neg_atTop_atBot.comp h1)
  filter_upwards [eventually_ge_atTop (max 1 (v i0))] with t ht
  exact hbound t ht

/-- **Existence of the restricted maximum likelihood estimate**: for `vᵢ > 0` and at least two
studies, the restricted log likelihood attains its maximum on `[0, ∞)`. A maximizer `t > 0` has
restricted score `0`; a maximizer at `0` has restricted score `≤ 0` at `0`. Proof: continuity on
`[0, ∞)`, the limit `-∞` at infinity, and the extreme value theorem off a compact set. -/
theorem exists_isMaxOn_restrictedLogLik {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hk : 2 ≤ Fintype.card ι) (y : ι → ℝ) :
    ∃ t, 0 ≤ t ∧ IsMaxOn (restrictedLogLik v y) (Set.Ici 0) t ∧
      (0 < t → restrictedScore v y t = 0) ∧ (t = 0 → restrictedScore v y 0 ≤ 0) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hfo := restrictedLogLik_firstOrder hv y
  have hcont : ContinuousOn (restrictedLogLik v y) (Set.Ici 0) := fun t ht =>
    (hfo.1 t ht).continuousAt.continuousWithinAt
  have htend := tendsto_restrictedLogLik_atTop hv hk y
  have hc : ∀ᶠ x in Filter.cocompact ℝ ⊓ 𝓟 (Set.Ici 0),
      restrictedLogLik v y x ≤ restrictedLogLik v y 0 := by
    rw [cocompact_eq_atBot_atTop, inf_sup_right, eventually_sup]
    refine ⟨?_, ?_⟩
    · refine eventually_inf_principal.2 ?_
      filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx hx'
      exact absurd (Set.mem_Ici.1 hx') (not_le.2 hx)
    · refine eventually_inf_principal.2 ?_
      filter_upwards [htend.eventually (eventually_le_atBot (restrictedLogLik v y 0))] with x hx _
      exact hx
  obtain ⟨t, ht, hmax⟩ := hcont.exists_isMaxOn' isClosed_Ici (Set.mem_Ici.2 le_rfl) hc
  refine ⟨t, ht, hmax, fun htpos => ?_, fun h0 => ?_⟩
  · exact (hmax.isLocalMax (Ici_mem_nhds htpos)).hasDerivAt_eq_zero (hfo.1 t ht)
  · subst h0
    exact hfo.2.2.2 hmax

/-! ### Equal within study variances -/

/-- With equal variances the pooled estimate is the arithmetic mean. -/
theorem ivwEstimate_equalVar [Nonempty ι] {c : ℝ} (hc : c ≠ 0) (y : ι → ℝ) :
    ivwEstimate (fun _ : ι => c) y = regMean y := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [ivwEstimate, weightedMean, ivWeight, regMean, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **The restricted log likelihood under equal variances**: for `vᵢ = v` and `v + t > 0`,
`ℓ_R(t) = -((k-1)/2) log(v + t) - ½ log k - ∑ (yᵢ - ȳ)² / (2 (v + t))`. -/
theorem restrictedLogLik_const [Nonempty ι] {v t : ℝ} (hvt : 0 < v + t) (y : ι → ℝ) :
    restrictedLogLik (fun _ : ι => v) y t =
      -(((Fintype.card ι : ℝ) - 1) / 2) * Real.log (v + t) -
        1 / 2 * Real.log (Fintype.card ι) - regSxx y / (2 * (v + t)) := by
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hW : ∑ i : ι, ivWeight (fun _ => v + t) i = Fintype.card ι / (v + t) := by
    simp [ivWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]
  have hQ : cochranQ (fun _ : ι => v + t) y = regSxx y / (v + t) := by
    rw [cochranQ, ivwEstimate_equalVar hvt.ne', regSxx, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ivWeight]
    ring
  simp only [restrictedLogLik]
  rw [hW, hQ, Real.log_div hk.ne' hvt.ne', Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- `log u + a / u` has the unique minimizer `max v a` on `[v, ∞)`, for `v > 0`. -/
theorem log_add_div_lt {v a u : ℝ} (hv : 0 < v) (hu : v ≤ u) (hne : u ≠ max v a) :
    Real.log (max v a) + a / max v a < Real.log u + a / u := by
  have hupos : 0 < u := lt_of_lt_of_le hv hu
  rcases le_total v a with hva | hav
  · rw [max_eq_right hva] at hne ⊢
    have hapos : 0 < a := lt_of_lt_of_le hv hva
    have hx : a / u ≠ 1 := fun h => hne ((div_eq_one_iff_eq hupos.ne').1 h).symm
    have hlog := Real.log_lt_sub_one_of_pos (div_pos hapos hupos) hx
    rw [Real.log_div hapos.ne' hupos.ne'] at hlog
    rw [div_self hapos.ne']
    linarith
  · rw [max_eq_left hav] at hne ⊢
    have hlt : v < u := lt_of_le_of_ne hu (Ne.symm hne)
    have hx : v / u ≠ 1 := fun h => hne ((div_eq_one_iff_eq hupos.ne').1 h).symm
    have hlog := Real.log_lt_sub_one_of_pos (div_pos hv hupos) hx
    rw [Real.log_div hv.ne' hupos.ne'] at hlog
    have hkey : 0 ≤ 1 - v / u + a / u - a / v := by
      have : 1 - v / u + a / u - a / v = (u - v) * (v - a) / (u * v) := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hupos hv).le
    linarith

/-- **Uniqueness and closed form under equal variances**: for `vᵢ = v > 0` and `k ≥ 2` studies,
`t ≥ 0` maximizes the restricted log likelihood on `[0, ∞)` exactly when
`t = max 0 (s² - v)`, with `s² = ∑ (yᵢ - ȳ)² / (k - 1)` the sample variance of the estimates. -/
theorem isMaxOn_restrictedLogLik_const_iff {v : ℝ} (hv : 0 < v) (hk : 2 ≤ Fintype.card ι)
    (y : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsMaxOn (restrictedLogLik (fun _ : ι => v) y) (Set.Ici 0) t ↔
      t = max 0 (regSxx y / ((Fintype.card ι : ℝ) - 1) - v) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hk' : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    linarith
  set m : ℝ := (Fintype.card ι : ℝ) - 1
  set s2 := regSxx y / m
  set tstar := max 0 (s2 - v)
  have htstar : 0 ≤ tstar := le_max_left _ _
  have hvt : v + tstar = max v s2 := by
    simp only [tstar]
    rcases le_total v s2 with h | h
    · rw [max_eq_right (by linarith), max_eq_right h]; ring
    · rw [max_eq_left (by linarith), max_eq_left h]; ring
  have hform : ∀ u, 0 ≤ u → restrictedLogLik (fun _ : ι => v) y u =
      -(m / 2) * (Real.log (v + u) + s2 / (v + u)) - 1 / 2 * Real.log (Fintype.card ι) := by
    intro u hu
    rw [restrictedLogLik_const (by linarith) y]
    simp only [s2]
    have : 0 < v + u := by linarith
    field_simp
    ring
  have hstrict : ∀ u, 0 ≤ u → u ≠ tstar →
      restrictedLogLik (fun _ : ι => v) y u < restrictedLogLik (fun _ : ι => v) y tstar := by
    intro u hu hne
    rw [hform u hu, hform tstar htstar, hvt]
    have hlt := log_add_div_lt (a := s2) hv (show v ≤ v + u by linarith)
      (fun h => hne (by rw [← hvt] at h; linarith))
    nlinarith
  constructor
  · intro hmax
    by_contra hne
    exact absurd (isMaxOn_iff.1 hmax tstar htstar) (not_le.2 (hstrict t ht hne))
  · rintro rfl
    refine isMaxOn_iff.2 fun u hu => ?_
    rcases eq_or_ne u tstar with h | h
    · rw [h]
    · exact (hstrict u hu h).le

/-! ### One study -/

/-- **One study**: with a single study the restricted log likelihood is `0` for every `t ≥ 0`
and every estimate, so every `t ≥ 0` maximizes it and the data carry no information about the
between study variance. -/
theorem restrictedLogLik_of_card_eq_one {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hk : Fintype.card ι = 1) (y : ι → ℝ) :
    ∀ t, 0 ≤ t → restrictedLogLik v y t = 0 ∧ IsMaxOn (restrictedLogLik v y) (Set.Ici 0) t := by
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 hk
  have hzero : ∀ t, 0 ≤ t → restrictedLogLik v y t = 0 := by
    intro t ht
    have hpos : ∀ i, 0 < v i + t := fun i => by linarith [hv i]
    have huniv : (Finset.univ : Finset ι) = {i0} := Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_univ _, fun j _ => hi0 j⟩
    simp only [restrictedLogLik, cochranQ_of_card_eq_one hpos hk y, huniv,
      Finset.sum_singleton, ivWeight, one_div, Real.log_inv]
    ring
  refine fun t ht => ⟨hzero t ht, isMaxOn_iff.2 fun u hu => ?_⟩
  rw [hzero u hu, hzero t ht]

/-! ### Instance -/

/-- **The closed form on data**: the estimates `(0, 1, 2)` have `∑ (yᵢ - ȳ)² = 2` and sample
variance `1`; with equal variances `1/4` the unique restricted maximum likelihood estimate is
`3/4`, and with equal variances `2` it is `0`. -/
theorem example_reml_const :
    regSxx exampleY = 2 ∧
      IsMaxOn (restrictedLogLik (fun _ : Fin 3 => (1 / 4 : ℝ)) exampleY) (Set.Ici 0) (3 / 4) ∧
      (∀ t, 0 ≤ t → IsMaxOn (restrictedLogLik (fun _ : Fin 3 => (1 / 4 : ℝ)) exampleY)
        (Set.Ici 0) t → t = 3 / 4) ∧
      IsMaxOn (restrictedLogLik (fun _ : Fin 3 => (2 : ℝ)) exampleY) (Set.Ici 0) 0 ∧
      (∀ t, 0 ≤ t → IsMaxOn (restrictedLogLik (fun _ : Fin 3 => (2 : ℝ)) exampleY)
        (Set.Ici 0) t → t = 0) := by
  have hS : regSxx exampleY = 2 := by
    rw [regSxx, regMean]
    norm_num [exampleY, Fin.sum_univ_three]
  have hk : 2 ≤ Fintype.card (Fin 3) := by simp
  have hc : ((Fintype.card (Fin 3) : ℝ) - 1) = 2 := by norm_num
  have h1 := fun t ht => isMaxOn_restrictedLogLik_const_iff (v := (1 / 4 : ℝ)) (by norm_num) hk
    exampleY (t := t) ht
  have h2 := fun t ht => isMaxOn_restrictedLogLik_const_iff (v := (2 : ℝ)) (by norm_num) hk
    exampleY (t := t) ht
  simp only [hS, hc] at h1 h2
  refine ⟨hS, (h1 (3 / 4) (by norm_num)).2 (by norm_num), fun t ht hmax => ?_,
    (h2 0 le_rfl).2 (by norm_num), fun t ht hmax => ?_⟩
  · rw [(h1 t ht).1 hmax]; norm_num
  · rw [(h2 t ht).1 hmax]; norm_num

/-- With the unequal variances `(1, 1/2, 1/4)` and estimates `(0, 1, 2)` of the example a
restricted maximum likelihood estimate exists. -/
theorem example_exists_reml :
    ∃ t, 0 ≤ t ∧ IsMaxOn (restrictedLogLik exampleVar exampleY) (Set.Ici 0) t ∧
      (0 < t → restrictedScore exampleVar exampleY t = 0) ∧
      (t = 0 → restrictedScore exampleVar exampleY 0 ≤ 0) :=
  exists_isMaxOn_restrictedLogLik exampleVar_pos (by simp) exampleY

end MetaAnalysis

end CausalInference
