/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.NodeSplitting
public import CausalInference.PopulationAdjustment.WeightedNormalityContrast
public import CausalInference.Estimation.ConfidenceInterval

/-!
# The limit law of the node split statistic from three independent comparisons

In the triangle with comparisons `a → b`, `a → c`, `b → c`, let `y_ab,n`, `y_ac,n`, `y_bc,n` be
estimates that are mutually independent for each `n`, each asymptotically normal at a rate
`r_n`: `r_n (y_·,n - d_·) → N(0, v_·)` in distribution. The inconsistency estimate is
`ω̂_n = y_ab,n - (y_ac,n - y_bc,n)` (`inconsistencyEstimate`) and the inconsistency
`ω₀ = d_ab - (d_ac - d_bc)`. The standard error `SE_n` is ratio consistent:
`r_n SE_n → √(v_ab + v_ac + v_bc)` in probability.

* **The limit law of the inconsistency estimate**
  (`tendstoInDistribution_inconsistencyEstimate_of_iIndepFun`): `r_n (ω̂_n - ω₀)` converges in
  distribution to `N(0, v_ab + v_ac + v_bc)`. The proof derives it from the three marginal limits
  and independence: the negation of a normal limit, then two sums of independent sequences with
  normal limits (`tendstoInDistribution_add_of_indepFun`, through characteristic functions).
* **The standardized statistic** (`tendstoInDistribution_inconsistencyEstimate_sub_div`,
  `tendstoInDistribution_inconsistencyEstimate_div`): `(ω̂_n - ω₀) / SE_n → N(0, 1)`; under
  consistency, `d_ab = d_ac - d_bc`, the node split statistic `ω̂_n / SE_n` is asymptotically
  standard normal.
* **Consistency of the test** (`tendsto_measure_abs_div_le_of_ne_zero`,
  `tendsto_measure_abs_inconsistencyEstimate_div_le`,
  `tendsto_measure_lt_abs_inconsistencyEstimate_div`): under inconsistency, `ω₀ ≠ 0`, and a rate
  `r_n → ∞`, `|ω̂_n / SE_n|` tends to infinity in probability: `P(|ω̂_n / SE_n| ≤ M) → 0` for
  every `M`, and the two sided test rejects with probability tending to one at every critical
  value.
* **The limiting level** (`tendsto_measureReal_lt_abs_of_tendstoInDistribution`,
  `tendsto_measureReal_lt_abs_inconsistencyEstimate_div`): under consistency the test that
  rejects when `|ω̂_n / SE_n| > z`, `z ≥ 0`, has rejection probability tending to
  `2 (1 - Φ(z))`, by the portmanteau theorem for the continuity set `{x | z < |x|}` of the
  standard normal law.
* **Exact normal data** (`nodeSplitSample`, `nodeSplitSE`, `nodeSplitSample_limits`,
  `nodeSplitSample_example`): with sample size `n + 1`, independent
  `y_·,n ∼ N(d_·, v_· / (n + 1))`, rate `√(n + 1)` and `SE_n = √((v_ab + v_ac + v_bc) / (n + 1))`,
  every hypothesis above holds.

The rate is a general sequence `r_n`; the hypotheses on it are only those each result uses:
none for the limit law, eventually `r_n ≠ 0` for the standardized statistic and the level, and
`r_n → ∞` for the consistency of the test. In particular `r_n = √n` is covered.

## Main definitions

* `nodeSplitNoise`, `nodeSplitSample`, `nodeSplitSE`.

## Main results

* `tendstoInDistribution_congr_of_eventuallyEq`.
* `tendstoInDistribution_inconsistencyEstimate_of_iIndepFun`.
* `tendstoInDistribution_inconsistencyEstimate_sub_div`,
  `tendstoInDistribution_inconsistencyEstimate_div`.
* `tendsto_measure_abs_div_le_of_ne_zero`, `tendsto_measure_lt_abs_div_of_ne_zero`,
  `tendsto_measure_abs_inconsistencyEstimate_div_le`,
  `tendsto_measure_lt_abs_inconsistencyEstimate_div`.
* `tendsto_measureReal_lt_abs_of_tendstoInDistribution`,
  `tendsto_measureReal_lt_abs_inconsistencyEstimate_div`.
* `nodeSplitSample_limits`, `nodeSplitSample_example`.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
* S. Dias, N. J. Welton, D. M. Caldwell and A. E. Ades, *Checking consistency in mixed treatment
  comparison meta-analysis*, Statistics in Medicine 29 (2010).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open MeasureTheory ProbabilityTheory Filter Set IndirectComparison PopulationAdjustment
open scoped NNReal ENNReal Topology

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Convergence in distribution depends only on the tail.** If `X n → Z` in distribution and
`X n = X' n` for all large `n`, with every `X' n` almost everywhere measurable, then
`X' n → Z` in distribution. -/
theorem tendstoInDistribution_congr_of_eventuallyEq {X X' : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => μ) P') (hXX' : ∀ᶠ n in atTop, X n = X' n)
    (hm : ∀ n, AEMeasurable (X' n) μ) :
    TendstoInDistribution X' atTop Z (fun _ => μ) P' where
  forall_aemeasurable := hm
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.congr' (hXX'.mono fun n hn => Subtype.ext (by simp only [hn]))

/-- **Divergence of the standardized statistic when the centering is wrong.** Let
`r_n → ∞`, let `r_n (est_n - ω₀)` converge in distribution (to any limit), and let
`r_n SE_n → c > 0` in probability. If `ω₀ ≠ 0`, then `|est_n / SE_n|` tends to infinity in
probability: `P(|est_n / SE_n| ≤ M) → 0` for every `M`. -/
theorem tendsto_measure_abs_div_le_of_ne_zero {est SE : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) {ω₀ : ℝ} (hω : ω₀ ≠ 0) {Z : Ω' → ℝ}
    (hT : TendstoInDistribution (fun n ω => r n * (est n ω - ω₀)) atTop Z (fun _ => μ) P')
    {c : ℝ} (hc : 0 < c) (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop (fun _ => c))
    (M : ℝ) : Tendsto (fun n => μ {ω | |est n ω / SE n ω| ≤ M}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K, hK, hKev⟩ := hT.boundedInProbability (ε / 2) hε2
  have hSev : ∀ᶠ n in atTop, μ {ω | c ≤ dist (r n * SE n ω) c} ≤ ε / 2 :=
    (ENNReal.tendsto_nhds_zero.1 ((tendstoInMeasure_iff_dist.1 hSE) c hc)) _ hε2
  have hω0 : 0 < |ω₀| := abs_pos.2 hω
  have hrev : ∀ᶠ n in atTop, 0 < r n ∧ K + 2 * |M| * c < r n * |ω₀| := by
    filter_upwards [hr.eventually_gt_atTop 0,
      hr.eventually_gt_atTop ((K + 2 * |M| * c) / |ω₀|)] with n h1 h2
    exact ⟨h1, (div_lt_iff₀ hω0).1 h2⟩
  filter_upwards [hKev, hSev, hrev] with n h1 h2 h3
  calc μ {ω | |est n ω / SE n ω| ≤ M}
      ≤ μ ({ω | K ≤ |‖r n * (est n ω - ω₀)‖|} ∪ {ω | c ≤ dist (r n * SE n ω) c}) := by
        refine measure_mono fun ω hω => ?_
        simp only [mem_ofPred_eq, mem_union, Real.norm_eq_abs, abs_abs, Real.dist_eq] at hω ⊢
        by_contra hn
        push Not at hn
        obtain ⟨hT1, hS1⟩ := hn
        obtain ⟨hS2, hS3⟩ := abs_lt.1 hS1
        have hSpos : 0 < r n * SE n ω := by linarith
        have hSE0 : 0 < SE n ω := (pos_iff_pos_of_mul_pos hSpos).1 h3.1
        rw [abs_div, abs_of_pos hSE0, div_le_iff₀ hSE0] at hω
        have h4 : r n * |est n ω| ≤ M * (r n * SE n ω) := by
          nlinarith [mul_le_mul_of_nonneg_left hω h3.1.le]
        have h5 : M * (r n * SE n ω) ≤ |M| * (2 * c) :=
          (mul_le_mul_of_nonneg_right (le_abs_self M) hSpos.le).trans
            (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg M))
        have h6 : |r n * ω₀| ≤ |r n * est n ω| + |r n * (est n ω - ω₀)| := by
          have := abs_sub (r n * est n ω) (r n * (est n ω - ω₀))
          rwa [show r n * est n ω - r n * (est n ω - ω₀) = r n * ω₀ by ring] at this
        rw [abs_mul, abs_mul, abs_of_pos h3.1] at h6
        nlinarith
    _ ≤ ε / 2 + ε / 2 := (measure_union_le _ _).trans (add_le_add h1 h2)
    _ = ε := ENNReal.add_halves ε

/-- **The test is consistent.** Under the hypotheses of `tendsto_measure_abs_div_le_of_ne_zero`,
the test that rejects when `|est_n / SE_n| > z` rejects with probability tending to one, for
every critical value `z`. -/
theorem tendsto_measure_lt_abs_div_of_ne_zero {est SE : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) {ω₀ : ℝ} (hω : ω₀ ≠ 0) {Z : Ω' → ℝ}
    (hT : TendstoInDistribution (fun n ω => r n * (est n ω - ω₀)) atTop Z (fun _ => μ) P')
    {c : ℝ} (hc : 0 < c) (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop (fun _ => c))
    (z : ℝ) : Tendsto (fun n => μ {ω | z < |est n ω / SE n ω|}) atTop (𝓝 1) := by
  have h0 := tendsto_measure_abs_div_le_of_ne_zero hr hω hT hc hSE z
  have hlow : Tendsto (fun n => 1 - μ {ω | |est n ω / SE n ω| ≤ z}) atTop (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h0 (Or.inl ENNReal.one_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => prob_le_one)
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = μ univ := measure_univ.symm
    _ ≤ μ ({ω | z < |est n ω / SE n ω|} ∪ {ω | |est n ω / SE n ω| ≤ z}) := by
        refine measure_mono fun ω _ => ?_
        simp only [mem_union, mem_ofPred_eq]
        exact lt_or_ge z _ |>.imp id id
    _ ≤ _ := measure_union_le _ _

/-- **The limiting level of the two sided test.** If `T_n → N(0, 1)` in distribution and
`z ≥ 0`, then `P(|T_n| > z) → 2 (1 - Φ(z))`, with `Φ` the standard normal distribution
function. -/
theorem tendsto_measureReal_lt_abs_of_tendstoInDistribution {T : ℕ → Ω → ℝ}
    (h : TendstoInDistribution T atTop (fun x => x) (fun _ => μ) (gaussianReal 0 1)) {z : ℝ}
    (hz : 0 ≤ z) :
    Tendsto (fun n => μ.real {ω | z < |T n ω|}) atTop
      (𝓝 (2 * (1 - cdf (gaussianReal 0 1) z))) := by
  set E : Set ℝ := {x | z < |x|} with hE
  have hEo : IsOpen E := isOpen_lt continuous_const continuous_abs
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => x) = gaussianReal 0 1 := Measure.map_id
  have hnull : (gaussianReal 0 1).map (fun x : ℝ => x) (frontier E) = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (one_ne_zero (α := ℝ≥0))
    rw [hmap]
    refine measure_mono_null (frontier_lt_subset_eq continuous_const continuous_abs) ?_
    refine measure_mono_null (t := {z, -z}) ?_ ((Set.toFinite _).measure_zero _)
    intro x hx
    simp only [mem_ofPred_eq] at hx
    rcases abs_eq hz |>.1 hx.symm with h | h <;> simp [h]
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto
    (E := E) hnull
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hlimval : ((gaussianReal 0 1).map (fun x : ℝ => x) E).toReal =
      2 * (1 - cdf (gaussianReal 0 1) z) := by
    have hEc : E = (Icc (-z) z)ᶜ := by
      ext x
      simp only [hE, mem_ofPred_eq, mem_compl_iff, mem_Icc, not_and_or, not_le, lt_abs]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (by linarith)
      · rintro (h | h)
        · exact Or.inr (by linarith)
        · exact Or.inl h
    rw [hmap, hEc, ← measureReal_def, probReal_compl_eq_one_sub measurableSet_Icc,
      gaussianReal_real_Icc_neg_self (α := 2 * (1 - cdf (gaussianReal 0 1) z)) hz (by ring)]
    ring
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  rw [hlimval] at hreal
  refine hreal.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hEo.measurableSet,
    measureReal_def]
  rfl

end General

/-! ### Three independent comparisons -/

section Triangle

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The limit law of the inconsistency estimate from three independent comparisons**.
Let the estimates `Y n 0, Y n 1, Y n 2` of the
comparisons `a → b`, `a → c`, `b → c` be mutually independent for each `n`, with
`r_n (Y n i - d i) → N(0, v i)` in distribution for each `i`. Then
`r_n (ω̂_n - ω₀) → N(0, v 0 + v 1 + v 2)` in distribution, where
`ω̂_n = Y n 0 - (Y n 1 - Y n 2)` and `ω₀ = d 0 - (d 1 - d 2)`. -/
theorem tendstoInDistribution_inconsistencyEstimate_of_iIndepFun {Y : ℕ → Fin 3 → Ω → ℝ}
    (hind : ∀ n, iIndepFun (Y n) μ) {d : Fin 3 → ℝ} {v : Fin 3 → ℝ≥0} {r : ℕ → ℝ}
    (hlim : ∀ i, TendstoInDistribution (fun n ω => r n * (Y n i ω - d i)) atTop (fun x => x)
      (fun _ => μ) (gaussianReal 0 (v i))) :
    TendstoInDistribution (fun n ω => r n *
        (inconsistencyEstimate (Y n 0) (Y n 1) (Y n 2) ω - (d 0 - (d 1 - d 2)))) atTop
      (fun x => x) (fun _ => μ) (gaussianReal 0 (v 0 + v 1 + v 2)) := by
  set W : ℕ → Fin 3 → Ω → ℝ := fun n i ω => r n * (Y n i ω - d i) with hW
  have hWind : ∀ n, iIndepFun (W n) μ := fun n =>
    (hind n).comp (fun i x => r n * (x - d i)) (fun i => by fun_prop)
  have hWm : ∀ n i, AEMeasurable (W n i) μ := fun n i => (hlim i).forall_aemeasurable n
  have hneg : TendstoInDistribution (fun n ω => -W n 1 ω) atTop (fun x => x) (fun _ => μ)
      (gaussianReal 0 (v 1)) := by
    have h := (hlim 1).continuous_comp continuous_neg
    refine h.of_hasLaw (ν := gaussianReal 0 (v 1)) ⟨by fun_prop, ?_⟩ HasLaw.id
    have := gaussianReal_map_neg (μ := (0 : ℝ)) (v := v 1)
    rw [neg_zero] at this
    exact this
  have hI : TendstoInDistribution (fun n ω => -W n 1 ω + W n 2 ω) atTop (fun x => x)
      (fun _ => μ) (gaussianReal 0 (v 1 + v 2)) :=
    tendstoInDistribution_add_of_indepFun hneg (hlim 2)
      (fun n => ((hWind n).indepFun (show (1 : Fin 3) ≠ 2 by decide)).comp measurable_neg
        measurable_id) HasLaw.id HasLaw.id HasLaw.id
  have hJ : TendstoInDistribution (fun n ω => W n 0 ω + (-W n 1 ω + W n 2 ω)) atTop
      (fun x => x) (fun _ => μ) (gaussianReal 0 (v 0 + (v 1 + v 2))) := by
    refine tendstoInDistribution_add_of_indepFun (hlim 0) hI (fun n => ?_) HasLaw.id
      HasLaw.id HasLaw.id
    have hpair := (hWind n).indepFun_prodMk₀ (hWm n) 1 2 0 (by decide) (by decide)
    exact (hpair.comp (φ := fun q : ℝ × ℝ => -q.1 + q.2) (ψ := id) (by fun_prop)
      measurable_id).symm
  rw [show v 0 + (v 1 + v 2) = v 0 + v 1 + v 2 from (add_assoc _ _ _).symm] at hJ
  refine TendstoInDistribution.congr (fun n => ae_of_all _ fun ω => ?_) EventuallyEq.rfl hJ
  simp only [hW, inconsistencyEstimate, indirectEstimate]
  ring

/-- **The standardized node split statistic is asymptotically standard normal.** Under the
hypotheses of `tendstoInDistribution_inconsistencyEstimate_of_iIndepFun`, with
`v = v 0 + v 1 + v 2 > 0`, rates eventually nonzero, a ratio consistent standard error,
`r_n SE_n → √v` in probability, and almost everywhere measurable estimates and standard errors,
`(ω̂_n - ω₀) / SE_n → N(0, 1)` in distribution. -/
theorem tendstoInDistribution_inconsistencyEstimate_sub_div {Y : ℕ → Fin 3 → Ω → ℝ}
    (hind : ∀ n, iIndepFun (Y n) μ) {d : Fin 3 → ℝ} {v : Fin 3 → ℝ≥0} {r : ℕ → ℝ}
    (hlim : ∀ i, TendstoInDistribution (fun n ω => r n * (Y n i ω - d i)) atTop (fun x => x)
      (fun _ => μ) (gaussianReal 0 (v i)))
    (hr : ∀ᶠ n in atTop, r n ≠ 0) (hv : 0 < v 0 + v 1 + v 2) {SE : ℕ → Ω → ℝ}
    (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop
      (fun _ => √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)))
    (hYm : ∀ n i, AEMeasurable (Y n i) μ) (hSEm : ∀ n, AEMeasurable (SE n) μ) :
    TendstoInDistribution (fun n ω =>
        (inconsistencyEstimate (Y n 0) (Y n 1) (Y n 2) ω - (d 0 - (d 1 - d 2))) / SE n ω) atTop
      (fun x => x) (fun _ => μ) (gaussianReal 0 1) := by
  set s := √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) with hs
  have hvR : (0 : ℝ) < ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) := by exact_mod_cast hv
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hvR).ne'
  have hA := tendstoInDistribution_inconsistencyEstimate_of_iIndepFun hind hlim
  have key := hA.div_tendstoInMeasure_const hs0 hSE fun n => (hSEm n).const_mul _
  have hlaw : HasLaw (fun x : ℝ => x / s) (gaussianReal 0 1)
      (gaussianReal 0 (v 0 + v 1 + v 2)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_div_const s, zero_div]
    congr 1
    ext
    rw [NNReal.coe_div, NNReal.coe_mk, hs, Real.sq_sqrt hvR.le, div_self hvR.ne', NNReal.coe_one]
  have key2 := key.of_hasLaw hlaw HasLaw.id
  refine tendstoInDistribution_congr_of_eventuallyEq key2
    (hr.mono fun n hn => funext fun ω => mul_div_mul_left _ _ hn) fun n => ?_
  have h0 := hYm n 0
  have h1 := hYm n 1
  have h2 := hYm n 2
  simp only [inconsistencyEstimate, indirectEstimate]
  exact ((h0.sub (h1.sub h2)).sub_const _).div (hSEm n)

/-- **Under consistency the node split statistic is asymptotically standard normal**.
Under the hypotheses of `tendstoInDistribution_inconsistencyEstimate_sub_div`
and consistency, `d 0 = d 1 - d 2`, the statistic `ω̂_n / SE_n` converges in distribution to
`N(0, 1)`. -/
theorem tendstoInDistribution_inconsistencyEstimate_div {Y : ℕ → Fin 3 → Ω → ℝ}
    (hind : ∀ n, iIndepFun (Y n) μ) {d : Fin 3 → ℝ} {v : Fin 3 → ℝ≥0} {r : ℕ → ℝ}
    (hlim : ∀ i, TendstoInDistribution (fun n ω => r n * (Y n i ω - d i)) atTop (fun x => x)
      (fun _ => μ) (gaussianReal 0 (v i)))
    (hr : ∀ᶠ n in atTop, r n ≠ 0) (hv : 0 < v 0 + v 1 + v 2) {SE : ℕ → Ω → ℝ}
    (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop
      (fun _ => √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)))
    (hYm : ∀ n i, AEMeasurable (Y n i) μ) (hSEm : ∀ n, AEMeasurable (SE n) μ)
    (hcons : d 0 = d 1 - d 2) :
    TendstoInDistribution (fun n ω => inconsistencyEstimate (Y n 0) (Y n 1) (Y n 2) ω / SE n ω)
      atTop (fun x => x) (fun _ => μ) (gaussianReal 0 1) := by
  have h := tendstoInDistribution_inconsistencyEstimate_sub_div hind hlim hr hv hSE hYm hSEm
  rw [hcons, sub_self] at h
  simpa only [sub_zero] using h

/-- **The node split test is consistent**. Under the hypotheses of
`tendstoInDistribution_inconsistencyEstimate_of_iIndepFun`, a rate `r_n → ∞`,
`v = v 0 + v 1 + v 2 > 0`, a ratio consistent standard error `r_n SE_n → √v`, and
inconsistency, `ω₀ = d 0 - (d 1 - d 2) ≠ 0`, the statistic `|ω̂_n / SE_n|` tends to infinity in
probability: `P(|ω̂_n / SE_n| ≤ M) → 0` for every `M`. -/
theorem tendsto_measure_abs_inconsistencyEstimate_div_le {Y : ℕ → Fin 3 → Ω → ℝ}
    (hind : ∀ n, iIndepFun (Y n) μ) {d : Fin 3 → ℝ} {v : Fin 3 → ℝ≥0} {r : ℕ → ℝ}
    (hlim : ∀ i, TendstoInDistribution (fun n ω => r n * (Y n i ω - d i)) atTop (fun x => x)
      (fun _ => μ) (gaussianReal 0 (v i)))
    (hr : Tendsto r atTop atTop) (hv : 0 < v 0 + v 1 + v 2) {SE : ℕ → Ω → ℝ}
    (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop
      (fun _ => √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)))
    (hincons : d 0 - (d 1 - d 2) ≠ 0) (M : ℝ) :
    Tendsto (fun n => μ {ω | |inconsistencyEstimate (Y n 0) (Y n 1) (Y n 2) ω / SE n ω| ≤ M})
      atTop (𝓝 0) := by
  have hvR : (0 : ℝ) < ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) := by exact_mod_cast hv
  exact tendsto_measure_abs_div_le_of_ne_zero hr hincons
    (tendstoInDistribution_inconsistencyEstimate_of_iIndepFun hind hlim)
    (Real.sqrt_pos.2 hvR) hSE M

/-- **Under inconsistency the node split test rejects with probability tending to one**, at
every critical value `z`, under the hypotheses of
`tendsto_measure_abs_inconsistencyEstimate_div_le`. -/
theorem tendsto_measure_lt_abs_inconsistencyEstimate_div {Y : ℕ → Fin 3 → Ω → ℝ}
    (hind : ∀ n, iIndepFun (Y n) μ) {d : Fin 3 → ℝ} {v : Fin 3 → ℝ≥0} {r : ℕ → ℝ}
    (hlim : ∀ i, TendstoInDistribution (fun n ω => r n * (Y n i ω - d i)) atTop (fun x => x)
      (fun _ => μ) (gaussianReal 0 (v i)))
    (hr : Tendsto r atTop atTop) (hv : 0 < v 0 + v 1 + v 2) {SE : ℕ → Ω → ℝ}
    (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop
      (fun _ => √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)))
    (hincons : d 0 - (d 1 - d 2) ≠ 0) (z : ℝ) :
    Tendsto (fun n => μ {ω | z < |inconsistencyEstimate (Y n 0) (Y n 1) (Y n 2) ω / SE n ω|})
      atTop (𝓝 1) := by
  have hvR : (0 : ℝ) < ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) := by exact_mod_cast hv
  exact tendsto_measure_lt_abs_div_of_ne_zero hr hincons
    (tendstoInDistribution_inconsistencyEstimate_of_iIndepFun hind hlim)
    (Real.sqrt_pos.2 hvR) hSE z

/-- **The limiting level of the node split test**. Under the hypotheses of
`tendstoInDistribution_inconsistencyEstimate_div` (in particular consistency,
`d 0 = d 1 - d 2`), the test that rejects when `|ω̂_n / SE_n| > z`, with `z ≥ 0`, has rejection
probability tending to `2 (1 - Φ(z))`. -/
theorem tendsto_measureReal_lt_abs_inconsistencyEstimate_div {Y : ℕ → Fin 3 → Ω → ℝ}
    (hind : ∀ n, iIndepFun (Y n) μ) {d : Fin 3 → ℝ} {v : Fin 3 → ℝ≥0} {r : ℕ → ℝ}
    (hlim : ∀ i, TendstoInDistribution (fun n ω => r n * (Y n i ω - d i)) atTop (fun x => x)
      (fun _ => μ) (gaussianReal 0 (v i)))
    (hr : ∀ᶠ n in atTop, r n ≠ 0) (hv : 0 < v 0 + v 1 + v 2) {SE : ℕ → Ω → ℝ}
    (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop
      (fun _ => √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)))
    (hYm : ∀ n i, AEMeasurable (Y n i) μ) (hSEm : ∀ n, AEMeasurable (SE n) μ)
    (hcons : d 0 = d 1 - d 2) {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun n => μ.real
        {ω | z < |inconsistencyEstimate (Y n 0) (Y n 1) (Y n 2) ω / SE n ω|}) atTop
      (𝓝 (2 * (1 - cdf (gaussianReal 0 1) z))) :=
  tendsto_measureReal_lt_abs_of_tendstoInDistribution
    (tendstoInDistribution_inconsistencyEstimate_div hind hlim hr hv hSE hYm hSEm hcons) hz

end Triangle

/-! ### Exact normal data -/

section Instance

/-- The product of three standard normal laws, the law of the standardized errors. -/
noncomputable abbrev nodeSplitNoise : Measure (Fin 3 → ℝ) :=
  Measure.pi fun _ : Fin 3 => gaussianReal 0 1

/-- **Exact normal comparison estimates at sample size `n + 1`**:
`y_i,n = d i + √(v i / (n + 1)) ξ_i` with independent standard normal `ξ_i`, so that
`y_i,n ∼ N(d i, v i / (n + 1))`. -/
noncomputable def nodeSplitSample (d : Fin 3 → ℝ) (v : Fin 3 → ℝ≥0) (n : ℕ) (i : Fin 3)
    (ξ : Fin 3 → ℝ) : ℝ :=
  d i + √((v i : ℝ) / (n + 1)) * ξ i

/-- The **standard error** `√((v 0 + v 1 + v 2) / (n + 1))` of the inconsistency estimate of
`nodeSplitSample`. -/
noncomputable def nodeSplitSE (v : Fin 3 → ℝ≥0) (n : ℕ) (_ξ : Fin 3 → ℝ) : ℝ :=
  √(((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) / (n + 1))

/-- `√(n + 1) √(x / (n + 1)) = √x`: the rate cancels the scale of the standard error. -/
theorem sqrt_succ_mul_sqrt_div (n : ℕ) (x : ℝ) :
    √((n : ℝ) + 1) * √(x / (n + 1)) = √x := by
  rw [← Real.sqrt_mul (by positivity), mul_div_cancel₀ _ (by positivity)]

/-- **Exact normal data satisfy every hypothesis.** For `nodeSplitSample` under
`nodeSplitNoise`, the rate `√(n + 1)` and the standard error `nodeSplitSE`, with
`v 0 + v 1 + v 2 > 0`: the estimates have the laws `N(d i, v i / (n + 1))` and are independent
for each `n`; `√(n + 1) (ω̂_n - ω₀) → N(0, v 0 + v 1 + v 2)`; under consistency
`ω̂_n / SE_n → N(0, 1)` and the test at `z ≥ 0` has limiting level `2 (1 - Φ(z))`; under
inconsistency `P(|ω̂_n / SE_n| ≤ M) → 0` for every `M` and the test rejects with probability
tending to one at every `z`. -/
theorem nodeSplitSample_limits (d : Fin 3 → ℝ) {v : Fin 3 → ℝ≥0} (hv : 0 < v 0 + v 1 + v 2) :
    (∀ (n : ℕ) i, HasLaw (nodeSplitSample d v n i)
        (gaussianReal (d i) (v i / ((n : ℝ≥0) + 1))) nodeSplitNoise) ∧
      (∀ n, iIndepFun (nodeSplitSample d v n) nodeSplitNoise) ∧
      TendstoInDistribution (fun (n : ℕ) ξ => √((n : ℝ) + 1) *
          (inconsistencyEstimate (nodeSplitSample d v n 0) (nodeSplitSample d v n 1)
            (nodeSplitSample d v n 2) ξ - (d 0 - (d 1 - d 2)))) atTop
        (fun x => x) (fun _ => nodeSplitNoise) (gaussianReal 0 (v 0 + v 1 + v 2)) ∧
      (d 0 = d 1 - d 2 →
        TendstoInDistribution (fun n ξ => inconsistencyEstimate (nodeSplitSample d v n 0)
            (nodeSplitSample d v n 1) (nodeSplitSample d v n 2) ξ / nodeSplitSE v n ξ) atTop
          (fun x => x) (fun _ => nodeSplitNoise) (gaussianReal 0 1) ∧
        ∀ z : ℝ, 0 ≤ z → Tendsto (fun n => nodeSplitNoise.real {ξ | z <
            |inconsistencyEstimate (nodeSplitSample d v n 0) (nodeSplitSample d v n 1)
              (nodeSplitSample d v n 2) ξ / nodeSplitSE v n ξ|}) atTop
          (𝓝 (2 * (1 - cdf (gaussianReal 0 1) z)))) ∧
      (d 0 - (d 1 - d 2) ≠ 0 → (∀ M : ℝ, Tendsto (fun n => nodeSplitNoise {ξ |
          |inconsistencyEstimate (nodeSplitSample d v n 0) (nodeSplitSample d v n 1)
            (nodeSplitSample d v n 2) ξ / nodeSplitSE v n ξ| ≤ M}) atTop (𝓝 0)) ∧
        ∀ z : ℝ, Tendsto (fun n => nodeSplitNoise {ξ | z <
          |inconsistencyEstimate (nodeSplitSample d v n 0) (nodeSplitSample d v n 1)
            (nodeSplitSample d v n 2) ξ / nodeSplitSE v n ξ|}) atTop (𝓝 1)) := by
  set r : ℕ → ℝ := fun n => √((n : ℝ) + 1) with hr
  have hcoord : ∀ i : Fin 3, HasLaw (fun ξ : Fin 3 → ℝ => ξ i) (gaussianReal 0 1)
      nodeSplitNoise := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hsample : ∀ n i, Measurable (nodeSplitSample d v n i) := fun n i => by
    unfold nodeSplitSample
    fun_prop
  -- the laws
  have hlaw : ∀ (n : ℕ) i, HasLaw (nodeSplitSample d v n i)
      (gaussianReal (d i) (v i / ((n : ℝ≥0) + 1))) nodeSplitNoise := fun n i => by
    have h := gaussianReal_const_add (gaussianReal_const_mul (hcoord i)
      (√((v i : ℝ) / (n + 1)))) (d i)
    convert h using 2 with ξ
    · rfl
    all_goals first
      | (apply NNReal.eq
         simp only [mul_one, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
           NNReal.coe_one]
         rw [Real.sq_sqrt (by positivity)])
      | ring
  -- independence
  have hind : ∀ n, iIndepFun (nodeSplitSample d v n) nodeSplitNoise := fun n =>
    iIndepFun_pi (X := fun i (x : ℝ) => d i + √((v i : ℝ) / (n + 1)) * x)
      (fun i => by fun_prop)
  -- the marginal limits: the scaled errors do not depend on `n`
  have hscaled : ∀ n i, (fun ξ => r n * (nodeSplitSample d v n i ξ - d i)) =
      fun ξ : Fin 3 → ℝ => √(v i : ℝ) * ξ i := fun n i => by
    funext ξ
    simp only [hr, nodeSplitSample, add_sub_cancel_left, ← mul_assoc,
      sqrt_succ_mul_sqrt_div n _]
  have hlim : ∀ i, TendstoInDistribution (fun n ξ => r n * (nodeSplitSample d v n i ξ - d i))
      atTop (fun x => x) (fun _ => nodeSplitNoise) (gaussianReal 0 (v i)) := fun i => by
    have hc : HasLaw (fun ξ : Fin 3 → ℝ => √(v i : ℝ) * ξ i) (gaussianReal 0 (v i))
        nodeSplitNoise := by
      have h := gaussianReal_const_mul (hcoord i) (√(v i : ℝ))
      convert h using 2
      · ring
      · ext
        simp only [NNReal.coe_mk, mul_one]
        rw [Real.sq_sqrt (NNReal.coe_nonneg _)]
    have h0 := (tendstoInDistribution_const (l := atTop) hc.aemeasurable).of_hasLaw hc
      HasLaw.id
    exact TendstoInDistribution.congr (fun n => by rw [hscaled n i]) EventuallyEq.rfl h0
  -- the standard error
  have hvR : (0 : ℝ) < ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) := by exact_mod_cast hv
  have hSE : TendstoInMeasure nodeSplitNoise (fun n ξ => r n * nodeSplitSE v n ξ) atTop
      (fun _ => √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)) := by
    have e : (fun n ξ => r n * nodeSplitSE v n ξ) =
        fun (_ : ℕ) (_ : Fin 3 → ℝ) => √((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) := by
      funext n ξ
      simp only [hr, nodeSplitSE, sqrt_succ_mul_sqrt_div n _]
    rw [e, tendstoInMeasure_iff_dist]
    intro ε hε
    simp only [dist_self, not_le.2 hε, ofPred_false, measure_empty]
    exact tendsto_const_nhds
  have hrne : ∀ᶠ n in atTop, r n ≠ 0 :=
    Eventually.of_forall fun n => (Real.sqrt_pos.2 (by positivity)).ne'
  have hrtop : Tendsto r atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hYm : ∀ n i, AEMeasurable (nodeSplitSample d v n i) nodeSplitNoise :=
    fun n i => (hsample n i).aemeasurable
  have hSEm : ∀ n, AEMeasurable (nodeSplitSE v n) nodeSplitNoise :=
    fun n => aemeasurable_const
  refine ⟨hlaw, hind, tendstoInDistribution_inconsistencyEstimate_of_iIndepFun hind hlim,
    fun hcons => ⟨tendstoInDistribution_inconsistencyEstimate_div hind hlim hrne hv hSE hYm hSEm
      hcons, fun z hz => tendsto_measureReal_lt_abs_inconsistencyEstimate_div hind hlim hrne hv
      hSE hYm hSEm hcons hz⟩,
    fun hincons => ⟨fun M => tendsto_measure_abs_inconsistencyEstimate_div_le hind hlim hrtop hv
      hSE hincons M, fun z => tendsto_measure_lt_abs_inconsistencyEstimate_div hind hlim hrtop hv
      hSE hincons z⟩⟩

/-- **Concrete instances**: with unit variances, the effects `(1, 3, 2)` are consistent and the
node split statistic is asymptotically standard normal, with limiting level `2 (1 - Φ(z))`;
the effects `(2, 3, 2)` have inconsistency `1` and the statistic diverges in probability. -/
theorem nodeSplitSample_example :
    TendstoInDistribution (fun n ξ => inconsistencyEstimate (nodeSplitSample ![1, 3, 2] 1 n 0)
        (nodeSplitSample ![1, 3, 2] 1 n 1) (nodeSplitSample ![1, 3, 2] 1 n 2) ξ /
          nodeSplitSE 1 n ξ) atTop
      (fun x => x) (fun _ => nodeSplitNoise) (gaussianReal 0 1) ∧
      ∀ M : ℝ, Tendsto (fun n => nodeSplitNoise {ξ |
        |inconsistencyEstimate (nodeSplitSample ![2, 3, 2] 1 n 0)
          (nodeSplitSample ![2, 3, 2] 1 n 1) (nodeSplitSample ![2, 3, 2] 1 n 2) ξ /
            nodeSplitSE 1 n ξ| ≤ M}) atTop (𝓝 0) := by
  have hv : (0 : ℝ≥0) < (1 : Fin 3 → ℝ≥0) 0 + (1 : Fin 3 → ℝ≥0) 1 + (1 : Fin 3 → ℝ≥0) 2 := by
    simp
  refine ⟨((nodeSplitSample_limits ![1, 3, 2] hv).2.2.2.1 (by norm_num)).1,
    ((nodeSplitSample_limits ![2, 3, 2] hv).2.2.2.2 (by norm_num)).1⟩

end Instance

end NetworkMetaAnalysis

end CausalInference
