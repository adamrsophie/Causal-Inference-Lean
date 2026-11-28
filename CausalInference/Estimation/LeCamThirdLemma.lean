/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LimitLaws
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Le Cam's third lemma and joint limits along subsequences

Le Cam's third lemma computes the limit law of a statistic under a sequence of alternatives from
its joint limit law with the log likelihood ratio under the null. This file proves it in change
of measure form, together with the extraction of joint limits from convergent marginals
(Prokhorov's theorem), which is how the lemma is used for regular estimators.

A limit law is written as a probability measure `μ` and convergence in distribution to it as
`TendstoInDistribution X atTop id (fun _ ↦ P) μ` (the identity variable on `(E, μ)`).

## Main results

* `CausalInference.le_liminf_lintegral_of_tendstoInDistribution`: the portmanteau lower bound
  `∫ g dμ ≤ liminf E g(Y_n)` for a nonnegative continuous, possibly unbounded, `g`, from
  Mathlib's portmanteau theorem.
* `CausalInference.lecam_third_lemma`: if `(X_n, L_n)` converges in distribution under `P` to
  `μ` with `∫ e^ℓ dμ(x, ℓ) = 1`, and measures `ν_n` of mass at most one dominate `e^{L_n} dP` on
  functions of `X_n`, then `∫ f dν_n → ∫ f(x) e^ℓ dμ(x, ℓ)` for every bounded continuous `f`.
  No contiguity or uniform integrability hypothesis is needed: the limit already has mass one,
  so the lower bounds for `f + ‖f‖` and `‖f‖ - f` squeeze `∫ f dν_n`.
* `CausalInference.exists_subseq_tendstoInDistribution_prodMk`: if `X_n → μ₁` and `Y_n → μ₂` in
  distribution on Polish spaces, some subsequence of `(X_n, Y_n)` converges in distribution to a
  probability measure with marginals `μ₁` and `μ₂`.
* `CausalInference.tendstoInMeasure_of_tendstoInDistribution_dirac`: convergence in distribution
  to the point mass at `0` is convergence in probability to `0`.

The instances in which every hypothesis is checked are in
`CausalInference.Estimation.HajekConvolutionExamples`.

References: L. Le Cam (1960), *Locally asymptotically normal families of distributions*,
University of California Publications in Statistics; Yu. V. Prokhorov (1956), *Convergence of
random processes and limit theorems in probability theory*, Theory of Probability and its
Applications; A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Le Cam's third lemma -/

section LeCam

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [TopologicalSpace.PseudoMetrizableSpace E]

/-- **Portmanteau lower bound for a nonnegative continuous function.** If `Y_n → μ` in
distribution and `g ≥ 0` is continuous, possibly unbounded, then `∫ g dμ ≤ liminf E g(Y_n)`.
This is Mathlib's portmanteau bound for open sets
(`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) fed into its layer cake form
(`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`), read through the
laws of the `Y_n`. -/
theorem le_liminf_lintegral_of_tendstoInDistribution {Y : ℕ → Ω → E} {μ : Measure E}
    [IsProbabilityMeasure μ] (h : TendstoInDistribution Y atTop id (fun _ ↦ P) μ) {g : E → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (g (Y n ω)) ∂P) atTop := by
  have hmap : ∀ n, ∫⁻ x, ENNReal.ofReal (g x) ∂(P.map (Y n)) =
      ∫⁻ ω, ENNReal.ofReal (g (Y n ω)) ∂P := fun n ↦
    lintegral_map' hg.measurable.ennreal_ofReal.aemeasurable (h.forall_aemeasurable n)
  have key := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := μ) (μs := fun n ↦ P.map (Y n)) hg (fun x ↦ hg0 x) fun G hG ↦ by
      simpa using ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hG
  simpa only [hmap] using key

/-- **The lower half of Le Cam's third lemma.** If `(X_n, L_n) → μ` in distribution under `P`,
`∫ e^ℓ dμ = 1`, and the measures `ν_n` (eventually of mass at most one) dominate `e^{L_n} dP` on
functions of `X_n`, then for every bounded continuous `g ≥ 0` and `ε > 0`, eventually
`∫ g(x) e^ℓ dμ - ε < ∫ g dν_n`. The proof applies
`CausalInference.le_liminf_lintegral_of_tendstoInDistribution` to `(x, ℓ) ↦ g(x) e^ℓ`. -/
theorem lecam_eventually_lt {X : ℕ → Ω → E} {L : ℕ → Ω → ℝ} {μ : Measure (E × ℝ)}
    [IsProbabilityMeasure μ]
    (hjoint : TendstoInDistribution (fun n ω ↦ (X n ω, L n ω)) atTop id (fun _ ↦ P) μ)
    (hmass : ∫ p, Real.exp p.2 ∂μ = 1) {ν : ℕ → Measure E}
    (hν1 : ∀ᶠ n in atTop, ν n univ ≤ 1)
    (hdom : ∀ᶠ n in atTop, ∀ g : E → ℝ≥0∞, Measurable g →
      ∫⁻ ω, g (X n ω) * ENNReal.ofReal (Real.exp (L n ω)) ∂P ≤ ∫⁻ x, g x ∂ν n)
    (g : E →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∫ p, g p.1 * Real.exp p.2 ∂μ - ε < ∫ x, g x ∂ν n := by
  have hint : Integrable (fun p : E × ℝ ↦ Real.exp p.2) μ :=
    Integrable.of_integral_ne_zero (by rw [hmass]; exact one_ne_zero)
  set G : E × ℝ → ℝ := fun p ↦ g p.1 * Real.exp p.2 with hGdef
  have hG0 : ∀ p, 0 ≤ G p := fun p ↦ mul_nonneg (hg0 _) (Real.exp_pos _).le
  have hGc : Continuous G := (g.continuous.comp continuous_fst).mul
    (Real.continuous_exp.comp continuous_snd)
  have hGi : Integrable G μ := by
    refine (hint.const_mul ‖g‖).mono' hGc.aestronglyMeasurable (Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 p)]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm p.1)) (Real.exp_pos _).le
  have h1 := le_liminf_lintegral_of_tendstoInDistribution hjoint hGc hG0
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hG0)] at h1
  by_cases hr : ∫ p, G p ∂μ - ε < 0
  · exact Eventually.of_forall fun n ↦ hr.trans_le (integral_nonneg hg0)
  have hr' : 0 ≤ ∫ p, G p ∂μ - ε := not_lt.1 hr
  have hlt : ENNReal.ofReal (∫ p, G p ∂μ - ε) < ENNReal.ofReal (∫ p, G p ∂μ) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr').2 (by linarith)
  have hev := eventually_lt_of_lt_liminf (hlt.trans_le h1)
  filter_upwards [hev, hν1, hdom] with n hn h1n hdn
  have : IsFiniteMeasure (ν n) := ⟨h1n.trans_lt ENNReal.one_lt_top⟩
  have hle : ∫⁻ ω, ENNReal.ofReal (G (X n ω, L n ω)) ∂P ≤ ENNReal.ofReal (∫ x, g x ∂ν n) := by
    rw [ofReal_integral_eq_lintegral_ofReal (g.integrable _) (Eventually.of_forall hg0)]
    refine le_trans (le_of_eq ?_) (hdn (fun x ↦ ENNReal.ofReal (g x))
      g.continuous.measurable.ennreal_ofReal)
    congr 1
    funext ω
    simp only [hGdef]
    rw [ENNReal.ofReal_mul (hg0 _)]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr').1 (hn.trans_le hle)

/-- **Le Cam's third lemma, change of measure form.** Let `(X_n, L_n) → μ` in distribution under
`P`, with `∫ e^ℓ dμ(x, ℓ) = 1`, and let `ν_n` be measures, eventually of mass at most one, with
`∫ g(X_n) e^{L_n} dP ≤ ∫ g dν_n` for every measurable `g ≥ 0` (for instance the law of `X_n` under
an alternative whose density relative to `P` on `σ(X_n)` is at least `e^{L_n}`). Then for every
bounded continuous `f`, `∫ f dν_n → ∫ f(x) e^ℓ dμ(x, ℓ)`: the laws `ν_n` converge weakly to the
exponential tilt of the first marginal of `μ`. -/
theorem lecam_third_lemma {X : ℕ → Ω → E} {L : ℕ → Ω → ℝ} {μ : Measure (E × ℝ)}
    [IsProbabilityMeasure μ]
    (hjoint : TendstoInDistribution (fun n ω ↦ (X n ω, L n ω)) atTop id (fun _ ↦ P) μ)
    (hmass : ∫ p, Real.exp p.2 ∂μ = 1) {ν : ℕ → Measure E}
    (hν1 : ∀ᶠ n in atTop, ν n univ ≤ 1)
    (hdom : ∀ᶠ n in atTop, ∀ g : E → ℝ≥0∞, Measurable g →
      ∫⁻ ω, g (X n ω) * ENNReal.ofReal (Real.exp (L n ω)) ∂P ≤ ∫⁻ x, g x ∂ν n)
    (f : E →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂ν n) atTop (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂μ)) := by
  have hint : Integrable (fun p : E × ℝ ↦ Real.exp p.2) μ :=
    Integrable.of_integral_ne_zero (by rw [hmass]; exact one_ne_zero)
  set c := ‖f‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg f
  have hfle : ∀ x, |f x| ≤ c := fun x ↦ by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
  have hfi : Integrable (fun p : E × ℝ ↦ f p.1 * Real.exp p.2) μ := by
    refine (hint.const_mul c).mono' ((f.continuous.comp continuous_fst).mul
      (Real.continuous_exp.comp continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hfle _) (Real.exp_pos _).le
  set β := ∫ p, f p.1 * Real.exp p.2 ∂μ with hβ
  let g₁ : E →ᵇ ℝ := f + BoundedContinuousFunction.const E c
  let g₂ : E →ᵇ ℝ := BoundedContinuousFunction.const E c - f
  let g₀ : E →ᵇ ℝ := BoundedContinuousFunction.const E 1
  have hg₁ : ∀ x, g₁ x = f x + c := fun x ↦ rfl
  have hg₂ : ∀ x, g₂ x = c - f x := fun x ↦ rfl
  have hg₀ : ∀ x, g₀ x = 1 := fun x ↦ rfl
  have h₁0 : ∀ x, 0 ≤ g₁ x := fun x ↦ by rw [hg₁]; linarith [(abs_le.1 (hfle x)).1]
  have h₂0 : ∀ x, 0 ≤ g₂ x := fun x ↦ by rw [hg₂]; linarith [(abs_le.1 (hfle x)).2]
  have h₀0 : ∀ x, 0 ≤ g₀ x := fun x ↦ by rw [hg₀]; exact zero_le_one
  have i₁ : ∫ p, g₁ p.1 * Real.exp p.2 ∂μ = β + c := by
    simp only [hg₁, add_mul]
    rw [integral_add hfi (hint.const_mul c), integral_const_mul, hmass, mul_one]
  have i₂ : ∫ p, g₂ p.1 * Real.exp p.2 ∂μ = c - β := by
    simp only [hg₂, sub_mul]
    rw [integral_sub (hint.const_mul c) hfi, integral_const_mul, hmass, mul_one]
  have i₀ : ∫ p, g₀ p.1 * Real.exp p.2 ∂μ = 1 := by simp only [hg₀, one_mul, hmass]
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set δ := ε / (2 * (2 + c)) with hδ
  have hδ0 : 0 < δ := by positivity
  filter_upwards [lecam_eventually_lt hjoint hmass hν1 hdom g₁ h₁0 hδ0,
    lecam_eventually_lt hjoint hmass hν1 hdom g₂ h₂0 hδ0,
    lecam_eventually_lt hjoint hmass hν1 hdom g₀ h₀0 hδ0, hν1] with n h1 h2 h0 hm
  have : IsFiniteMeasure (ν n) := ⟨hm.trans_lt ENNReal.one_lt_top⟩
  set m := (ν n).real univ with hmdef
  have hm1 : m ≤ 1 := by
    rw [hmdef, measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hm)
  have e₁ : ∫ x, g₁ x ∂ν n = ∫ x, f x ∂ν n + c * m := by
    simp only [hg₁]
    rw [integral_add (f.integrable _) (integrable_const c), integral_const, smul_eq_mul,
      mul_comm]
  have e₂ : ∫ x, g₂ x ∂ν n = c * m - ∫ x, f x ∂ν n := by
    simp only [hg₂]
    rw [integral_sub (integrable_const c) (f.integrable _), integral_const, smul_eq_mul,
      mul_comm]
  have e₀ : ∫ x, g₀ x ∂ν n = m := by
    simp only [hg₀]
    rw [integral_const, smul_eq_mul, mul_one]
  rw [i₁, e₁] at h1
  rw [i₂, e₂] at h2
  rw [i₀, e₀] at h0
  rw [Real.dist_eq, abs_lt]
  have hcm : c * (1 - m) ≤ c * δ := mul_le_mul_of_nonneg_left (by linarith) hc0
  have hδε : δ * (2 + c) < ε := by
    rw [hδ, div_mul_eq_mul_div, mul_comm 2 (2 + c), ← div_div, mul_div_assoc, div_self
      (by positivity : (2 + c : ℝ) ≠ 0), mul_one]
    linarith
  constructor <;> nlinarith

end LeCam

/-! ### Joint limits along subsequences -/

section Prokhorov

/-- **A sequence converging in distribution is tight.** The laws together with their limit form
a compact set of probability measures, and on a Polish space a set of probability measures with
compact closure is tight (`isTightMeasureSet_of_isCompact_closure`). -/
theorem _root_.MeasureTheory.TendstoInDistribution.isTightMeasureSet_range {E : Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] {X : ℕ → Ω → E} {μ : Measure E} [IsProbabilityMeasure μ]
    (h : TendstoInDistribution X atTop id (fun _ ↦ P) μ) :
    IsTightMeasureSet (range fun n ↦ P.map (X n)) := by
  have hc := h.tendsto.isCompact_insert_range
  have ht := isTightMeasureSet_of_isCompact_closure (by rwa [hc.isClosed.closure_eq])
  refine ht.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨_, mem_insert_of_mem _ ⟨n, rfl⟩, rfl⟩

/-- Convergence in distribution passes to reindexings `k ↦ X (N k)` with `N k → ∞`, in
particular to subsequences. -/
theorem _root_.MeasureTheory.TendstoInDistribution.comp_tendsto_atTop {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] {X : ℕ → Ω → E}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → E} (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) :
    TendstoInDistribution (fun k ↦ X (N k)) atTop Z (fun _ ↦ P) P' where
  forall_aemeasurable k := h.forall_aemeasurable (N k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hN

/-- The push forward of a subsequential limit of laws: if the laws `J_n` converge along `φ` to
`a`, and their images under a continuous `π` are the laws of `Z_n → ρ`, then `a.map π = ρ`. -/
theorem map_eq_of_tendsto_subseq {E G : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [T2Space (ProbabilityMeasure G)] (J : ℕ → ProbabilityMeasure E) {a : ProbabilityMeasure E}
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hlim : Tendsto (J ∘ φ) atTop (𝓝 a)) {π : E → G}
    (hπ : Continuous π) {Z : ℕ → Ω → G} {ρ : Measure G} [IsProbabilityMeasure ρ]
    (hZ : TendstoInDistribution Z atTop id (fun _ ↦ P) ρ)
    (he : ∀ n, (J n : Measure E).map π = P.map (Z n)) :
    (a : Measure E).map π = ρ := by
  have h1 := ((ProbabilityMeasure.continuous_map hπ).tendsto a).comp hlim
  have h2 := hZ.tendsto.comp hφ.tendsto_atTop
  have h1' : Tendsto (β := ProbabilityMeasure G) (fun k ↦ ⟨P.map (Z (φ k)),
      (Measure.isProbabilityMeasure_map_iff (hZ.forall_aemeasurable (φ k))).2 inferInstance⟩)
      atTop (𝓝 (a.map π)) := by
    refine h1.congr fun k ↦ ?_
    apply Subtype.ext
    simp only [Function.comp_apply]
    exact he (φ k)
  have := tendsto_nhds_unique h1' h2
  have e := congrArg (fun ν : ProbabilityMeasure G ↦ (ν : Measure G)) this
  simpa using e

/-- **Joint limits along a subsequence** (Prokhorov's theorem). If `X_n → μ₁` and `Y_n → μ₂` in
distribution on Polish spaces, some subsequence of `(X_n, Y_n)` converges in distribution to a
probability measure `μ` with marginals `μ₁` and `μ₂`. Both marginal families are tight, hence so
is the joint family; its closure is compact (`isCompact_closure_of_isTightMeasureSet`) in a
metrizable space; the marginals of the limit are identified by continuity of the push forward and
uniqueness of limits. -/
theorem exists_subseq_tendstoInDistribution_prodMk {E F : Type*} [MetricSpace E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F]
    [BorelSpace F] {X : ℕ → Ω → E} {Y : ℕ → Ω → F} {μ₁ : Measure E} {μ₂ : Measure F}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hX : TendstoInDistribution X atTop id (fun _ ↦ P) μ₁)
    (hY : TendstoInDistribution Y atTop id (fun _ ↦ P) μ₂) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : ProbabilityMeasure (E × F),
      TendstoInDistribution (fun k ω ↦ (X (φ k) ω, Y (φ k) ω)) atTop id (fun _ ↦ P)
        (μ : Measure (E × F)) ∧
      (μ : Measure (E × F)).map Prod.fst = μ₁ ∧ (μ : Measure (E × F)).map Prod.snd = μ₂ := by
  have hXm := hX.forall_aemeasurable
  have hYm := hY.forall_aemeasurable
  let J : ℕ → ProbabilityMeasure (E × F) := fun n ↦
    ⟨P.map (fun ω ↦ (X n ω, Y n ω)),
      (Measure.isProbabilityMeasure_map_iff ((hXm n).prodMk (hYm n))).2 inferInstance⟩
  have hJ : ∀ n, (J n : Measure (E × F)) = P.map (fun ω ↦ (X n ω, Y n ω)) := fun n ↦ rfl
  have htight : IsTightMeasureSet {((ν : ProbabilityMeasure (E × F)) : Measure (E × F)) |
      ν ∈ range J} := by
    refine IsTightMeasureSet.prodMk (hX.isTightMeasureSet_range.subset ?_)
      (hY.isTightMeasureSet_range.subset ?_)
    · rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨n, (Measure.fst_map_prodMk₀ (hXm n) (hYm n)).symm⟩
    · rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨n, (Measure.snd_map_prodMk₀ (hXm n) (hYm n)).symm⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
      (fun n ↦ subset_closure ⟨n, rfl⟩)
  refine ⟨φ, hφ, a, ⟨fun k ↦ (hXm (φ k)).prodMk (hYm (φ k)), aemeasurable_id, ?_⟩,
    map_eq_of_tendsto_subseq J hφ hlim continuous_fst hX fun n ↦ by
      rw [hJ, AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        ((hXm n).prodMk (hYm n))]
      rfl,
    map_eq_of_tendsto_subseq J hφ hlim continuous_snd hY fun n ↦ by
      rw [hJ, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        ((hXm n).prodMk (hYm n))]
      rfl⟩
  have e : (⟨(a : Measure (E × F)).map id, inferInstance⟩ : ProbabilityMeasure (E × F)) = a :=
    Subtype.ext (by simp)
  rw [e]
  exact hlim

end Prokhorov

/-- **Convergence in distribution to the point mass at `0` is convergence in probability to
`0`.** The portmanteau theorem for the closed set `{ε ≤ |y|}`, whose mass and boundary mass under
`δ₀` vanish. -/
theorem tendstoInMeasure_of_tendstoInDistribution_dirac {Y : ℕ → Ω → ℝ}
    (h : TendstoInDistribution Y atTop id (fun _ ↦ P) (Measure.dirac 0)) :
    TendstoInMeasure P Y atTop 0 := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set E : Set ℝ := {y | ε ≤ |y|} with hE
  have hEc : IsClosed E := isClosed_le continuous_const continuous_abs
  have h0 : Measure.dirac (0 : ℝ) E = 0 := by
    rw [Measure.dirac_apply' _ hEc.measurableSet]
    simp [hE, not_le.2 hε]
  have hfr : Measure.dirac (0 : ℝ) (frontier E) = 0 :=
    measure_mono_null hEc.frontier_subset h0
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto
    (E := E) (by simpa using hfr)
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id, h0] at key
  refine key.congr fun n ↦ ?_
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hEc.measurableSet]
  congr 1
  ext ω
  simp [hE]

end CausalInference
