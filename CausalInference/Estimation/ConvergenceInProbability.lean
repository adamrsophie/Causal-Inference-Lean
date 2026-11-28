/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.DeltaMethodSeveralSamples
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# The calculus of convergence in probability

Convergence in probability of a sequence `X n` to a constant `c` is
`MeasureTheory.TendstoInMeasure μ X atTop (fun _ ↦ c)`; for real estimators this is
`CausalInference.IsConsistent`. The measure of a set that is not measurable is its outer measure,
so none of the statements below asks the variables to be measurable.

## Main definitions

* `CausalInference.WithProbTendingToOne μ A`: the events `A n` have probability tending to one,
  that is `μ (A n)ᶜ → 0`.

## Main results

* `MeasureTheory.TendstoInMeasure.comp_continuousAt`: continuous mapping at a constant limit, for
  maps between pseudo metric spaces.
* `MeasureTheory.TendstoInMeasure.prodMk` and `CausalInference.tendstoInMeasure_pi`: joint
  convergence of two, and of finitely many, sequences converging to constants.
* `MeasureTheory.TendstoInMeasure.congr_withProbTendingToOne`: changing a sequence on events of
  probability tending to zero does not change its limit in probability.
* `MeasureTheory.TendstoInMeasure.of_perturb`: a sequence within `η S n` of a convergent one for
  every `η > 0`, with `S n` convergent, has the same limit.
* `CausalInference.tendstoInMeasure_of_good_events`: convergence in probability from good events.
* `MeasureTheory.TendstoInMeasure.smul_boundedInProbability`: `o_p(1) • O_p(1) = o_p(1)` in a
  normed space.
* `MeasureTheory.TendstoInMeasure.tendsto_integral_of_uniformIntegrable`: a uniformly integrable
  sequence converging in probability converges in mean (Vitali).

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Events of probability tending to one -/

/-- The events `A n` have probability tending to one under `μ`: `μ (A n)ᶜ → 0`. The measure of a
set that is not measurable is its outer measure, so the events need not be measurable. -/
def WithProbTendingToOne (μ : Measure Ω) (A : ℕ → Set Ω) : Prop :=
  Tendsto (fun n ↦ μ (A n)ᶜ) atTop (𝓝 0)

namespace WithProbTendingToOne

variable {A B : ℕ → Set Ω}

/-- The intersection of two families of events of probability tending to one has probability
tending to one. -/
theorem inter (hA : WithProbTendingToOne μ A) (hB : WithProbTendingToOne μ B) :
    WithProbTendingToOne μ (fun n ↦ A n ∩ B n) := by
  have h := hA.add hB
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
    fun n ↦ ?_
  rw [Set.compl_inter]
  exact measure_union_le _ _

/-- Families of events containing events of probability tending to one have probability tending
to one. -/
theorem mono (hA : WithProbTendingToOne μ A) (hAB : ∀ n, A n ⊆ B n) :
    WithProbTendingToOne μ B :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA (fun _ ↦ bot_le)
    fun n ↦ measure_mono (Set.compl_subset_compl.2 (hAB n))

/-- An almost sure event, taken at every `n`, has probability tending to one. -/
theorem of_ae {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    WithProbTendingToOne μ (fun _ ↦ {ω | p ω}) := by
  have : μ {ω | p ω}ᶜ = 0 := by rw [ae_iff] at h; simpa [Set.compl_def] using h
  simp only [WithProbTendingToOne, this]
  exact tendsto_const_nhds

/-- Events of probability tending to one have probability at least `1 - κ` for all large `n`. -/
theorem eventually_le (hA : WithProbTendingToOne μ A) {κ : ℝ≥0∞} (hκ : 0 < κ) :
    ∀ᶠ n in atTop, μ (A n)ᶜ ≤ κ :=
  (ENNReal.tendsto_nhds_zero.1 hA) κ hκ

end WithProbTendingToOne

/-- A sequence of events with probability eventually one has probability tending to one. -/
theorem withProbTendingToOne_univ : WithProbTendingToOne μ (fun _ ↦ Set.univ) := by
  simp [WithProbTendingToOne]

/-- A constant sequence converges in probability to its value. -/
theorem tendstoInMeasure_const {E : Type*} [PseudoMetricSpace E] (c : E) :
    TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) ↦ c) atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have h0 : ¬ (ε ≤ 0) := not_le.2 hε
  simp only [dist_self, h0]
  simp

/-- **Convergence in probability from good events.** If for every `ε > 0` and `κ > 0` there are
events of probability eventually at least `1 - κ` on which `X n` is eventually within `ε` of `c`,
then `X n → c` in probability. -/
theorem tendstoInMeasure_of_good_events {E : Type*} [PseudoMetricSpace E] {X : ℕ → Ω → E} {c : E}
    (h : ∀ ε : ℝ, 0 < ε → ∀ κ : ℝ≥0∞, 0 < κ → ∃ A : ℕ → Set Ω,
      (∀ᶠ n in atTop, μ (A n)ᶜ ≤ κ) ∧ ∀ᶠ n in atTop, ∀ ω ∈ A n, dist (X n ω) c < ε) :
    TendstoInMeasure μ X atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  obtain ⟨A, hA, hXA⟩ := h ε hε κ hκ
  filter_upwards [hA, hXA] with n hn hXn
  refine le_trans (measure_mono fun ω hω ↦ ?_) hn
  intro hωA
  exact absurd (hXn ω hωA) (not_lt.2 hω)


/-- A sequence converging in probability to `c` lies within `δ` of `c` with probability tending
to one. -/
theorem _root_.MeasureTheory.TendstoInMeasure.withProbTendingToOne_dist_lt
    {E : Type*} [PseudoMetricSpace E] {X : ℕ → Ω → E} {c : E}
    (hX : TendstoInMeasure μ X atTop (fun _ ↦ c)) {δ : ℝ} (hδ : 0 < δ) :
    WithProbTendingToOne μ (fun n ↦ {ω | dist (X n ω) c < δ}) := by
  rw [tendstoInMeasure_iff_dist] at hX
  refine (hX δ hδ).congr fun n ↦ ?_
  congr 1
  ext ω
  simp

/-- **Continuous mapping at a constant limit.** If `X n → c` in probability and `g` is continuous
at `c`, then `g (X n) → g c` in probability. No measurability of `g` is needed. -/
theorem _root_.MeasureTheory.TendstoInMeasure.comp_continuousAt
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {X : ℕ → Ω → E} {c : E} {g : E → F} (hX : TendstoInMeasure μ X atTop (fun _ ↦ c))
    (hg : ContinuousAt g c) :
    TendstoInMeasure μ (fun n ω ↦ g (X n ω)) atTop (fun _ ↦ g c) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hX δ hδ)
    (fun _ ↦ bot_le) fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra h
  exact absurd (hδg (not_le.1 h)) (not_lt.2 hω)

/-- **Joint convergence.** If `X n → a` and `Y n → b` in probability, then
`(X n, Y n) → (a, b)` in probability. -/
theorem _root_.MeasureTheory.TendstoInMeasure.prodMk
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {X : ℕ → Ω → E} {Y : ℕ → Ω → F} {a : E} {b : F}
    (hX : TendstoInMeasure μ X atTop (fun _ ↦ a)) (hY : TendstoInMeasure μ Y atTop (fun _ ↦ b)) :
    TendstoInMeasure μ (fun n ω ↦ (X n ω, Y n ω)) atTop (fun _ ↦ (a, b)) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro ε hε
  have h := (hX ε hε).add (hY ε hε)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
    fun n ↦ (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union, Prod.dist_eq] at hω ⊢
  exact le_max_iff.1 hω

/-- **Agreement on events of probability tending to one.** If `X n → c` in probability and
`Y n = X n` on events `A n` of probability tending to one, then `Y n → c` in probability. -/
theorem _root_.MeasureTheory.TendstoInMeasure.congr_withProbTendingToOne
    {E : Type*} [PseudoMetricSpace E] {X Y : ℕ → Ω → E} {c : E}
    {A : ℕ → Set Ω} (hX : TendstoInMeasure μ X atTop (fun _ ↦ c))
    (hA : WithProbTendingToOne μ A) (hXY : ∀ n, ∀ ω ∈ A n, X n ω = Y n ω) :
    TendstoInMeasure μ Y atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  have h := (hX ε hε).add hA
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
    fun n ↦ (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_cases hω' : ω ∈ A n
  · left
    change ε ≤ dist (X n ω) c
    rw [hXY n ω hω']
    exact hω
  · exact Or.inr hω'

/-- **Perturbation of a convergent sequence.** If `B n → c` and `S n → s` in probability and, for
every `η > 0`, with probability tending to one `|A n - B n| ≤ η S n`, then `A n → c` in
probability. -/
theorem _root_.MeasureTheory.TendstoInMeasure.of_perturb
    {A B S : ℕ → Ω → ℝ} {c s : ℝ} (hB : TendstoInMeasure μ B atTop (fun _ ↦ c))
    (hS : TendstoInMeasure μ S atTop (fun _ ↦ s))
    (h : ∀ η, 0 < η → WithProbTendingToOne μ (fun n ↦ {ω | |A n ω - B n ω| ≤ η * S n ω})) :
    TendstoInMeasure μ A atTop (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set η := ε / (2 * (|s| + 1)) with hη
  have hs1 : 0 < |s| + 1 := by positivity
  have hηpos : 0 < η := by positivity
  have hηs : η * (|s| + 1) = ε / 2 := by rw [hη]; field_simp
  have h1 := (hB.withProbTendingToOne_dist_lt (half_pos hε)).inter
    ((hS.withProbTendingToOne_dist_lt one_pos).inter (h η hηpos))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ ↦ bot_le)
    fun n ↦ measure_mono ?_
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and]
  intro hB' hS' hA'
  rw [Real.dist_eq] at hB' hS' hω
  have hSle : S n ω ≤ |s| + 1 := by
    have := (abs_lt.1 hS').2
    linarith [le_abs_self s]
  have h2 : η * S n ω ≤ ε / 2 := by
    rw [← hηs]
    exact mul_le_mul_of_nonneg_left hSle hηpos.le
  have h3 : |A n ω - c| ≤ |A n ω - B n ω| + |B n ω - c| := by
    have := abs_add_le (A n ω - B n ω) (B n ω - c)
    rwa [sub_add_sub_cancel] at this
  linarith

/-- **`o_p(1)` times `O_p(1)`.** If the real sequence `X n` tends to zero in probability and the
norms of the vectors `Y n` are bounded in probability, then `X n • Y n → 0` in probability. -/
theorem _root_.MeasureTheory.TendstoInMeasure.smul_boundedInProbability
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ℕ → Ω → ℝ} {Y : ℕ → Ω → E} (hX : TendstoInMeasure μ X atTop (fun _ ↦ 0))
    (hY : BoundedInProbability μ (fun n ω ↦ ‖Y n ω‖)) :
    TendstoInMeasure μ (fun n ω ↦ X n ω • Y n ω) atTop (fun _ ↦ 0) := by
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ ↦ ?_
  obtain ⟨K, hK, hYK⟩ := hY (κ / 2) (ENNReal.half_pos hκ.ne')
  have hXd := (hX.withProbTendingToOne_dist_lt (div_pos hε hK)).eventually_le
    (ENNReal.half_pos hκ.ne')
  refine ⟨fun n ↦ {ω | ‖Y n ω‖ < K} ∩ {ω | dist (X n ω) 0 < ε / K}, ?_, ?_⟩
  · filter_upwards [hYK, hXd] with n h1 h2
    rw [Set.compl_inter]
    refine (measure_union_le _ _).trans ((add_le_add ?_ h2).trans (ENNReal.add_halves κ).le)
    refine le_trans (measure_mono fun ω hω ↦ ?_) h1
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
    rwa [abs_of_nonneg (norm_nonneg _)]
  · refine Eventually.of_forall fun n ω hω ↦ ?_
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at h1 h2
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc |X n ω| * ‖Y n ω‖ ≤ |X n ω| * K := by gcongr
    _ < ε / K * K := mul_lt_mul_of_pos_right h2 hK
    _ = ε := div_mul_cancel₀ ε hK.ne'

/-- **Uniformly integrable sequences converging in probability converge in mean.** If
`X n → c` in probability under a probability measure and the `X n` are uniformly integrable,
then `E X n → c` (Vitali's convergence theorem). -/
theorem _root_.MeasureTheory.TendstoInMeasure.tendsto_integral_of_uniformIntegrable
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {c : ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ ↦ c)) (hUI : UniformIntegrable X 1 μ) :
    Tendsto (fun n ↦ ∫ ω, X n ω ∂μ) atTop (𝓝 c) := by
  have hL := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    hUI.aestronglyMeasurable (memLp_const c) hUI.unifIntegrable hX
  have h := tendsto_integral_of_L1 (μ := μ) (l := atTop) (fun _ ↦ c) aestronglyMeasurable_const
    (Eventually.of_forall fun n ↦ (hUI.memLp n).integrable le_rfl) ?_
  · simpa using h
  · refine hL.congr fun n ↦ ?_
    rw [eLpNorm_one_eq_lintegral_eNorm
      ((hUI.aestronglyMeasurable n).sub aestronglyMeasurable_const)]
    rfl


/-- **Joint convergence of finitely many sequences.** If every coordinate `X i n` converges in
probability to `c i`, the vector `(X i n)ᵢ` converges in probability to `c` for the sup
distance. -/
theorem tendstoInMeasure_pi {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, PseudoMetricSpace (E i)] {X : ∀ i, ℕ → Ω → E i} {c : ∀ i, E i}
    (h : ∀ i, TendstoInMeasure μ (X i) atTop (fun _ ↦ c i)) :
    TendstoInMeasure μ (fun n ω i ↦ X i n ω) atTop (fun _ ↦ c) := by
  simp_rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  have hs := tendsto_finsetSum Finset.univ (fun i _ ↦ h i ε hε)
  simp only [Finset.sum_const_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ ↦ bot_le)
    fun n ↦ (measure_mono ?_).trans (measure_biUnion_finset_le Finset.univ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hω ⊢
  by_contra hne
  simp only [not_exists, not_le] at hne
  exact absurd hω (not_le.2 ((dist_pi_lt_iff hε).2 hne))

/-! ### The special cases already in the library -/

/-- The continuous mapping lemma for consistency is the real case of
`TendstoInMeasure.comp_continuousAt`. -/
example {θhat : ℕ → Ω → ℝ} {θ : ℝ} {g : ℝ → ℝ} (hg : ContinuousAt g θ)
    (h : IsConsistent θhat θ μ) : IsConsistent (fun n ω ↦ g (θhat n ω)) (g θ) μ :=
  TendstoInMeasure.comp_continuousAt h hg

/-- The joint continuous mapping lemma for consistency follows from `TendstoInMeasure.prodMk`. -/
example {a b : ℕ → Ω → ℝ} {α β : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : ContinuousAt (Function.uncurry g) (α, β)) (ha : IsConsistent a α μ)
    (hb : IsConsistent b β μ) : IsConsistent (fun n ω ↦ g (a n ω) (b n ω)) (g α β) μ :=
  (TendstoInMeasure.prodMk ha hb).comp_continuousAt hg

/-- The product rule `o_p(1) O_p(1) = o_p(1)` of the delta method is the real case of
`TendstoInMeasure.smul_boundedInProbability`. -/
example {X Y : ℕ → Ω → ℝ} (hX : TendstoInMeasure μ X atTop 0)
    (hY : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, μ {ω | M ≤ |Y n ω|} ≤ η) :
    TendstoInMeasure μ (fun n ω ↦ X n ω * Y n ω) atTop 0 := by
  have hY' : BoundedInProbability μ (fun n ω ↦ ‖Y n ω‖) := by
    simpa [BoundedInProbability, Real.norm_eq_abs] using hY
  exact TendstoInMeasure.smul_boundedInProbability hX hY'

end CausalInference
