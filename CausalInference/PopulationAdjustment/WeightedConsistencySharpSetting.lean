/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralTrial

/-!
# The weighted estimator for the individual data trial of the setting itself

The composed consistency theorems of `WeightedConsistencyGeneralTrial` take an index trial `T`
with arms `true` and `false`, linked to the anchored (or unanchored) setting only through the
regression surfaces. In an anchored setting `S` the individual data trial `S.ipdTrial` has
treatments in `ι`, and its records are triples `(X, A, Y)` with `A : ι`. This file proves the
versions in which the index trial is the trial of the setting.

**The bridge.** For treatments `a ≠ c` of a trial `T` with treatments in `ι`,
`T.twoArmView a c` is the trial with arm `true` for `a` and arm `false` for `c`: the assignment
`1{A = a}` and the potential outcomes `Y(true) = Y(a)`, `Y(false) = Y(c)`
(`Trial.twoArmView`). A record `(x, s, y)` is recoded as `(x, 1{s = a}, y)` (`twoArmRecord`).
When the assignment takes the values `a` and `c` only (almost surely):

* the recoded individual data law is that of the two arm view
  (`Trial.map_twoArmRecord_ipdLaw`), so the recoded records of an i.i.d. sample of the trial
  are an i.i.d. sample of the two arm view;
* conditional means, randomization and arm probabilities pass to the two arm view
  (`Trial.twoArmView_isCondMean_true`, `Trial.twoArmView_isCondMean_false`,
  `Trial.indepFun_twoArmView_true`, `Trial.indepFun_twoArmView_false`,
  `Trial.twoArmView_prob_true`, `Trial.twoArmView_prob_false_pos`);
* the weighted arm means of the recoded sample are the weighted means of the treatments `a` and
  `c` of the records with their own labels (`sampleBalancedArmMean_twoArmRecord_true`,
  `sampleBalancedArmMean_twoArmRecord_false`).

**The final theorems.** `anchoredWeightedEstimate_isConsistent_setting`: for an anchored
setting satisfying the identification assumptions on the identity scale, whose individual data
trial is randomized with assignments `a` and `c`, an i.i.d. sample of the records of that trial
and reported targets converging to the target feature means, the anchored weighted estimate
(`anchoredWeightedEstimate`, with the entropy balancing weights at the reported targets and the
treatment labels of the trial) is consistent for the target effect `E_Q[Y(b)] - E_Q[Y(a)]`.
`unanchoredWeightedEstimate_isConsistent_setting`: the unanchored comparison when the source of
`a` is the population of a randomized trial of `a` against a control `c`.

## Main definitions

* `Trial.twoArmView`, `twoArmRecord`.

## Main results

* `Trial.map_twoArmRecord_ipdLaw`, `Trial.isIIDSample_twoArmRecord`.
* `anchoredWeightedEstimate_isConsistent_setting`,
  `unanchoredWeightedEstimate_isConsistent_setting`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

section Bridge

variable {Ω₁ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [DecidableEq ι]

/-- **The two arm view of a trial of `a` against `c`**: arm `true` is the treatment `a`, arm
`false` the treatment `c`; the assignment is `1{A = a}`. -/
def _root_.CausalInference.IndirectComparison.Trial.twoArmView (T : Trial Ω₁ 𝒳 ι) (a c : ι) :
    Trial Ω₁ 𝒳 Bool where
  μ := T.μ
  X := T.X
  Y b := cond b (T.Y a) (T.Y c)
  A ω := decide (T.A ω = a)

/-- The record `(x, s, y)` with the treatment label `s` recoded as the arm `1{s = a}`. -/
def twoArmRecord (a : ι) (z : 𝒳 × ι × ℝ) : 𝒳 × Bool × ℝ := (z.1, decide (z.2.1 = a), z.2.2)

variable [MeasurableSpace 𝒳] (T : Trial Ω₁ 𝒳 ι)

/-- The conditional mean of arm `true` of the two arm view is that of `Y(a)`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.twoArmView_isCondMean_true (a c : ι)
    (m : 𝒳 → ℝ) : (T.twoArmView a c).IsCondMean true m ↔ T.IsCondMean a m := Iff.rfl

/-- The conditional mean of arm `false` of the two arm view is that of `Y(c)`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.twoArmView_isCondMean_false (a c : ι)
    (m : 𝒳 → ℝ) : (T.twoArmView a c).IsCondMean false m ↔ T.IsCondMean c m := Iff.rfl

theorem _root_.CausalInference.IndirectComparison.Trial.twoArmView_covLaw (a c : ι) :
    (T.twoArmView a c).covLaw = T.covLaw := rfl

variable {T}

omit [MeasurableSpace 𝒳] in
/-- The observed outcome of the two arm view is that of the trial when the assignment is `a` or
`c`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.twoArmView_obsOutcome {a c : ι}
    (hac : a ≠ c) {ω : Ω₁} (h : T.A ω = a ∨ T.A ω = c) :
    (T.twoArmView a c).obsOutcome ω = T.obsOutcome ω := by
  rcases h with h | h
  · simp [Trial.obsOutcome, Trial.twoArmView, h]
  · simp [Trial.obsOutcome, Trial.twoArmView, h, Ne.symm hac]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem measurable_twoArmRecord (a : ι) : Measurable (twoArmRecord (𝒳 := 𝒳) a) :=
  measurable_fst.prodMk ((measurable_to_bool (by
    have : (fun z : 𝒳 × ι × ℝ => decide (z.2.1 = a)) ⁻¹' {true} = {z | z.2.1 = a} := by
      ext z; simp
    rw [this]
    exact measurable_snd.fst (measurableSet_singleton a))).prodMk measurable_snd.snd)

omit [MeasurableSpace 𝒳] in
theorem _root_.CausalInference.IndirectComparison.Trial.measurable_twoArmView_A
    (hA : Measurable T.A) (a c : ι) : Measurable (T.twoArmView a c).A :=
  measurable_to_bool (by
    have : (T.twoArmView a c).A ⁻¹' {true} = T.A ⁻¹' {a} := by ext ω; simp [Trial.twoArmView]
    rw [this]
    exact hA (measurableSet_singleton a))

/-- **The recoded individual data law is the individual data law of the two arm view**, when the
assignment takes the values `a ≠ c` only, almost surely. -/
theorem _root_.CausalInference.IndirectComparison.Trial.map_twoArmRecord_ipdLaw {a c : ι}
    (hac : a ≠ c)
    (hg : AEMeasurable (fun ω => (T.X ω, T.A ω, T.obsOutcome ω)) T.μ)
    (hAac : ∀ᵐ ω ∂T.μ, T.A ω = a ∨ T.A ω = c) :
    T.ipdLaw.map (twoArmRecord a) = (T.twoArmView a c).ipdLaw := by
  rw [Trial.ipdLaw, AEMeasurable.map_map_of_aemeasurable
    (measurable_twoArmRecord a).aemeasurable hg, Trial.ipdLaw]
  refine Measure.map_congr (hAac.mono fun ω h => ?_)
  simp only [Function.comp_apply, twoArmRecord]
  rw [Trial.twoArmView_obsOutcome hac h]
  rfl

omit [MeasurableSpace 𝒳] in
theorem measurable_decide_eq (a : ι) : Measurable fun s : ι => decide (s = a) :=
  measurable_to_bool (by
    have : (fun s : ι => decide (s = a)) ⁻¹' {true} = {a} := by ext s; simp
    rw [this]
    exact measurableSet_singleton a)

/-- Randomization passes to arm `true` of the two arm view. -/
theorem _root_.CausalInference.IndirectComparison.Trial.indepFun_twoArmView_true (a c : ι)
    (h : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ) :
    IndepFun (T.twoArmView a c).A
      (fun ω => ((T.twoArmView a c).X ω, (T.twoArmView a c).Y true ω)) (T.twoArmView a c).μ :=
  h.comp (measurable_decide_eq a) measurable_id

/-- Randomization passes to arm `false` of the two arm view. -/
theorem _root_.CausalInference.IndirectComparison.Trial.indepFun_twoArmView_false (a c : ι)
    (h : IndepFun T.A (fun ω => (T.X ω, T.Y c ω)) T.μ) :
    IndepFun (T.twoArmView a c).A
      (fun ω => ((T.twoArmView a c).X ω, (T.twoArmView a c).Y false ω)) (T.twoArmView a c).μ :=
  h.comp (measurable_decide_eq a) measurable_id

omit [MeasurableSpace 𝒳] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Arm `true` of the two arm view has the probability of the treatment `a`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.twoArmView_prob_true (a c : ι) :
    (T.twoArmView a c).μ.real ((T.twoArmView a c).A ⁻¹' {true}) = T.μ.real (T.A ⁻¹' {a}) := by
  congr 1; ext ω; simp [Trial.twoArmView]

omit [MeasurableSpace 𝒳] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Arm `false` of the two arm view has positive probability when the treatment `c ≠ a` has. -/
theorem _root_.CausalInference.IndirectComparison.Trial.twoArmView_prob_false_pos
    [IsFiniteMeasure T.μ] {a c : ι} (hac : a ≠ c) (h : 0 < T.μ.real (T.A ⁻¹' {c})) :
    0 < (T.twoArmView a c).μ.real ((T.twoArmView a c).A ⁻¹' {false}) := by
  refine h.trans_le (measureReal_mono (fun ω hω => ?_))
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
  simp [Trial.twoArmView, hω, Ne.symm hac]

/-- **The recoded records of an i.i.d. sample of the trial are an i.i.d. sample of the two arm
view**, when the assignment takes the values `a ≠ c` only, almost surely. -/
theorem _root_.CausalInference.IndirectComparison.Trial.isIIDSample_twoArmRecord
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {a c : ι}
    (hac : a ≠ c) (hX : Measurable T.X) (hA : Measurable T.A) (hYa : Measurable (T.Y a))
    (hYc : Measurable (T.Y c)) (hAac : ∀ᵐ ω ∂T.μ, T.A ω = a ∨ T.A ω = c) {R : ℕ → Ω → 𝒳 × ι × ℝ}
    (hR : IsIIDSample R P) (hRm : ∀ i, Measurable (R i)) (hlaw : P.map (R 0) = T.ipdLaw) :
    IsIIDSample (fun i ω => twoArmRecord a (R i ω)) P ∧
      (∀ i, Measurable fun ω => twoArmRecord a (R i ω)) ∧
      P.map (fun ω => twoArmRecord a (R 0 ω)) = (T.twoArmView a c).ipdLaw ∧
      ∀ᵐ ω ∂P, ∀ i, (R i ω).2.1 = a ∨ (R i ω).2.1 = c := by
  have hYo : AEMeasurable T.obsOutcome T.μ := by
    have hm : Measurable fun ω => if T.A ω = a then T.Y a ω else T.Y c ω :=
      Measurable.ite (hA (measurableSet_singleton a)) hYa hYc
    refine hm.aemeasurable.congr (hAac.mono fun ω h => ?_)
    rcases h with h | h
    · simp [Trial.obsOutcome, h]
    · simp [Trial.obsOutcome, h, Ne.symm hac]
  have hg : AEMeasurable (fun ω => (T.X ω, T.A ω, T.obsOutcome ω)) T.μ :=
    hX.aemeasurable.prodMk (hA.aemeasurable.prodMk hYo)
  have hset : MeasurableSet {z : 𝒳 × ι × ℝ | z.2.1 = a ∨ z.2.1 = c} :=
    (measurable_snd.fst (measurableSet_singleton a)).union
      (measurable_snd.fst (measurableSet_singleton c))
  refine ⟨hR.comp (measurable_twoArmRecord a),
    fun i => (measurable_twoArmRecord a).comp (hRm i), ?_,
    hR.ae_forall (p := fun z => z.2.1 = a ∨ z.2.1 = c) ?_⟩
  · rw [show (fun ω => twoArmRecord a (R 0 ω)) = twoArmRecord a ∘ R 0 from rfl,
      ← Measure.map_map (measurable_twoArmRecord a) (hRm 0), hlaw,
      T.map_twoArmRecord_ipdLaw hac hg hAac]
  · rw [hlaw, Trial.ipdLaw, ae_map_iff hg hset]
    exact hAac

end Bridge

/-! ### The weighted arm means with treatment labels -/

section Labels

variable {Ω 𝒳 ι : Type*} [DecidableEq ι] {p : ℕ}

/-- The weighted arm mean of arm `true` of the recoded sample is the weighted mean of the
treatment `a` of the records with their own labels. -/
theorem sampleBalancedArmMean_twoArmRecord_true (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (R : ℕ → Ω → 𝒳 × ι × ℝ) (a : ι) (n : ℕ) (ω : Ω) :
    sampleBalancedArmMean φ t (fun i ω => twoArmRecord a (R i ω)) true n ω =
      weightedArmMean (balancingWeights fun i : Fin n => φ (R i ω).1 - t)
        (fun i => (R i ω).2.1) (fun i => (R i ω).2.2) a := by
  simp only [sampleBalancedArmMean, twoArmRecord, weightedArmMean]
  congr 1
  funext i
  simp [armWeights]

/-- The weighted arm mean of arm `false` of the recoded sample is the weighted mean of the
treatment `c` of the records with their own labels, when every label is `a` or `c`. -/
theorem sampleBalancedArmMean_twoArmRecord_false (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (R : ℕ → Ω → 𝒳 × ι × ℝ) {a c : ι} (hac : a ≠ c) (n : ℕ) (ω : Ω)
    (h : ∀ i, (R i ω).2.1 = a ∨ (R i ω).2.1 = c) :
    sampleBalancedArmMean φ t (fun i ω => twoArmRecord a (R i ω)) false n ω =
      weightedArmMean (balancingWeights fun i : Fin n => φ (R i ω).1 - t)
        (fun i => (R i ω).2.1) (fun i => (R i ω).2.2) c := by
  simp only [sampleBalancedArmMean, twoArmRecord, weightedArmMean]
  congr 1
  funext i
  simp only [armWeights]
  rcases h i with h' | h'
  · simp [h', hac]
  · simp [h', Ne.symm hac]

end Labels

/-! ### The composed theorems for the trial of the setting -/

section Setting

variable {Ω₁ Ω₂ Ω₃ Ω 𝒳 ι 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MeasurableSpace Ω₃] [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [DecidableEq ι] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The anchored weighted estimate for the individual data trial of the setting is consistent
for the target effect.** Let `S` be an anchored setting satisfying the identification
assumptions on the identity scale for the surfaces `m₁` (individual data trial), `m₂`
(aggregate data trial) and `m` (target). Let its individual data trial be randomized for the
treatments `a ≠ c`: the assignment is measurable and takes the values `a` and `c` only (almost
surely), it is independent of `(X, Y(a))` and of `(X, Y(c))`, both treatments have positive
probability, and `Y(a)`, `Y(c)` are measurable. Let `R` be a measurable i.i.d. sample of the
records `(X, A, Y)` of that trial. Assume the interior and moment conditions at `t` for the
trial feature law, reported targets `tₙ = Gₙ(W) → t` in probability from data `W` independent of
the sample, square integrable residuals `Y(s) - m₁ s (X)` with conditional variance at most `σ²`
and surfaces `m₁ a`, `m₁ c` affine in the features, target features integrable with means `t`, and
`d̂_bc` consistent for `∫ (m₂ c - m₂ b) dQ_X`. Then the anchored weighted estimate with the
entropy balancing weights at `tₙ` and the treatment labels of the records,
`(μ̂_c - μ̂_a) - d̂_bc`, is consistent for the target effect `E_Q[Y(b)] - E_Q[Y(a)]`. -/
theorem anchoredWeightedEstimate_isConsistent_setting {S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.ipdTrial.μ] [IsFiniteMeasure S.agdTrial.μ]
    [IsProbabilityMeasure S.target.μ] {m₁ m₂ m : ι → 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions id Set.univ m₁ m₂ m) (hac : S.a ≠ S.c)
    (hA : Measurable S.ipdTrial.A) (hYa : Measurable (S.ipdTrial.Y S.a))
    (hYc : Measurable (S.ipdTrial.Y S.c))
    (hAac : ∀ᵐ ω ∂S.ipdTrial.μ, S.ipdTrial.A ω = S.a ∨ S.ipdTrial.A ω = S.c)
    (hra : IndepFun S.ipdTrial.A (fun ω => (S.ipdTrial.X ω, S.ipdTrial.Y S.a ω)) S.ipdTrial.μ)
    (hrc : IndepFun S.ipdTrial.A (fun ω => (S.ipdTrial.X ω, S.ipdTrial.Y S.c ω)) S.ipdTrial.μ)
    (hqa : 0 < S.ipdTrial.μ.real (S.ipdTrial.A ⁻¹' {S.a}))
    (hqc : 0 < S.ipdTrial.μ.real (S.ipdTrial.A ⁻¹' {S.c}))
    {R : ℕ → Ω → 𝒳 × ι × ℝ} (hR : IsIIDSample R P) (hRm : ∀ i, Measurable (R i))
    (hlaw : P.map (R 0) = S.ipdTrial.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (S.ipdTrial.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) S.ipdTrial.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWR : IndepFun W (fun ω k => R k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hrA : Integrable (fun ω => (S.ipdTrial.Y S.a ω - m₁ S.a (S.ipdTrial.X ω)) ^ 2)
      S.ipdTrial.μ)
    (hrC : Integrable (fun ω => (S.ipdTrial.Y S.c ω - m₁ S.c (S.ipdTrial.X ω)) ^ 2)
      S.ipdTrial.μ) {σ2 : ℝ}
    (hvA : S.ipdTrial.μ[fun ω => (S.ipdTrial.Y S.a ω - m₁ S.a (S.ipdTrial.X ω)) ^ 2 |
      MeasurableSpace.comap S.ipdTrial.X inferInstance] ≤ᵐ[S.ipdTrial.μ] fun _ => σ2)
    (hvC : S.ipdTrial.μ[fun ω => (S.ipdTrial.Y S.c ω - m₁ S.c (S.ipdTrial.X ω)) ^ 2 |
      MeasurableSpace.comap S.ipdTrial.X inferInstance] ≤ᵐ[S.ipdTrial.μ] fun _ => σ2)
    {a0 c0 : ℝ} {b d : Fin p → ℝ} (hafA : ∀ x, m₁ S.a x = a0 + b ⬝ᵥ φ x)
    (hafC : ∀ x, m₁ S.c x = c0 + d ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k) {dBC : ℕ → Ω → ℝ}
    (hd : IsConsistent dBC (∫ x, linkContrast id (m₂ S.b) (m₂ S.c) x ∂S.target.covLaw) P) :
    IsConsistent (fun n => anchoredWeightedEstimate id
        (fun ω => balancingWeights fun i : Fin n => φ (R i ω).1 - G n (W ω))
        (fun ω i => (R i ω).2.1) (fun ω i => (R i ω).2.2) S.a S.c (dBC n))
      (S.target.marginalEffect id S.a S.b) P := by
  have hX := hS.measurable_ipd
  obtain ⟨hR', hR'm, hlaw', hae⟩ :=
    S.ipdTrial.isIIDSample_twoArmRecord hac hX hA hYa hYc hAac hR hRm hlaw
  have hWR' : IndepFun W (fun ω k => twoArmRecord S.a (R k ω)) P :=
    hWR.comp measurable_id
      (Measurable.of_eval fun k => (measurable_twoArmRecord S.a).comp (measurable_pi_apply k))
  have h := anchoredBalancedEstimate_isConsistent_identity_trial
    (T := S.ipdTrial.twoArmView S.a S.c) hS hX (S.ipdTrial.measurable_twoArmView_A hA _ _)
    hYa hYc (S.ipdTrial.indepFun_twoArmView_true _ _ hra)
    (S.ipdTrial.indepFun_twoArmView_false _ _ hrc) hR' hR'm hlaw' hφ hint hexp hW hWR' hG htm
    (by rw [Trial.twoArmView_prob_true]; exact hqa)
    (S.ipdTrial.twoArmView_prob_false_pos hac hqc) hS.isCondMean_ipd_a hS.isCondMean_ipd_c
    hrA hrC hvA hvC hafA hafC hQφ ht hd
  refine TendstoInMeasure.congr' (Eventually.of_forall fun n => hae.mono fun ω hω => ?_)
    EventuallyEq.rfl h
  rw [anchoredWeightedEstimate_eq, sampleBalancedArmMean_twoArmRecord_true,
    sampleBalancedArmMean_twoArmRecord_false φ _ R hac n ω hω]
  rfl

/-- **The unanchored weighted comparison when the source of `a` is a randomized trial.** Let `S`
be an unanchored setting satisfying the identification assumptions for the surfaces `m_a` and
`m_b`, and let the source of `a` be the population of a trial `T` of `a` against a control
`c ≠ a` (`T.toPopulation = S.sourceA`): the assignment is measurable and takes the values `a` and
`c` only (almost surely), is independent of `(X, Y(a))`, and `a` has positive probability. Let
`R` be a measurable i.i.d. sample of the records of `T`. Under the interior and moment conditions
at `t` for the trial feature law, reported targets `tₙ → t` from data independent of the sample,
a square integrable residual `Y(a) - m_a(X)` with conditional variance at most `σ²`, `m_a` affine
in the features, target features integrable with means `t`, `m̂_b` consistent for `∫ m_b dQ_X`
and `g` continuous at the target means, the comparison `g(m̂_b) - g(μ̂_a)`, with `μ̂_a` the
weighted mean of the treatment `a` of the records with their own labels, is consistent for the
target effect `g(E_Q[Y(b)]) - g(E_Q[Y(a)])`. -/
theorem unanchoredWeightedEstimate_isConsistent_setting {S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.sourceA.μ] [IsFiniteMeasure S.sourceB.μ]
    [IsProbabilityMeasure S.target.μ] {D : Set ℝ} {ma mb : 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions D ma mb) {T : Trial Ω₁ 𝒳 ι}
    (hsrc : T.toPopulation = S.sourceA) {c : ι} (hac : S.a ≠ c)
    (hA : Measurable T.A) (hYa : Measurable (T.Y S.a)) (hYc : Measurable (T.Y c))
    (hAac : ∀ᵐ ω ∂T.μ, T.A ω = S.a ∨ T.A ω = c)
    (hra : IndepFun T.A (fun ω => (T.X ω, T.Y S.a ω)) T.μ)
    (hqa : 0 < T.μ.real (T.A ⁻¹' {S.a}))
    {R : ℕ → Ω → 𝒳 × ι × ℝ} (hR : IsIIDSample R P) (hRm : ∀ i, Measurable (R i))
    (hlaw : P.map (R 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWR : IndepFun W (fun ω k => R k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hres2 : Integrable (fun ω => (T.Y S.a ω - ma (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y S.a ω - ma (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, ma x = a0 + b ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k)
    {mB : ℕ → Ω → ℝ} (hmB : IsConsistent mB (∫ x, mb x ∂S.target.covLaw) P) {g : ℝ → ℝ}
    (hga : ContinuousAt g (S.target.armMean S.a)) (hgb : ContinuousAt g (S.target.armMean S.b)) :
    IsConsistent (fun n ω => g (mB n ω) - g (weightedArmMean
        (balancingWeights fun i : Fin n => φ (R i ω).1 - G n (W ω))
        (fun i => (R i ω).2.1) (fun i => (R i ω).2.2) S.a))
      (S.target.marginalEffect g S.a S.b) P := by
  have hX : Measurable T.X := by
    have := hS.measurable_sourceA
    rw [← hsrc] at this
    exact this
  have hm : (T.twoArmView S.a c).IsCondMean true ma := by
    rw [Trial.twoArmView_isCondMean_true]
    rw [hsrc]
    exact hS.isCondMean_a
  obtain ⟨hR', hR'm, hlaw', -⟩ := T.isIIDSample_twoArmRecord hac hX hA hYa hYc hAac hR hRm hlaw
  have hWR' : IndepFun W (fun ω k => twoArmRecord S.a (R k ω)) P :=
    hWR.comp measurable_id
      (Measurable.of_eval fun k => (measurable_twoArmRecord S.a).comp (measurable_pi_apply k))
  have hA' := T.measurable_twoArmView_A hA S.a c
  have h := unanchoredBalancedEstimate_isConsistent_trial (T := T.twoArmView S.a c) hS hX hA'
    (measurable_obsOutcome_bool hA' hYa hYc) hYa (T.indepFun_twoArmView_true _ _ hra) hR' hR'm
    hlaw' hφ hint hexp hW hWR' hG htm (by rw [Trial.twoArmView_prob_true]; exact hqa) hm hres2
    hvar haff hQφ ht hmB hga hgb
  simp only [sampleBalancedArmMean_twoArmRecord_true] at h
  exact h

end Setting

end PopulationAdjustment

end CausalInference
