/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.SimulatedCovariatesConsistency
public import CausalInference.PopulationAdjustment.StandardizationInstancesTargetSample
public import CausalInference.PopulationAdjustment.SimulatedCovariatesLimitLaw

/-!
# The simulated comparison in a finite model: every hypothesis verified

* **The trial** (`coinTrial f`): an assignment `A` and two binary covariates `X = (X₀, X₁)`, all
  independent and each equally likely (the law `halfLaw ⊗ halfLaw ⊗ halfLaw` on
  `Bool × Bool × Bool`), with potential outcomes `Y(t) = f(t, X)`.
* **The additive model** (`simOutcome`): `f(t, x) = x₀ + x₁ + 1[t]`, fitted by least squares with
  the design `z(t, x) = (1, x₀, x₁, 1[t])` and coefficient `ξ₀ = (0, 1, 1, 1)`.
* **The target** (`simTarget`): the covariates have the law `dependentCoinLaw`, fair coins with
  Pearson correlation `1/2`, and the same potential outcomes.
* **The simulation**: fair coin margins (the target margins) and the Gaussian correlation
  matrix with entry `1/2`, from i.i.d. `N(0, R)` draws independent of the trial sample.

Results.

* `simExample_armMean`: the simulated standardized mean of arm `false` is the target arm mean
  `1`, although the simulated law is not the target covariate law
  (`dependentCoin_vs_simulated`): the surface is additive.
* `simExample_unanchored`: the unanchored least squares simulated comparison with the target mean
  `E_Q[Y(true)] = 2` reported exactly converges in probability to the target effect `1`; every
  hypothesis of `tendstoInMeasure_simulated_leastSquares_unanchored` is verified.
* `simExample_pair`: for the interacting surface `x₀ + x₁ + x₀x₁ + 1[t]` and a target whose
  covariate law is the simulated law itself, every hypothesis of
  `integral_nortaLaw_eq_armMean_of_pair` is verified and the target arm mean is `4/3`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport BiasAnalysis.Distributions

/-- A function of the covariates is a version of its own conditional expectation. -/
theorem ae_eq_condExp_comp {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → 𝒳} (hX : Measurable X) {g : 𝒳 → ℝ}
    (hg : Measurable g) (hi : Integrable (fun ω => g (X ω)) μ) :
    (fun ω => g (X ω)) =ᵐ[μ] μ[fun ω => g (X ω) | MeasurableSpace.comap X inferInstance] :=
  EventuallyEq.of_eq (condExp_of_stronglyMeasurable hX.comap_le
    (hg.comp (comap_measurable X)).stronglyMeasurable hi).symm

/-! ### The trial -/

/-- The law of the trial: assignment and two covariates, independent fair coins. -/
noncomputable abbrev coinTrialLaw : Measure (Bool × Bool × Bool) :=
  halfLaw.prod (halfLaw.prod halfLaw)

/-- `coinTrialLaw`-almost sure statements hold at every point. -/
theorem ae_coinTrialLaw_iff {p : Bool × Bool × Bool → Prop} :
    (∀ᵐ ω ∂coinTrialLaw, p ω) ↔ ∀ ω, p ω := by
  refine ⟨fun h ω => ?_, fun h => ae_of_all _ h⟩
  have h1 := Measure.ae_ae_of_ae_prod (μ := halfLaw) (ν := halfLaw.prod halfLaw) h
  rw [ae_halfLaw_iff] at h1
  have h2 := Measure.ae_ae_of_ae_prod (μ := halfLaw) (ν := halfLaw) (h1 ω.1)
  rw [ae_halfLaw_iff] at h2
  exact ae_halfLaw_iff.1 (h2 ω.2.1) ω.2.2

/-- The trial with potential outcomes `Y(t) = f(t, X)`: assignment `ω.1` and covariates
`coinCode ω.2`. -/
noncomputable def coinTrial (f : Bool → (Fin 2 → ℝ) → ℝ) :
    Trial (Bool × Bool × Bool) (Fin 2 → ℝ) Bool where
  μ := coinTrialLaw
  X ω := coinCode ω.2
  Y t ω := f t (coinCode ω.2)
  A := Prod.fst

instance (f : Bool → (Fin 2 → ℝ) → ℝ) : IsProbabilityMeasure (coinTrial f).μ := by
  unfold coinTrial; infer_instance

theorem measurable_coinTrial_X (f : Bool → (Fin 2 → ℝ) → ℝ) : Measurable (coinTrial f).X :=
  measurable_of_finite _

/-- **The trial is randomized.** -/
theorem coinTrial_isRandomizedTwoArm (f : Bool → (Fin 2 → ℝ) → ℝ) :
    (coinTrial f).IsRandomizedTwoArm where
  measurable_X := measurable_coinTrial_X f
  measurable_A := measurable_fst
  measurable_Y _ := measurable_of_finite _
  indepFun := by
    have h : IndepFun (Prod.fst : Bool × Bool × Bool → Bool) Prod.snd coinTrialLaw :=
      indepFun_prod (X := (id : Bool → Bool)) (Y := (id : Bool × Bool → Bool × Bool))
        measurable_id measurable_id
    exact h.comp measurable_id (measurable_of_finite (fun b : Bool × Bool =>
      (coinCode b, potentialPair (fun t (b : Bool × Bool) => f t (coinCode b)) b)))
  prob_pos := by
    change 0 < coinTrialLaw.real (Prod.fst ⁻¹' {true})
    rw [measureReal_def, ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    simp [halfLaw, stratumLaw]
  prob_lt_one := by
    change coinTrialLaw.real (Prod.fst ⁻¹' {true}) < 1
    rw [measureReal_def, ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    simp [halfLaw, stratumLaw]
    norm_num

/-- The covariate law of the trial puts positive mass on each of the four points. -/
theorem coinTrial_covLaw_eq_zero (f : Bool → (Fin 2 → ℝ) → ℝ) {s : Set (Fin 2 → ℝ)}
    (hs : MeasurableSet s) (h0 : (coinTrial f).covLaw s = 0) (b : Bool × Bool) :
    coinCode b ∉ s := by
  rw [Population.covLaw, Measure.map_apply (measurable_coinTrial_X f) hs,
    measure_eq_zero_iff_ae_notMem] at h0
  exact ae_coinTrialLaw_iff.1 h0 (true, b)

/-! ### The additive model -/

/-- The additive surface `x₀ + x₁ + 1[t]`. -/
noncomputable def simOutcome (t : Bool) (x : Fin 2 → ℝ) : ℝ :=
  x 0 + x 1 + if t then 1 else 0

/-- The design `z(t, x) = (1, x₀, x₁, 1[t])`. -/
noncomputable def simDesign (t : Bool) (x : Fin 2 → ℝ) : Fin 4 → ℝ :=
  ![1, x 0, x 1, if t then 1 else 0]

/-- The coefficient `ξ₀ = (0, 1, 1, 1)`. -/
noncomputable def simCoef : Fin 4 → ℝ := ![0, 1, 1, 1]

theorem simDesign_dotProduct (t : Bool) (x : Fin 2 → ℝ) :
    simDesign t x ⬝ᵥ simCoef = simOutcome t x := by
  simp [simDesign, simCoef, simOutcome, dotProduct, Fin.sum_univ_four]

theorem measurable_simOutcome (t : Bool) : Measurable (simOutcome t) := by
  unfold simOutcome; fun_prop

theorem measurable_simDesign (t : Bool) (j : Fin 4) : Measurable fun x => simDesign t x j := by
  fin_cases j
  · exact measurable_const
  · exact measurable_pi_apply 0
  · exact measurable_pi_apply 1
  · exact measurable_const

theorem simOutcome_additive (t : Bool) (x : Fin 2 → ℝ) :
    simDesign t x ⬝ᵥ simCoef = (if t then 1 else 0) + ∑ j, (fun _ y => y) j (x j) := by
  rw [simDesign_dotProduct, simOutcome, Fin.sum_univ_two]; ring

theorem abs_simDesign_le {t : Bool} {x : Fin 2 → ℝ} (h0 : x 0 = 0 ∨ x 0 = 1)
    (h1 : x 1 = 0 ∨ x 1 = 1) (j : Fin 4) : |simDesign t x j| ≤ 1 := by
  fin_cases j
  · simp [simDesign]
  · rcases h0 with h | h <;> simp [simDesign, h]
  · rcases h1 with h | h <;> simp [simDesign, h]
  · cases t <;> simp [simDesign]

/-- **The trial satisfies the linear outcome model.** -/
theorem simExample_linearOutcomeModel :
    (coinTrial simOutcome).LinearOutcomeModel simDesign simCoef where
  measurable_z := measurable_simDesign
  memLp_z a j := MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rcases ω with ⟨_, b₀, b₁⟩
      refine (Real.norm_eq_abs _).le.trans (abs_simDesign_le ?_ ?_ j) <;>
        simp [coinTrial, coinCode])
  memLp_Y t := MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 3
    (ae_of_all _ fun ω => by
      rcases ω with ⟨_, b₀, b₁⟩
      cases t <;> cases b₀ <;> cases b₁ <;> norm_num [coinTrial, coinCode, simOutcome])
  posDef := by
    refine posDef_gram_of_ae (fun j => MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      1 (ae_of_all _ fun ω => ?_)) fun v hv => ?_
    · rcases ω with ⟨a, b₀, b₁⟩
      cases a <;> cases b₀ <;> cases b₁ <;> fin_cases j <;>
        norm_num [simDesign, coinTrial, coinCode]
    · change ∀ᵐ ω ∂coinTrialLaw, _ at hv
      rw [ae_coinTrialLaw_iff] at hv
      have h0 := hv (false, false, false)
      have h1 := hv (false, true, false)
      have h2 := hv (false, false, true)
      have h3 := hv (true, false, false)
      simp [coinTrial, coinCode, simDesign, dotProduct, Fin.sum_univ_four] at h0 h1 h2 h3
      funext j
      fin_cases j <;> simp <;> linarith
  isOutcomeRegression := by
    refine ⟨fun a => by simp_rw [simDesign_dotProduct]; exact measurable_simOutcome a, ?_⟩
    have hg : Measurable fun q : (Fin 2 → ℝ) × Bool => simOutcome q.2 q.1 :=
      measurable_from_prod_countable_left fun t => measurable_simOutcome t
    have hm : Measurable[MeasurableSpace.comap
        (fun ω => ((coinTrial simOutcome).X ω, (coinTrial simOutcome).A ω)) inferInstance]
        (coinTrial simOutcome).obsOutcome :=
      hg.comp (comap_measurable _)
    rw [condExp_of_stronglyMeasurable ((coinTrial_isRandomizedTwoArm _).measurable_X.prodMk
      (coinTrial_isRandomizedTwoArm _).measurable_A).comap_le hm.stronglyMeasurable
      Integrable.of_finite]
    exact ae_of_all _ fun ω => (simDesign_dotProduct _ _).symm

/-! ### The target -/

/-- The target: covariates with the law `dependentCoinLaw` and the additive potential
outcomes. -/
noncomputable def simTarget : Population (Bool × Bool) (Fin 2 → ℝ) Bool :=
  ⟨stratumLaw dependentCoinWeight, coinCode, fun s b => simOutcome s (coinCode b)⟩

instance : IsProbabilityMeasure simTarget.μ := by
  unfold simTarget; infer_instance

theorem simTarget_covLaw : simTarget.covLaw = dependentCoinLaw := rfl

/-- The target arm means: `E_Q[Y(s)] = 1 + 1[s]`. -/
theorem simTarget_armMean (s : Bool) : simTarget.armMean s = 1 + if s then 1 else 0 := by
  have h := integral_dependentCoinLaw (measurable_simOutcome s)
  change ∫ b, simOutcome s (coinCode b) ∂stratumLaw dependentCoinWeight = _
  rw [← integral_map measurable_coinCode.aemeasurable
    (measurable_simOutcome s).aestronglyMeasurable]
  change ∫ x, simOutcome s x ∂dependentCoinLaw = _
  rw [h]
  cases s <;> norm_num [simOutcome]

/-- **Both arms are transported.** -/
theorem simExample_structurallyInvariant (t : Bool) :
    StructurallyInvariant (coinTrial simOutcome).μ (coinTrial simOutcome).X
      ((coinTrial simOutcome).Y t) simTarget.μ simTarget.X (simTarget.Y t) :=
  ⟨simOutcome t, measurable_simOutcome t,
    ae_eq_condExp_comp (measurable_coinTrial_X _) (measurable_simOutcome t) Integrable.of_finite,
    ae_eq_condExp_comp measurable_coinCode (measurable_simOutcome t) Integrable.of_finite⟩

/-- **Overlap**: the target covariate law is dominated by the trial covariate law. -/
theorem simExample_absolutelyContinuous :
    simTarget.covLaw ≪ (coinTrial simOutcome).covLaw := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
  rw [simTarget_covLaw, dependentCoinLaw, Measure.map_apply measurable_coinCode hs,
    show coinCode ⁻¹' s = ∅ from
      Set.eq_empty_of_forall_notMem fun b hb => coinTrial_covLaw_eq_zero _ hs h0 b hb,
    measure_empty]

/-! ### The simulation -/

/-- The simulated covariates are binary. -/
theorem ae_nortaLaw_half_binary :
    ∀ᵐ x ∂nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin),
      (x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1) :=
  Filter.eventually_and.2 ⟨ae_nortaLaw_fairCoin_binary _ 0, ae_nortaLaw_fairCoin_binary _ 1⟩

theorem integrable_id_fairCoin : Integrable (fun y : ℝ => y) fairCoin := by
  have := map_eval_nortaLaw (μ := fun _ : Fin 2 => fairCoin)
    (corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)) (corrMatrix_diag _) 0
  rw [← this]
  refine (integrable_map_measure (g := fun y : ℝ => y) aestronglyMeasurable_id
    (measurable_pi_apply 0).aemeasurable).2 ?_
  refine Integrable.of_bound (measurable_pi_apply 0).aestronglyMeasurable 1
    (ae_nortaLaw_half_binary.mono fun x hx => ?_)
  rcases hx.1 with h | h <;> simp [Function.comp, h]

/-- The law of the two samples: the trial sample and the Gaussian draws, independent. -/
noncomputable abbrev simSampleLaw :
    Measure ((ℕ → Bool × Bool × Bool) × (ℕ → EuclideanSpace ℝ (Fin 2))) :=
  independentSamplesLaw (coinTrial simOutcome).μ (bivariateNormal (1 / 2))

/-- The individual record `(X, A, Y)` of a unit of the trial. -/
noncomputable def simRecord (ω : Bool × Bool × Bool) : (Fin 2 → ℝ) × Bool × ℝ :=
  ((coinTrial simOutcome).X ω, (coinTrial simOutcome).A ω, (coinTrial simOutcome).obsOutcome ω)

/-- The trial records of the sample. -/
noncomputable def simSample (i : ℕ)
    (ω : (ℕ → Bool × Bool × Bool) × (ℕ → EuclideanSpace ℝ (Fin 2))) : (Fin 2 → ℝ) × Bool × ℝ :=
  simRecord (ω.1 i)

/-- The Gaussian draws of the sample. -/
def simDraws (i : ℕ) (ω : (ℕ → Bool × Bool × Bool) × (ℕ → EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) :=
  ω.2 i

theorem isIIDSample_simSample : IsIIDSample simSample simSampleLaw :=
  isIIDSample_independentSamplesLaw_fst _ _ (measurable_of_finite simRecord)

theorem map_simSample : simSampleLaw.map (simSample 0) = (coinTrial simOutcome).ipdLaw :=
  map_independentSamplesLaw_fst _ _ (measurable_of_finite simRecord) 0

theorem isIIDSample_simDraws : IsIIDSample simDraws simSampleLaw :=
  isIIDSample_independentSamplesLaw_snd _ _ (f := id) measurable_id

theorem map_simDraws :
    simSampleLaw.map (simDraws 0) = multivariateGaussian 0 (corrMatrix (1 / 2)) := by
  have := map_independentSamplesLaw_snd (coinTrial simOutcome).μ (bivariateNormal (1 / 2))
    (f := id) measurable_id 0
  rw [Measure.map_id] at this
  exact this

/-! ### Results -/

/-- **Identification in the example.** The simulated standardized mean of arm `false` equals the
target arm mean `1`: every hypothesis of `integral_nortaLaw_eq_armMean_of_additive` is
verified, and the simulated law is not the target covariate law. -/
theorem simExample_armMean :
    ∫ x, simOutcome false x ∂nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin) = 1 ∧
      simTarget.armMean false = 1 := by
  have h := integral_nortaLaw_eq_armMean_of_additive (T := coinTrial simOutcome) (Q := simTarget)
    (μ := fun _ => fairCoin) (t := false) (s := false)
    (corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)) (corrMatrix_diag _)
    (fun j => by rw [simTarget_covLaw]; exact map_eval_dependentCoinLaw j)
    (measurable_coinTrial_X _) measurable_coinCode
    Integrable.of_finite
    ((coinTrial_isRandomizedTwoArm _).isCondMean (fun t => Integrable.of_finite)
      ⟨fun a => measurable_simOutcome a, (simExample_linearOutcomeModel.isOutcomeRegression).2.trans
        (ae_of_all _ fun ω => simDesign_dotProduct _ _)⟩ false)
    (simExample_structurallyInvariant false) simExample_absolutelyContinuous
    (fun x => by rw [← simDesign_dotProduct]; exact simOutcome_additive false x)
    (fun _ => integrable_id_fairCoin)
  rw [h, simTarget_armMean]
  norm_num

/-- **The unanchored simulated comparison in the example.** Arm `false` of the trial is fitted
by least squares and averaged over `n` simulated covariate vectors, and the target mean of
`true` is reported exactly as `2`; the unanchored estimator converges in probability to the
target effect `1`. Every hypothesis of `tendstoInMeasure_simulated_leastSquares_unanchored` is
verified. -/
theorem simExample_unanchored :
    TendstoInMeasure simSampleLaw
      (fun n ω => id (simTarget.armMean true) - id (sampleMean (fun x => simDesign false x ⬝ᵥ
        leastSquaresFit (recordDesign simDesign) recordResponse simSample n ω)
        (fun i ω => nortaMap (fun _ => fairCoin) (simDraws i ω)) n ω))
      atTop (fun _ => 1) := by
  have he : simTarget.marginalEffect id false true = 1 := by
    simp only [Population.marginalEffect, id, simTarget_armMean]; norm_num
  rw [← he]
  exact tendstoInMeasure_simulated_leastSquares_unanchored (coinTrial_isRandomizedTwoArm _)
    simExample_linearOutcomeModel isIIDSample_simSample map_simSample measurable_coinCode
    Integrable.of_finite (simExample_structurallyInvariant false) simExample_absolutelyContinuous
    (corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)) (corrMatrix_diag _)
    (fun j => by rw [simTarget_covLaw]; exact map_eval_dependentCoinLaw j)
    (simOutcome_additive false)
    (fun _ => integrable_id_fairCoin)
    (fun j => Integrable.of_bound (measurable_simDesign false j).aestronglyMeasurable 1
      (ae_nortaLaw_half_binary.mono fun x hx => (Real.norm_eq_abs _).le.trans
        (abs_simDesign_le hx.1 hx.2 j)))
    isIIDSample_simDraws map_simDraws tendsto_id (tendstoInMeasure_const _)
    continuousAt_id continuousAt_id

/-! ### A surface with an interacting pair -/

/-- The interacting surface `x₀ + x₁ + x₀x₁ + 1[t]`. -/
noncomputable def simInteraction (t : Bool) (x : Fin 2 → ℝ) : ℝ :=
  x 0 + x 1 + x 0 * x 1 + if t then 1 else 0

theorem measurable_simInteraction (t : Bool) : Measurable (simInteraction t) := by
  unfold simInteraction; fun_prop

/-- The simulated law of the example. -/
noncomputable abbrev simLaw : Measure (Fin 2 → ℝ) :=
  nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin)

/-- Every function is integrable under the simulated law, which lives on four points. -/
theorem integrable_simLaw (f : (Fin 2 → ℝ) → ℝ) : Integrable f simLaw :=
  (integral_binary_expand ae_nortaLaw_half_binary f).1

/-- The target whose covariate law is the simulated law: its covariate pair has the Gaussian
copula with parameter `1/2`. -/
noncomputable def pairTarget : Population (Fin 2 → ℝ) (Fin 2 → ℝ) Bool :=
  ⟨simLaw, id, simInteraction⟩

instance : IsProbabilityMeasure pairTarget.μ := by
  unfold pairTarget; infer_instance

theorem pairTarget_covLaw : pairTarget.covLaw = simLaw := Measure.map_id

/-- The target arm mean of `false` under the interacting surface is `1/2 + 1/2 + 1/3 = 4/3`. -/
theorem pairTarget_armMean : pairTarget.armMean false = 4 / 3 := by
  change ∫ x, simInteraction false x ∂simLaw = 4 / 3
  rw [(integral_binary_expand ae_nortaLaw_half_binary _).2,
    integral_eval_nortaLaw_fairCoin (corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num))
      (corrMatrix_diag _),
    integral_eval_nortaLaw_fairCoin (corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num))
      (corrMatrix_diag _), integral_mul_nortaLaw_half]
  norm_num [simInteraction, binaryInteraction]

/-- A binary vector is one of the four coin codes. -/
theorem exists_coinCode {x : Fin 2 → ℝ} (h0 : x 0 = 0 ∨ x 0 = 1) (h1 : x 1 = 0 ∨ x 1 = 1) :
    ∃ b, coinCode b = x := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact ⟨(false, false), funext fun i => by fin_cases i <;> simp [coinCode, h0, h1]⟩
  · exact ⟨(false, true), funext fun i => by fin_cases i <;> simp [coinCode, h0, h1]⟩
  · exact ⟨(true, false), funext fun i => by fin_cases i <;> simp [coinCode, h0, h1]⟩
  · exact ⟨(true, true), funext fun i => by fin_cases i <;> simp [coinCode, h0, h1]⟩

/-- **Identification with an interacting pair in the example.** For the interacting surface
`x₀ + x₁ + x₀x₁ + 1[t]` and a target whose covariate pair has the Gaussian copula with
parameter `1/2` and fair coin margins, the simulated standardized mean of arm `false` is the
target arm mean, `4/3`. Every hypothesis of `integral_nortaLaw_eq_armMean_of_pair` is
verified. -/
theorem simExample_pair :
    ∫ x, simInteraction false x ∂simLaw = pairTarget.armMean false ∧
      pairTarget.armMean false = 4 / 3 := by
  have hR := corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)
  have hmarg : ∀ j, pairTarget.covLaw.map (fun x => x j) = fairCoin := fun j => by
    rw [pairTarget_covLaw, map_eval_nortaLaw hR (corrMatrix_diag _) j]
  have hpair : pairTarget.covLaw.map (fun x => (x 0, x 1)) =
      (bivariateNormal (corrMatrix (1 / 2) 0 1)).map (fun z =>
        (quantile fairCoin (cdf (gaussianReal 0 1) (z 0)),
          quantile fairCoin (cdf (gaussianReal 0 1) (z 1)))) := by
    rw [pairTarget_covLaw, map_pair_nortaLaw hR (corrMatrix_diag _)]
  have hm : Measurable fun x : Fin 2 → ℝ => (x 0, x 1) := by fun_prop
  have hov : pairTarget.covLaw ≪ (coinTrial simInteraction).covLaw := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [pairTarget_covLaw]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 ae_nortaLaw_half_binary)
    intro hbin
    obtain ⟨b, rfl⟩ := exists_coinCode hbin.1 hbin.2
    exact coinTrial_covLaw_eq_zero _ hs h0 b hx
  refine ⟨integral_nortaLaw_eq_armMean_of_pair (T := coinTrial simInteraction) (Q := pairTarget)
    (t := false) (s := false) hR (corrMatrix_diag _) (fun j _ _ => hmarg j)
    hpair (measurable_coinTrial_X _)
    measurable_id (integrable_simLaw _)
    ⟨measurable_simInteraction false, ae_eq_condExp_comp (measurable_coinTrial_X _)
      (measurable_simInteraction false) Integrable.of_finite⟩
    ⟨simInteraction false, measurable_simInteraction false,
      ae_eq_condExp_comp (measurable_coinTrial_X _) (measurable_simInteraction false)
        Integrable.of_finite,
      ae_eq_condExp_comp measurable_id (measurable_simInteraction false) (integrable_simLaw _)⟩
    hov (c := 0) (f := fun _ y => y) (g := fun p => p.1 * p.2)
    (fun x => by simp [simInteraction, Fin.sum_univ_two]) (fun _ => integrable_id_fairCoin)
    ?_, pairTarget_armMean⟩
  rw [pairTarget_covLaw, integrable_map_measure (by fun_prop) hm.aemeasurable]
  exact integrable_simLaw _

/-- **The closed form in the example**: the simulated standardized mean of `x₀ + x₁` is the sum
of the margin means, `1/2 + 1/2`; every hypothesis of `integral_nortaLaw_additive` is
verified. -/
theorem simExample_additive_closedForm :
    ∫ x, (0 + ∑ j, (fun _ y => y) j (x j)) ∂simLaw = 1 := by
  have hR := corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)
  have hmean : ∫ t, t ∂fairCoin = 1 / 2 := by
    rw [← integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _) 0]
    exact (integral_nortaLaw_eval (f := fun t => t) (μ := fun _ => fairCoin) hR
      (corrMatrix_diag _) 0 aestronglyMeasurable_id).symm
  rw [integral_nortaLaw_additive (μ := fun _ => fairCoin) hR (corrMatrix_diag _) 0
    (fun _ => integrable_id_fairCoin)]
  simp only [Fin.sum_univ_two, hmean]
  norm_num

/-! ### The limit law -/

/-- Integrals against the trial law are averages over the eight points. -/
theorem integral_coinTrialLaw (F : Bool × Bool × Bool → ℝ) : ∫ ω, F ω ∂coinTrialLaw =
    (F (true, true, true) + F (true, true, false) + F (true, false, true) +
      F (true, false, false) + F (false, true, true) + F (false, true, false) +
      F (false, false, true) + F (false, false, false)) / 8 := by
  rw [integral_prod _ Integrable.of_finite, integral_halfLaw]
  simp only [integral_prod _ Integrable.of_finite, integral_halfLaw]
  ring

/-- The observed outcome of a trial record. -/
noncomputable def recordOutcome (p : (Fin 2 → ℝ) × Bool × ℝ) : ℝ := p.2.2

theorem measurable_recordOutcome : Measurable recordOutcome := by
  unfold recordOutcome; fun_prop

theorem integral_ipdLaw_simOutcome (F : ℝ → ℝ) (hF : Measurable F) :
    ∫ p, F (recordOutcome p) ∂(coinTrial simOutcome).ipdLaw =
      (F 3 + 2 * F 2 + F 1 + F 2 + 2 * F 1 + F 0) / 8 := by
  rw [Trial.ipdLaw, integral_map (f := fun p => F (recordOutcome p))
    (measurable_of_finite _).aemeasurable (hF.comp measurable_recordOutcome).aestronglyMeasurable]
  change ∫ ω, F (simOutcome ω.1 (coinCode ω.2)) ∂coinTrialLaw = _
  rw [integral_coinTrialLaw]
  norm_num [simOutcome, coinCode]
  ring

/-- The simulated average of `x₀ + x₁` as a function of the Gaussian draws. -/
theorem measurable_simAverage (n : ℕ) (c : ℝ) :
    Measurable fun z : ℕ → EuclideanSpace ℝ (Fin 2) => √(n : ℝ) *
      ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, simOutcome false (nortaMap (fun _ => fairCoin) (z i)) -
        c) := by
  refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_simOutcome false).comp ((measurable_nortaMap _).comp
      (measurable_pi_apply i)))).sub measurable_const)

/-- The mean observed outcome of the trial records as a function of the trial sample. -/
theorem measurable_trialAverage (n : ℕ) (c : ℝ) :
    Measurable fun ω : ℕ → Bool × Bool × Bool => √(n : ℝ) *
      ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, recordOutcome (simRecord (ω i)) - c) := by
  refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_of_finite (fun b => recordOutcome (simRecord b))).comp
      (measurable_pi_apply i))).sub measurable_const)

/-- **The limit law in the example.** The scaled Monte Carlo error of the simulated average of
`x₀ + x₁` (target mean `1`, simulated variance `2/3`) plus the scaled error of the mean observed
outcome of the independent trial sample (mean `3/2`, variance `3/4`) converges in distribution
to `N(0, 2/3 + 3/4)`. Every hypothesis of `tendstoInDistribution_simulated_contrast` is
verified. -/
theorem simExample_limitLaw :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (sampleMean (simOutcome false) (fun i ω => nortaMap (fun _ => fairCoin) (simDraws i ω))
        n ω - 1) + √(n : ℝ) * (sampleMean recordOutcome simSample n ω - 3 / 2))
      atTop id (fun _ => simSampleLaw) (gaussianReal 0 (2 / 3 + 3 / 4)) := by
  have hR := corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)
  have hm1 : ∫ x, simOutcome false x ∂simLaw = 1 := simExample_armMean.1
  have hv1 : (∫ x, (simOutcome false x - ∫ y, simOutcome false y ∂simLaw) ^ 2 ∂simLaw).toNNReal =
      2 / 3 := by
    rw [hm1, (integral_binary_expand ae_nortaLaw_half_binary _).2,
      integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _),
      integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _), integral_mul_nortaLaw_half]
    norm_num [simOutcome, binaryInteraction]
    rw [Real.toNNReal_div (by norm_num)]; norm_num
  have hm2 : ∫ p, recordOutcome p ∂(coinTrial simOutcome).ipdLaw = 3 / 2 := by
    have := integral_ipdLaw_simOutcome (fun y => y) measurable_id
    norm_num at this
    rw [this]
  have hv2 : (∫ p, (recordOutcome p - ∫ q, recordOutcome q ∂(coinTrial simOutcome).ipdLaw) ^ 2
      ∂(coinTrial simOutcome).ipdLaw).toNNReal = 3 / 4 := by
    rw [hm2, integral_ipdLaw_simOutcome (fun y => (y - 3 / 2) ^ 2) (by fun_prop)]
    norm_num
    rw [Real.toNNReal_div (by norm_num)]; norm_num
  have hrec2 : MemLp recordOutcome 2 (coinTrial simOutcome).ipdLaw := by
    rw [Trial.ipdLaw, memLp_map_measure_iff measurable_recordOutcome.aestronglyMeasurable
      (measurable_of_finite _).aemeasurable]
    exact (memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).2
      Integrable.of_finite
  have hW := tendstoInDistribution_sampleMean_of_map isIIDSample_simSample map_simSample
    measurable_recordOutcome hrec2 (Y := id) (P' := gaussianReal 0 (3 / 4))
    (by rw [hv2]; exact HasLaw.id)
  rw [hm2] at hW
  have h := tendstoInDistribution_simulated_contrast (μ := fun _ => fairCoin)
    isIIDSample_simDraws map_simDraws (measurable_simOutcome false)
    ((memLp_two_iff_integrable_sq (measurable_simOutcome false).aestronglyMeasurable).2
      (integrable_simLaw _)) hv1 hW HasLaw.id
    (fun n => ((indepFun_independentSamplesLaw (coinTrial simOutcome).μ
      (bivariateNormal (1 / 2))).symm.comp (measurable_simAverage n _)
        (measurable_trialAverage n _)))
    HasLaw.id
  rw [hm1] at h
  exact h

end PopulationAdjustment

end CausalInference
