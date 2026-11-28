/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.GeneralLikelihoodAggregate
public import CausalInference.NetworkMetaRegression.AggregationIdentity
public import CausalInference.PopulationAdjustment.OutcomeModelFitLikelihood

/-!
# The general likelihood of the multilevel model and its reductions

The multilevel network meta-regression model (Phillippo et al. 2020) gives a patient of arm
`(j, k)` with covariates `x` an outcome with density `f(η_{jk}(x), ·)` with respect to a
dominating measure `ν`, at the linear predictor `η_{jk}(x) = μ_j + xᵀβ₁ + γ_k + xᵀβ₂,k`. A patient
with individual data contributes `f(η_{jk}(x), y)`. A patient of an arm with aggregate data has
covariates drawn from the covariate law `F_j` of the study, which are not reported, and
contributes the integrated density `∫ f(η_{jk}(x), y) F_j(dx)`
(`MultilevelModel.marginalLikelihood`).

* **It is the density of the data** (`MultilevelModel.map_data_eq_withDensity`): if the outcomes
  of the patients with individual data are independent given their covariates and the pairs
  (covariates, outcome) of the patients with aggregate data are independent with law `F_j ⊗ κ`,
  the law of all outcomes has density `marginalLikelihood` with respect to `ν ⊗ ⋯ ⊗ ν`.
* **Individual data only** (`MultilevelModel.marginalLikelihood_nil`): with no aggregate record it
  is the likelihood `MultilevelModel.likelihood` of individual data. This holds by unfolding.
* **The generalized linear reduction** (`MultilevelModel.marginalLikelihood_eq_likelihood`): if
  `f(η, y) = L(g⁻¹(η), y)` with `L(·, y)` affine, the integrated factor is the plug in factor
  `L(θ_{jk}, y)` at the aggregate arm mean `θ_{jk} = ∫ g⁻¹(η_{jk}) dF_j`, so the general likelihood
  is `MultilevelModel.likelihood`. This covers the logistic kernel `logisticKernel` of a binary
  outcome (`MultilevelModel.marginalLikelihood_logisticDens`). It fails for a kernel that is not
  affine in the mean: the Poisson kernel at a two point covariate law
  (`MultilevelModel.marginalLikelihood_ne_likelihood_poisson`).
* **The number of events** (`MultilevelModel.map_card_singleton_eq_likelihood`): for a binary
  outcome, the reported number of events of an arm with aggregate data has the density
  `MultilevelModel.likelihood` with the binomial summary density `binomialMass`.
* **No covariate effects** (`MultilevelModel.marginalLikelihood_eq_armLikelihood`): with
  `β₁ = 0` and `β₂ = 0` the general likelihood is the arm based network likelihood
  `armLikelihood` for every family of covariate laws.
* **Categorical outcomes** (`snd_compProd_categorical`): if the outcome takes the values of a
  finite set with probabilities `π_c(x)`, the outcome of a patient with unreported covariates has
  the categorical law with probabilities `∫ π_c dF`.

## Main definitions

* `MultilevelModel.marginalLikelihood`, `poissonDens`.

## Main results

* `MultilevelModel.map_data_eq_withDensity`, `MultilevelModel.marginalLikelihood_nil`,
  `MultilevelModel.marginalLikelihood_eq_likelihood`,
  `MultilevelModel.marginalLikelihood_logisticDens`,
  `MultilevelModel.marginalLikelihood_ne_likelihood_poisson`,
  `MultilevelModel.map_card_singleton_eq_likelihood`,
  `MultilevelModel.marginalLikelihood_eq_armLikelihood`, `snd_compProd_categorical`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory NetworkMetaAnalysis PopulationAdjustment
open scoped ENNReal

/-- The **Bernoulli mass** `θ` at `y = 1` and `1 - θ` elsewhere, the summary density of one binary
outcome with event probability `θ`. -/
noncomputable def binaryMass (θ y : ℝ) : ℝ := if y = 1 then θ else 1 - θ

/-- The **Poisson density** `θ^y e^{-θ} / y!` at the natural number `y` (a real outcome is read
through its floor). -/
noncomputable def poissonDens (θ y : ℝ) : ℝ := θ ^ ⌊y⌋₊ * Real.exp (-θ) / (⌊y⌋₊.factorial)

namespace MultilevelModel

variable {J K : Type*} {p : ℕ} {arms : J → Finset K}

/-- The **general likelihood of the multilevel model** with individual outcome density `f` (of the
outcome given the linear predictor) and covariate laws `F_j` of the studies: an individual record
`(a, x, y)` of the arm `a = (j, k)` contributes `f(η_{jk}(x), y)` and a patient `(a, y)` of an arm
with aggregate data contributes the integrated density `∫ f(η_{jk}(x), y) F_j(dx)`. -/
noncomputable def marginalLikelihood (f : ℝ → ℝ → ℝ) (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ))
    (agd : List (ArmIndex arms × ℝ)) : ℝ≥0∞ :=
  (ipd.map fun d => ENNReal.ofReal (f (M.eta (M.μ d.1.1.1) d.1.1.2 d.2.1) d.2.2)).prod *
    (agd.map fun d =>
      ∫⁻ x, ENNReal.ofReal (f (M.eta (M.μ d.1.1.1) d.1.1.2 x) d.2) ∂F d.1.1.1).prod

/-- **With individual data only the general likelihood is `MultilevelModel.likelihood`**, for every
summary density and inverse link. This holds by unfolding: both aggregate factors are empty
products. -/
theorem marginalLikelihood_nil (f L : ℝ → ℝ → ℝ) (ginv : ℝ → ℝ) (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) :
    M.marginalLikelihood f F ipd [] = M.likelihood f L ginv F ipd [] := by
  simp [marginalLikelihood, likelihood]

/-- **The general likelihood is the density of the data.** Let `ν` be a σ-finite measure on `ℝ`
and `f` jointly measurable. For every arm `a` let `κ_a` be a Markov kernel whose law at the
covariates `x` has density `f(η_a(x), ·)` with respect to `ν`. Let the outcomes of the patients
`i` with individual data (arm `aI i`, covariates `xI i`) be independent with laws `κ_{aI i}(xI i)`,
let the pairs (covariates, outcome) of the patients `i` with aggregate data (arm `aA i`) be
independent with laws `F_j ⊗ κ_{aA i}`, `j` the study of the arm, and let the two groups be
independent. Then the law of the outcomes `(yI, yA)` has density
`marginalLikelihood f M F (records of yI) (records of yA)` with respect to `ν ⊗ ⋯ ⊗ ν`. -/
theorem map_data_eq_withDensity (f : ℝ → ℝ → ℝ) (hf : Measurable (Function.uncurry f))
    (M : MultilevelModel J K p) (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
    (ν : Measure ℝ) [SigmaFinite ν] (κ : ArmIndex arms → Kernel (Fin p → ℝ) ℝ)
    [∀ a, IsMarkovKernel (κ a)]
    (hκ : ∀ a x, κ a x = ν.withDensity fun y => ENNReal.ofReal (f (M.eta (M.μ a.1.1) a.1.2 x) y))
    {nI nA : ℕ} (aI : Fin nI → ArmIndex arms) (xI : Fin nI → Fin p → ℝ)
    (aA : Fin nA → ArmIndex arms) :
    (Measure.pi fun i => κ (aI i) (xI i)).prod
        ((Measure.pi fun i => F (aA i).1.1 ⊗ₘ κ (aA i)).map fun z i => (z i).2) =
      ((Measure.pi fun _ : Fin nI => ν).prod (Measure.pi fun _ : Fin nA => ν)).withDensity
        fun y => M.marginalLikelihood f F (List.ofFn fun i => (aI i, xI i, y.1 i))
          (List.ofFn fun i => (aA i, y.2 i)) := by
  have hη : ∀ a : ArmIndex arms, Measurable fun q : (Fin p → ℝ) × ℝ =>
      ENNReal.ofReal (f (M.eta (M.μ a.1.1) a.1.2 q.1) q.2) := fun a =>
    ENNReal.measurable_ofReal.comp (hf.comp
      (((M.continuous_eta _ _).measurable.comp measurable_fst).prodMk measurable_snd))
  have hI : Measure.pi (fun i => κ (aI i) (xI i)) = (Measure.pi fun _ : Fin nI => ν).withDensity
      fun y => ∏ i, ENNReal.ofReal (f (M.eta (M.μ (aI i).1.1) (aI i).1.2 (xI i)) (y i)) := by
    have : ∀ i, IsProbabilityMeasure (ν.withDensity fun y =>
        ENNReal.ofReal (f (M.eta (M.μ (aI i).1.1) (aI i).1.2 (xI i)) y)) := fun i => by
      rw [← hκ]; infer_instance
    simp_rw [hκ]
    exact pi_withDensity ν
      (fun i y => ENNReal.ofReal (f (M.eta (M.μ (aI i).1.1) (aI i).1.2 (xI i)) y))
      fun i => ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.prodMk measurable_id))
  have hA := map_pi_compProd_eq_withDensity (fun i => F (aA i).1.1) ν (fun i => κ (aA i))
    (fun i x y => ENNReal.ofReal (f (M.eta (M.μ (aA i).1.1) (aA i).1.2 x) y))
    (fun i => hη (aA i)) (fun i => Filter.Eventually.of_forall fun x => hκ (aA i) x)
  rw [hI, hA, prod_withDensity]
  · congr 1
    funext y
    simp [marginalLikelihood, List.map_ofFn, List.prod_ofFn, Function.comp_def]
  · exact Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (hf.comp (measurable_const.prodMk (measurable_pi_apply i)))
  · have hm : ∀ i, Measurable fun y : ℝ =>
        ∫⁻ x, ENNReal.ofReal (f (M.eta (M.μ (aA i).1.1) (aA i).1.2 x) y) ∂F (aA i).1.1 :=
      fun i => (hη (aA i)).lintegral_prod_left'
    exact Finset.measurable_prod _ fun i _ => (hm i).comp (measurable_pi_apply i)

/-! ### The generalized linear reduction -/

/-- **A kernel affine in the mean integrates to the plug in factor.** Let the individual density
be `f(η, y) = L(g⁻¹(η), y)` with `L(θ, y) = A(y) + B(y) θ` for every `θ`, let the covariate laws
be probability laws, and for every aggregate record let the surface `g⁻¹(η_{jk})` be integrable
and `f(η_{jk}(x), y) ≥ 0` almost everywhere. Then the general likelihood is
`MultilevelModel.likelihood f L g⁻¹`: each integrated factor is the plug in factor `L(θ_{jk}, y)`
at the aggregate arm mean `θ_{jk} = ∫ g⁻¹(η_{jk}) dF_j`. -/
theorem marginalLikelihood_eq_likelihood (f L : ℝ → ℝ → ℝ) (ginv : ℝ → ℝ) {A B : ℝ → ℝ}
    (hfL : ∀ η y, f η y = L (ginv η) y) (hL : ∀ θ y, L θ y = A y + B y * θ)
    (M : MultilevelModel J K p) (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
    (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) (agd : List (ArmIndex arms × ℝ))
    (hint : ∀ d ∈ agd, Integrable (M.surface ginv (M.μ d.1.1.1) d.1.1.2) (F d.1.1.1))
    (hnn : ∀ d ∈ agd, ∀ᵐ x ∂F d.1.1.1, 0 ≤ f (M.eta (M.μ d.1.1.1) d.1.1.2 x) d.2) :
    M.marginalLikelihood f F ipd agd = M.likelihood f L ginv F ipd agd := by
  simp only [marginalLikelihood, likelihood]
  congr 1
  refine congrArg List.prod (List.map_congr_left fun d hd => ?_)
  have hfa : ∀ x, f (M.eta (M.μ d.1.1.1) d.1.1.2 x) d.2 =
      A d.2 + B d.2 * M.surface ginv (M.μ d.1.1.1) d.1.1.2 x := fun x => by
    rw [hfL, hL]; rfl
  have hi : Integrable (fun x => f (M.eta (M.μ d.1.1.1) d.1.1.2 x) d.2) (F d.1.1.1) := by
    simp_rw [hfa]
    exact (integrable_const _).add ((hint d hd).const_mul _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (hnn d hd)]
  congr 1
  simp_rw [hfa]
  rw [integral_add (integrable_const _) ((hint d hd).const_mul _), integral_const_mul,
    integral_const, probReal_univ, one_smul, hL, armMean]

/-- **The logistic multilevel model: the general likelihood is `MultilevelModel.likelihood`.** For
the logistic kernel `logisticDens` of a binary outcome, every model and every family of
probability laws of the covariates, the general likelihood is the likelihood with the inverse
link `σ` and the summary density `binaryMass` at the aggregate event probabilities
`θ_{jk} = ∫ σ(η_{jk}) dF_j`. -/
theorem marginalLikelihood_logisticDens (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
    (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) (agd : List (ArmIndex arms × ℝ)) :
    M.marginalLikelihood logisticDens F ipd agd =
      M.likelihood logisticDens binaryMass Real.sigmoid F ipd agd := by
  refine marginalLikelihood_eq_likelihood logisticDens binaryMass Real.sigmoid
    (A := fun y => if y = 1 then 0 else 1) (B := fun y => if y = 1 then 1 else -1)
    (fun η y => rfl) (fun θ y => ?_) M F ipd agd (fun d _ => ?_)
    (fun d _ => Filter.Eventually.of_forall fun x => (logisticDens_pos _ _).le)
  · simp only [binaryMass]
    split_ifs <;> ring
  · refine Integrable.of_bound (M.measurable_surface continuous_sigmoid.measurable _ _
      ).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, surface, abs_of_pos (Real.sigmoid_pos _)]
    exact (Real.sigmoid_lt_one _).le

/-- **The likelihood of the logistic multilevel model is the density of the data.** With the
logistic kernel on `{0, 1}` (dominating measure `δ₀ + δ₁`) and the data of
`map_data_eq_withDensity`, the law of all outcomes has density
`MultilevelModel.likelihood logisticDens binaryMass σ` with respect to `ν ⊗ ⋯ ⊗ ν`. -/
theorem map_data_eq_withDensity_likelihood_logistic (M : MultilevelModel J K p)
    (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
    (κ : ArmIndex arms → Kernel (Fin p → ℝ) ℝ) [∀ a, IsMarkovKernel (κ a)]
    (hκ : ∀ a x, κ a x = (Measure.dirac (0 : ℝ) + Measure.dirac 1).withDensity
      fun y => ENNReal.ofReal (logisticDens (M.eta (M.μ a.1.1) a.1.2 x) y))
    {nI nA : ℕ} (aI : Fin nI → ArmIndex arms) (xI : Fin nI → Fin p → ℝ)
    (aA : Fin nA → ArmIndex arms) :
    (Measure.pi fun i => κ (aI i) (xI i)).prod
        ((Measure.pi fun i => F (aA i).1.1 ⊗ₘ κ (aA i)).map fun z i => (z i).2) =
      ((Measure.pi fun _ : Fin nI => (Measure.dirac 0 + Measure.dirac 1 : Measure ℝ)).prod
          (Measure.pi fun _ : Fin nA =>
            (Measure.dirac 0 + Measure.dirac 1 : Measure ℝ))).withDensity
        fun y => M.likelihood logisticDens binaryMass Real.sigmoid F
          (List.ofFn fun i => (aI i, xI i, y.1 i)) (List.ofFn fun i => (aA i, y.2 i)) := by
  rw [map_data_eq_withDensity logisticDens logisticKernel.measurable_dens M F _ κ hκ aI xI aA]
  simp_rw [marginalLikelihood_logisticDens]

end MultilevelModel

/-- The model of the Poisson witness: one study, one treatment, one covariate with prognostic
effect `log 3` and every other coefficient `0`. -/
noncomputable def poissonWitnessModel : MultilevelModel Unit Unit 1 :=
  ⟨fun _ => 0, fun _ => Real.log 3, fun _ => 0, fun _ _ => 0⟩

/-- The single arm of the Poisson witness. -/
def poissonWitnessArm : ArmIndex (fun _ : Unit => (Finset.univ : Finset Unit)) :=
  ⟨((), ()), Finset.mem_univ _⟩

namespace MultilevelModel

variable {J K : Type*} {p : ℕ} {arms : J → Finset K}

/-- **The plug in factor is not the integrated factor for the Poisson kernel.** With the
Poisson kernel at the mean `exp η` (inverse link `exp`), the model `poissonWitnessModel` and the
covariate law with atoms `0` and `1` of mass `1/2`, the patient means are `1` and `3`, and a
patient of the arm with aggregate data and outcome `0` has the integrated factor
`(e^{-1} + e^{-3}) / 2`, while the plug in factor at the arm mean `θ = 2` is `e^{-2}`, which is
strictly smaller. So the general likelihood is not `MultilevelModel.likelihood` for this kernel. -/
theorem marginalLikelihood_ne_likelihood_poisson :
    poissonWitnessModel.marginalLikelihood (fun η y => poissonDens (Real.exp η) y)
        (fun _ => twoAtomLaw (fun _ => 0) (fun _ => 1) (1 / 2)) [] [(poissonWitnessArm, 0)] =
      ENNReal.ofReal ((Real.exp (-1) + Real.exp (-3)) / 2) ∧
    poissonWitnessModel.likelihood (fun η y => poissonDens (Real.exp η) y) poissonDens Real.exp
        (fun _ => twoAtomLaw (fun _ => 0) (fun _ => 1) (1 / 2)) [] [(poissonWitnessArm, 0)] =
      ENNReal.ofReal (Real.exp (-2)) ∧
    Real.exp (-2) < (Real.exp (-1) + Real.exp (-3)) / 2 := by
  have h0 : poissonWitnessModel.eta 0 () (fun _ => 0) = 0 := by
    simp [poissonWitnessModel, eta, metaRegressionPredictor]
  have h1 : poissonWitnessModel.eta 0 () (fun _ => 1) = Real.log 3 := by
    simp [poissonWitnessModel, eta, metaRegressionPredictor, dotProduct]
  have hμ : poissonWitnessModel.μ () = 0 := rfl
  have hd : ∀ θ : ℝ, poissonDens θ 0 = Real.exp (-θ) := fun θ => by simp [poissonDens]
  have h3 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp only [marginalLikelihood, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
      mul_one, one_mul, twoAtomLaw, poissonWitnessArm]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
      lintegral_dirac]
    simp only [hμ, h0, h1, hd, Real.exp_zero, h3, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    norm_num
    ring
  · simp only [likelihood, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
      mul_one, one_mul, poissonWitnessArm, armMean, surface]
    rw [integral_twoAtomLaw (by norm_num) (by norm_num)]
    simp only [hμ, h0, h1, hd, Real.exp_zero, h3]
    norm_num
  · have e2 : Real.exp (-1) = Real.exp (-2) * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have e3 : Real.exp (-3) = Real.exp (-2) * Real.exp (-1) := by
      rw [← Real.exp_add]; norm_num
    have hm : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
    have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hpos := Real.exp_pos (-2)
    have hpos1 := Real.exp_pos (-1)
    rw [e2, e3]
    nlinarith [sq_nonneg (Real.exp 1 - 1), Real.exp_pos 1]

/-! ### The reported number of events -/

/-- **The reported number of events has the density `MultilevelModel.likelihood`.** Let the
covariates of the `n` patients of the arm `a = (j, k)` with aggregate data be drawn from the
probability law `F_j`, let the outcome be binary with event probability `g⁻¹(η_{jk}(x))` given
the covariates `x` (`g⁻¹` measurable), and let the pairs (covariates, outcome) of the
patients be independent. Then the number of events takes the value `s` with probability
`MultilevelModel.likelihood f L g⁻¹ F [] [(a, s)]`, the aggregate factor with the binomial summary
density `L(θ, y) = (n choose y) θ^y (1 - θ)^(n - y)`, for every individual density `f`. -/
theorem map_card_singleton_eq_likelihood (f : ℝ → ℝ → ℝ) {ginv : ℝ → ℝ}
    (hginv : Measurable ginv)
    (M : MultilevelModel J K p) (F : J → Measure (Fin p → ℝ)) [∀ j, IsProbabilityMeasure (F j)]
    (a : ArmIndex arms) (κ : Kernel (Fin p → ℝ) Bool) [IsMarkovKernel κ]
    (hκ : ∀ x, κ x = Measure.count.withDensity fun b => ENNReal.ofReal
      (if b then M.surface ginv (M.μ a.1.1) a.1.2 x else 1 - M.surface ginv (M.μ a.1.1) a.1.2 x))
    (n s : ℕ) :
    (Measure.pi fun _ : Fin n => F a.1.1 ⊗ₘ κ).map
        (fun z => (Finset.univ.filter fun i => (z i).2 = true).card) {s} =
      M.likelihood f (fun θ y => binomialMass n θ ⌊y⌋₊) ginv F [] [(a, (s : ℝ))] := by
  rw [map_pi_compProd_card_singleton (F a.1.1) (M.measurable_surface hginv _ _) κ
    (Filter.Eventually.of_forall hκ) s]
  simp [likelihood, armMean]

/-! ### No covariate effects -/

variable [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

/-- **Without covariate effects the general likelihood is the arm based network likelihood.** If
`β₁ = 0` and `β₂ = 0`, then for every family of probability laws of the covariates and every data
set, the general likelihood is `armLikelihood f f id` at `nmaCoef`: each integrated factor is
the density at the arm design `(X β)(j, k)`, and the covariates of the individual records are
dropped. -/
theorem marginalLikelihood_eq_armLikelihood (f : ℝ → ℝ → ℝ) (M : MultilevelModel J K p)
    (hβ₁ : M.β₁ = 0) (hβ₂ : ∀ k, M.β₂ k = 0) (F : J → Measure (Fin p → ℝ))
    [∀ j, IsProbabilityMeasure (F j)] (base : J → K) (r : K)
    (ipd : List (ArmIndex arms × (Fin p → ℝ) × ℝ)) (agd : List (ArmIndex arms × ℝ)) :
    M.marginalLikelihood f F ipd agd =
      armLikelihood f f id base r (M.nmaCoef base r) (ipd.map fun d => (d.1, d.2.2)) agd := by
  rw [← likelihood_eq_armLikelihood f f id M hβ₁ hβ₂ F base r]
  simp only [marginalLikelihood, likelihood,
    armMean_eq_armDesign_mulVec (ginv := id) M hβ₁ hβ₂ F base r,
    eta_eq_armDesign_mulVec M hβ₁ hβ₂ base r, lintegral_const, measure_univ, mul_one, id]

end MultilevelModel

/-! ### Categorical outcomes -/

/-- **The outcome of a patient with unreported covariates has the integrated categorical law.**
Let the outcome take values in a countable set `𝒞` with probabilities `π_c(x) ≥ 0` given the
covariates `x` (each `π_c` measurable), so that the Markov kernel `κ` has density `π(x)` with
respect to the counting measure for `F`-almost every `x`, and let the covariates have the
probability law `F`. Then the outcome of a patient drawn from `F` has density `c ↦ ∫ π_c dF`
with respect to the counting measure: the categorical law at the integrated probability vector. -/
theorem snd_compProd_categorical {𝒳 𝒞 : Type*} [MeasurableSpace 𝒳] [Countable 𝒞]
    [MeasurableSpace 𝒞] [MeasurableSingletonClass 𝒞] (F : Measure 𝒳) [IsProbabilityMeasure F]
    {π : 𝒳 → 𝒞 → ℝ} (hπ : ∀ c, Measurable fun x => π x c) (hπ0 : ∀ x c, 0 ≤ π x c)
    (κ : Kernel 𝒳 𝒞) [IsMarkovKernel κ]
    (hκ : ∀ᵐ x ∂F, κ x = Measure.count.withDensity fun c => ENNReal.ofReal (π x c)) :
    (F ⊗ₘ κ).snd = Measure.count.withDensity fun c => ENNReal.ofReal (∫ x, π x c ∂F) := by
  have hL : Measurable (Function.uncurry fun x c => ENNReal.ofReal (π x c)) :=
    measurable_from_prod_countable_left fun c => ENNReal.measurable_ofReal.comp (hπ c)
  rw [snd_compProd_eq_withDensity F Measure.count κ _ hL hκ]
  congr 1
  funext c
  refine (ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun x =>
    hπ0 x c)).symm
  refine Integrable.of_bound (hπ c).aestronglyMeasurable 1 (hκ.mono fun x hx => ?_)
  have h1 : κ x {c} ≤ 1 := prob_le_one
  rw [hx, withDensity_apply _ (measurableSet_singleton c), Measure.restrict_singleton,
    Measure.count_singleton, one_smul, lintegral_dirac, ENNReal.ofReal_le_one] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (hπ0 x c)]
  exact h1

end NetworkMetaRegression

end CausalInference
