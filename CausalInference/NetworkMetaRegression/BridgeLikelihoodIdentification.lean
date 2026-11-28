/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.IdentifiabilityNetwork
public import CausalInference.MetaAnalysis.HierarchicalPosterior
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Shared effect modifiers are identified from the likelihood

The likelihood of the multilevel model is built from two kinds of laws: the joint law of the
covariates and the outcome of a patient of an arm with individual data, `F ⊗ κ` with `κ(x)` the
outcome law at covariates `x`, and the law of the reported summary of an arm with aggregate data.
When the outcome law at `x` is `π(g⁻¹(η(x)))` for a family `π` of laws parameterized by their mean,
and the summary law of an arm is `Λ(θ)` for a family `Λ` parameterized by its mean and the
aggregate arm mean `θ`, equal likelihood laws give equal surfaces and equal arm means.

* **Identification from the likelihood laws** (`MultilevelModel.network_identifiable_of_laws`):
  in a connected network with a strictly increasing inverse link, two models anchored at `r` with
  shared effect modifiers among the non-reference treatments, whose individual data laws agree on
  one arm of `r` and on one arm of a non-reference treatment (both arms with covariate laws of full
  affine rank), and whose summary laws agree on every arm, are equal. So the whole model, and with
  it every conditional and marginal estimand in every target population, is a function of the
  likelihood laws. The two steps from laws to means are `ae_surface_eq_of_compProd_eq` and
  `armMean_eq_of_summaryLaw_eq`; the identification from means is
  `MultilevelModel.network_identifiable_of_shared`.
* **An instance** (`network_identifiable_of_laws_example`): one study with arms `false`, `true`,
  the reference `false`, a two point covariate law on `{0, 1}`, the identity link and point mass
  outcome and summary laws.
* **A bounded likelihood gives a proper posterior**
  (`isProbabilityMeasure_normalizedPosterior_of_le`): for a finite prior, a measurable
  likelihood bounded by a finite constant and positive on a set of positive prior mass has a
  normalizing constant in `(0, ∞)`, so the normalized posterior of
  `MetaAnalysis.normalizedPosterior` is a probability law. The instance
  (`isProbabilityMeasure_normalizedPosterior_sigmoid`) is the logistic likelihood `σ(ξ)` of one
  success under the standard normal prior.

## Main results

* `MultilevelModel.armMean_eq_of_summaryLaw_eq`, `MultilevelModel.network_identifiable_of_laws`,
  `network_identifiable_of_laws_example`, `isProbabilityMeasure_normalizedPosterior_of_le`,
  `isProbabilityMeasure_normalizedPosterior_sigmoid`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis
open scoped ENNReal

namespace MultilevelModel

variable {J K : Type*} {p : ℕ} {arms : J → Finset K} {base : J → K}
  {F : ArmIndex arms → Measure (Fin p → ℝ)} {ginv : ℝ → ℝ} {M M' : MultilevelModel J K p}

/-- **Equal summary laws give equal arm means**: for a family `Λ` of summary laws parameterized
by their mean, `Λ(θ) = Λ(θ')` gives `θ = θ'`. -/
theorem armMean_eq_of_summaryLaw_eq {Λ : ℝ → Measure ℝ} (hΛ : ∀ θ, ∫ y, y ∂Λ θ = θ)
    {θ θ' : ℝ} (h : Λ θ = Λ θ') : θ = θ' := by
  rw [← hΛ θ, h, hΛ]

/-- **The model is identified from its likelihood laws under shared effect modifiers.** Let the
network be finite with baseline arms `base j ∈ arms j` and a connected contrast graph, `g⁻¹` be
strictly increasing, every arm law `F x` be a probability law, and `M`, `M'` be anchored at `r`
with shared effect modifiers among the treatments `k ≠ r`. Let the outcome of a patient with
covariates `x` follow `π(g⁻¹(η(x)))` and the summary of an arm follow `Λ(θ)` at the arm mean `θ`,
for families `π`, `Λ` of laws parameterized by their mean. If

* the joint laws `F x ⊗ κ` of covariates and outcome agree for the two models on one arm `xr` of
  `r` and on one arm `xt` of a treatment `t ≠ r`, both arm laws of full affine rank, and
* the summary laws agree on every arm,

then `M = M'` (with `g⁻¹(s + xᵀ(β₁ + β₂,k))` integrable under every arm law for `M`). -/
theorem network_identifiable_of_laws [Finite J] [Finite K] {r : K}
    (hbase : ∀ j, base j ∈ arms j) (hcon : (armContrastGraph arms base).Connected)
    (hmono : StrictMono ginv) [∀ x, IsProbabilityMeasure (F x)] (hM : M.IsAnchoredAt r)
    (hM' : M'.IsAnchoredAt r) (hS : M.SharedEffectModifiers {k | k ≠ r})
    (hS' : M'.SharedEffectModifiers {k | k ≠ r}) {π Λ : ℝ → Measure ℝ}
    (hπ : ∀ θ, ∫ y, y ∂π θ = θ) (hΛ : ∀ θ, ∫ y, y ∂Λ θ = θ)
    (xr : ArmIndex arms) (hxr : xr.1.2 = r) (hrr : AffineRank (F xr))
    {κr κr' : Kernel (Fin p → ℝ) ℝ} [IsFiniteKernel κr] [IsFiniteKernel κr']
    (hκr : ∀ x, κr x = π (M.surface ginv (M.μ xr.1.1) xr.1.2 x))
    (hκr' : ∀ x, κr' x = π (M'.surface ginv (M'.μ xr.1.1) xr.1.2 x))
    (ipdr : F xr ⊗ₘ κr = F xr ⊗ₘ κr')
    (xt : ArmIndex arms) (hxt : xt.1.2 ≠ r) (hrt : AffineRank (F xt))
    {κt κt' : Kernel (Fin p → ℝ) ℝ} [IsFiniteKernel κt] [IsFiniteKernel κt']
    (hκt : ∀ x, κt x = π (M.surface ginv (M.μ xt.1.1) xt.1.2 x))
    (hκt' : ∀ x, κt' x = π (M'.surface ginv (M'.μ xt.1.1) xt.1.2 x))
    (ipdt : F xt ⊗ₘ κt = F xt ⊗ₘ κt')
    (hint : ∀ x : ArmIndex arms, ∀ s,
      Integrable (fun y => ginv (s + y ⬝ᵥ (M.β₁ + M.β₂ x.1.2))) (F x))
    (agd : ∀ x : ArmIndex arms, Λ (M.armMean ginv (M.μ x.1.1) (F x) x.1.2) =
      Λ (M'.armMean ginv (M'.μ x.1.1) (F x) x.1.2)) :
    M = M' :=
  network_identifiable_of_shared hbase hcon hmono hM hM' hS hS' xr hxr hrr
    (ae_surface_eq_of_compProd_eq hπ hκr hκr' ipdr) xt hxt hrt
    (ae_surface_eq_of_compProd_eq hπ hκt hκt' ipdt) hint
    fun x => armMean_eq_of_summaryLaw_eq hΛ (agd x)

end MultilevelModel

/-! ### An instance -/

section Example

/-- The arms of the one study network: both treatments `false` and `true`. -/
def exampleArms : Unit → Finset Bool := fun _ => Finset.univ

/-- The covariate law of the instance: equal masses at `0` and `1`. -/
noncomputable def twoPointLaw : Measure (Fin 1 → ℝ) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac fun _ => 1

instance : IsProbabilityMeasure twoPointLaw :=
  ⟨by simp only [twoPointLaw, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]; exact ENNReal.add_halves 1⟩

theorem affineRank_twoPointLaw : AffineRank twoPointLaw := by
  intro s b h
  have h' := ae_add_measure_iff.1 h
  have h0 := (Measure.ae_ennreal_smul_measure_iff (by norm_num)).1 h'.1
  have h1 := (Measure.ae_ennreal_smul_measure_iff (by norm_num)).1 h'.2
  rw [ae_dirac_eq, Filter.eventually_pure] at h0 h1
  simp only [zero_dotProduct, add_zero] at h0
  subst h0
  refine ⟨rfl, funext fun i => ?_⟩
  fin_cases i
  simpa [dotProduct] using h1

theorem integrable_twoPointLaw {f : (Fin 1 → ℝ) → ℝ} : Integrable f twoPointLaw :=
  ((integrable_dirac (by simp)).smul_measure (by norm_num)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))

theorem connected_exampleArms :
    (armContrastGraph exampleArms fun _ => false).Connected := by
  have hadj : (armContrastGraph exampleArms fun _ => false).Adj false true := by
    rw [armContrastGraph, comparisonGraph_adj]
    exact ⟨Bool.false_ne_true,
      Or.inl ⟨⟨⟨((), true), Finset.mem_univ _⟩, (by decide)⟩, rfl, rfl⟩⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨false, fun w => ?_⟩
  cases w
  · rfl
  · exact hadj.reachable

/-- The model of the instance: baseline `0`, `β₁ = 1`, `γ = (0, 1)` and no interactions,
anchored at `false`. -/
noncomputable def identificationExampleModel : MultilevelModel Unit Bool 1 :=
  ⟨fun _ => 0, fun _ => 1, fun k => if k then 1 else 0, fun _ _ => 0⟩

/-- **The hypotheses of the identification from the likelihood laws hold in the instance**: the
one study network with arms `false`, `true`, the two point covariate law, the identity link, point
mass outcome laws (kernels `x ↦ δ_{η(x)}`) and point mass summary laws. Every hypothesis of
`MultilevelModel.network_identifiable_of_laws` is proved, for the model `identificationExampleModel`
and any model `M'` with the same laws. -/
theorem network_identifiable_of_laws_example {M' : MultilevelModel Unit Bool 1}
    (hM' : M'.IsAnchoredAt false) (hS' : M'.SharedEffectModifiers {k | k ≠ false})
    (xr xt : ArmIndex exampleArms) (hxr : xr.1.2 = false) (hxt : xt.1.2 ≠ false)
    (ipdr : twoPointLaw ⊗ₘ ProbabilityTheory.Kernel.deterministic
        (identificationExampleModel.surface id (identificationExampleModel.μ ()) xr.1.2)
          (MultilevelModel.measurable_surface measurable_id _ _ _) =
      twoPointLaw ⊗ₘ ProbabilityTheory.Kernel.deterministic (M'.surface id (M'.μ ()) xr.1.2)
          (MultilevelModel.measurable_surface measurable_id _ _ _))
    (ipdt : twoPointLaw ⊗ₘ ProbabilityTheory.Kernel.deterministic
        (identificationExampleModel.surface id (identificationExampleModel.μ ()) xt.1.2)
          (MultilevelModel.measurable_surface measurable_id _ _ _) =
      twoPointLaw ⊗ₘ ProbabilityTheory.Kernel.deterministic (M'.surface id (M'.μ ()) xt.1.2)
          (MultilevelModel.measurable_surface measurable_id _ _ _))
    (agd : ∀ x : ArmIndex exampleArms,
      identificationExampleModel.armMean id (identificationExampleModel.μ x.1.1) twoPointLaw
        x.1.2 = M'.armMean id (M'.μ x.1.1) twoPointLaw x.1.2) :
    identificationExampleModel = M' := by
  have hπ : ∀ θ : ℝ, ∫ y, y ∂(Measure.dirac θ) = θ := fun θ => by rw [integral_dirac]
  exact MultilevelModel.network_identifiable_of_laws (F := fun _ => twoPointLaw)
    (base := fun _ => false) (fun _ => Finset.mem_univ _) connected_exampleArms strictMono_id
    ⟨rfl, rfl⟩ hM' (fun _ _ _ _ => rfl) hS' hπ hπ xr hxr affineRank_twoPointLaw
    (fun _ => rfl) (fun _ => rfl) ipdr xt hxt affineRank_twoPointLaw (fun _ => rfl)
    (fun _ => rfl) ipdt (fun _ _ => integrable_twoPointLaw) fun x => by rw [agd x]

/- The hypotheses on `M'` are satisfiable: `identificationExampleModel` itself satisfies them. -/
example : identificationExampleModel = identificationExampleModel :=
  network_identifiable_of_laws_example ⟨rfl, rfl⟩ (fun _ _ _ _ => rfl)
    ⟨((), false), Finset.mem_univ _⟩ ⟨((), true), Finset.mem_univ _⟩ rfl (by decide)
    rfl rfl fun _ => rfl

end Example

/-! ### A proper posterior -/

section Posterior

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- **A bounded likelihood that is positive on a set of positive prior mass gives a proper
posterior.** For a finite prior `μ` and a measurable likelihood `L ≤ C < ∞` with
`μ {ξ | 0 < L ξ} > 0`, the normalizing constant `∫⁻ L dμ` lies in `(0, ∞)`, and the normalized
posterior `MetaAnalysis.normalizedPosterior μ L` is a probability law. -/
theorem isProbabilityMeasure_normalizedPosterior_of_le {μ : Measure Ξ} [IsFiniteMeasure μ]
    {L : Ξ → ℝ≥0∞} (hL : Measurable L) {C : ℝ≥0∞} (hC : C ≠ ∞) (hle : ∀ ξ, L ξ ≤ C)
    (hpos : 0 < μ {ξ | 0 < L ξ}) :
    0 < ∫⁻ ξ, L ξ ∂μ ∧ ∫⁻ ξ, L ξ ∂μ < ∞ ∧
      IsProbabilityMeasure (MetaAnalysis.normalizedPosterior μ L) := by
  have h0 : ∫⁻ ξ, L ξ ∂μ ≠ 0 := by
    rw [Ne, lintegral_eq_zero_iff hL]
    intro h
    refine hpos.ne' (measure_eq_zero_iff_ae_notMem.2 ?_)
    filter_upwards [h] with ξ hξ
    simp [hξ]
  have htop : ∫⁻ ξ, L ξ ∂μ < ∞ :=
    (lintegral_mono hle).trans_lt (by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ _))
  exact ⟨pos_iff_ne_zero.2 h0, htop,
    MetaAnalysis.isProbabilityMeasure_normalizedPosterior h0 htop.ne⟩

/-- **Instance**: the logistic likelihood `σ(ξ)` of one success under the standard normal prior
has a normalizing constant in `(0, ∞)` and a proper posterior. -/
theorem isProbabilityMeasure_normalizedPosterior_sigmoid :
    0 < ∫⁻ ξ, ENNReal.ofReal (Real.sigmoid ξ) ∂gaussianReal 0 1 ∧
      ∫⁻ ξ, ENNReal.ofReal (Real.sigmoid ξ) ∂gaussianReal 0 1 < ∞ ∧
      IsProbabilityMeasure (MetaAnalysis.normalizedPosterior (gaussianReal 0 1)
        fun ξ => ENNReal.ofReal (Real.sigmoid ξ)) := by
  refine isProbabilityMeasure_normalizedPosterior_of_le
    (ENNReal.measurable_ofReal.comp continuous_sigmoid.measurable) ENNReal.one_ne_top
    (fun ξ => ENNReal.ofReal_le_one.2 (Real.sigmoid_lt_one ξ).le) ?_
  have hset : {ξ : ℝ | 0 < ENNReal.ofReal (Real.sigmoid ξ)} = Set.univ :=
    Set.eq_univ_of_forall fun ξ => ENNReal.ofReal_pos.2 (Real.sigmoid_pos ξ)
  rw [hset, measure_univ]
  exact one_pos

end Posterior

end NetworkMetaRegression

end CausalInference
