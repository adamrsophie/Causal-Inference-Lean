/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapMeanLimit
public import CausalInference.Estimation.PosteriorLimitQuantile

/-!
# Convergence of bootstrap quantiles

The bootstrap law `Bootstrap.bootstrapLaw T O n ω` is a probability law on `ℝ` for every `n`,
including `n = 0`, so its quantile `Bootstrap.bootstrapQuantile T O n ω p` for `p ∈ (0, 1)` is a
genuine quantile: `q ≤ x ↔ p ≤ F*(x)`, with `F*` the bootstrap distribution function
(`Bootstrap.bootstrapQuantile_le_iff`).

If the bootstrap laws converge weakly to `L` in probability, with centering `θ̂_n` and rate `√n`
(the weak Bernstein and von Mises predicate), and the distribution function of `L` crosses the
level `p` strictly at `c`, then `√n (q*_n(p) - θ̂_n) → c` in probability. This is
`PosteriorLimit.IsBernsteinVonMisesWeak.tendstoInMeasure_quantile`; its proof works with the outer
measure and needs no measurability of the quantile in the data. For the bootstrap of the mean with
a finite positive variance `σ²` and `Φ(z) = p`, the limit is `σ z`, both in probability
(`Bootstrap.tendstoInMeasure_bootstrapQuantile_resampleMean`) and almost surely along the data
path (`Bootstrap.ae_tendsto_bootstrapQuantile_resampleMean`). The path form comes from the
deterministic statement `Bootstrap.tendsto_quantile_of_forall_integral`.

## References

* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 23.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

namespace Bootstrap

open PosteriorLimit BiasAnalysis.Distributions

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-- The bootstrap distribution function `F*_n(x) = P*(T_n ≤ x)` of a real statistic. -/
noncomputable def bootstrapCDF (T : (n : ℕ) → (Fin n → 𝒪) → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) (x : ℝ) : ℝ :=
  cdf (bootstrapLaw T O n ω) x

/-- The bootstrap quantile `q*_n(p)` of a real statistic: the quantile at level `p` of its
bootstrap law. -/
noncomputable def bootstrapQuantile (T : (n : ℕ) → (Fin n → 𝒪) → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) (p : ℝ) : ℝ :=
  quantile (bootstrapLaw T O n ω) p

/-- For a measurable statistic the bootstrap distribution function is the resampling probability
of `{T_n ≤ x}`. -/
theorem bootstrapCDF_eq (T : (n : ℕ) → (Fin n → 𝒪) → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (hT : Measurable (T n)) (ω : Ω) (x : ℝ) :
    bootstrapCDF T O n ω x = (resampleLaw O n ω).real {y | T n y ≤ x} := by
  rw [bootstrapCDF, cdf_eq_real, bootstrapLaw, map_measureReal_apply hT measurableSet_Iic]
  rfl

/-- **The Galois property of the bootstrap quantile.** For `p ∈ (0, 1)`,
`q*_n(p) ≤ x ↔ p ≤ F*_n(x)`. -/
theorem bootstrapQuantile_le_iff (T : (n : ℕ) → (Fin n → 𝒪) → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : ℝ) :
    bootstrapQuantile T O n ω p ≤ x ↔ p ≤ bootstrapCDF T O n ω x :=
  quantile_le_iff hp x

/-- The bootstrap distribution function at the bootstrap quantile is at least the level. -/
theorem le_bootstrapCDF_bootstrapQuantile (T : (n : ℕ) → (Fin n → 𝒪) → ℝ) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    p ≤ bootstrapCDF T O n ω (bootstrapQuantile T O n ω p) :=
  (bootstrapQuantile_le_iff T O n ω hp _).1 le_rfl

/-- Below the bootstrap quantile the bootstrap distribution function is below the level. -/
theorem bootstrapCDF_lt_of_lt_bootstrapQuantile (T : (n : ℕ) → (Fin n → 𝒪) → ℝ)
    (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) {x : ℝ}
    (hx : x < bootstrapQuantile T O n ω p) : bootstrapCDF T O n ω x < p :=
  lt_of_not_ge fun h ↦ (not_le.2 hx) ((bootstrapQuantile_le_iff T O n ω hp x).2 h)

/-! ### Deterministic quantile convergence -/

/-- **Quantile convergence under weak convergence.** Let `Q_n` be probability laws on `ℝ` and
`a_n` reals with `∫ φ(√n (x - a_n)) dQ_n(x) → ∫ φ dL` for every bounded continuous `φ`, and let
the distribution function of the probability law `L` cross the level `p` strictly at `c`. Then
`√n (q_n(p) - a_n) → c`. -/
theorem tendsto_quantile_of_forall_integral {Q : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (Q n)]
    {a : ℕ → ℝ} {L : Measure ℝ} [IsProbabilityMeasure L]
    (hQ : ∀ φ : ℝ → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n : ℕ ↦ ∫ x, φ (√(n : ℝ) * (x - a n)) ∂Q n) atTop (𝓝 (∫ x, φ x ∂L)))
    {p c : ℝ} (hlo : ∀ ε, 0 < ε → cdf L (c - ε) < p) (hhi : ∀ ε, 0 < ε → p < cdf L (c + ε)) :
    Tendsto (fun n : ℕ ↦ √(n : ℝ) * (quantile (Q n) p - a n)) atTop (𝓝 c) := by
  have hB : IsBernsteinVonMisesWeak (Measure.dirac ()) (fun n (_ : Unit) ↦ Q n)
      (fun n _ ↦ a n) L := by
    refine ⟨fun _ _ ↦ inferInstance, inferInstance, fun φ hφc hφb ↦ ?_⟩
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ ?_)
    simpa only [smul_eq_mul] using hQ φ hφc hφb
  have h := hB.tendstoInMeasure_quantile hlo hhi
  rw [tendstoInMeasure_iff_dist] at h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((h ε hε).eventually (gt_mem_nhds zero_lt_one))
  refine ⟨N, fun n hn ↦ lt_of_not_ge fun hle ↦ ?_⟩
  have h1 := hN n hn
  rw [Measure.dirac_apply_of_mem (show () ∈ {x : Unit | ε ≤ dist (√(n : ℝ) *
    (quantile (Q n) p - a n)) c} from hle)] at h1
  exact lt_irrefl _ h1

/-! ### The bootstrap of the mean -/

/-- **Bootstrap quantiles of the mean in probability.** For an i.i.d. sample, `f` measurable
with `E[f(O_0)²] < ∞` and positive variance `σ²`, and `Φ(z) = p` with `Φ` the standard normal
distribution function, `√n (q*_n(p) - X̄_n) → σ z` in probability, where `q*_n(p)` is the
bootstrap quantile of the resample mean. -/
theorem tendstoInMeasure_bootstrapQuantile_resampleMean {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) (hσ : 0 < Var[fun ω ↦ f (O 0 ω); P]) {p z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = p) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      √(n : ℝ) * (bootstrapQuantile (resampleMean f) O n ω p - sampleMean f O n ω)) atTop
      (fun _ ↦ √(Var[fun ω ↦ f (O 0 ω); P]) * z) := by
  obtain ⟨h1, h2⟩ := gaussianReal_cdf_strict_crossing hσ z
  rw [hz] at h1 h2
  exact (isBernsteinVonMisesWeak_resampleMean hO hf hf2).tendstoInMeasure_quantile h1 h2

/-- **Bootstrap quantiles of the mean along almost every path.** Under the hypotheses of
`Bootstrap.tendstoInMeasure_bootstrapQuantile_resampleMean`, for almost every data path
`√n (q*_n(p) - X̄_n) → σ z`. -/
theorem ae_tendsto_bootstrapQuantile_resampleMean {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) (hσ : 0 < Var[fun ω ↦ f (O 0 ω); P]) {p z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = p) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
      √(n : ℝ) * (bootstrapQuantile (resampleMean f) O n ω p - sampleMean f O n ω)) atTop
      (𝓝 (√(Var[fun ω ↦ f (O 0 ω); P]) * z)) := by
  obtain ⟨h1, h2⟩ := gaussianReal_cdf_strict_crossing hσ z
  rw [hz] at h1 h2
  filter_upwards [ae_tendstoInDistribution_resampleMean hO hf hf2] with ω hω
  refine tendsto_quantile_of_forall_integral (fun φ hφc hφb ↦ ?_) h1 h2
  obtain ⟨C, hC⟩ := hφb
  set b : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨φ, hφc⟩ (2 * C) fun x y ↦ by
    rw [Real.dist_eq]
    simp only [ContinuousMap.coe_mk]
    rw [abs_le]
    constructor <;> linarith [abs_le.1 (hC x), abs_le.1 (hC y)]
  have h3 := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hω.forall_aemeasurable aemeasurable_id).1 hω b
  simp only [b, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, id_eq] at h3
  refine h3.congr fun n ↦ ?_
  rw [bootstrapLaw, integral_map (measurable_resampleMean hf n).aemeasurable
    (f := fun x ↦ φ (√(n : ℝ) * (x - sampleMean f O n ω)))
    (hφc.comp (by fun_prop : Continuous fun x : ℝ ↦
      √(n : ℝ) * (x - sampleMean f O n ω))).aestronglyMeasurable]

end Bootstrap

end CausalInference
