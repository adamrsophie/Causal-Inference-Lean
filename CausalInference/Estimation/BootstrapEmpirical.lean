/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Estimator
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Resampling from the empirical law of a data path

The nonparametric bootstrap draws, given the data `O 0 ω, O 1 ω, …`, a resample of size `n` from
the empirical law `ℙ_n = n⁻¹ ∑_{k < n} δ_{O k ω}` of the first `n` observations
(`CausalInference.empiricalMeasure`). Here the resample is built from indices: `n` independent
indices, each uniform on `{0, …, n - 1}`, and the resampled observations `O (κ i) ω`.

## Main definitions

* `Bootstrap.indexLaw n`: the uniform law on `{0, …, n - 1} ⊂ ℕ`, a probability measure for
  `n ≠ 0`.
* `Bootstrap.resampleIndexLaw n`: the law of `n` independent uniform indices, on `Fin n → ℕ`; a
  probability measure for every `n` (for `n = 0` it is the point mass at the empty family).
* `Bootstrap.resampleLaw O n ω`: the law of the resample `(O (κ 0) ω, …, O (κ (n - 1)) ω)`.
* `Bootstrap.bootstrapLaw T O n ω`: the bootstrap law of a statistic `T n` of the resample, the
  conditional law of the statistic given the data.

## Main results

* `Bootstrap.map_indexLaw`: a uniform index picks an observation with the empirical law.
* `Bootstrap.resampleLaw_eq_pi`: the resample law is the `n` fold product of the empirical law, so
  the resampled observations are independent with the empirical law
  (`Bootstrap.iIndepFun_resampleLaw`, `Bootstrap.hasLaw_eval_resampleLaw`).
* `Bootstrap.integral_resampleLaw`: integrals against the resample law are integrals over the
  indices.
* `Bootstrap.memLp_two_empiricalMeasure`: every measurable function is square integrable for the
  empirical measure.
* `Bootstrap.aestronglyMeasurable_integral_resampleLaw`: for data that are almost everywhere
  measurable, `ω ↦ ∫ H(x_ω, ·) d(resample law)` is almost everywhere strongly measurable, where
  `x_ω` is the data prefix (`Bootstrap.dataPrefix`).

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal

namespace CausalInference

namespace Bootstrap

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-! ### The empirical law of a path prefix -/

/-- On any observation space, integrating a strongly measurable real function against the
empirical measure gives the sample mean (no measurable singletons are needed). -/
theorem integral_empiricalMeasure_of_stronglyMeasurable {f : 𝒪 → ℝ} (hf : StronglyMeasurable f)
    (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    ∫ x, f x ∂(empiricalMeasure O n ω) = sampleMean f O n ω := by
  rw [empiricalMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp [sampleMean, integral_dirac' _ _ hf]
  · intro i _
    exact integrable_dirac' hf (by simp)

/-- Every strongly measurable function into a normed group is integrable for the empirical
measure: a finite combination of Dirac masses. -/
theorem integrable_empiricalMeasure {E : Type*} [NormedAddCommGroup E] {f : 𝒪 → E}
    (hf : StronglyMeasurable f) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    Integrable f (empiricalMeasure O n ω) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empiricalMeasure]
  rw [empiricalMeasure]
  refine Integrable.smul_measure ?_ (by simpa using hn.ne')
  exact integrable_finsetSum_measure.2 fun i _ ↦ integrable_dirac' hf (by simp)

/-- Every strongly measurable function is square integrable for the empirical measure. -/
theorem memLp_two_empiricalMeasure {E : Type*} [NormedAddCommGroup E] {f : 𝒪 → E}
    (hf : StronglyMeasurable f) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    MemLp f 2 (empiricalMeasure O n ω) :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
    (integrable_empiricalMeasure (hf.norm.pow 2) O n ω)

/-! ### Uniform indices -/

/-- The uniform law `n⁻¹ ∑_{k < n} δ_k` on the indices `{0, …, n - 1}`. -/
noncomputable def indexLaw (n : ℕ) : Measure ℕ :=
  (n : ℝ≥0∞)⁻¹ • ∑ k ∈ range n, Measure.dirac k

/-- The uniform index law is a probability measure for `n ≠ 0`. -/
instance isProbabilityMeasure_indexLaw (n : ℕ) [NeZero n] : IsProbabilityMeasure (indexLaw n) :=
  by
  constructor
  simpa [indexLaw] using
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (NeZero.ne n)) (ENNReal.natCast_ne_top n)

/-- **A uniform index picks an observation with the empirical law**: the image of the uniform law
on `{0, …, n - 1}` under `k ↦ O k ω` is the empirical measure of the first `n` observations. -/
theorem map_indexLaw (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    (indexLaw n).map (fun k ↦ O k ω) = empiricalMeasure O n ω := by
  have hm : Measurable fun k : ℕ ↦ O k ω := measurable_from_nat
  ext A hA
  have hpt : ∀ k, ((fun k ↦ O k ω) ⁻¹' A).indicator (1 : ℕ → ℝ≥0∞) k =
      A.indicator 1 (O k ω) := fun k ↦ by
    by_cases h : O k ω ∈ A <;> simp [h]
  simp [indexLaw, empiricalMeasure, Measure.map_apply hm hA, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ (hm hA), hpt]

/-- The law of `n` independent indices, each uniform on `{0, …, n - 1}`. -/
noncomputable def resampleIndexLaw (n : ℕ) : Measure (Fin n → ℕ) :=
  Measure.pi fun _ : Fin n ↦ indexLaw n

/-- The law of the resampling indices is a probability measure for every `n`. For `n = 0` there is
nothing to draw and it is the point mass at the empty family. -/
instance isProbabilityMeasure_resampleIndexLaw (n : ℕ) :
    IsProbabilityMeasure (resampleIndexLaw n) := by
  have : ∀ _ : Fin n, IsProbabilityMeasure (indexLaw n) := fun i ↦ by
    have : NeZero n := ⟨by have := i.pos; omega⟩
    infer_instance
  unfold resampleIndexLaw
  infer_instance

/-! ### The resample -/

/-- The resample of size `n`: the observations `O (κ i) ω`, `i < n`, at the indices `κ`. -/
def resample (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) (κ : Fin n → ℕ) : Fin n → 𝒪 :=
  fun i ↦ O (κ i) ω

/-- The resample is a measurable function of the indices, which range over a countable set. -/
theorem measurable_resample (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    Measurable (resample O n ω) :=
  measurable_of_countable _

/-- The law of the resample of size `n` from the data at `ω`. -/
noncomputable def resampleLaw (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : Measure (Fin n → 𝒪) :=
  (resampleIndexLaw n).map (resample O n ω)

instance isProbabilityMeasure_resampleLaw (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (resampleLaw O n ω) := by
  unfold resampleLaw
  infer_instance

/-- **The resample law is the product of the empirical laws**: the `n` resampled observations
are independent, each with the empirical law of the first `n` observations. -/
theorem resampleLaw_eq_pi (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    resampleLaw O n ω = Measure.pi fun _ : Fin n ↦ empiricalMeasure O n ω := by
  have hm : Measurable fun k : ℕ ↦ O k ω := measurable_from_nat
  have : ∀ _ : Fin n, IsProbabilityMeasure (indexLaw n) := fun i ↦ by
    have : NeZero n := ⟨by have := i.pos; omega⟩
    infer_instance
  have : ∀ _ : Fin n, SigmaFinite ((indexLaw n).map fun k ↦ O k ω) := fun i ↦ by
    have : NeZero n := ⟨by have := i.pos; omega⟩
    infer_instance
  rw [resampleLaw, resampleIndexLaw]
  have h := Measure.pi_map_pi (μ := fun _ : Fin n ↦ indexLaw n)
    (f := fun _ (k : ℕ) ↦ O k ω) fun _ ↦ hm.aemeasurable
  simp only [map_indexLaw] at h
  exact h

/-- The resampled observations are independent under the resample law. -/
theorem iIndepFun_resampleLaw (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    iIndepFun (fun (i : Fin n) (y : Fin n → 𝒪) ↦ y i) (resampleLaw O n ω) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S _ _
    rw [Finset.eq_empty_of_isEmpty S]
    simp
  have : NeZero n := ⟨hn.ne'⟩
  rw [resampleLaw_eq_pi]
  exact iIndepFun_pi (μ := fun _ : Fin n ↦ empiricalMeasure O n ω) (X := fun _ (x : 𝒪) ↦ x)
    fun _ ↦ aemeasurable_id

/-- Each resampled observation has the empirical law of the first `n` observations. -/
theorem hasLaw_eval_resampleLaw (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) (i : Fin n) :
    HasLaw (fun y : Fin n → 𝒪 ↦ y i) (empiricalMeasure O n ω) (resampleLaw O n ω) := by
  have : NeZero n := ⟨by have := i.pos; omega⟩
  rw [resampleLaw_eq_pi]
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  exact (measurePreserving_eval (fun _ : Fin n ↦ empiricalMeasure O n ω) i).map_eq

/-- **The bootstrap law of a statistic**: the law of `T n` evaluated at the resample of size `n`
from the data at `ω`, that is, the conditional law of the bootstrap statistic given the data. -/
noncomputable def bootstrapLaw {E : Type*} [MeasurableSpace E] (T : (n : ℕ) → (Fin n → 𝒪) → E)
    (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : Measure E :=
  (resampleLaw O n ω).map (T n)

instance isProbabilityMeasure_bootstrapLaw {E : Type*} [MeasurableSpace E]
    (T : (n : ℕ) → (Fin n → 𝒪) → E) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (bootstrapLaw T O n ω) := by
  unfold bootstrapLaw
  infer_instance

/-! ### Integrals against the resample law -/

/-- Integrals against the resample law are integrals over the indices. -/
theorem integral_resampleLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : ℕ → Ω → 𝒪} {n : ℕ} {ω : Ω} {g : (Fin n → 𝒪) → E}
    (hg : AEStronglyMeasurable g (resampleLaw O n ω)) :
    ∫ y, g y ∂resampleLaw O n ω = ∫ κ, g (resample O n ω κ) ∂resampleIndexLaw n :=
  integral_map (measurable_resample O n ω).aemeasurable hg

/-- For measurable data, `(ω, κ) ↦ (O (κ i) ω)_i` is measurable on the product of the data space
and the index space, because the index space is countable. -/
theorem measurable_resample_uncurry {O : ℕ → Ω → 𝒪} (hO : ∀ k, Measurable (O k)) (n : ℕ) :
    Measurable fun p : Ω × (Fin n → ℕ) ↦ resample O n p.1 p.2 := by
  refine measurable_from_prod_countable_left fun κ ↦ ?_
  exact Measurable.of_eval fun i ↦ hO (κ i)

/-- The first `n` observations `(O 0 ω, …, O (n - 1) ω)` of the data path at `ω`. -/
def dataPrefix (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : Fin n → 𝒪 :=
  fun i ↦ O i ω

/-- **Measurability of resampling integrals in the data.** Let every observation be almost
everywhere measurable and let `H : (Fin n → 𝒪) → (Fin n → 𝒪) → E` be jointly strongly measurable.
Then `ω ↦ ∫ H(x_ω, y) d(resample law at ω)(y)`, with `x_ω` the first `n` observations, is almost
everywhere strongly measurable. Replace the observations by measurable versions; this changes the
integral only on a null set of data points. -/
theorem aestronglyMeasurable_integral_resampleLaw {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {P : Measure Ω} {O : ℕ → Ω → 𝒪} (hO : ∀ k, AEMeasurable (O k) P) (n : ℕ)
    {H : (Fin n → 𝒪) → (Fin n → 𝒪) → E} (hH : StronglyMeasurable (Function.uncurry H)) :
    AEStronglyMeasurable (fun ω ↦ ∫ y, H (dataPrefix O n ω) y ∂resampleLaw O n ω) P := by
  set O' : ℕ → Ω → 𝒪 := fun k ↦ (hO k).mk (O k) with hO'
  have hO'm : ∀ k, Measurable (O' k) := fun k ↦ (hO k).measurable_mk
  have hae : ∀ᵐ ω ∂P, ∀ k, O k ω = O' k ω := ae_all_iff.2 fun k ↦ (hO k).ae_eq_mk
  have hpre : Measurable fun p : Ω × (Fin n → ℕ) ↦ dataPrefix O' n p.1 :=
    Measurable.of_eval fun i ↦ (hO'm i).comp measurable_fst
  have hmeas : StronglyMeasurable fun ω ↦
      ∫ κ, H (dataPrefix O' n ω) (resample O' n ω κ) ∂resampleIndexLaw n :=
    (hH.comp_measurable (hpre.prodMk (measurable_resample_uncurry hO'm n))).integral_prod_right'
  refine hmeas.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with ω hω
  have h1 : resample O n ω = resample O' n ω := by
    funext κ i
    exact hω _
  have h2 : dataPrefix O n ω = dataPrefix O' n ω := by
    funext i
    exact hω _
  have hHm : AEStronglyMeasurable (H (dataPrefix O n ω)) (resampleLaw O n ω) :=
    (hH.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [integral_resampleLaw hHm, h1, h2]

end Bootstrap

end CausalInference
