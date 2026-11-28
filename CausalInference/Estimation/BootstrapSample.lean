/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapEmpirical
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The bootstrap on the product of the data space and the index space

At sample size `n` the data `ω ∈ Ω` (law `P`) and the resampling indices `κ ∈ Fin n → ℕ` (law
`Bootstrap.resampleIndexLaw n`) live on the product space with the product law
`P ⊗ resampleIndexLaw n`. Under it the indices are independent of the data and of each other, each
uniform on `{0, …, n - 1}`; the `i`-th resampled observation is `O (κ i) ω`.

The **conditional law of a bootstrap statistic given the data** is the bootstrap law
`Bootstrap.bootstrapLaw T O n ω`: for every bounded measurable `f`, the conditional expectation
(Mathlib's `condExp`) of `f (T n (resample))` given the data coordinate is
`ω ↦ ∫ f d(bootstrapLaw T O n ω)` (`Bootstrap.condExp_bootstrapLaw_ae_eq`); statistics that
also depend on the data, such as `√n (θ*_n - θ̂_n)`, are covered by
`Bootstrap.condExp_bootstrapStat_ae_eq`. The general step is
that on a product space the conditional expectation given the first coordinate integrates out the
second coordinate (`Bootstrap.condExp_comap_fst_ae_eq`).

## Main definitions

* `Bootstrap.resampleRow O n i`: the `i`-th resampled observation on the product space.

## Main results

* `Bootstrap.iIndepFun_resampleIndexLaw`, `Bootstrap.hasLaw_eval_resampleIndexLaw`: the indices
  are independent and uniform.
* `Bootstrap.indepFun_fst_snd_resample`: the indices are independent of the data.
* `Bootstrap.condExp_comap_fst_ae_eq`, `Bootstrap.condExp_bootstrapStat_ae_eq`,
  `Bootstrap.condExp_bootstrapLaw_ae_eq`.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal

namespace CausalInference

namespace Bootstrap

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-! ### The resampling indices -/

/-- The resampling indices are independent under their law. -/
theorem iIndepFun_resampleIndexLaw (n : ℕ) :
    iIndepFun (fun (i : Fin n) (κ : Fin n → ℕ) ↦ κ i) (resampleIndexLaw n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S _ _
    rw [Finset.eq_empty_of_isEmpty S]
    simp
  have : NeZero n := ⟨hn.ne'⟩
  exact iIndepFun_pi (μ := fun _ : Fin n ↦ indexLaw n) (X := fun _ (k : ℕ) ↦ k)
    fun _ ↦ aemeasurable_id

/-- Each resampling index is uniform on `{0, …, n - 1}`. -/
theorem hasLaw_eval_resampleIndexLaw (n : ℕ) (i : Fin n) :
    HasLaw (fun κ : Fin n → ℕ ↦ κ i) (indexLaw n) (resampleIndexLaw n) := by
  have : NeZero n := ⟨by have := i.pos; omega⟩
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  exact (measurePreserving_eval (fun _ : Fin n ↦ indexLaw n) i).map_eq

/-- On the product space the resampling indices are independent of the data. -/
theorem indepFun_fst_snd_resample (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) :
    IndepFun (fun p : Ω × (Fin n → ℕ) ↦ p.1) (fun p ↦ p.2) (P.prod (resampleIndexLaw n)) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- On the product space the data have law `P` and the indices have law `resampleIndexLaw n`. -/
theorem hasLaw_fst_snd_resample (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) :
    HasLaw (fun p : Ω × (Fin n → ℕ) ↦ p.1) P (P.prod (resampleIndexLaw n)) ∧
      HasLaw (fun p : Ω × (Fin n → ℕ) ↦ p.2) (resampleIndexLaw n) (P.prod (resampleIndexLaw n)) :=
  ⟨⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩,
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩⟩

/-- The `i`-th resampled observation `O (κ i) ω` on the product space. -/
def resampleRow (O : ℕ → Ω → 𝒪) (n : ℕ) (i : Fin n) (p : Ω × (Fin n → ℕ)) : 𝒪 :=
  O (p.2 i) p.1

/-- For measurable data the resampled observations are measurable on the product space. -/
theorem measurable_resampleRow {O : ℕ → Ω → 𝒪} (hO : ∀ k, Measurable (O k)) (n : ℕ)
    (i : Fin n) : Measurable (resampleRow O n i) :=
  (measurable_pi_apply i).comp (measurable_resample_uncurry hO n)

/-! ### Conditional expectation given the data -/

/-- **Conditioning on the first coordinate of a product integrates out the second.** For
probability measures `P`, `Q` and an integrable strongly measurable `F` on the product,
`E[F | first coordinate] = (ω, κ) ↦ ∫ F(ω, κ') dQ(κ')` almost everywhere. -/
theorem condExp_comap_fst_ae_eq {K : Type*} [MeasurableSpace K] (P : Measure Ω)
    [IsProbabilityMeasure P] (Q : Measure K) [IsProbabilityMeasure Q] {F : Ω × K → ℝ}
    (hF : StronglyMeasurable F) (hFi : Integrable F (P.prod Q)) :
    (P.prod Q)[F | MeasurableSpace.comap Prod.fst mΩ] =ᵐ[P.prod Q]
      fun p ↦ ∫ k, F (p.1, k) ∂Q := by
  have hG : StronglyMeasurable fun x ↦ ∫ k, F (x, k) ∂Q := hF.integral_prod_right'
  have hGi : Integrable (fun x ↦ ∫ k, F (x, k) ∂Q) P := hFi.integral_prod_left
  refine (ae_eq_condExp_of_forall_setIntegral_eq (measurable_fst.comap_le) hFi
    (fun s _ _ ↦ (hGi.comp_fst Q).integrableOn) ?_ ?_).symm
  · rintro s ⟨A, hA, rfl⟩ _
    have hs : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set K) := (Set.prod_univ).symm
    rw [hs, setIntegral_prod _ (hGi.comp_fst Q).integrableOn, setIntegral_prod _ hFi.integrableOn]
    simp
  · exact (hG.comp_measurable (comap_measurable Prod.fst)).aestronglyMeasurable

/-- **The conditional law of a bootstrap statistic given the data.** Let the data `O` be
measurable, let `T n x y` be a jointly measurable statistic of the data prefix `x` and the
resample `y`, and let `f` be bounded measurable. Under `P ⊗ resampleIndexLaw n`, the conditional
expectation of `f (T n (O 0 ω, …, O (n - 1) ω) (O (κ 0) ω, …, O (κ (n - 1)) ω))` given the data is
`ω ↦ ∫ f (T n (O 0 ω, …) y) d(resampleLaw O n ω)(y)` almost everywhere: the conditional law of the
statistic given the data is its law under resampling from the empirical law. -/
theorem condExp_bootstrapStat_ae_eq {E : Type*} [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} (hO : ∀ k, Measurable (O k)) (n : ℕ)
    {T : (Fin n → 𝒪) → (Fin n → 𝒪) → E} (hT : Measurable (Function.uncurry T)) {f : E → ℝ}
    (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    (P.prod (resampleIndexLaw n))[fun p ↦ f (T (dataPrefix O n p.1) (resample O n p.1 p.2)) |
      MeasurableSpace.comap Prod.fst mΩ] =ᵐ[P.prod (resampleIndexLaw n)]
      fun p ↦ ∫ y, f (T (dataPrefix O n p.1) y) ∂resampleLaw O n p.1 := by
  obtain ⟨C, hC⟩ := hb
  have hpre : Measurable fun p : Ω × (Fin n → ℕ) ↦ dataPrefix O n p.1 :=
    Measurable.of_eval fun i ↦ (hO i).comp measurable_fst
  have hFm : Measurable fun p : Ω × (Fin n → ℕ) ↦
      f (T (dataPrefix O n p.1) (resample O n p.1 p.2)) :=
    hf.comp (hT.comp (hpre.prodMk (measurable_resample_uncurry hO n)))
  have hFi : Integrable (fun p : Ω × (Fin n → ℕ) ↦
      f (T (dataPrefix O n p.1) (resample O n p.1 p.2))) (P.prod (resampleIndexLaw n)) :=
    Integrable.of_bound hFm.aestronglyMeasurable C (ae_of_all _ fun p ↦ by
      rw [Real.norm_eq_abs]; exact hC _)
  filter_upwards [condExp_comap_fst_ae_eq P (resampleIndexLaw n) hFm.stronglyMeasurable hFi]
    with p hp
  have hg : Measurable fun y ↦ f (T (dataPrefix O n p.1) y) :=
    hf.comp (hT.comp (measurable_const.prodMk measurable_id))
  rw [hp, integral_resampleLaw (g := fun y ↦ f (T (dataPrefix O n p.1) y))
    hg.aestronglyMeasurable]

/-- **The conditional law of a statistic of the resample given the data** is its bootstrap law:
for a measurable statistic `T n` of the resample and a bounded measurable `f`, the conditional
expectation of `f (T n (resample))` given the data is `ω ↦ ∫ f d(bootstrapLaw T O n ω)`. -/
theorem condExp_bootstrapLaw_ae_eq {E : Type*} [MeasurableSpace E] (P : Measure Ω)
    [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪} (hO : ∀ k, Measurable (O k))
    {T : (n : ℕ) → (Fin n → 𝒪) → E} (n : ℕ) (hT : Measurable (T n)) {f : E → ℝ}
    (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    (P.prod (resampleIndexLaw n))[fun p ↦ f (T n (resample O n p.1 p.2)) |
      MeasurableSpace.comap Prod.fst mΩ] =ᵐ[P.prod (resampleIndexLaw n)]
      fun p ↦ ∫ x, f x ∂bootstrapLaw T O n p.1 := by
  filter_upwards [condExp_bootstrapStat_ae_eq P hO n (T := fun _ y ↦ T n y)
    (hT.comp measurable_snd) hf hb] with p hp
  rw [hp, bootstrapLaw, integral_map hT.aemeasurable hf.aestronglyMeasurable]

end Bootstrap

end CausalInference
