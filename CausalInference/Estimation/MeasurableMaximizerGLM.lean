/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MeasurableMaximizer
public import CausalInference.PopulationAdjustment.OutcomeModelFitLikelihood

/-!
# A measurable maximum likelihood fit of a generalized linear model

For a density `dens(η, y)` jointly measurable and continuous in the linear predictor `η`, a
measurable design `z` and a compact nonempty set `K` of coefficients, the likelihood
`∏ᵢ dens(z(cᵢ) ⬝ ξ, yᵢ)` of a data vector `x = ((cᵢ, yᵢ))_{i < n}` is measurable in `x` and
continuous in `ξ`, so a maximizer over `K` can be chosen measurably in the data
(`exists_measurable_isMaxOn_glmLikelihood`, from `exists_measurable_forall_isMaxOn`).

* `measurableGLMCoef dens z K n` is such a choice, a measurable function of the data vector
  (`measurable_measurableGLMCoef`) that maximizes the likelihood over `K` for every data vector
  (`measurableGLMCoef_mem_isMaxOn`).
* `measurableGLMFit dens z K O n ω` is the fit from the first `n` records of a sample `O`. It is
  almost everywhere measurable whenever the records are (`aemeasurable_measurableGLMFit`), and
  it maximizes the likelihood for every `ω` (`measurableGLMFit_mem_isMaxOn`), so it is a maximum
  likelihood estimator of the family of records (`isMLE_measurableGLMFit`).
* `measurableLogisticFit` is the logistic case.

The fit `glmMLE` of `OutcomeModelFitLikelihood` is also a maximizer for every data vector, but
it is chosen without regard to measurability; the fit of this file can replace it wherever a
measurable maximizer is needed.

## Main definitions

* `measurableGLMCoef`, `measurableGLMFit`, `measurableLogisticFit`.

## Main results

* `measurable_glmLikelihood`, `exists_measurable_isMaxOn_glmLikelihood`.
* `measurable_measurableGLMCoef`, `measurableGLMCoef_mem_isMaxOn`,
  `aemeasurable_measurableGLMFit`, `measurableGLMFit_mem_isMaxOn`, `isMLE_measurableGLMFit`.
* `aemeasurable_measurableLogisticFit`, `measurableLogisticFit_mem_isMaxOn`.

## References

* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalInference

namespace PopulationAdjustment

variable {C κ : Type*} [MeasurableSpace C] [Fintype κ]

/-- **The likelihood is measurable in the data** for a jointly measurable density and a
measurable design. -/
theorem measurable_glmLikelihood {dens : ℝ → ℝ → ℝ}
    (hdm : Measurable fun q : ℝ × ℝ ↦ dens q.1 q.2) {z : C → κ → ℝ}
    (hz : ∀ j, Measurable fun c ↦ z c j) (n : ℕ) (ξ : κ → ℝ) :
    Measurable fun x : Fin n → C × ℝ ↦ glmLikelihood dens z x ξ :=
  Finset.measurable_prod _ fun i _ ↦ hdm.comp
    ((((measurable_dotProduct_design hz ξ).comp measurable_fst).comp (measurable_pi_apply i)).prodMk
      (measurable_snd.comp (measurable_pi_apply i)))

/-- **A maximizer of the likelihood can be chosen measurably in the data**: for a jointly
measurable density continuous in the predictor, a measurable design and a compact nonempty `K`,
some measurable `g` of the data vector maximizes the likelihood over `K` at every data vector. -/
theorem exists_measurable_isMaxOn_glmLikelihood {dens : ℝ → ℝ → ℝ}
    (hdm : Measurable fun q : ℝ × ℝ ↦ dens q.1 q.2) (hc : ∀ y, Continuous fun η ↦ dens η y)
    {z : C → κ → ℝ} (hz : ∀ j, Measurable fun c ↦ z c j) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (n : ℕ) :
    ∃ g : (Fin n → C × ℝ) → κ → ℝ, Measurable g ∧
      ∀ x, g x ∈ K ∧ IsMaxOn (glmLikelihood dens z x) K (g x) :=
  exists_measurable_forall_isMaxOn (fun ξ _ ↦ measurable_glmLikelihood hdm hz n ξ) hK hne
    fun _ ↦ (continuous_finsetProd _ fun _ _ ↦
      (hc _).comp (continuous_const.dotProduct continuous_id)).continuousOn

/-- The **measurable maximum likelihood coefficient** over `K` of data vectors of length `n`: a
measurable function of the data vector maximizing the likelihood over `K` at every data vector
when one exists (`exists_measurable_isMaxOn_glmLikelihood` gives one for a jointly measurable
density continuous in the predictor, a measurable design and `K` compact and nonempty), and `0`
otherwise. -/
noncomputable def measurableGLMCoef (dens : ℝ → ℝ → ℝ) (z : C → κ → ℝ) (K : Set (κ → ℝ))
    (n : ℕ) : (Fin n → C × ℝ) → κ → ℝ :=
  open Classical in
  if h : ∃ g : (Fin n → C × ℝ) → κ → ℝ, Measurable g ∧
      ∀ x, g x ∈ K ∧ IsMaxOn (glmLikelihood dens z x) K (g x) then h.choose else fun _ ↦ 0

section Coef

variable {dens : ℝ → ℝ → ℝ} (hdm : Measurable fun q : ℝ × ℝ ↦ dens q.1 q.2)
  (hc : ∀ y, Continuous fun η ↦ dens η y) {z : C → κ → ℝ} (hz : ∀ j, Measurable fun c ↦ z c j)
  {K : Set (κ → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)

include hdm hc hz hK hne

lemma measurableGLMCoef_spec (n : ℕ) :
    Measurable (measurableGLMCoef dens z K n) ∧ ∀ x, measurableGLMCoef dens z K n x ∈ K ∧
      IsMaxOn (glmLikelihood dens z x) K (measurableGLMCoef dens z K n x) := by
  have h := exists_measurable_isMaxOn_glmLikelihood hdm hc hz hK hne n
  have e : measurableGLMCoef dens z K n = h.choose := by simp [measurableGLMCoef, h]
  rw [e]
  exact h.choose_spec

/-- **The measurable coefficient is measurable** in the data vector. -/
theorem measurable_measurableGLMCoef (n : ℕ) : Measurable (measurableGLMCoef dens z K n) :=
  (measurableGLMCoef_spec hdm hc hz hK hne n).1

/-- **The measurable coefficient maximizes the likelihood** over `K` at every data vector. -/
theorem measurableGLMCoef_mem_isMaxOn {n : ℕ} (x : Fin n → C × ℝ) :
    measurableGLMCoef dens z K n x ∈ K ∧
      IsMaxOn (glmLikelihood dens z x) K (measurableGLMCoef dens z K n x) :=
  (measurableGLMCoef_spec hdm hc hz hK hne n).2 x

end Coef

/-- The **measurable maximum likelihood fit** from the first `n` records of a sample. -/
noncomputable def measurableGLMFit {Ω : Type*} (dens : ℝ → ℝ → ℝ) (z : C → κ → ℝ)
    (K : Set (κ → ℝ)) (O : ℕ → Ω → C × ℝ) (n : ℕ) (ω : Ω) : κ → ℝ :=
  measurableGLMCoef dens z K n fun i : Fin n ↦ O i ω

section Fit

variable {Ω : Type*} [MeasurableSpace Ω] {dens : ℝ → ℝ → ℝ}
  (hdm : Measurable fun q : ℝ × ℝ ↦ dens q.1 q.2) (hc : ∀ y, Continuous fun η ↦ dens η y)
  {z : C → κ → ℝ} (hz : ∀ j, Measurable fun c ↦ z c j) {K : Set (κ → ℝ)} (hK : IsCompact K)
  (hne : K.Nonempty)

include hdm hc hz hK hne

/-- **The measurable fit is almost everywhere measurable** when the records are. -/
theorem aemeasurable_measurableGLMFit {P : Measure Ω} {O : ℕ → Ω → C × ℝ}
    (hO : ∀ i, AEMeasurable (O i) P) (n : ℕ) :
    AEMeasurable (measurableGLMFit dens z K O n) P :=
  (measurable_measurableGLMCoef hdm hc hz hK hne n).comp_aemeasurable
    (AEMeasurable.of_eval fun i ↦ hO i)

omit [MeasurableSpace Ω] in
/-- **The measurable fit maximizes the likelihood** of the first `n` records over `K`, at every
point of the sample space. -/
theorem measurableGLMFit_mem_isMaxOn (O : ℕ → Ω → C × ℝ) (n : ℕ) (ω : Ω) :
    measurableGLMFit dens z K O n ω ∈ K ∧
      IsMaxOn (glmLikelihood dens z fun i : Fin n ↦ O i ω) K (measurableGLMFit dens z K O n ω) :=
  measurableGLMCoef_mem_isMaxOn hdm hc hz hK hne _

end Fit

/-- **The measurable fit is a maximum likelihood estimator** of the family of records
(`ParametricFamily.IsMLE`), for any regressor law. -/
theorem isMLE_measurableGLMFit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : GLMKernel}
    {R : Measure C} [IsProbabilityMeasure R] {z : C → κ → ℝ} {hz : ∀ j, Measurable fun c ↦ z c j}
    (hc : ∀ y, Continuous fun η ↦ G.dens η y) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (O : ℕ → Ω → C × ℝ) :
    (glmFamily G R z hz).IsMLE μ K O (measurableGLMFit G.dens z K O) := by
  intro n
  refine ae_of_all _ fun ω ↦ ?_
  obtain ⟨hK', hmax⟩ := measurableGLMFit_mem_isMaxOn G.measurable_dens hc hz hK hne O n ω
  have hl : ∀ ξ, (glmFamily G R z hz).likelihood O n ω ξ =
      glmLikelihood G.dens z (fun i : Fin n ↦ O i ω) ξ := fun ξ ↦ by
    simp only [ParametricFamily.likelihood, glmLikelihood]
    exact Finset.prod_range fun i ↦ G.dens (z (O i ω).1 ⬝ᵥ ξ) (O i ω).2
  refine ⟨hK', fun ξ hξ ↦ ?_⟩
  rw [hl, hl]
  exact hmax hξ

/-! ### The logistic fit -/

/-- The **measurable logistic fit** over `K` from the first `n` records of a sample. -/
noncomputable abbrev measurableLogisticFit {Ω : Type*} (z : C → κ → ℝ) (K : Set (κ → ℝ))
    (O : ℕ → Ω → C × ℝ) : ℕ → Ω → κ → ℝ :=
  measurableGLMFit logisticDens z K O

variable {Ω : Type*} [MeasurableSpace Ω] {z : C → κ → ℝ} {K : Set (κ → ℝ)}

/-- **The measurable logistic fit is almost everywhere measurable** for a measurable design,
`K` compact and nonempty, and almost everywhere measurable records. -/
theorem aemeasurable_measurableLogisticFit (hz : ∀ j, Measurable fun c ↦ z c j)
    (hK : IsCompact K) (hne : K.Nonempty) {P : Measure Ω} {O : ℕ → Ω → C × ℝ}
    (hO : ∀ i, AEMeasurable (O i) P) (n : ℕ) :
    AEMeasurable (measurableLogisticFit z K O n) P :=
  aemeasurable_measurableGLMFit logisticKernel.measurable_dens continuous_logisticDens hz hK hne
    hO n

omit [MeasurableSpace Ω] in
/-- **The measurable logistic fit maximizes the likelihood** over `K` at every point of the
sample space, for a measurable design and `K` compact and nonempty. -/
theorem measurableLogisticFit_mem_isMaxOn (hz : ∀ j, Measurable fun c ↦ z c j)
    (hK : IsCompact K) (hne : K.Nonempty) (O : ℕ → Ω → C × ℝ) (n : ℕ) (ω : Ω) :
    measurableLogisticFit z K O n ω ∈ K ∧ IsMaxOn (glmLikelihood logisticDens z
      fun i : Fin n ↦ O i ω) K (measurableLogisticFit z K O n ω) :=
  measurableGLMFit_mem_isMaxOn logisticKernel.measurable_dens continuous_logisticDens hz hK hne
    O n ω

end PopulationAdjustment

end CausalInference
