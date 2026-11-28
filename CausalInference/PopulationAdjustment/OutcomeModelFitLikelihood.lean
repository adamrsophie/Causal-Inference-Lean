/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MaximumLikelihood
public import CausalInference.PointTreatment.Assumptions
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Maximum likelihood fit of a generalized linear outcome model

A generalized linear outcome model specifies the conditional law of the outcome `y` given the
regressors `c` (in a trial, the covariates and the arm) through a linear predictor `z(c) ⬝ ξ`:
`y | c` has density `dens(z(c) ⬝ ξ, ·)` with respect to a fixed measure `λ` on `ℝ`
(`GLMKernel`). With the regressor law `R` in the dominating measure, the model is an instance
of the library's `ParametricFamily` on `C × ℝ` (`glmFamily`): the dominating measure is
`R ⊗ λ` and the density of a record `(c, y)` is the conditional density `dens(z(c) ⬝ ξ, y)`, so
the likelihood of a sample is the conditional likelihood and does not involve `R`.

* **Identifiability** (`glmFamily_pointIdentified`): if the kernel identifies the predictor and
  no nonzero `v` has `z(c) ⬝ v = 0` for `R`-almost every `c`, the law of a record identifies `ξ`.
* **The regression is the model mean** (`condExp_eq_glmMean`): if the law of the records of a
  population is `P_{ξ₀}` and the outcome is integrable, then `E[Y | C] = mean(z(C) ⬝ ξ₀)` with
  `mean η = ∫ y dens(η, y) dλ(y)`; the regression assumption used by standardization is derived
  from the likelihood model, not assumed beside it.
* **The maximum likelihood fit** (`glmMLE`) is a function of the data: a maximizer of the
  likelihood over a compact set `K`, which exists for every sample when `K` is nonempty and the
  density is continuous in the predictor (`exists_isMaxOn_glmLikelihood`); `isMLE_glmMLE`
  verifies `ParametricFamily.IsMLE`.
* **Consistency** (`tendstoInMeasure_glmMLE`) by `tendstoInMeasure_of_isMLE`: for a positive
  density continuous in the predictor, with `|log dens(η, y)| ≤ a(y) + b |η|`, `a(Y)` and the
  design coordinates integrable, and the identifiability conditions.
* **The logistic model** (`logisticKernel`, `tendstoInMeasure_logisticMLE`): the Bernoulli
  outcome with success probability `σ(η)`; every regularity condition is proved, with
  `|log σ(η)| ≤ |η| + log 2` (`abs_log_sigmoid_le`), and its mean is `σ(η)`
  (`logisticKernel_mean`).

## Main definitions

* `GLMKernel`, `GLMKernel.mean`, `glmFamily`, `glmMLECoef`, `glmMLE`, `logisticKernel`.

## Main results

* `glmFamily_pointIdentified`, `condExp_eq_glmMean`, `isMLE_glmMLE`, `tendstoInMeasure_glmMLE`.
* `abs_log_sigmoid_le`, `logisticKernel_mean`, `tendstoInMeasure_logisticMLE`.

## References

* A. Wald (1949), *Note on the consistency of the maximum likelihood estimate*, Annals of
  Mathematical Statistics 20.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

/-! ### The conditional outcome kernel and the family of records -/

/-- A **conditional outcome kernel** of a generalized linear model: a probability density
`dens(η, ·)` with respect to a fixed s-finite measure `λ` on `ℝ`, for every value `η` of the
linear predictor, jointly measurable in `(η, y)`. -/
structure GLMKernel where
  /-- The dominating measure of the outcome. -/
  lam : Measure ℝ
  /-- The dominating measure is s-finite. -/
  sFinite_lam : SFinite lam
  /-- The density of the outcome at the predictor `η`. -/
  dens : ℝ → ℝ → ℝ
  /-- The density is jointly measurable. -/
  measurable_dens : Measurable fun q : ℝ × ℝ => dens q.1 q.2
  /-- The density is nonnegative. -/
  dens_nonneg : ∀ η y, 0 ≤ dens η y
  /-- The density is integrable. -/
  integrable_dens : ∀ η, Integrable (dens η) lam
  /-- The density integrates to one. -/
  integral_dens : ∀ η, ∫ y, dens η y ∂lam = 1

attribute [instance] GLMKernel.sFinite_lam

/-- The **mean of the outcome** at the predictor `η`: `∫ y dens(η, y) dλ(y)`. -/
noncomputable def GLMKernel.mean (G : GLMKernel) (η : ℝ) : ℝ := ∫ y, y * G.dens η y ∂G.lam

variable {C κ : Type*} [MeasurableSpace C] [Fintype κ]

omit [MeasurableSpace C] in
/-- The linear predictor is bounded by the norm of the coefficient times `∑ⱼ |zⱼ|`. -/
theorem abs_dotProduct_le_norm_mul (w ξ : κ → ℝ) : |w ⬝ᵥ ξ| ≤ ‖ξ‖ * ∑ j, |w j| := by
  rw [dotProduct, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm ξ j) (abs_nonneg _)

/-- The linear predictor of a measurable design is measurable. -/
theorem measurable_dotProduct_design {z : C → κ → ℝ} (hz : ∀ j, Measurable fun c => z c j)
    (ξ : κ → ℝ) : Measurable fun c => z c ⬝ᵥ ξ :=
  Finset.measurable_sum _ fun j _ => (hz j).mul_const _

/-- The **family of records** `(c, y)` of a generalized linear model with regressor law `R`
and design `z`: dominating measure `R ⊗ λ`, parameter set all of `ℝ^κ`, and density the
conditional density `dens(z(c) ⬝ ξ, y)`. -/
noncomputable def glmFamily (G : GLMKernel) (R : Measure C) [IsProbabilityMeasure R]
    (z : C → κ → ℝ) (hz : ∀ j, Measurable fun c => z c j) :
    ParametricFamily (κ → ℝ) (C × ℝ) where
  ν := R.prod G.lam
  Θ := Set.univ
  density ξ q := G.dens (z q.1 ⬝ᵥ ξ) q.2
  measurable_density ξ :=
    G.measurable_dens.comp (((measurable_dotProduct_design hz ξ).comp measurable_fst).prodMk
      measurable_snd)
  density_nonneg _ _ _ := G.dens_nonneg _ _
  integrable_density ξ _ := by
    have hm : Measurable fun q : C × ℝ => G.dens (z q.1 ⬝ᵥ ξ) q.2 :=
      G.measurable_dens.comp (((measurable_dotProduct_design hz ξ).comp measurable_fst).prodMk
        measurable_snd)
    refine (integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨ae_of_all _ fun c => G.integrable_dens (z c ⬝ᵥ ξ), (integrable_const (1 : ℝ)).congr ?_⟩
    refine ae_of_all _ fun c => ?_
    simp only [Real.norm_of_nonneg (G.dens_nonneg _ _), G.integral_dens]
  integral_density ξ _ := by
    have hm : Measurable fun q : C × ℝ => G.dens (z q.1 ⬝ᵥ ξ) q.2 :=
      G.measurable_dens.comp (((measurable_dotProduct_design hz ξ).comp measurable_fst).prodMk
        measurable_snd)
    have hi : Integrable (fun q : C × ℝ => G.dens (z q.1 ⬝ᵥ ξ) q.2) (R.prod G.lam) := by
      refine (integrable_prod_iff hm.aestronglyMeasurable).2
        ⟨ae_of_all _ fun c => G.integrable_dens (z c ⬝ᵥ ξ), (integrable_const (1 : ℝ)).congr ?_⟩
      refine ae_of_all _ fun c => ?_
      simp only [Real.norm_of_nonneg (G.dens_nonneg _ _), G.integral_dens]
    rw [integral_prod _ hi]
    simp [G.integral_dens]

variable {G : GLMKernel} {R : Measure C} [IsProbabilityMeasure R] {z : C → κ → ℝ}
  {hz : ∀ j, Measurable fun c => z c j}

/-- **Identifiability of a generalized linear model.** If the kernel identifies the predictor
(`dens(η, ·) = dens(η', ·)` `λ`-almost everywhere only for `η = η'`) and the design has full
rank under `R` (no nonzero `v` has `z(c) ⬝ v = 0` for `R`-almost every `c`), the law of a record
identifies the coefficient. -/
theorem glmFamily_pointIdentified
    (hG : ∀ η η', G.dens η =ᵐ[G.lam] G.dens η' → η = η')
    (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0) (K : Set (κ → ℝ)) :
    PointIdentified K (glmFamily G R z hz).law id := by
  intro ξ _ ξ' _ h
  have hd := (ParametricFamily.law_eq_law_iff (F := glmFamily G R z hz) (Set.mem_univ ξ)
    (Set.mem_univ ξ')).1 h
  have h2 := Measure.ae_ae_of_ae_prod (μ := R) (ν := G.lam)
    (p := fun q : C × ℝ => G.dens (z q.1 ⬝ᵥ ξ) q.2 = G.dens (z q.1 ⬝ᵥ ξ') q.2) hd
  have h3 : ∀ᵐ c ∂R, z c ⬝ᵥ (ξ - ξ') = 0 := by
    filter_upwards [h2] with c hc
    rw [dotProduct_sub, hG _ _ hc, sub_self]
  exact sub_eq_zero.1 (hfull _ h3)

/-! ### The regression of the outcome is the model mean -/

section Regression

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Cv : Ω → C} {Yo : Ω → ℝ}

/-- **The regression of a generalized linear model is its mean.** If the records `(C, Y)` of a
population have the law `P_{ξ₀}` of the family with regressor law `R = law(C)`, and the outcome
is integrable, then `E[Y | C] = mean(z(C) ⬝ ξ₀)` almost surely. -/
theorem condExp_eq_glmMean (hCv : Measurable Cv) (hYo : Measurable Yo) (hYi : Integrable Yo μ)
    (hR : μ.map Cv = R) {ξ₀ : κ → ℝ}
    (hmodel : μ.map (fun ω => (Cv ω, Yo ω)) = (glmFamily G R z hz).law ξ₀) :
    Measurable (fun c => G.mean (z c ⬝ᵥ ξ₀)) ∧
      μ[Yo | MeasurableSpace.comap Cv inferInstance] =ᵐ[μ] fun ω => G.mean (z (Cv ω) ⬝ᵥ ξ₀) := by
  set F := glmFamily G R z hz
  have hD : Measurable fun ω => (Cv ω, Yo ω) := hCv.prodMk hYo
  set k : C × ℝ → ℝ := fun q => q.2 * G.dens (z q.1 ⬝ᵥ ξ₀) q.2
  have hkm : Measurable k := measurable_snd.mul
    (G.measurable_dens.comp (((measurable_dotProduct_design hz ξ₀).comp measurable_fst).prodMk
      measurable_snd))
  have hsnd : Integrable (fun q : C × ℝ => q.2) (F.law ξ₀) := by
    rw [← hmodel, integrable_map_measure measurable_snd.aestronglyMeasurable hD.aemeasurable]
    exact hYi
  have hk : Integrable k (R.prod G.lam) := by
    have := (ParametricFamily.integrable_law_iff (F := F) (Set.mem_univ ξ₀)).1 hsnd
    exact this.congr (ae_of_all _ fun q => mul_comm _ _)
  have hmean_eq : ∀ c, G.mean (z c ⬝ᵥ ξ₀) = ∫ y, k (c, y) ∂G.lam := fun c => rfl
  have hmm : Measurable fun c => G.mean (z c ⬝ᵥ ξ₀) := by
    simp only [hmean_eq]
    exact (hkm.stronglyMeasurable.integral_prod_right' (ν := G.lam)).measurable
  have hmi : Integrable (fun c => G.mean (z c ⬝ᵥ ξ₀)) R := by
    simp only [hmean_eq]
    exact hk.integral_prod_left
  refine ⟨hmm, ?_⟩
  have hle := hCv.comap_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hYi (fun s _ _ => ?_) (fun s hs _ => ?_)
    ?_).symm
  · rw [← hR] at hmi
    exact ((integrable_map_measure hmm.aestronglyMeasurable hCv.aemeasurable).1 hmi).integrableOn
  · obtain ⟨B, hB, rfl⟩ := hs
    -- the left side
    rw [← setIntegral_map hB hmm.aestronglyMeasurable hCv.aemeasurable, hR]
    -- the right side
    have hBU : MeasurableSet (B ×ˢ (Set.univ : Set ℝ)) := hB.prod MeasurableSet.univ
    have hpre : Cv ⁻¹' B = (fun ω => (Cv ω, Yo ω)) ⁻¹' (B ×ˢ Set.univ) := by
      ext ω; simp
    rw [hpre, ← setIntegral_map (f := fun q : C × ℝ => q.2) hBU
      measurable_snd.aestronglyMeasurable hD.aemeasurable, hmodel,
      ← integral_indicator hBU, ParametricFamily.integral_law (Set.mem_univ ξ₀),
      ← integral_indicator hB]
    have hint : Integrable (fun q : C × ℝ => F.density ξ₀ q *
        (B ×ˢ (Set.univ : Set ℝ)).indicator (fun q => q.2) q) (R.prod G.lam) := by
      refine (hk.indicator hBU).congr (ae_of_all _ fun q => ?_)
      by_cases hq : q ∈ B ×ˢ (Set.univ : Set ℝ)
      · simp only [Set.indicator_of_mem hq, k]
        exact mul_comm _ _
      · simp [Set.indicator_of_notMem hq]
    change _ = ∫ q, F.density ξ₀ q * (B ×ˢ (Set.univ : Set ℝ)).indicator (fun q => q.2) q
      ∂(R.prod G.lam)
    rw [integral_prod _ hint]
    refine integral_congr_ae (ae_of_all _ fun c => ?_)
    by_cases hc : c ∈ B
    · simp only [Set.indicator_of_mem hc, hmean_eq]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [Set.indicator_of_mem (Set.mk_mem_prod hc (Set.mem_univ y)), k]
      exact mul_comm _ _
    · simp only [Set.indicator_of_notMem hc]
      symm
      refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
      simp [Set.indicator_of_notMem (fun h : (c, y) ∈ B ×ˢ Set.univ => hc h.1)]
  · exact ((hmm.comp (comap_measurable Cv)).stronglyMeasurable).aestronglyMeasurable

/-- **The observed regression of a trial under a generalized linear model.** If the records
`((X, A), Y)` of a trial have the law `P_{ξ₀}` of the family with regressor law
`R = law(X, A)` and the observed outcome is integrable, then `mean(z(x, a) ⬝ ξ₀)` is a version
of `E[Y | X, A]` (`PointTreatment.IsOutcomeRegression`). -/
theorem isOutcomeRegression_of_glm {𝒳 : Type*} [MeasurableSpace 𝒳] {z : 𝒳 × Bool → κ → ℝ}
    {hz : ∀ j, Measurable fun c => z c j} {R : Measure (𝒳 × Bool)} [IsProbabilityMeasure R]
    {X : Ω → 𝒳} {A : Ω → Bool} (hX : Measurable X) (hA : Measurable A) (hYo : Measurable Yo)
    (hYi : Integrable Yo μ) (hR : μ.map (fun ω => (X ω, A ω)) = R) {ξ₀ : κ → ℝ}
    (hmodel : μ.map (fun ω => ((X ω, A ω), Yo ω)) = (glmFamily G R z hz).law ξ₀) :
    PointTreatment.IsOutcomeRegression μ A X Yo fun a x => G.mean (z (x, a) ⬝ᵥ ξ₀) := by
  obtain ⟨hm, h⟩ := condExp_eq_glmMean (Cv := fun ω => (X ω, A ω)) (hX.prodMk hA) hYo hYi hR
    hmodel
  exact ⟨fun a => hm.comp (measurable_id.prodMk measurable_const), h⟩

end Regression

/-! ### The maximum likelihood fit -/

section Fit

/-- The **likelihood** `∏ᵢ dens(z(cᵢ) ⬝ ξ, yᵢ)` of a data vector of records. -/
noncomputable def glmLikelihood (dens : ℝ → ℝ → ℝ) (z : C → κ → ℝ) {n : ℕ}
    (x : Fin n → C × ℝ) (ξ : κ → ℝ) : ℝ :=
  ∏ i, dens (z (x i).1 ⬝ᵥ ξ) (x i).2

/-- The **maximum likelihood coefficient** of a data vector over the set `K`: a maximizer of
the likelihood over `K` when one exists (`exists_isMaxOn_glmLikelihood` gives one for every data
vector when `K` is compact and nonempty and the density is continuous in the predictor), and `0`
otherwise. -/
noncomputable def glmMLECoef (dens : ℝ → ℝ → ℝ) (z : C → κ → ℝ) (K : Set (κ → ℝ)) {n : ℕ}
    (x : Fin n → C × ℝ) : κ → ℝ :=
  open Classical in
  if h : ∃ ξ ∈ K, IsMaxOn (glmLikelihood dens z x) K ξ then h.choose else 0

/-- The **maximum likelihood fit** from the first `n` records of a sample. -/
noncomputable def glmMLE {Ω : Type*} (dens : ℝ → ℝ → ℝ) (z : C → κ → ℝ) (K : Set (κ → ℝ))
    (O : ℕ → Ω → C × ℝ) (n : ℕ) (ω : Ω) : κ → ℝ :=
  glmMLECoef dens z K (fun i : Fin n => O i ω)

omit [MeasurableSpace C] in
/-- **A maximizer of the likelihood exists** for every data vector, when `K` is compact and
nonempty and the density is continuous in the predictor. -/
theorem exists_isMaxOn_glmLikelihood {dens : ℝ → ℝ → ℝ} (hc : ∀ y, Continuous fun η => dens η y)
    (z : C → κ → ℝ) {K : Set (κ → ℝ)} (hK : IsCompact K) (hne : K.Nonempty) {n : ℕ}
    (x : Fin n → C × ℝ) : ∃ ξ ∈ K, IsMaxOn (glmLikelihood dens z x) K ξ :=
  hK.exists_isMaxOn hne (continuous_finsetProd _ fun _ _ =>
    (hc _).comp (continuous_const.dotProduct continuous_id)).continuousOn

/-- **The fit is a maximum likelihood estimator** of the family of records
(`ParametricFamily.IsMLE`), for any regressor law in the dominating measure. -/
theorem isMLE_glmMLE {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (hc : ∀ y, Continuous fun η => G.dens η y) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (O : ℕ → Ω → C × ℝ) :
    (glmFamily G R z hz).IsMLE μ K O (glmMLE G.dens z K O) := by
  intro n
  refine ae_of_all _ fun ω => ?_
  have h := exists_isMaxOn_glmLikelihood hc z hK hne (fun i : Fin n => O i ω)
  have hsel : glmMLE G.dens z K O n ω = h.choose := by
    simp [glmMLE, glmMLECoef, h]
  have hl : ∀ ξ, (glmFamily G R z hz).likelihood O n ω ξ =
      glmLikelihood G.dens z (fun i : Fin n => O i ω) ξ := fun ξ => by
    simp only [ParametricFamily.likelihood, glmLikelihood]
    exact Finset.prod_range fun i => G.dens (z (O i ω).1 ⬝ᵥ ξ) (O i ω).2
  rw [hsel]
  refine ⟨h.choose_spec.1, fun ξ hξ => ?_⟩
  rw [hl, hl]
  exact h.choose_spec.2 hξ

end Fit

/-! ### Consistency of the maximum likelihood fit -/

section Consistency

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω}
  {P : Measure Ξ} [IsProbabilityMeasure P] {Cv : Ω → C} {Yo : Ω → ℝ}

/-- **Consistency of the maximum likelihood fit of a generalized linear model.** Let the records
`(C, Y)` of a population have the law `P_{ξ₀}` of the family with regressor law `R = law(C)`,
with a kernel whose density is positive and continuous in the predictor and identifies it, a
design of full rank (`z(C) ⬝ v = 0` almost surely only for `v = 0`) with integrable coordinates,
and a log density bounded by `a(y) + b |η|` with `a(Y)` integrable. Then for an i.i.d. sample of
records with that law and a compact `K ∋ ξ₀`, the maximum likelihood fit over `K` converges in
probability to `ξ₀`. -/
theorem tendstoInMeasure_glmMLE (hCv : Measurable Cv) (hYo : Measurable Yo) (hR : μ.map Cv = R)
    {ξ₀ : κ → ℝ} (hmodel : μ.map (fun ω => (Cv ω, Yo ω)) = (glmFamily G R z hz).law ξ₀)
    (hGid : ∀ η η', G.dens η =ᵐ[G.lam] G.dens η' → η = η')
    (hfull : ∀ v : κ → ℝ, (∀ᵐ ω ∂μ, z (Cv ω) ⬝ᵥ v = 0) → v = 0)
    (hzi : ∀ j, Integrable (fun ω => z (Cv ω) j) μ)
    (hc : ∀ y, Continuous fun η => G.dens η y) (hpos : ∀ η y, 0 < G.dens η y) {a : ℝ → ℝ}
    (ha : Measurable a) (hai : Integrable (fun ω => a (Yo ω)) μ) {b : ℝ} (hb : 0 ≤ b)
    (hlog : ∀ η y, |Real.log (G.dens η y)| ≤ a y + b * |η|) {K : Set (κ → ℝ)}
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) {O : ℕ → Ξ → C × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (Cv ω, Yo ω)) :
    TendstoInMeasure P (glmMLE G.dens z K O) atTop (fun _ => ξ₀) := by
  set F := glmFamily G R z hz
  have hD : Measurable fun ω => (Cv ω, Yo ω) := hCv.prodMk hYo
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ξ₀ hξ₀)
  set H : C × ℝ → ℝ := fun q => a q.2 + b * (B * ∑ j, |z q.1 j|)
  have hHm : Measurable H :=
    (ha.comp measurable_snd).add (measurable_const.mul (measurable_const.mul
      (Finset.measurable_sum _ fun j _ =>
        continuous_abs.measurable.comp ((hz j).comp measurable_fst))))
  have hH : Integrable H (F.law ξ₀) := by
    rw [← hmodel, integrable_map_measure hHm.aestronglyMeasurable hD.aemeasurable]
    exact hai.add ((integrable_finsetSum _ fun j _ => (hzi j).abs).const_mul B |>.const_mul b)
  have hfullR : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0 := fun v hv => by
    refine hfull v ?_
    rw [← hR] at hv
    exact ae_of_ae_map hCv.aemeasurable hv
  refine ParametricFamily.tendstoInMeasure_of_isMLE hO (hlaw.trans hmodel) hK (Set.subset_univ _)
    hξ₀
    (glmFamily_pointIdentified hGid hfullR K)
    (ae_of_all _ fun q => ((hc q.2).comp (continuous_const.dotProduct continuous_id)).continuousOn)
    (ae_of_all _ fun q θ _ => hpos _ _) hH (ae_of_all _ fun q θ hθ => ?_)
    (isMLE_glmMLE hc hK ⟨ξ₀, hξ₀⟩ O)
  change |Real.log (G.dens (z q.1 ⬝ᵥ θ) q.2)| ≤ H q
  refine (hlog _ _).trans (add_le_add_right (mul_le_mul_of_nonneg_left ?_ hb) _)
  refine (abs_dotProduct_le_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (hB θ hθ) (Finset.sum_nonneg fun j _ => abs_nonneg _))

end Consistency

/-! ### The logistic model -/

section Logistic

/-- **The logarithm of the logistic function is bounded**: `|log σ(η)| ≤ |η| + log 2`. -/
theorem abs_log_sigmoid_le (η : ℝ) : |Real.log (Real.sigmoid η)| ≤ |η| + Real.log 2 := by
  have h1 : 1 ≤ 1 + Real.exp (-η) := by linarith [Real.exp_pos (-η)]
  have hpos : 0 < 1 + Real.exp (-η) := by linarith
  rw [Real.sigmoid_def, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg h1)]
  have h2 : 1 + Real.exp (-η) ≤ 2 * Real.exp |η| := by
    have h3 := Real.add_one_le_exp |η|
    have h4 := Real.exp_le_exp.2 (neg_le_abs η)
    have h5 : 0 ≤ |η| := abs_nonneg η
    linarith
  calc Real.log (1 + Real.exp (-η)) ≤ Real.log (2 * Real.exp |η|) := Real.log_le_log hpos h2
    _ = |η| + Real.log 2 := by
      rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]; ring

/-- The **logistic density**: success probability `σ(η)` at `y = 1` and `1 - σ(η)` elsewhere;
under the counting measure on `{0, 1}` it is the Bernoulli law with success probability
`σ(η)`. -/
noncomputable def logisticDens (η y : ℝ) : ℝ := if y = 1 then Real.sigmoid η else 1 - Real.sigmoid η

theorem logisticDens_pos (η y : ℝ) : 0 < logisticDens η y := by
  unfold logisticDens
  split_ifs
  · exact Real.sigmoid_pos η
  · linarith [Real.sigmoid_lt_one η]

theorem continuous_logisticDens (y : ℝ) : Continuous fun η => logisticDens η y := by
  unfold logisticDens
  split_ifs
  · exact continuous_sigmoid
  · exact continuous_const.sub continuous_sigmoid

theorem integral_logisticDens (η : ℝ) :
    ∫ y, logisticDens η y ∂(Measure.dirac 0 + Measure.dirac 1) = 1 := by
  rw [integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  simp [logisticDens]

/-- The **logistic kernel**: the outcome in `{0, 1}` with success probability `σ(η)`, as a
density with respect to `δ₀ + δ₁`. -/
noncomputable def logisticKernel : GLMKernel where
  lam := Measure.dirac 0 + Measure.dirac 1
  sFinite_lam := inferInstance
  dens := logisticDens
  measurable_dens := by
    unfold logisticDens
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      (continuous_sigmoid.measurable.comp measurable_fst)
      (measurable_const.sub (continuous_sigmoid.measurable.comp measurable_fst))
  dens_nonneg η y := (logisticDens_pos η y).le
  integrable_dens η := (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))
  integral_dens := integral_logisticDens

/-- **The mean of the logistic kernel is the logistic function**: `mean η = σ(η)`. -/
theorem logisticKernel_mean (η : ℝ) : logisticKernel.mean η = Real.sigmoid η := by
  simp only [GLMKernel.mean, logisticKernel]
  rw [integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
    integral_dirac, integral_dirac]
  simp [logisticDens]

/-- The logistic kernel identifies the predictor: the success probability `σ(η)` is the mass at
`1`, and `σ` is injective. -/
theorem logisticKernel_identifies (η η' : ℝ)
    (h : logisticKernel.dens η =ᵐ[logisticKernel.lam] logisticKernel.dens η') : η = η' := by
  have h1 : ∀ᵐ y ∂(Measure.dirac (1 : ℝ)), logisticDens η y = logisticDens η' y :=
    (ae_add_measure_iff.1 h).2
  rw [ae_dirac_eq, Filter.eventually_pure] at h1
  simpa [logisticDens] using h1

/-- The logistic log density is bounded by `log 2 + |η|`. -/
theorem abs_log_logisticDens_le (η y : ℝ) :
    |Real.log (logisticDens η y)| ≤ Real.log 2 + 1 * |η| := by
  unfold logisticDens
  split_ifs
  · linarith [abs_log_sigmoid_le η]
  · rw [← Real.sigmoid_neg]
    linarith [abs_log_sigmoid_le (-η), abs_neg η]

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω}
  {P : Measure Ξ} [IsProbabilityMeasure P] {Cv : Ω → C} {Yo : Ω → ℝ}

/-- **Consistency of the logistic maximum likelihood fit.** Let the records `(C, Y)` of a
population follow the logistic model, `law(C, Y) = P_{ξ₀}` for the logistic kernel with
regressor law `R = law(C)` (that is, `Y ∈ {0, 1}` with `P(Y = 1 | C) = σ(z(C) ⬝ ξ₀)`), with a
design of full rank and integrable coordinates. Then for an i.i.d. sample of records with that
law and a compact `K ∋ ξ₀`, the logistic maximum likelihood fit over `K` converges in
probability to `ξ₀`. Every regularity condition of `tendstoInMeasure_glmMLE` is proved. -/
theorem tendstoInMeasure_logisticMLE [IsProbabilityMeasure μ] (hCv : Measurable Cv)
    (hYo : Measurable Yo) (hR : μ.map Cv = R) {ξ₀ : κ → ℝ}
    (hmodel : μ.map (fun ω => (Cv ω, Yo ω)) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hfull : ∀ v : κ → ℝ, (∀ᵐ ω ∂μ, z (Cv ω) ⬝ᵥ v = 0) → v = 0)
    (hzi : ∀ j, Integrable (fun ω => z (Cv ω) j) μ) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hξ₀ : ξ₀ ∈ K) {O : ℕ → Ξ → C × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (Cv ω, Yo ω)) :
    TendstoInMeasure P (glmMLE logisticDens z K O) atTop (fun _ => ξ₀) :=
  tendstoInMeasure_glmMLE (G := logisticKernel) hCv hYo hR hmodel logisticKernel_identifies
    hfull hzi continuous_logisticDens logisticDens_pos measurable_const (integrable_const _)
    zero_le_one abs_log_logisticDens_le hK hξ₀ hO hlaw

end Logistic

end PopulationAdjustment

end CausalInference
