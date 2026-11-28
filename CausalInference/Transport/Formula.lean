/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Basic
public import CausalInference.PointTreatment.Identification

/-!
# Transport: the transport formula

A study of a point treatment is run in the source population `(Ω₁, μ₁)`, with covariates `X₁`,
treatment `A`, potential outcomes `Y₁` and observed outcome `obsOutcome A Y₁`. The target
population `(Ω₂, μ₂)` has covariates `X₂` and potential outcome `Y₂` of the arm `a`.
**Conditional transportability** of the mean of arm `a` consists of

* exchangeability in the source, `A ⫫ Y(a) | X` (here the indicator form
  `MARMean μ₁ X₁ (Y₁ a) (arm A a)`, or `IndicatorIgnorable` for the g-formula), with positivity
  `π_a(X₁) > 0`;
* structural invariance: one `g` is a version of `E[Y(a) | X]` in both populations;
* overlap of the populations: `P*_X ≪ P_X`;
* integrability of the target potential outcome and of `w(X₁) Y₁(a)` in the source, with `w` the
  density ratio (equivalently, of `E₁[|Y₁(a)| | X₁ = x]` under `P*_X`,
  `integrable_densityRatio_mul_iff_condExp_abs`).

Then the target mean is given by the transport formula (Westreich and coauthors 2017; Dahabreh
and coauthors 2019) in four equivalent forms:

`E₂[Y₂(a)] = ∫ g dP*_X = E₁[w(X₁) g(X₁)] = E₁[w(X₁) Y₁(a)] = E₁[w(X₁) 1{A = a} Y / π_a(X₁)]`,

and, in g-formula form, `E₂[Y₂(a)] = ∫ m(a, x) dP*_X(x)` for any version `m(A, X₁)` of the
observed source regression `E₁[Y | X₁, A]`.

## Main results

* `marMean_of_comap_le`: the indicator form of exchangeability passes to functions of the
  covariates and the outcome.
* `integral_respInd_mul_of_marMean`: the weighting lemma for a function of `(X, Y)`.
* `integral_target_eq_transport`: the four forms of the transport formula.
* `integral_target_eq_integral_regression`: the transport g-formula.

## References

* D. Westreich, J. K. Edwards, C. R. Lesko, E. Stuart and S. R. Cole, *Transportability of
  trial results using inverse odds of sampling weights*, American Journal of Epidemiology 186
  (2017).
* I. J. Dahabreh, S. E. Robertson, E. J. Tchetgen Tchetgen, E. A. Stuart and M. A. Hernán,
  *Generalizing causal inferences from individuals in randomized trials to all trial-eligible
  individuals*, Biometrics 75 (2019).
-/

@[expose] public section

namespace CausalInference

namespace Transport

open MeasureTheory ProbabilityTheory MissingData PointTreatment

/-! ### Exchangeability for functions of the covariates and the outcome -/

section Weighting

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒳] {μ : Measure Ω}
  [IsFiniteMeasure μ] {X : Ω → 𝒳} {Y : Ω → ℝ} {R : Ω → Bool}

/-- **Exchangeability passes to coarser outcomes.** If `E[1{R} | X, Y] = E[1{R} | X]` and `Z` is
such that `σ(X, Z) ⊆ σ(X, Y)`, then `E[1{R} | X, Z] = E[1{R} | X]`. -/
theorem marMean_of_comap_le (h : MARMean μ X Y R) (hX : Measurable X) (hY : Measurable Y)
    {Z : Ω → ℝ} (hle : MeasurableSpace.comap (fun ω => (X ω, Z ω)) inferInstance ≤
      MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance) : MARMean μ X Z R := by
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hXZ : MeasurableSpace.comap X inferInstance ≤
      MeasurableSpace.comap (fun ω => (X ω, Z ω)) inferInstance :=
    (measurable_fst.comp (comap_measurable (fun ω => (X ω, Z ω)))).comap_le
  unfold MARMean at h ⊢
  refine (condExp_condExp_of_le hle hXY.comap_le).symm.trans ?_
  refine (condExp_congr_ae h).trans ?_
  rw [condExp_of_stronglyMeasurable (hle.trans hXY.comap_le)
    (stronglyMeasurable_condExp.mono hXZ) integrable_condExp]

/-- **The weighting lemma for a function of the covariates and the outcome.** Under the
indicator form of exchangeability `MARMean μ X Y R` and a version `p(X)` of `E[1{R} | X]`, for a
measurable `g`, `1{R} g(X, Y)` is integrable exactly when `p(X) g(X, Y)` is, and then the two
have the same mean. -/
theorem integral_respInd_mul_of_marMean (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) (h : MARMean μ X Y R) {p : 𝒳 → ℝ}
    (hp : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => p (X ω))
    {g : 𝒳 × ℝ → ℝ} (hg : Measurable g) :
    (Integrable (fun ω => respInd R ω * g (X ω, Y ω)) μ ↔
      Integrable (fun ω => p (X ω) * g (X ω, Y ω)) μ) ∧
    ∫ ω, respInd R ω * g (X ω, Y ω) ∂μ = ∫ ω, p (X ω) * g (X ω, Y ω) ∂μ := by
  have hgm := (measurable_comap_prod (X := X) (Y := Y) hg).stronglyMeasurable
  have hr := integrable_respInd (μ := μ) hR
  have hp' := h.trans hp
  have hle := (hX.prodMk hY).comap_le
  have hiff : Integrable (fun ω => respInd R ω * g (X ω, Y ω)) μ ↔
      Integrable (fun ω => p (X ω) * g (X ω, Y ω)) μ :=
    ⟨fun h => (integral_mul_eq_of_condExp_eq hle hr hgm h hp').1,
      integrable_mul_of_condExp_eq hle hr
        (Filter.Eventually.of_forall fun ω => respInd_nonneg _ ω) hgm hp'⟩
  refine ⟨hiff, ?_⟩
  by_cases hi : Integrable (fun ω => respInd R ω * g (X ω, Y ω)) μ
  · exact (integral_mul_eq_of_condExp_eq hle hr hgm hi hp').2
  · rw [integral_undef hi, integral_undef (mt hiff.2 hi)]

end Weighting

/-! ### The transport formula -/

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsFiniteMeasure μ₁]
  [IsFiniteMeasure μ₂] {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳} {A : Ω₁ → Bool} {Y₁ : Bool → Ω₁ → ℝ}
  {Y₂ : Ω₂ → ℝ} {e : 𝒳 → ℝ} {g : 𝒳 → ℝ}

/-- The target mean is the mean of the common regression under the target covariate law, and
the common regression is integrable under that law. -/
theorem integral_target_eq_integral_common (hX₂ : Measurable X₂) (hY₂ : Integrable Y₂ μ₂)
    (hg : Measurable g)
    (Htgt : (fun ω => g (X₂ ω)) =ᵐ[μ₂] μ₂[Y₂ | MeasurableSpace.comap X₂ inferInstance]) :
    Integrable g (μ₂.map X₂) ∧ ∫ ω, Y₂ ω ∂μ₂ = ∫ x, g x ∂(μ₂.map X₂) := by
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable hX₂.aemeasurable).2
    ((integrable_condExp (μ := μ₂) (f := Y₂)).congr Htgt.symm), ?_⟩
  have h := setIntegral_condExp hX₂.comap_le hY₂ MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [integral_map hX₂.aemeasurable hg.aestronglyMeasurable, integral_congr_ae Htgt, h]

omit [IsFiniteMeasure μ₂] in
/-- In the source, `E₁[w(X₁) g(X₁)] = E₁[w(X₁) Y]` when `g(X₁)` is a version of `E₁[Y | X₁]`
and `w(X₁) Y` is integrable: condition the second on `X₁`. -/
theorem integral_densityRatio_mul_common (hX₁ : Measurable X₁) {Y : Ω₁ → ℝ}
    (hY : Integrable Y μ₁)
    (Hsrc : (fun ω => g (X₁ ω)) =ᵐ[μ₁] μ₁[Y | MeasurableSpace.comap X₁ inferInstance])
    (hwY : Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * Y ω) μ₁) :
    ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * g (X₁ ω) ∂μ₁ =
      ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * Y ω ∂μ₁ := by
  have hwm : StronglyMeasurable[MeasurableSpace.comap X₁ inferInstance]
      (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω)) :=
    ((measurable_densityRatio μ₁ X₁ μ₂ X₂).comp (comap_measurable X₁)).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left hwm hwY hY
  rw [← integral_condExp hX₁.comap_le (f := fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * Y ω)]
  refine integral_congr_ae ?_
  filter_upwards [hpull, Hsrc] with ω h1 h2
  exact (congrArg _ h2).trans h1.symm |>.trans rfl

/-- **The transport formula.** Under conditional transportability of the mean of arm `a`
(source exchangeability in indicator form, positivity, structural invariance through `g`,
overlap, and integrability of `Y₂`, `Y₁(a)` and `w(X₁) Y₁(a)`), the target mean is

`E₂[Y₂] = ∫ g dP*_X = E₁[w(X₁) g(X₁)] = E₁[w(X₁) Y₁(a)] = E₁[w(X₁) 1{A = a} Y / π_a(X₁)]`,

and the weighted observed outcome `w(X₁) 1{A = a} Y / π_a(X₁)` is integrable in the source. -/
theorem integral_target_eq_transport (a : Bool) (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hA : Measurable A) (hYa : Measurable (Y₁ a)) (hY₁ : Integrable (Y₁ a) μ₁)
    (hY₂ : Integrable Y₂ μ₂) (hmar : MARMean μ₁ X₁ (Y₁ a) (arm A a))
    (hps : IsPropensityScore μ₁ A X₁ e) (hpos : ∀ᵐ ω ∂μ₁, 0 < armProb e a (X₁ ω))
    (hcom : IsCommonRegression μ₁ X₁ (Y₁ a) μ₂ X₂ Y₂ g) (hov : μ₂.map X₂ ≪ μ₁.map X₁)
    (hwY : Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * Y₁ a ω) μ₁) :
    ∫ ω, Y₂ ω ∂μ₂ = ∫ x, g x ∂(μ₂.map X₂) ∧
    ∫ ω, Y₂ ω ∂μ₂ = ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * g (X₁ ω) ∂μ₁ ∧
    ∫ ω, Y₂ ω ∂μ₂ = ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * Y₁ a ω ∂μ₁ ∧
    Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * respInd (arm A a) ω *
      obsOutcome A Y₁ ω / armProb e a (X₁ ω)) μ₁ ∧
    ∫ ω, Y₂ ω ∂μ₂ = ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * respInd (arm A a) ω *
      obsOutcome A Y₁ ω / armProb e a (X₁ ω) ∂μ₁ := by
  obtain ⟨hg, Hsrc, Htgt⟩ := hcom
  set w := densityRatio μ₁ X₁ μ₂ X₂
  have hw := measurable_densityRatio μ₁ X₁ μ₂ X₂
  have e1 := (integral_target_eq_integral_common hX₂ hY₂ hg Htgt).2
  have e2 := integral_densityRatio_mul hX₁ hov hg
  have e3 := integral_densityRatio_mul_common hX₁ hY₁ Hsrc hwY
  -- the weighting lemma with `G(x, y) = w(x) y / π_a(x)`
  have hG : Measurable fun q : 𝒳 × ℝ => w q.1 * q.2 / armProb e a q.1 :=
    ((hw.comp measurable_fst).mul measurable_snd).div
      ((measurable_armProb hps.1 a).comp measurable_fst)
  obtain ⟨hiff, hint⟩ := integral_respInd_mul_of_marMean hX₁ hYa (measurable_arm hA a) hmar
    (hps.condExp_arm hX₁ hA a) hG
  have hπ : (fun ω => armProb e a (X₁ ω) * (w (X₁ ω) * Y₁ a ω / armProb e a (X₁ ω))) =ᵐ[μ₁]
      fun ω => w (X₁ ω) * Y₁ a ω := by
    filter_upwards [hpos] with ω h
    field_simp
  have hobs : (fun ω => w (X₁ ω) * respInd (arm A a) ω * obsOutcome A Y₁ ω /
      armProb e a (X₁ ω)) = fun ω => respInd (arm A a) ω *
        (w (X₁ ω) * Y₁ a ω / armProb e a (X₁ ω)) := by
    funext ω
    have := respInd_arm_mul_obsOutcome A Y₁ a ω
    calc w (X₁ ω) * respInd (arm A a) ω * obsOutcome A Y₁ ω / armProb e a (X₁ ω)
        = w (X₁ ω) * (respInd (arm A a) ω * obsOutcome A Y₁ ω) / armProb e a (X₁ ω) := by ring
      _ = _ := by rw [this]; ring
  refine ⟨e1, e1.trans e2, (e1.trans e2).trans e3, ?_, ?_⟩
  · rw [hobs]
    exact hiff.2 (hwY.congr hπ.symm)
  · rw [hobs, hint, integral_congr_ae hπ, ← e3, ← e2, e1]

/-- **The transport g-formula.** Under the indicator form of ignorability in the source, with
integrable potential outcomes, positivity of the arm, structural invariance through `g`,
overlap and integrability of `Y₂`, the target mean is the mean under the target covariate law of
any version `m(a, ·)` of the observed source regression `E₁[Y | X₁, A = a]`:
`E₂[Y₂] = ∫ m(a, x) dP*_X(x)`. -/
theorem integral_target_eq_integral_regression (a : Bool) (hX₁ : Measurable X₁)
    (hX₂ : Measurable X₂) (hA : Measurable A) (hY : ∀ b, Measurable (Y₁ b))
    (hYi : ∀ b, Integrable (Y₁ b) μ₁) (hY₂ : Integrable Y₂ μ₂)
    (hign : IndicatorIgnorable μ₁ A X₁ Y₁) (hps : IsPropensityScore μ₁ A X₁ e)
    (hpos : ∀ᵐ ω ∂μ₁, 0 < armProb e a (X₁ ω)) {m : Bool → 𝒳 → ℝ}
    (hreg : IsOutcomeRegression μ₁ A X₁ (obsOutcome A Y₁) m)
    (hcom : IsCommonRegression μ₁ X₁ (Y₁ a) μ₂ X₂ Y₂ g) (hov : μ₂.map X₂ ≪ μ₁.map X₁) :
    ∫ ω, Y₂ ω ∂μ₂ = ∫ x, m a x ∂(μ₂.map X₂) := by
  obtain ⟨hg, Hsrc, Htgt⟩ := hcom
  have hm := hreg.ae_eq_condExp hX₁ hA hYi hps a (hign.meanIgnorable hX₁ hA hY a (hYi a)) hpos
  have h1 : ∀ᵐ ω ∂μ₁, m a (X₁ ω) = g (X₁ ω) := by
    filter_upwards [hm, Hsrc] with ω h1 h2
    rw [h1, h2]
  have h2 : ∀ᵐ x ∂(μ₁.map X₁), m a x = g x :=
    (ae_map_iff hX₁.aemeasurable (measurableSet_eq_fun (hreg.1 a) hg)).2 h1
  rw [(integral_target_eq_integral_common hX₂ hY₂ hg Htgt).2]
  have h3 : ∀ᵐ x ∂(μ₂.map X₂), m a x = g x := hov.ae_le h2
  exact integral_congr_ae (h3.mono fun x hx => hx.symm)

end Transport

end CausalInference
