/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.AugmentedWeighting

/-!
# The efficient influence function of an arm mean and of the average effect

For a binary point treatment `A`, covariates `W` and potential outcomes `Y`, the observed data
of a unit are `O = (W, A, Y)` with `Y = Y(A)` (`obsData`). With the propensity score `e`
(arm probability `π_a = armProb e a`) and the outcome regression `m`, the augmented summand of
the arm `a` on the observation space is
`1{A = a} Y / π_a(W) - (1{A = a} - π_a(W)) / π_a(W) · m(a, W)` (`aipwScore`), the same formula
as `PointTreatment.aipwTerm` (`aipwScore_obsData`). Centered at `ψ_a = E[Y(a)]` it is the
efficient influence function of the arm mean (`armEIF`); the difference of the two arms
centered at the average effect is that of the average effect (`ateEIF`).

## Main definitions

* `obsData A Y W`: the observation `ω ↦ (W ω, A ω, Y(A ω) ω)`.
* `aipwScore e m a`, `armEIF e m a ψ`, `ateEIF e m ψ`: the augmented summand and the two
  centered influence functions, as functions of an observation.
* `weightedResidual A Y W e m a`: the weighted residual `1{A = a} (Y - m(a, W)) / π_a(W)`.

## Main results

* `integral_weightedResidual_mul_eq_zero`: the weighted residual is orthogonal to every square
  integrable function of `W`; only the regression property of `m` is used.
* `integral_weightedResidual_sq`: `E[R_a²] = E[v(a, W) / π_a(W)]`, with `v(A, W)` a version of
  `E[(Y - m(A, W))² | W, A]`.
* `integral_armEIF_eq_zero`, `integral_ateEIF_eq_zero`: the influence functions are centered.
* `integral_armEIF_sq`: `E[φ_a²] = E[v(a, W) / π_a(W)] + Var(E[Y(a) | W])`.
* `integral_ateEIF_sq`:
  `E[φ²] = E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])`.
* `Ignorable.integral_armEIF_sq`, `Ignorable.integral_ateEIF_sq`: the same under ignorability
  `A ⫫ (Y(0), Y(1)) | W`.

The positivity hypothesis is the strict form `ε ≤ π_a(W)` almost surely, with `ε > 0`; it makes
the weights bounded, so that every integral above is that of an integrable function.

## References

* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66 (1998).
* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, Journal of the American Statistical Association 89
  (1994).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory MissingData PointTreatment

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]

section Definitions

omit [MeasurableSpace 𝒲]

/-- The observed data `(W, A, Y)` of a unit, with the observed outcome `Y = Y(A)`. -/
def obsData (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲) : Ω → 𝒲 × Bool × ℝ :=
  fun ω => (W ω, A ω, obsOutcome A Y ω)

/-- The indicator `1{t = a}` of the arm `a` at an observation `(w, t, y)`. -/
def armIndicator (a : Bool) (z : 𝒲 × Bool × ℝ) : ℝ := if z.2.1 = a then 1 else 0

/-- The augmented summand of the arm `a` at an observation `z = (w, t, y)`, for a score `e`
and a regression `m`: `1{t = a} y / π_a(w) - (1{t = a} - π_a(w)) / π_a(w) · m(a, w)`, with
`π_a = armProb e a`. -/
noncomputable def aipwScore (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool) (z : 𝒲 × Bool × ℝ) : ℝ :=
  armIndicator a z * z.2.2 / armProb e a z.1 -
    (armIndicator a z - armProb e a z.1) / armProb e a z.1 * m a z.1

/-- The influence function of the arm mean `ψ = E[Y(a)]`: the augmented summand minus `ψ`. -/
noncomputable def armEIF (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool) (ψ : ℝ)
    (z : 𝒲 × Bool × ℝ) : ℝ :=
  aipwScore e m a z - ψ

/-- The influence function of the average effect `ψ = E[Y(1) - Y(0)]`: the difference of the
augmented summands of the two arms minus `ψ`. -/
noncomputable def ateEIF (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (ψ : ℝ) (z : 𝒲 × Bool × ℝ) : ℝ :=
  aipwScore e m true z - aipwScore e m false z - ψ

/-- The weighted residual `1{A = a} (Y - m(a, W)) / π_a(W)` of the arm `a`. -/
noncomputable def weightedResidual (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲) (e : 𝒲 → ℝ)
    (m : Bool → 𝒲 → ℝ) (a : Bool) : Ω → ℝ :=
  fun ω => respInd (arm A a) ω * (obsOutcome A Y ω - m a (W ω)) / armProb e a (W ω)

variable {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}

theorem armIndicator_obsData (a : Bool) (ω : Ω) :
    armIndicator a (obsData A Y W ω) = respInd (arm A a) ω := by
  unfold armIndicator obsData
  rw [respInd_arm_apply]

/-- The augmented summand at the observed data is `PointTreatment.aipwTerm`. -/
theorem aipwScore_obsData (a : Bool) (ω : Ω) :
    aipwScore e m a (obsData A Y W ω) = aipwTerm A Y W e m a ω := by
  simp only [aipwScore, aipwTerm, armIndicator_obsData]
  rfl

/-- Where `π_a(w) ≠ 0`, the augmented summand is the regression plus the weighted residual:
`m(a, w) + 1{t = a} (y - m(a, w)) / π_a(w)`. -/
theorem aipwScore_eq (a : Bool) {z : 𝒲 × Bool × ℝ} (h : armProb e a z.1 ≠ 0) :
    aipwScore e m a z = m a z.1 + armIndicator a z * (z.2.2 - m a z.1) / armProb e a z.1 := by
  simp only [aipwScore]
  field_simp
  ring

theorem armEIF_obsData_eq (a : Bool) (ψ : ℝ) {ω : Ω} (h : armProb e a (W ω) ≠ 0) :
    armEIF e m a ψ (obsData A Y W ω) = weightedResidual A Y W e m a ω + (m a (W ω) - ψ) := by
  rw [armEIF, aipwScore_eq a h, armIndicator_obsData]
  simp only [obsData, weightedResidual]
  ring

theorem ateEIF_obsData_eq (ψ : ℝ) {ω : Ω} (h1 : armProb e true (W ω) ≠ 0)
    (h0 : armProb e false (W ω) ≠ 0) :
    ateEIF e m ψ (obsData A Y W ω) = weightedResidual A Y W e m true ω -
      weightedResidual A Y W e m false ω + (m true (W ω) - m false (W ω) - ψ) := by
  rw [ateEIF, aipwScore_eq true h1, aipwScore_eq false h0, armIndicator_obsData,
    armIndicator_obsData]
  simp only [obsData, weightedResidual]
  ring

/-- The weighted residuals of the two arms have product zero at every unit. -/
theorem weightedResidual_true_mul_false (ω : Ω) :
    weightedResidual A Y W e m true ω * weightedResidual A Y W e m false ω = 0 := by
  simp only [weightedResidual, respInd_arm_apply]
  cases A ω <;> simp

end Definitions

section Measurability

variable {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}

theorem measurable_obsData (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) :
    Measurable (obsData A Y W) :=
  hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))

theorem measurable_armIndicator (a : Bool) : Measurable (armIndicator (𝒲 := 𝒲) a) :=
  (Measurable.of_discrete (f := fun b : Bool => if b = a then (1 : ℝ) else 0)).comp
    (measurable_fst.comp measurable_snd)

theorem measurable_aipwScore (he : Measurable e) {a : Bool} (hm : Measurable (m a)) :
    Measurable (aipwScore e m a) := by
  have hp : Measurable fun z : 𝒲 × Bool × ℝ => armProb e a z.1 :=
    (measurable_armProb he a).comp measurable_fst
  have hy : Measurable fun z : 𝒲 × Bool × ℝ => z.2.2 := measurable_snd.comp measurable_snd
  exact (((measurable_armIndicator a).mul hy).div hp).sub
    ((((measurable_armIndicator a).sub hp).div hp).mul (hm.comp measurable_fst))

theorem measurable_armEIF (he : Measurable e) {a : Bool} (hm : Measurable (m a)) (ψ : ℝ) :
    Measurable (armEIF e m a ψ) :=
  (measurable_aipwScore he hm).sub_const ψ

theorem measurable_ateEIF (he : Measurable e) (hm : ∀ a, Measurable (m a)) (ψ : ℝ) :
    Measurable (ateEIF e m ψ) :=
  ((measurable_aipwScore he (hm true)).sub (measurable_aipwScore he (hm false))).sub_const ψ

end Measurability

section Moments

variable {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω}

/-- Conditioning inside an integral: for `g` strongly measurable for a sub σ-algebra `m'`,
`∫ f g = ∫ E[f | m'] g`, when `f` and `f g` are integrable. -/
theorem integral_mul_eq_integral_condExp_mul {m' : MeasurableSpace Ω} (hm : m' ≤ mΩ)
    [SigmaFinite (μ.trim hm)] {f g : Ω → ℝ} (hg : StronglyMeasurable[m'] g)
    (hf : Integrable f μ) (hfg : Integrable (f * g) μ) :
    ∫ ω, f ω * g ω ∂μ = ∫ ω, μ[f | m'] ω * g ω ∂μ :=
  calc ∫ ω, f ω * g ω ∂μ = ∫ ω, μ[f * g | m'] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, μ[f | m'] ω * g ω ∂μ :=
      integral_congr_ae (condExp_mul_of_stronglyMeasurable_right hg hfg hf)

omit [MeasurableSpace 𝒲] in
/-- The inverse weight `1{A = a} / π_a(W)` as a function of `(W, A)`. -/
theorem respInd_div_armProb_eq (a : Bool) (ω : Ω) :
    respInd (arm A a) ω / armProb e a (W ω) =
      (fun p : 𝒲 × Bool => (if p.2 = a then (1 : ℝ) else 0) / armProb e p.2 p.1)
        (W ω, A ω) := by
  simp only [respInd_arm_apply]
  split_ifs with h
  · rw [h]
  · simp

omit [MeasurableSpace 𝒲] in
theorem weightedResidual_eq (a : Bool) (ω : Ω) :
    weightedResidual A Y W e m a ω =
      (obsOutcome A Y ω - m (A ω) (W ω)) * (respInd (arm A a) ω / armProb e a (W ω)) := by
  simp only [weightedResidual, respInd_arm_apply]
  split_ifs with h
  · rw [h]; ring
  · simp

theorem stronglyMeasurable_respInd_div (he : Measurable e) (a : Bool) :
    StronglyMeasurable[MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance]
      fun ω => respInd (arm A a) ω / armProb e a (W ω) := by
  have hk : Measurable fun p : 𝒲 × Bool =>
      (if p.2 = a then (1 : ℝ) else 0) / armProb e p.2 p.1 := by
    have h1 : Measurable fun p : 𝒲 × Bool => if p.2 = a then (1 : ℝ) else 0 :=
      (Measurable.of_discrete (f := fun b : Bool => if b = a then (1 : ℝ) else 0)).comp
        measurable_snd
    have h2 : Measurable fun p : 𝒲 × Bool => armProb e p.2 p.1 := by
      have : (fun p : 𝒲 × Bool => armProb e p.2 p.1) =
          fun p => if p.2 = true then e p.1 else 1 - e p.1 := by
        funext p; cases p.2 <;> simp [armProb]
      rw [this]
      exact Measurable.ite (measurable_snd (measurableSet_singleton true)) (he.comp measurable_fst)
        (measurable_const.sub (he.comp measurable_fst))
    exact h1.div h2
  have heq : (fun ω => respInd (arm A a) ω / armProb e a (W ω)) =
      (fun p : 𝒲 × Bool => (if p.2 = a then (1 : ℝ) else 0) / armProb e p.2 p.1) ∘
        (fun ω => (W ω, A ω)) := funext fun ω => respInd_div_armProb_eq a ω
  rw [heq]
  exact (hk.comp (comap_measurable (fun ω => (W ω, A ω)))).stronglyMeasurable

omit [MeasurableSpace 𝒲] in
theorem norm_respInd_div_le {a : Bool} {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    ∀ᵐ ω ∂μ, ‖respInd (arm A a) ω / armProb e a (W ω)‖ ≤ ε⁻¹ := by
  filter_upwards [hpos] with ω h
  have hp : 0 < armProb e a (W ω) := hε.trans_le h
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, abs_of_nonneg (respInd_nonneg _ ω),
    div_le_iff₀ hp]
  calc respInd (arm A a) ω ≤ 1 := respInd_le_one _ ω
    _ = ε⁻¹ * ε := by field_simp
    _ ≤ ε⁻¹ * armProb e a (W ω) := mul_le_mul_of_nonneg_left h (by positivity)

omit [MeasurableSpace 𝒲] in
/-- Under consistency the observed outcome is square integrable when both potential outcomes
are: `|Y| ≤ |Y(1)| + |Y(0)|`. -/
theorem memLp_obsOutcome (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hY2 : ∀ a, MemLp (Y a) 2 μ) : MemLp (obsOutcome A Y) 2 μ := by
  refine ((hY2 true).norm.add (hY2 false).norm).of_le
    (measurable_obsOutcome hA hY).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, obsOutcome]
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖Y true ω‖ + ‖Y false ω‖)]
  cases A ω
  · exact le_add_of_nonneg_left (norm_nonneg _)
  · exact le_add_of_nonneg_right (norm_nonneg _)

omit [MeasurableSpace 𝒲] in
/-- The Pythagorean identity: if `∫ R B = 0` for square integrable `R` and `B`, then
`∫ (R + B)² = ∫ R² + ∫ B²`. -/
theorem integral_add_sq_of_integral_mul_eq_zero {R B : Ω → ℝ} (hR : MemLp R 2 μ)
    (hB : MemLp B 2 μ) (h : ∫ ω, R ω * B ω ∂μ = 0) :
    ∫ ω, (R ω + B ω) ^ 2 ∂μ = ∫ ω, R ω ^ 2 ∂μ + ∫ ω, B ω ^ 2 ∂μ := by
  have i1 : Integrable (fun ω => R ω ^ 2) μ := hR.integrable_sq
  have i2 : Integrable (fun ω => R ω * B ω) μ := hR.integrable_mul hB
  have i3 : Integrable (fun ω => B ω ^ 2) μ := hB.integrable_sq
  calc ∫ ω, (R ω + B ω) ^ 2 ∂μ = ∫ ω, (R ω ^ 2 + 2 * (R ω * B ω) + B ω ^ 2) ∂μ := by
        congr 1; funext ω; ring
    _ = ∫ ω, R ω ^ 2 ∂μ + 2 * ∫ ω, R ω * B ω ∂μ + ∫ ω, B ω ^ 2 ∂μ := by
        rw [integral_add (f := fun ω => R ω ^ 2 + 2 * (R ω * B ω)) (i1.add (i2.const_mul 2)) i3,
          integral_add (f := fun ω => R ω ^ 2) i1 (i2.const_mul 2), integral_const_mul]
    _ = _ := by rw [h, mul_zero, add_zero]

variable [IsProbabilityMeasure μ]

/-- **The weighted residual is orthogonal to the functions of `W`.** If `m(A, W)` is a version
of `E[Y | W, A]` and `π_a(W) ≥ ε > 0` almost surely, then
`E[1{A = a} (Y - m(a, W)) / π_a(W) · h(W)] = 0` for every measurable `h` with `Y h(W)` and
`m(A, W) h(W)` integrable. Neither ignorability nor a correct score is used. -/
theorem integral_weightedResidual_mul_eq_zero (hW : Measurable W) (hA : Measurable A)
    (he : Measurable e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hYo : Integrable (obsOutcome A Y) μ) (a : Bool) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) {h : 𝒲 → ℝ} (hh : Measurable h)
    (h1 : Integrable (fun ω => obsOutcome A Y ω * h (W ω)) μ)
    (h2 : Integrable (fun ω => m (A ω) (W ω) * h (W ω)) μ) :
    ∫ ω, weightedResidual A Y W e m a ω * h (W ω) ∂μ = 0 := by
  have hmWA : MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance ≤ mΩ :=
    (hW.prodMk hA).comap_le
  have hK := stronglyMeasurable_respInd_div (W := W) (A := A) he a
  have hWm : Measurable[MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] W :=
    measurable_fst.comp (comap_measurable _)
  set G : Ω → ℝ := fun ω => respInd (arm A a) ω / armProb e a (W ω) * h (W ω) with hGdef
  have hG : StronglyMeasurable[MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] G :=
    hK.mul (hh.comp hWm).stronglyMeasurable
  have hKb := norm_respInd_div_le (A := A) hε hpos
  have hKm := (hK.mono hmWA).aestronglyMeasurable (μ := μ)
  have i1 : Integrable (obsOutcome A Y * G) μ :=
    (h1.bdd_mul hKm hKb).congr (Filter.Eventually.of_forall fun ω => by
      simp only [Pi.mul_apply, hGdef]; ring)
  have i2 : Integrable (fun ω => m (A ω) (W ω) * G ω) μ :=
    (h2.bdd_mul hKm hKb).congr (Filter.Eventually.of_forall fun ω => by
      simp only [hGdef]; ring)
  have e1 := integral_mul_eq_integral_condExp_mul hmWA hG hYo i1
  have e2 : ∫ ω, μ[obsOutcome A Y | MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] ω *
      G ω ∂μ = ∫ ω, m (A ω) (W ω) * G ω ∂μ :=
    integral_congr_ae (hreg.2.mono fun ω hω => by simp only [hω])
  calc ∫ ω, weightedResidual A Y W e m a ω * h (W ω) ∂μ
      = ∫ ω, (obsOutcome A Y ω * G ω - m (A ω) (W ω) * G ω) ∂μ := by
        congr 1; funext ω; rw [weightedResidual_eq]; simp only [hGdef]; ring
    _ = 0 := by
        rw [integral_sub (f := fun ω => obsOutcome A Y ω * G ω) i1 i2, e1, e2, sub_self]

/-- **The second moment of the weighted residual**: `E[R_a²] = E[v(a, W) / π_a(W)]`, where
`v(A, W)` is a version of `E[(Y - m(A, W))² | W, A]` (so `v(a, W)` is the conditional variance
of the outcome in the arm `a`), `e` is the propensity score and `π_a(W) ≥ ε > 0`. -/
theorem integral_weightedResidual_sq (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hYo2 : MemLp (obsOutcome A Y) 2 μ) {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) {ε : ℝ} (hε : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    ∫ ω, weightedResidual A Y W e m a ω ^ 2 ∂μ =
      ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ := by
  have he := hps.1
  have hmWA : MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance ≤ mΩ :=
    (hW.prodMk hA).comap_le
  have hmW : MeasurableSpace.comap W inferInstance ≤ mΩ := hW.comap_le
  set K : Ω → ℝ := fun ω => respInd (arm A a) ω / armProb e a (W ω) with hKdef
  have hK : StronglyMeasurable[MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] K :=
    stronglyMeasurable_respInd_div he a
  have hKK := hK.mul hK
  have hKb := norm_respInd_div_le (A := A) hε hpos
  have hKKb : ∀ᵐ ω ∂μ, ‖K ω * K ω‖ ≤ ε⁻¹ * ε⁻¹ := hKb.mono fun ω h => by
    rw [norm_mul]; exact mul_le_mul h h (norm_nonneg _) (by positivity)
  have hKKm := (hKK.mono hmWA).aestronglyMeasurable (μ := μ)
  have hmTX2 : MemLp (fun ω => m (A ω) (W ω)) 2 μ := (hYo2.condExp one_le_two).ae_eq hreg.2
  set r : Ω → ℝ := fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2 with hrdef
  have hr : Integrable r μ := (hYo2.sub hmTX2).integrable_sq
  have hrKK : Integrable (r * (K * K)) μ :=
    (hr.mul_bdd hKKm hKKb).congr (Filter.Eventually.of_forall fun _ => rfl)
  have hvI : Integrable (fun ω => v (A ω) (W ω)) μ := integrable_condExp.congr hv.2
  set H : Ω → ℝ := fun ω => v a (W ω) / armProb e a (W ω) ^ 2 with hHdef
  have hH : StronglyMeasurable[MeasurableSpace.comap W inferInstance] H :=
    (((hv.1 a).comp (comap_measurable W)).div
      (((measurable_armProb he a).comp (comap_measurable W)).pow_const 2)).stronglyMeasurable
  have hvK : ∀ ω, v (A ω) (W ω) * (K ω * K ω) = respInd (arm A a) ω * H ω := fun ω => by
    simp only [hKdef, hHdef, respInd_arm_apply]
    split_ifs with h
    · rw [h]; ring
    · simp
  have hbH : Integrable (respInd (arm A a) * H) μ :=
    (hvI.mul_bdd hKKm hKKb).congr (Filter.Eventually.of_forall fun ω => (hvK ω))
  have hbI : Integrable (respInd (arm A a)) μ := integrable_respInd (measurable_arm hA a)
  have hne : ∀ᵐ ω ∂μ, armProb e a (W ω) ≠ 0 := hpos.mono fun ω h => (hε.trans_le h).ne'
  calc ∫ ω, weightedResidual A Y W e m a ω ^ 2 ∂μ = ∫ ω, r ω * (K ω * K ω) ∂μ := by
        congr 1; funext ω; rw [weightedResidual_eq]; simp only [hrdef, hKdef]; ring
    _ = ∫ ω, μ[r | MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] ω *
          (K ω * K ω) ∂μ := integral_mul_eq_integral_condExp_mul hmWA hKK hr hrKK
    _ = ∫ ω, respInd (arm A a) ω * H ω ∂μ :=
        integral_congr_ae (hv.2.mono fun ω hω => by simp only [hω, hvK])
    _ = ∫ ω, μ[respInd (arm A a) | MeasurableSpace.comap W inferInstance] ω * H ω ∂μ :=
        integral_mul_eq_integral_condExp_mul hmW hH hbI hbH
    _ = ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hps.condExp_arm hW hA a, hne] with ω h1 h2
        rw [h1, hHdef]
        field_simp

omit [IsProbabilityMeasure μ] in
theorem memLp_weightedResidual (hA : Measurable A) (hW : Measurable W) (he : Measurable e)
    {a : Bool} (hm : Measurable (m a)) (hYo2 : MemLp (obsOutcome A Y) 2 μ)
    (hm2 : MemLp (fun ω => m a (W ω)) 2 μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    MemLp (weightedResidual A Y W e m a) 2 μ := by
  have hr := hYo2.sub hm2
  refine hr.of_le_mul (c := ε⁻¹) ?_ ?_
  · exact (((measurable_respInd (measurable_arm hA a)).aemeasurable.mul
      (hYo2.aestronglyMeasurable.aemeasurable.sub (hm.comp hW).aemeasurable)).div
        ((measurable_armProb he a).comp hW).aemeasurable).aestronglyMeasurable
  · filter_upwards [norm_respInd_div_le (A := A) hε hpos] with ω h
    have : weightedResidual A Y W e m a ω =
        respInd (arm A a) ω / armProb e a (W ω) * (obsOutcome A Y ω - m a (W ω)) := by
      simp only [weightedResidual]; ring
    rw [this, norm_mul]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

omit [IsProbabilityMeasure μ] in
theorem integrable_weightedResidual (hW : Measurable W) (hA : Measurable A) (he : Measurable e)
    (hYo : Integrable (obsOutcome A Y) μ) (hmA : Integrable (fun ω => m (A ω) (W ω)) μ)
    (a : Bool) {ε : ℝ} (hε : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    Integrable (weightedResidual A Y W e m a) μ := by
  have hK := ((stronglyMeasurable_respInd_div (W := W) (A := A) he a).mono
    (hW.prodMk hA).comap_le).aestronglyMeasurable (μ := μ)
  exact ((hYo.sub hmA).mul_bdd hK (norm_respInd_div_le (A := A) hε hpos)).congr
    (Filter.Eventually.of_forall fun ω => (weightedResidual_eq a ω).symm)

/-- The influence function of the arm mean is integrable. -/
theorem integrable_armEIF (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (ψ : ℝ) :
    Integrable (fun ω => armEIF e m a ψ (obsData A Y W ω)) μ := by
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h => hε.trans_le h
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
  have hmI : Integrable (fun ω => m a (W ω)) μ := integrable_condExp.congr hid.symm
  have hmAI : Integrable (fun ω => m (A ω) (W ω)) μ := integrable_condExp.congr hreg.2
  have hRI := integrable_weightedResidual hW hA hps.1 (integrable_obsOutcome hA hYi) hmAI a hε hpos
  exact (hRI.add (hmI.sub (integrable_const ψ))).congr
    (hpos'.mono fun ω h => (armEIF_obsData_eq a ψ h.ne').symm)

/-- **The influence function of the arm mean is centered**: `E[φ_a(O)] = 0` at
`ψ_a = E[Y(a)]`, under mean ignorability of the arm, a correct score and a correct regression,
and `π_a(W) ≥ ε > 0`. -/
theorem integral_armEIF_eq_zero (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ∂μ = 0 := by
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h => hε.trans_le h
  have hYo := integrable_obsOutcome hA hYi
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
  have hmI : Integrable (fun ω => m a (W ω)) μ := integrable_condExp.congr hid.symm
  have hmAI : Integrable (fun ω => m (A ω) (W ω)) μ := integrable_condExp.congr hreg.2
  have hR0 := integral_weightedResidual_mul_eq_zero hW hA hps.1 hreg hYo a hε hpos
    (h := fun _ => 1) measurable_const (by simpa using hYo) (by simpa using hmAI)
  simp only [mul_one] at hR0
  have hRI := integrable_weightedResidual hW hA hps.1 hYo hmAI a hε hpos
  calc ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ∂μ
      = ∫ ω, (weightedResidual A Y W e m a ω + (m a (W ω) - armMean μ Y a)) ∂μ :=
        integral_congr_ae (hpos'.mono fun ω h => armEIF_obsData_eq a _ h.ne')
    _ = 0 := by
        rw [integral_add (g := fun ω => m a (W ω) - armMean μ Y a) hRI
            (hmI.sub (integrable_const _)),
          integral_sub hmI (integrable_const _), integral_const, hR0,
          ← armMean_eq_integral_regression hW hA hYi hreg hps a hmi hpos']
        simp

/-- **The variance of the efficient influence function of an arm mean.** Under mean
ignorability of the arm, a correct score `e` and regression `m`, square integrable potential
outcomes and `π_a(W) ≥ ε > 0`,
`E[φ_a(O)²] = E[v(a, W) / π_a(W)] + Var(E[Y(a) | W])`,
where `v(A, W)` is a version of `E[(Y - m(A, W))² | W, A]`. -/
theorem integral_armEIF_sq (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ =
      ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
        Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h => hε.trans_le h
  have hYo2 := memLp_obsOutcome hA hY hY2
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
  have hm2 : MemLp (fun ω => m a (W ω)) 2 μ := ((hY2 a).condExp one_le_two).ae_eq hid.symm
  have hmA2 : MemLp (fun ω => m (A ω) (W ω)) 2 μ := (hYo2.condExp one_le_two).ae_eq hreg.2
  set ψ := armMean μ Y a with hψ
  have hB2 : MemLp (fun ω => m a (W ω) - ψ) 2 μ := hm2.sub (memLp_const ψ)
  have hR2 := memLp_weightedResidual hA hW hps.1 (hreg.1 a) hYo2 hm2 hε hpos
  have hcross := integral_weightedResidual_mul_eq_zero hW hA hps.1 hreg
    (hYo2.integrable one_le_two) a hε hpos (h := fun w => m a w - ψ) ((hreg.1 a).sub_const ψ)
    (hYo2.integrable_mul hB2) (hmA2.integrable_mul hB2)
  have hsq := integral_weightedResidual_sq hW hA hps hreg hYo2 hv a hε hpos
  have hB : ∫ ω, (m a (W ω) - ψ) ^ 2 ∂μ =
      Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] := by
    rw [variance_eq_integral (stronglyMeasurable_condExp.mono hW.comap_le).measurable.aemeasurable,
      integral_condExp hW.comap_le]
    exact integral_congr_ae (hid.mono fun ω h => by simp only [h, hψ]; rfl)
  calc ∫ ω, armEIF e m a ψ (obsData A Y W ω) ^ 2 ∂μ
      = ∫ ω, (weightedResidual A Y W e m a ω + (m a (W ω) - ψ)) ^ 2 ∂μ :=
        integral_congr_ae (hpos'.mono fun ω h => by simp only [armEIF_obsData_eq a ψ h.ne'])
    _ = _ := by rw [integral_add_sq_of_integral_mul_eq_zero hR2 hB2 hcross, hsq, hB]

omit [MeasurableSpace 𝒲] [IsProbabilityMeasure μ] in
theorem ateEIF_eq_sub (ψ₁ ψ₀ : ℝ) (z : 𝒲 × Bool × ℝ) :
    ateEIF e m (ψ₁ - ψ₀) z = armEIF e m true ψ₁ z - armEIF e m false ψ₀ z := by
  simp only [ateEIF, armEIF]; ring

/-- **The influence function of the average effect is centered** under mean ignorability of
both arms and strict overlap `ε ≤ e(W) ≤ 1 - ε`. -/
theorem integral_ateEIF_eq_zero (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) :
    ∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ∂μ = 0 := by
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  rw [ate_eq_armMean_sub (hYi true) (hYi false)]
  simp only [ateEIF_eq_sub]
  rw [integral_sub (integrable_armEIF hW hA hYi hps hreg true (hmi true) hov.1 (hpos true) _)
    (integrable_armEIF hW hA hYi hps hreg false (hmi false) hov.1 (hpos false) _),
    integral_armEIF_eq_zero hW hA hYi hps hreg true (hmi true) hov.1 (hpos true),
    integral_armEIF_eq_zero hW hA hYi hps hreg false (hmi false) hov.1 (hpos false), sub_zero]

/-- **The variance of the efficient influence function of the average effect.** Under mean
ignorability of both arms, a correct score and regression, square integrable potential outcomes
and strict overlap `ε ≤ e(W) ≤ 1 - ε`,
`E[φ(O)²] = E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])`. -/
theorem integral_ateEIF_sq (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) :
    ∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ^ 2 ∂μ =
      ∫ ω, v true (W ω) / e (W ω) ∂μ + ∫ ω, v false (W ω) / (1 - e (W ω)) ∂μ +
        Var[cate μ W Y; μ] := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  have hε := hov.1
  have hpos' : ∀ a, ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := fun a =>
    (hpos a).mono fun _ h => hε.trans_le h
  have hYo2 := memLp_obsOutcome hA hY hY2
  have hYo := hYo2.integrable one_le_two
  have hid := fun a => hreg.ae_eq_condExp hW hA hYi hps a (hmi a) (hpos' a)
  have hm2 : ∀ a, MemLp (fun ω => m a (W ω)) 2 μ := fun a =>
    ((hY2 a).condExp one_le_two).ae_eq (hid a).symm
  have hmA2 : MemLp (fun ω => m (A ω) (W ω)) 2 μ := (hYo2.condExp one_le_two).ae_eq hreg.2
  set ψ := ate μ Y with hψ
  set B : Ω → ℝ := fun ω => m true (W ω) - m false (W ω) - ψ with hBdef
  have hB2 : MemLp B 2 μ := ((hm2 true).sub (hm2 false)).sub (memLp_const ψ)
  have hR2 := fun a => memLp_weightedResidual hA hW hps.1 (hreg.1 a) hYo2 (hm2 a) hε (hpos a)
  have hcross := fun a => integral_weightedResidual_mul_eq_zero hW hA hps.1 hreg hYo a hε
    (hpos a) (h := fun w => m true w - m false w - ψ)
    (((hreg.1 true).sub (hreg.1 false)).sub_const ψ)
    (hYo2.integrable_mul hB2) (hmA2.integrable_mul hB2)
  set R₁ := weightedResidual A Y W e m true
  set R₀ := weightedResidual A Y W e m false
  have hc : ∫ ω, (R₁ ω + -R₀ ω) * B ω ∂μ = 0 := by
    have e1 : (fun ω => (R₁ ω + -R₀ ω) * B ω) = fun ω => R₁ ω * B ω - R₀ ω * B ω := by
      funext ω; ring
    rw [e1, integral_sub (f := fun ω => R₁ ω * B ω) (g := fun ω => R₀ ω * B ω)
      ((hR2 true).integrable_mul hB2)
      ((hR2 false).integrable_mul hB2)]
    simp only [hBdef] at hcross ⊢
    rw [hcross true, hcross false, sub_self]
  have hc' : ∫ ω, R₁ ω * -R₀ ω ∂μ = 0 := by
    have e1 : (fun ω => R₁ ω * -R₀ ω) = fun _ => (0 : ℝ) := by
      funext ω; rw [mul_neg, weightedResidual_true_mul_false, neg_zero]
    rw [e1, integral_zero]
  have hsq := fun a => integral_weightedResidual_sq hW hA hps hreg hYo2 hv a hε (hpos a)
  have hcate := hreg.sub_ae_eq_cate hW hA hYi hps hmi hov.overlapAE
  have hB : ∫ ω, B ω ^ 2 ∂μ = Var[cate μ W Y; μ] := by
    have hcm : AEMeasurable (cate μ W Y) μ :=
      (stronglyMeasurable_condExp.mono hW.comap_le).measurable.aemeasurable
    rw [variance_eq_integral hcm, ← ate_eq_integral_cate hW]
    exact integral_congr_ae (hcate.mono fun ω h => by simp only [hBdef, h, hψ])
  have hne : ∀ᵐ ω ∂μ, armProb e true (W ω) ≠ 0 ∧ armProb e false (W ω) ≠ 0 := by
    filter_upwards [hpos' true, hpos' false] with ω h1 h0 using ⟨h1.ne', h0.ne'⟩
  calc ∫ ω, ateEIF e m ψ (obsData A Y W ω) ^ 2 ∂μ
      = ∫ ω, ((R₁ ω + -R₀ ω) + B ω) ^ 2 ∂μ :=
        integral_congr_ae (hne.mono fun ω h => by
          simp only [ateEIF_obsData_eq ψ h.1 h.2, hBdef, R₁, R₀]; ring)
    _ = ∫ ω, R₁ ω ^ 2 ∂μ + ∫ ω, R₀ ω ^ 2 ∂μ + ∫ ω, B ω ^ 2 ∂μ := by
        have h1 := integral_add_sq_of_integral_mul_eq_zero (R := fun ω => R₁ ω + -R₀ ω)
          ((hR2 true).add (hR2 false).neg) hB2 hc
        have h2 := integral_add_sq_of_integral_mul_eq_zero (R := R₁) (B := fun ω => -R₀ ω)
          (hR2 true) (hR2 false).neg hc'
        beta_reduce at h1 h2
        simp only [neg_sq] at h2
        rw [h1, h2]
    _ = _ := by
        rw [hsq true, hsq false, hB]
        simp only [armProb_true, armProb_false]

/-- **The variance of the efficient influence function of an arm mean under ignorability**
`A ⫫ (Y(0), Y(1)) | W`. -/
theorem _root_.CausalInference.PointTreatment.Ignorable.integral_armEIF_sq
    [StandardBorelSpace Ω] (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hign : Ignorable μ A hW Y)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) {ε : ℝ} (hε : 0 < ε) (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ =
      ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
        Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] :=
  CausalInference.Efficiency.integral_armEIF_sq hW hA hY hY2 hps hreg hv a
    (hign.meanIgnorable hW hA hY a ((hY2 a).integrable one_le_two)) hε hpos

/-- **The variance of the efficient influence function of the average effect under
ignorability** `A ⫫ (Y(0), Y(1)) | W` and strict overlap. -/
theorem _root_.CausalInference.PointTreatment.Ignorable.integral_ateEIF_sq
    [StandardBorelSpace Ω] (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hign : Ignorable μ A hW Y)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) :
    ∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ^ 2 ∂μ =
      ∫ ω, v true (W ω) / e (W ω) ∂μ + ∫ ω, v false (W ω) / (1 - e (W ω)) ∂μ +
        Var[cate μ W Y; μ] :=
  CausalInference.Efficiency.integral_ateEIF_sq hW hA hY hY2 hps hreg hv
    (fun a => hign.meanIgnorable hW hA hY a ((hY2 a).integrable one_le_two)) hov

end Moments

end Efficiency
end CausalInference
