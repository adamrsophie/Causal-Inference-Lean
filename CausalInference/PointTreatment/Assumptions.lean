/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Basic
public import CausalInference.PointTreatment.CondIndep

/-!
# Point treatment: positivity, ignorability, propensity score, outcome regression

The identifying assumptions for a binary point treatment `A : Ω → Bool` with potential
outcomes `Y : Bool → Ω → ℝ` given a conditioning variable `W : Ω → 𝒲` (the covariates, or a
function of them such as a balancing score). The conditioning variable is an argument of every
predicate.

## Main definitions

* Positivity of a score `e : 𝒲 → ℝ`: `Overlap e` (`0 < e < 1` everywhere), `StrictOverlap e ε`
  (`ε ≤ e ≤ 1 - ε` everywhere, `ε > 0`), and their almost sure versions `OverlapAE e ν`,
  `StrictOverlapAE e ν ε` under a law `ν` of the conditioning variable.
* `arm A a`: the Boolean event `{A = a}`; its real indicator is `respInd (arm A a)`.
* `armProb e a`: the probability `e` of the treated arm, `1 - e` of the control arm.
* `IsPropensityScore μ A W e`: `e` is measurable and `e(W)` is a version of `E[1{A} | W]`.
* `IsOutcomeRegression μ A W Yo m`: each `m a` is measurable and `m(A, W)` is a version of
  `E[Yo | W, A]` (for the observed outcome `Yo`).
* `MeanIgnorable μ A W Y a`: the mean form `E[Y(a) | W, A] = E[Y(a) | W]`.
* `potentialPair Y`: the pair `(Y(0), Y(1))`.
* `IndicatorIgnorable μ A W Y`: the indicator form `E[1{A} | W, (Y(0), Y(1))] = E[1{A} | W]`.
* `Ignorable μ hW A Y`: the full form `A ⫫ (Y(0), Y(1)) | W`, Mathlib's `CondIndepFun` given the
  σ-algebra of `W` (it needs `StandardBorelSpace Ω`).

## Main results

* `StrictOverlap.overlap`, `Overlap.overlapAE`, `StrictOverlapAE.overlapAE`,
  `StrictOverlap.strictOverlapAE`, `OverlapAE.ae_comp`, `overlapAE_map_iff`: the implications
  between the positivity forms, and the passage from the law of `W` to almost every unit.
* `ignorable_iff_indicatorIgnorable`: the full form is the indicator form.
* `ignorable_iff_condExp_mul_eq`: the full form is the product rule for bounded test functions
  of the treatment and of the pair of potential outcomes.
* `IndicatorIgnorable.meanIgnorable`, `Ignorable.meanIgnorable`: the full form implies the mean
  form for each arm; more generally `IndicatorIgnorable.condExp_comp_eq` gives
  `E[g(W, Y(0), Y(1)) | W, A] = E[g(W, Y(0), Y(1)) | W]` for every integrable measurable `g`.
* `IndicatorIgnorable.marMean`, `Ignorable.mar`: each arm is missing at random in the sense of
  `CausalInference.MissingData` (response indicator `{A = a}`, full outcome `Y(a)`).
* `IsPropensityScore.condExp_arm`: `armProb e a (W)` is a version of `E[1{A = a} | W]`.

## References

* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70 (1983).
* G. W. Imbens, *The role of the propensity score in estimating dose-response functions*,
  Biometrika 87 (2000) (the weak, per arm, form of unconfoundedness).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]

/-! ### Positivity -/

section Positivity

variable (e : 𝒲 → ℝ)

/-- Positivity (overlap): `0 < e(w) < 1` for every value `w` of the conditioning variable. -/
def Overlap : Prop := ∀ w, 0 < e w ∧ e w < 1

/-- Strict positivity: `ε ≤ e(w) ≤ 1 - ε` for every `w`, for a constant `ε > 0`. It bounds the
inverse probability weights by `1 / ε`. -/
def StrictOverlap (ε : ℝ) : Prop := 0 < ε ∧ ∀ w, ε ≤ e w ∧ e w ≤ 1 - ε

/-- Positivity for almost every value of the conditioning variable under its law `ν`. -/
def OverlapAE (ν : Measure 𝒲) : Prop := ∀ᵐ w ∂ν, 0 < e w ∧ e w < 1

/-- Strict positivity for almost every value of the conditioning variable under its law `ν`. -/
def StrictOverlapAE (ν : Measure 𝒲) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ᵐ w ∂ν, ε ≤ e w ∧ e w ≤ 1 - ε

variable {e}

omit [MeasurableSpace 𝒲] in
theorem StrictOverlap.overlap {ε : ℝ} (h : StrictOverlap e ε) : Overlap e :=
  fun w => ⟨h.1.trans_le (h.2 w).1, (h.2 w).2.trans_lt (by linarith [h.1])⟩

theorem Overlap.overlapAE (h : Overlap e) (ν : Measure 𝒲) : OverlapAE e ν :=
  Filter.Eventually.of_forall h

theorem StrictOverlap.strictOverlapAE {ε : ℝ} (h : StrictOverlap e ε) (ν : Measure 𝒲) :
    StrictOverlapAE e ν ε :=
  ⟨h.1, Filter.Eventually.of_forall h.2⟩

theorem StrictOverlapAE.overlapAE {ν : Measure 𝒲} {ε : ℝ} (h : StrictOverlapAE e ν ε) :
    OverlapAE e ν :=
  h.2.mono fun _ hw => ⟨h.1.trans_le hw.1, hw.2.trans_lt (by linarith [h.1])⟩

variable {μ : Measure Ω} {W : Ω → 𝒲}

/-- Positivity under the law of `W` holds at almost every unit. -/
theorem OverlapAE.ae_comp (hW : AEMeasurable W μ) (h : OverlapAE e (μ.map W)) :
    ∀ᵐ ω ∂μ, 0 < e (W ω) ∧ e (W ω) < 1 :=
  ae_of_ae_map hW h

/-- Strict positivity under the law of `W` holds at almost every unit. -/
theorem StrictOverlapAE.ae_comp {ε : ℝ} (hW : AEMeasurable W μ)
    (h : StrictOverlapAE e (μ.map W) ε) : ∀ᵐ ω ∂μ, ε ≤ e (W ω) ∧ e (W ω) ≤ 1 - ε :=
  ae_of_ae_map hW h.2

/-- For a measurable score, positivity under the law of `W` is positivity at almost every
unit. -/
theorem overlapAE_map_iff (hW : Measurable W) (he : Measurable e) :
    OverlapAE e (μ.map W) ↔ ∀ᵐ ω ∂μ, 0 < e (W ω) ∧ e (W ω) < 1 := by
  refine ⟨OverlapAE.ae_comp hW.aemeasurable, fun h => ?_⟩
  have hs : MeasurableSet {w | 0 < e w ∧ e w < 1} :=
    (measurableSet_lt measurable_const he).inter (measurableSet_lt he measurable_const)
  exact (ae_map_iff hW.aemeasurable hs).2 h

end Positivity

/-! ### The arms -/

/-- The Boolean event `{A = a}` of the arm `a`. Its real indicator is `respInd (arm A a)`. -/
def arm (A : Ω → Bool) (a : Bool) : Ω → Bool := fun ω => A ω == a

theorem respInd_arm_apply (A : Ω → Bool) (a : Bool) (ω : Ω) :
    respInd (arm A a) ω = if A ω = a then 1 else 0 := by
  simp [respInd_apply, arm]

theorem arm_true (A : Ω → Bool) : arm A true = A := by
  funext ω; simp [arm]

theorem respInd_arm_false (A : Ω → Bool) (ω : Ω) :
    respInd (arm A false) ω = 1 - respInd A ω := by
  rw [respInd_arm_apply, respInd_apply]
  cases A ω <;> simp

theorem measurable_arm {A : Ω → Bool} (hA : Measurable A) (a : Bool) : Measurable (arm A a) :=
  (Measurable.of_discrete (f := fun b : Bool => b == a)).comp hA

/-- The probability of the arm `a` given the score `e` of the treated arm: `e` for the treated
arm and `1 - e` for the control arm. -/
def armProb (e : 𝒲 → ℝ) (a : Bool) : 𝒲 → ℝ := fun w => if a then e w else 1 - e w

omit [MeasurableSpace 𝒲] in
@[simp] theorem armProb_true (e : 𝒲 → ℝ) : armProb e true = e := rfl

omit [MeasurableSpace 𝒲] in
@[simp] theorem armProb_false (e : 𝒲 → ℝ) (w : 𝒲) : armProb e false w = 1 - e w := rfl

theorem measurable_armProb {e : 𝒲 → ℝ} (he : Measurable e) (a : Bool) :
    Measurable (armProb e a) := by
  cases a
  · exact measurable_const.sub he
  · exact he

omit [MeasurableSpace 𝒲] in
theorem Overlap.armProb_pos {e : 𝒲 → ℝ} (h : Overlap e) (a : Bool) (w : 𝒲) :
    0 < armProb e a w := by
  cases a
  · simp only [armProb_false]; linarith [(h w).2]
  · exact (h w).1

omit [MeasurableSpace 𝒲] in
theorem armProb_pos_of_ae {μ : Measure Ω} {W : Ω → 𝒲} {e : 𝒲 → ℝ}
    (h : ∀ᵐ ω ∂μ, 0 < e (W ω) ∧ e (W ω) < 1) (a : Bool) :
    ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := by
  filter_upwards [h] with ω hω
  cases a
  · simp only [armProb_false]; linarith [hω.2]
  · exact hω.1

omit [MeasurableSpace 𝒲] in
theorem le_armProb_of_ae {μ : Measure Ω} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {ε : ℝ}
    (h : ∀ᵐ ω ∂μ, ε ≤ e (W ω) ∧ e (W ω) ≤ 1 - ε) (a : Bool) :
    ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω) := by
  filter_upwards [h] with ω hω
  cases a
  · simp only [armProb_false]; linarith [hω.2]
  · exact hω.1

/-! ### Propensity score and outcome regression -/

/-- The propensity score: a measurable `e : 𝒲 → ℝ` such that `e(W)` is a version of the
conditional expectation `E[1{A} | W] = P(A = 1 | W)`. -/
def IsPropensityScore (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲) (e : 𝒲 → ℝ) : Prop :=
  Measurable e ∧ μ[respInd A | MeasurableSpace.comap W inferInstance] =ᵐ[μ] fun ω => e (W ω)

/-- The outcome regression: measurable `m a : 𝒲 → ℝ` such that `m(A, W)` is a version of the
conditional expectation `E[Yo | W, A]` of the outcome `Yo` given the conditioning variable and
the treatment. Evaluated at a fixed arm, `m a (w)` is the regression `E[Yo | W = w, A = a]`. -/
def IsOutcomeRegression (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲) (Yo : Ω → ℝ)
    (m : Bool → 𝒲 → ℝ) : Prop :=
  (∀ a, Measurable (m a)) ∧
    μ[Yo | MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] =ᵐ[μ]
      fun ω => m (A ω) (W ω)

variable {μ : Measure Ω} {A : Ω → Bool} {W : Ω → 𝒲} {e : 𝒲 → ℝ}

/-- The propensity score of the arm `a`: if `e(W)` is a version of `E[1{A} | W]`, then
`armProb e a (W)` is a version of `E[1{A = a} | W]`. -/
theorem IsPropensityScore.condExp_arm [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (h : IsPropensityScore μ A W e) (a : Bool) :
    μ[respInd (arm A a) | MeasurableSpace.comap W inferInstance] =ᵐ[μ]
      fun ω => armProb e a (W ω) := by
  have hf : respInd (arm A a) = fun ω => (fun b : Bool => if b = a then (1 : ℝ) else 0) (A ω) :=
    funext fun ω => respInd_arm_apply A a ω
  rw [hf]
  filter_upwards [condExp_comp_bool hW.comap_le hA (fun b : Bool => if b = a then (1 : ℝ) else 0),
    h.2] with ω h1 h2
  rw [h1, h2]
  cases a
  · simp [armProb]; ring
  · simp [armProb]

/-- A propensity score takes values in `[0, 1]` at almost every unit. -/
theorem IsPropensityScore.ae_mem_Icc [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (h : IsPropensityScore μ A W e) :
    ∀ᵐ ω ∂μ, 0 ≤ e (W ω) ∧ e (W ω) ≤ 1 := by
  have h0 := condExp_nonneg (m := MeasurableSpace.comap W inferInstance)
    (Filter.Eventually.of_forall fun ω => respInd_nonneg A ω : 0 ≤ᵐ[μ] respInd A)
  have h1 := condExp_mono (m := MeasurableSpace.comap W inferInstance)
    (integrable_respInd hA) (integrable_const (1 : ℝ))
    (Filter.Eventually.of_forall fun ω => respInd_le_one A ω : respInd A ≤ᵐ[μ] fun _ => 1)
  rw [condExp_const hW.comap_le] at h1
  filter_upwards [h0, h1, h.2] with ω h0 h1 h2
  rw [h2] at h0 h1
  exact ⟨h0, h1⟩

/-! ### Ignorability -/

/-- The pair `(Y(0), Y(1))` of potential outcomes. -/
def potentialPair (Y : Bool → Ω → ℝ) : Ω → ℝ × ℝ := fun ω => (Y false ω, Y true ω)

theorem measurable_potentialPair {Y : Bool → Ω → ℝ} (hY : ∀ a, Measurable (Y a)) :
    Measurable (potentialPair Y) :=
  (hY false).prodMk (hY true)

/-- Mean ignorability for the arm `a`: `E[Y(a) | W, A] = E[Y(a) | W]` almost everywhere. Within
levels of `W`, the treatment carries no information about the mean of `Y(a)`. -/
def MeanIgnorable (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲) (Y : Bool → Ω → ℝ) (a : Bool) :
    Prop :=
  μ[Y a | MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] =ᵐ[μ]
    μ[Y a | MeasurableSpace.comap W inferInstance]

/-- Ignorability in indicator form: `E[1{A} | W, (Y(0), Y(1))] = E[1{A} | W]` almost everywhere.
For measurable variables on a finite measure it is equivalent to the full form `Ignorable`
(`ignorable_iff_indicatorIgnorable`), and it needs no `StandardBorelSpace Ω`. -/
def IndicatorIgnorable (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲) (Y : Bool → Ω → ℝ) : Prop :=
  μ[respInd A | MeasurableSpace.comap (fun ω => (W ω, potentialPair Y ω)) inferInstance] =ᵐ[μ]
    μ[respInd A | MeasurableSpace.comap W inferInstance]

/-- Ignorability (strong ignorability without the positivity part; Rosenbaum and Rubin 1983):
the treatment is conditionally independent of the pair of potential outcomes given `W`,
`A ⫫ (Y(0), Y(1)) | W`, as Mathlib's `CondIndepFun` given the σ-algebra generated by `W`. -/
def Ignorable [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → Bool)
    (hW : Measurable W) (Y : Bool → Ω → ℝ) : Prop :=
  CondIndepFun (MeasurableSpace.comap W inferInstance) hW.comap_le A (potentialPair Y) μ

variable {Y : Bool → Ω → ℝ}

/-- **The full form of ignorability is the indicator form.** -/
theorem ignorable_iff_indicatorIgnorable [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) :
    Ignorable μ A hW Y ↔ IndicatorIgnorable μ A W Y :=
  condIndepFun_iff_condExp_respInd_eq hW (measurable_potentialPair hY) hA

/-- **The full form of ignorability is the product rule for bounded test functions**:
`E[f(A) g(Y(0), Y(1)) | W] = E[f(A) | W] E[g(Y(0), Y(1)) | W]` for every `f : Bool → ℝ` and every
bounded measurable `g : ℝ × ℝ → ℝ`. -/
theorem ignorable_iff_condExp_mul_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) :
    Ignorable μ A hW Y ↔
      ∀ (f : Bool → ℝ) (g : ℝ × ℝ → ℝ), Measurable g → (∃ C, ∀ p, |g p| ≤ C) →
        μ[fun ω => f (A ω) * g (potentialPair Y ω) | MeasurableSpace.comap W inferInstance]
          =ᵐ[μ] μ[fun ω => f (A ω) | MeasurableSpace.comap W inferInstance] *
            μ[fun ω => g (potentialPair Y ω) | MeasurableSpace.comap W inferInstance] :=
  condIndepFun_iff_condExp_mul_eq hW (measurable_potentialPair hY) hA

/-- Under the indicator form of ignorability, every integrable measurable function of
`(W, Y(0), Y(1))` is mean independent of the treatment given `W`:
`E[g(W, Y(0), Y(1)) | W, A] = E[g(W, Y(0), Y(1)) | W]`. -/
theorem IndicatorIgnorable.condExp_comp_eq [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (h : IndicatorIgnorable μ A W Y)
    {g : 𝒲 × (ℝ × ℝ) → ℝ} (hg : Measurable g)
    (hgi : Integrable (fun ω => g (W ω, potentialPair Y ω)) μ) :
    μ[fun ω => g (W ω, potentialPair Y ω) |
        MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] =ᵐ[μ]
      μ[fun ω => g (W ω, potentialPair Y ω) | MeasurableSpace.comap W inferInstance] :=
  condExp_eq_of_condExp_respInd_eq hW (measurable_potentialPair hY) hA
    (hg.comp (comap_measurable _)) hgi h

/-- **The indicator form of ignorability implies mean ignorability** for each arm with an
integrable potential outcome. -/
theorem IndicatorIgnorable.meanIgnorable [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (h : IndicatorIgnorable μ A W Y)
    (a : Bool) (hYa : Integrable (Y a) μ) : MeanIgnorable μ A W Y a := by
  have hg : Measurable fun q : 𝒲 × (ℝ × ℝ) => if a then q.2.2 else q.2.1 := by
    cases a
    · exact measurable_snd.fst
    · exact measurable_snd.snd
  have hYa' : (fun ω => (fun q : 𝒲 × (ℝ × ℝ) => if a then q.2.2 else q.2.1)
      (W ω, potentialPair Y ω)) = Y a := by
    funext ω; cases a <;> rfl
  have := h.condExp_comp_eq hW hA hY hg (hYa'.symm ▸ hYa)
  rwa [hYa'] at this

/-- **The full form of ignorability implies mean ignorability** for each arm with an
integrable potential outcome. -/
theorem Ignorable.meanIgnorable [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (h : Ignorable μ A hW Y) (a : Bool)
    (hYa : Integrable (Y a) μ) : MeanIgnorable μ A W Y a :=
  ((ignorable_iff_indicatorIgnorable hW hA hY).1 h).meanIgnorable hW hA hY a hYa

/-- Under the indicator form of ignorability, the conditional expectation of `1{A}` is the same
given every σ-algebra between that of `W` and that of `(W, Y(0), Y(1))`. -/
theorem IndicatorIgnorable.condExp_respInd_of_le [IsFiniteMeasure μ] (hW : Measurable W)
    (hY : ∀ a, Measurable (Y a)) (h : IndicatorIgnorable μ A W Y) {m : MeasurableSpace Ω}
    (h1 : MeasurableSpace.comap W inferInstance ≤ m)
    (h2 : m ≤ MeasurableSpace.comap (fun ω => (W ω, potentialPair Y ω)) inferInstance) :
    μ[respInd A | m] =ᵐ[μ] μ[respInd A | MeasurableSpace.comap W inferInstance] := by
  have hle : MeasurableSpace.comap (fun ω => (W ω, potentialPair Y ω)) inferInstance ≤ mΩ :=
    (hW.prodMk (measurable_potentialPair hY)).comap_le
  refine (condExp_condExp_of_le h2 hle).symm.trans ?_
  refine (condExp_congr_ae h).trans ?_
  rw [condExp_of_stronglyMeasurable (h2.trans hle) (stronglyMeasurable_condExp.mono h1)
    integrable_condExp]

/-- **Each arm is missing at random.** Under the indicator form of ignorability, the arm `a`
is a missing data problem with response indicator `{A = a}` and full outcome `Y(a)` that
satisfies the mean form of missing at random, `MissingData.MARMean`. -/
theorem IndicatorIgnorable.marMean [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (h : IndicatorIgnorable μ A W Y) (a : Bool) :
    MARMean μ W (Y a) (arm A a) := by
  have hle : MeasurableSpace.comap (fun ω => (W ω, Y a ω)) inferInstance ≤
      MeasurableSpace.comap (fun ω => (W ω, potentialPair Y ω)) inferInstance := by
    have hg : Measurable fun q : 𝒲 × (ℝ × ℝ) => (q.1, if a then q.2.2 else q.2.1) := by
      cases a
      · exact measurable_fst.prodMk measurable_snd.fst
      · exact measurable_fst.prodMk measurable_snd.snd
    have hcomp : (fun ω => (W ω, Y a ω)) = (fun q : 𝒲 × (ℝ × ℝ) =>
        (q.1, if a then q.2.2 else q.2.1)) ∘ fun ω => (W ω, potentialPair Y ω) := by
      funext ω; cases a <;> rfl
    rw [hcomp]
    exact (hg.comp (comap_measurable _)).comap_le
  have hmid := h.condExp_respInd_of_le hW hY (comap_le_comap_prodMk W (Y a)) hle
  have hmXY : MeasurableSpace.comap (fun ω => (W ω, Y a ω)) inferInstance ≤ mΩ :=
    (hW.prodMk (hY a)).comap_le
  have hf : respInd (arm A a) = fun ω => (fun b : Bool => if b = a then (1 : ℝ) else 0) (A ω) :=
    funext fun ω => respInd_arm_apply A a ω
  unfold MARMean
  rw [hf]
  filter_upwards [condExp_comp_bool hmXY hA (fun b : Bool => if b = a then (1 : ℝ) else 0),
    condExp_comp_bool hW.comap_le hA (fun b : Bool => if b = a then (1 : ℝ) else 0), hmid]
    with ω h1 h2 h3
  rw [h1, h2, h3]

/-- **Each arm is missing at random, full form.** Under ignorability, `{A = a} ⫫ Y(a) | W`: the
arm `a` satisfies `MissingData.MAR` with response indicator `{A = a}` and full outcome
`Y(a)`. -/
theorem Ignorable.mar [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (h : Ignorable μ A hW Y) (a : Bool) : MAR μ hW (arm A a) (Y a) := by
  have hg : Measurable fun p : ℝ × ℝ => if a then p.2 else p.1 := by
    cases a
    · exact measurable_fst
    · exact measurable_snd
  have := h.comp (Measurable.of_discrete (f := fun b : Bool => b == a)) hg
  have hcomp : Y a = (fun p : ℝ × ℝ => if a then p.2 else p.1) ∘ potentialPair Y := by
    funext ω; cases a <;> rfl
  unfold MAR
  rw [hcomp]
  exact this

end PointTreatment

end CausalInference
