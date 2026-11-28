/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.CondIndepGraphoid
public import CausalInference.PointTreatment.Assumptions
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Balancing scores and the propensity score

A function `b(W)` of the covariates is a balancing score (Rosenbaum and Rubin 1983) when the
treatment is conditionally independent of the covariates given it, `A ⫫ W | b(W)` (Mathlib's
`ProbabilityTheory.CondIndepFun`, which needs `StandardBorelSpace Ω`). For a binary treatment
this is the regression statement `E[1{A} | W] = E[1{A} | b(W)]`, so `b` is balancing exactly
when the propensity score `e(W) = E[1{A} | W]` is almost surely a function `f(b(W))` of it. The
propensity score is therefore the coarsest balancing score, and ignorability and positivity given
the covariates pass to every balancing score.

The statements that do not need `StandardBorelSpace Ω` are stated in regression form: the
factorization `E[1{A} | W] = f(b(W))` in place of `IsBalancingScore`, and `IndicatorIgnorable` in
place of `Ignorable`.

## Main definitions

* `IsBalancingScore μ A hW hb`: `A ⫫ W | b(W)`.

## Main results

* `condIndepFun_bool_iff_condExp_respInd_sup_eq`: for a binary `A` and any sub σ-algebra `m`,
  `A ⫫ U | m` if and only if `E[1{A} | σ(U) ∨ m] = E[1{A} | m]`.
* `isBalancingScore_iff_condExp_respInd_eq`: `b` is balancing if and only if
  `E[1{A} | W] = E[1{A} | b(W)]`.
* `isBalancingScore_iff_exists_comp`, `IsPropensityScore.isBalancingScore_iff`: `b` is balancing
  if and only if `e(W) = f(b(W))` almost surely for a measurable `f` (Rosenbaum and Rubin 1983,
  Theorem 2).
* `IsPropensityScore.isBalancingScore`: the propensity score is a balancing score (Rosenbaum and
  Rubin 1983, Theorem 1).
* `condExp_respInd_score_eq`, `IsPropensityScore.isPropensityScore_score`: the propensity score
  on the scale of the score, and the calibration `E[1{A} | e(W)] = e(W)`.
* `isBalancingScore_id`, `isBalancingScore_const_iff`: the covariates themselves are a balancing
  score; a constant is one if and only if `A` and `W` are independent.
* `IsBalancingScore.condIndepFun`, `IsBalancingScore.ignorable`, `IndicatorIgnorable.score`:
  conditional independence and ignorability given `W` pass to a balancing score (Rosenbaum and
  Rubin 1983, Theorem 3).
* `OverlapAE.score`, `StrictOverlapAE.score`, `IsBalancingScore.exists_overlapAE`: positivity
  passes to a balancing score.
* `IsPropensityScore.ignorable_score`: strong ignorability given the propensity score.

## References

* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70 (1983).
* A. P. Dawid, *Conditional independence in statistical theory*, Journal of the Royal Statistical
  Society B 41 (1979).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

/-! ### A binary variable given an arbitrary sub σ-algebra -/

section Binary

variable {Ω β : Type*} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [MeasurableSpace β]
  {μ : Measure Ω} [IsFiniteMeasure μ] {A : Ω → Bool} {U : Ω → β}

/-- **Conditional independence of a binary variable given any sub σ-algebra.** For a binary
`A`, a measurable `U` and a sub σ-algebra `m`, `A ⫫ U | m` if and only if
`E[1{A} | σ(U) ∨ m] = E[1{A} | m]` almost everywhere: a function of `A` is affine in `1{A}`. -/
theorem condIndepFun_bool_iff_condExp_respInd_sup_eq (hm : m ≤ mΩ) (hA : Measurable A)
    (hU : Measurable U) :
    CondIndepFun m hm A U μ ↔
      μ[respInd A | MeasurableSpace.comap U inferInstance ⊔ m] =ᵐ[μ] μ[respInd A | m] := by
  have hsup : MeasurableSpace.comap U inferInstance ⊔ m ≤ mΩ := sup_le hU.comap_le hm
  have hind : respInd A = fun ω => ({true} : Set Bool).indicator (1 : Bool → ℝ) (A ω) := by
    funext ω
    cases h : A ω <;> simp [respInd_apply, h]
  rw [condIndepFun_iff_forall_condExp_indicator_sup_eq hA hU]
  refine ⟨fun H => ?_, fun H S _ => ?_⟩
  · rw [hind]
    exact H {true} (measurableSet_singleton true)
  · filter_upwards [condExp_comp_bool (μ := μ) hsup hA (S.indicator 1),
      condExp_comp_bool (μ := μ) hm hA (S.indicator 1), H] with ω h1 h2 h3
    rw [h1, h2, h3]

end Binary

/-! ### Balancing scores -/

section Balancing

variable {Ω 𝒲 𝒷 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] [MeasurableSpace 𝒷]
  {μ : Measure Ω} {A : Ω → Bool} {W : Ω → 𝒲} {b : 𝒲 → 𝒷} {e : 𝒲 → ℝ} {Y : Bool → Ω → ℝ}

omit mΩ in
/-- The σ-algebra of a measurable function `b(W)` of `W` is contained in that of `W`. -/
theorem comap_score_le (hb : Measurable b) (W : Ω → 𝒲) :
    MeasurableSpace.comap (fun ω => b (W ω)) inferInstance ≤
      MeasurableSpace.comap W inferInstance :=
  (hb.comp (comap_measurable W)).comap_le

omit mΩ in
/-- The pair `(b(W), W)` generates the σ-algebra of `W`. -/
theorem comap_score_prodMk_eq (hb : Measurable b) (W : Ω → 𝒲) :
    MeasurableSpace.comap (fun ω => (b (W ω), W ω)) inferInstance =
      MeasurableSpace.comap W inferInstance := by
  rw [comap_prodMk_eq_sup]
  exact sup_eq_right.2 (comap_score_le hb W)

/-- A **balancing score** (Rosenbaum and Rubin 1983): a measurable `b` such that the treatment is
conditionally independent of the covariates given `b(W)`, `A ⫫ W | b(W)`. -/
def IsBalancingScore [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (A : Ω → Bool)
    (hW : Measurable W) (hb : Measurable b) : Prop :=
  CondIndepFun (MeasurableSpace.comap (fun ω => b (W ω)) inferInstance) (hb.comp hW).comap_le
    A W μ

/-- **The regression form of a balancing score**: `b` is balancing if and only if
`E[1{A} | W] = E[1{A} | b(W)]` almost everywhere. -/
theorem isBalancingScore_iff_condExp_respInd_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A) :
    IsBalancingScore μ A hW hb ↔
      μ[respInd A | MeasurableSpace.comap W inferInstance] =ᵐ[μ]
        μ[respInd A | MeasurableSpace.comap (fun ω => b (W ω)) inferInstance] := by
  have hbW : Measurable fun ω => b (W ω) := hb.comp hW
  refine (condIndepFun_iff_condExp_respInd_eq hbW hW hA).trans ?_
  rw [comap_score_prodMk_eq hb W]

/-- **The propensity score on the scale of a score.** If `E[1{A} | W] = f(b(W))` almost
everywhere for a measurable `f`, then also `E[1{A} | b(W)] = f(b(W))`, by the tower property.
No `StandardBorelSpace` is needed. -/
theorem condExp_respInd_score_eq [IsFiniteMeasure μ] (hW : Measurable W) (hb : Measurable b)
    {f : 𝒷 → ℝ} (hf : Measurable f)
    (h : μ[respInd A | MeasurableSpace.comap W inferInstance] =ᵐ[μ] fun ω => f (b (W ω))) :
    μ[respInd A | MeasurableSpace.comap (fun ω => b (W ω)) inferInstance] =ᵐ[μ]
      fun ω => f (b (W ω)) := by
  have hsm : StronglyMeasurable[MeasurableSpace.comap (fun ω => b (W ω)) inferInstance]
      (fun ω => f (b (W ω))) := (hf.comp (comap_measurable _)).stronglyMeasurable
  have hbW : Measurable fun ω => b (W ω) := hb.comp hW
  refine (condExp_condExp_of_le (comap_score_le hb W) hW.comap_le).symm.trans
    ((condExp_congr_ae h).trans ?_)
  rw [condExp_of_stronglyMeasurable hbW.comap_le hsm (integrable_condExp.congr h)]

/-- **A balancing score is a score of which the propensity score is a function** (Rosenbaum and
Rubin 1983, Theorem 2, in regression form): `b` is balancing if and only if
`E[1{A} | W] = f(b(W))` almost everywhere for some measurable `f`. The forward direction is the
Doob and Dynkin factorization of `E[1{A} | b(W)]` through `b(W)`. -/
theorem isBalancingScore_iff_exists_comp [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A) :
    IsBalancingScore μ A hW hb ↔
      ∃ f : 𝒷 → ℝ, Measurable f ∧
        μ[respInd A | MeasurableSpace.comap W inferInstance] =ᵐ[μ] fun ω => f (b (W ω)) := by
  rw [isBalancingScore_iff_condExp_respInd_eq hW hb hA]
  refine ⟨fun h => ?_, fun ⟨f, hf, h⟩ => h.trans (condExp_respInd_score_eq hW hb hf h).symm⟩
  obtain ⟨f, hf, hfe⟩ := Measurable.exists_eq_measurable_comp
    (stronglyMeasurable_condExp (μ := μ) (f := respInd A)
      (m := MeasurableSpace.comap (fun ω => b (W ω)) inferInstance)).measurable
  exact ⟨f, hf, h.trans (Filter.EventuallyEq.of_eq hfe)⟩

/-- **Rosenbaum and Rubin 1983, Theorem 2.** For a propensity score `e`, a measurable `b` is a
balancing score if and only if `e(W) = f(b(W))` almost surely for some measurable `f`: the
propensity score is the coarsest balancing score. -/
theorem IsPropensityScore.isBalancingScore_iff [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A)
    (he : IsPropensityScore μ A W e) :
    IsBalancingScore μ A hW hb ↔
      ∃ f : 𝒷 → ℝ, Measurable f ∧ ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω)) := by
  rw [isBalancingScore_iff_exists_comp hW hb hA]
  exact exists_congr fun f => and_congr_right fun _ =>
    ⟨fun h => he.2.symm.trans h, fun h => he.2.trans h⟩

/-- **The propensity score is a balancing score** (Rosenbaum and Rubin 1983, Theorem 1):
`A ⫫ W | e(W)`. -/
theorem IsPropensityScore.isBalancingScore [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (he : IsPropensityScore μ A W e) :
    IsBalancingScore μ A hW he.1 :=
  (isBalancingScore_iff_exists_comp hW he.1 hA).2 ⟨id, measurable_id, he.2⟩

/-- **The propensity score of a score.** If `e(W) = f(b(W))` almost surely, then `f` is the
propensity score of `A` given `b(W)`. -/
theorem IsPropensityScore.isPropensityScore_comp [IsFiniteMeasure μ] (hW : Measurable W)
    (hb : Measurable b) (he : IsPropensityScore μ A W e) {f : 𝒷 → ℝ} (hf : Measurable f)
    (hfe : ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω))) :
    IsPropensityScore μ A (fun ω => b (W ω)) f :=
  ⟨hf, condExp_respInd_score_eq hW hb hf (he.2.trans hfe)⟩

/-- **Calibration of the propensity score**: `E[1{A} | e(W)] = e(W)`, that is, the identity is
the propensity score of `A` given `e(W)`. -/
theorem IsPropensityScore.isPropensityScore_score [IsFiniteMeasure μ] (hW : Measurable W)
    (he : IsPropensityScore μ A W e) : IsPropensityScore μ A (fun ω => e (W ω)) id :=
  he.isPropensityScore_comp hW he.1 measurable_id (Filter.Eventually.of_forall fun _ => rfl)

/-- The covariates themselves are a balancing score. (Mathlib's `condIndepFun_self_right` is the
same statement for an arbitrary variable.) -/
theorem isBalancingScore_id [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) : IsBalancingScore μ A hW (measurable_id (α := 𝒲)) :=
  (isBalancingScore_iff_condExp_respInd_eq hW measurable_id hA).2 Filter.EventuallyEq.rfl

/-- **A constant is a balancing score if and only if the treatment is independent of the
covariates**, for a probability measure. -/
theorem isBalancingScore_const_iff [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (c : 𝒷) :
    IsBalancingScore μ A hW (measurable_const : Measurable fun _ : 𝒲 => c) ↔ IndepFun A W μ :=
  condIndepFun_comap_const_iff_indepFun hA hW c

/-! ### Ignorability and positivity pass to a balancing score -/

/-- **Conditional independence given the covariates passes to a balancing score** (the
conditional independence core of Rosenbaum and Rubin 1983, Theorem 3): if `b` is balancing and
`A ⫫ U | W`, then `A ⫫ U | b(W)`. By contraction `A ⫫ W | b(W)` and `A ⫫ U | (W, b(W))` give
`A ⫫ (W, U) | b(W)`, and decomposition drops `W`. -/
theorem IsBalancingScore.condIndepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ] {γ : Type*}
    [MeasurableSpace γ] {U : Ω → γ} (hW : Measurable W) (hb : Measurable b) (hA : Measurable A)
    (hU : Measurable U) (hbal : IsBalancingScore μ A hW hb)
    (h : CondIndepFun (MeasurableSpace.comap W inferInstance) hW.comap_le A U μ) :
    CondIndepFun (MeasurableSpace.comap (fun ω => b (W ω)) inferInstance) (hb.comp hW).comap_le
      A U μ := by
  have e : MeasurableSpace.comap W inferInstance =
      MeasurableSpace.comap W inferInstance ⊔
        MeasurableSpace.comap (fun ω => b (W ω)) inferInstance :=
    (sup_eq_left.2 (comap_score_le hb W)).symm
  exact (condIndepFun_contraction hA hW hU hbal
    ((condIndepFun_congr_sigma e _ _).1 h)).comp measurable_id measurable_snd

/-- **Ignorability given the covariates passes to a balancing score** (Rosenbaum and Rubin 1983,
Theorem 3): `A ⫫ (Y(0), Y(1)) | W` gives `A ⫫ (Y(0), Y(1)) | b(W)`. -/
theorem IsBalancingScore.ignorable [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hbal : IsBalancingScore μ A hW hb) (h : Ignorable μ A hW Y) :
    Ignorable μ A (W := fun ω => b (W ω)) (hb.comp hW) Y :=
  hbal.condIndepFun hW hb hA (measurable_potentialPair hY) h

/-- **The indicator form of ignorability passes to a score of which the propensity score is a
function**, without `StandardBorelSpace Ω`: if `E[1{A} | W, Y(0), Y(1)] = E[1{A} | W]` and
`E[1{A} | W] = f(b(W))`, then `E[1{A} | b(W), Y(0), Y(1)] = E[1{A} | b(W)]`. -/
theorem IndicatorIgnorable.score [IsFiniteMeasure μ] (hW : Measurable W) (hb : Measurable b)
    (hY : ∀ a, Measurable (Y a)) {f : 𝒷 → ℝ} (hf : Measurable f)
    (hfb : μ[respInd A | MeasurableSpace.comap W inferInstance] =ᵐ[μ] fun ω => f (b (W ω)))
    (h : IndicatorIgnorable μ A W Y) : IndicatorIgnorable μ A (fun ω => b (W ω)) Y := by
  unfold IndicatorIgnorable at h ⊢
  have hP := measurable_potentialPair hY
  have hm𝒢 : Measurable[MeasurableSpace.comap (fun ω => (W ω, potentialPair Y ω)) inferInstance]
      (fun ω => (b (W ω), potentialPair Y ω)) :=
    ((hb.comp measurable_fst).prodMk measurable_snd).comp (comap_measurable _)
  have h𝒢ℋ := hm𝒢.comap_le
  have hℋ : MeasurableSpace.comap (fun ω => (W ω, potentialPair Y ω)) inferInstance ≤ mΩ :=
    (hW.prodMk hP).comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap (fun ω => (b (W ω), potentialPair Y ω))
      inferInstance] (fun ω => f (b (W ω))) :=
    (hf.comp (measurable_fst.comp (comap_measurable _))).stronglyMeasurable
  refine (condExp_condExp_of_le h𝒢ℋ hℋ).symm.trans ((condExp_congr_ae (h.trans hfb)).trans ?_)
  rw [condExp_of_stronglyMeasurable (h𝒢ℋ.trans hℋ) hsm (integrable_condExp.congr hfb)]
  exact (condExp_respInd_score_eq hW hb hf hfb).symm

/-- **Positivity passes to the scale of a score**: if `0 < e(W) < 1` almost surely and
`e(W) = f(b(W))` almost surely, then `0 < f < 1` almost everywhere under the law of `b(W)`. -/
theorem OverlapAE.score (hW : Measurable W) (hb : Measurable b) (he : Measurable e)
    {f : 𝒷 → ℝ} (hf : Measurable f) (hfe : ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω)))
    (h : OverlapAE e (μ.map W)) : OverlapAE f (μ.map fun ω => b (W ω)) := by
  have hbW : Measurable fun ω => b (W ω) := hb.comp hW
  refine (overlapAE_map_iff hbW hf).2 ?_
  filter_upwards [(overlapAE_map_iff hW he).1 h, hfe] with ω h1 h2
  rwa [← h2]

/-- **Strict positivity passes to the scale of a score.** -/
theorem StrictOverlapAE.score (hW : Measurable W) (hb : Measurable b) {f : 𝒷 → ℝ}
    (hf : Measurable f) (hfe : ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω))) {ε : ℝ}
    (h : StrictOverlapAE e (μ.map W) ε) : StrictOverlapAE f (μ.map fun ω => b (W ω)) ε := by
  have hs : MeasurableSet {s : 𝒷 | ε ≤ f s ∧ f s ≤ 1 - ε} :=
    (measurableSet_le measurable_const hf).inter (measurableSet_le hf measurable_const)
  have hbW : Measurable fun ω => b (W ω) := hb.comp hW
  refine ⟨h.1, (ae_map_iff hbW.aemeasurable hs).2 ?_⟩
  filter_upwards [h.ae_comp hW.aemeasurable, hfe] with ω h1 h2
  rwa [← h2]

/-- **Strong ignorability passes to a balancing score** (Rosenbaum and Rubin 1983, Theorem 3,
positivity part): if `b` is balancing and `0 < e(W) < 1` almost surely, then the propensity
score given `b(W)` is a measurable `f` with `e(W) = f(b(W))` almost surely, and
`0 < f < 1` almost everywhere under the law of `b(W)`. -/
theorem IsBalancingScore.exists_overlapAE [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A)
    (he : IsPropensityScore μ A W e) (hbal : IsBalancingScore μ A hW hb)
    (hov : OverlapAE e (μ.map W)) :
    ∃ f : 𝒷 → ℝ, IsPropensityScore μ A (fun ω => b (W ω)) f ∧
      (∀ᵐ ω ∂μ, e (W ω) = f (b (W ω))) ∧ OverlapAE f (μ.map fun ω => b (W ω)) := by
  obtain ⟨f, hf, hfe⟩ := (he.isBalancingScore_iff hW hb hA).1 hbal
  exact ⟨f, he.isPropensityScore_comp hW hb hf hfe, hfe, hov.score hW hb he.1 hf hfe⟩

/-- **Strong ignorability given the propensity score** (Rosenbaum and Rubin 1983, Theorem 3 for
the propensity score): if `A ⫫ (Y(0), Y(1)) | W` and `0 < e(W) < 1` almost surely, then
`A ⫫ (Y(0), Y(1)) | e(W)` and `0 < e(W) < 1` almost everywhere under the law of `e(W)`. -/
theorem IsPropensityScore.ignorable_score [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (he : IsPropensityScore μ A W e) (h : Ignorable μ A hW Y) (hov : OverlapAE e (μ.map W)) :
    Ignorable μ A (W := fun ω => e (W ω)) (he.1.comp hW) Y ∧
      OverlapAE id (μ.map fun ω => e (W ω)) :=
  ⟨(he.isBalancingScore hW hA).ignorable hW he.1 hA hY h,
    hov.score hW he.1 he.1 measurable_id (Filter.Eventually.of_forall fun _ => rfl)⟩

end Balancing

end PointTreatment

end CausalInference
