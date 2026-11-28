/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.InfluenceFunction
public import CausalInference.PointTreatment.Randomized
public import CausalInference.PointTreatment.OverlapVarianceExample
public import CausalInference.Efficiency.EfficiencyBound

/-!
# A randomized population with a two point covariate and the efficient variance

This file builds a population in which every hypothesis of the variance formulas of
`CausalInference.Efficiency.InfluenceFunction` holds, and computes the efficient variances.

**The population.** The sample space is `Fin 3 → Bool` with the product law of three independent
coins: the covariate `W = ω 0` is fair, the treatment `A = ω 1` has `P(A = 1) = 1/4`, and the
noise sign `U = ω 2` is fair. The potential outcomes are
`Y(a) = 2 · 1{a = 1, W = 1} + σ(U)` with `σ(true) = 1` and `σ(false) = -1`.
Then:

* the propensity score is the constant `1/4` (randomization);
* the treatment is independent of `(W, Y(0), Y(1))`, so ignorability holds;
* the outcome regression is `m(a, w) = 2 · 1{a = 1, w = 1}`, because `U` is independent of
  `(W, A)` and `E[σ(U)] = 0`;
* the conditional variance of the residual is the constant `1`;
* `E[Y(1) | W] = 2 · 1{W = 1}` and `E[Y(1) - Y(0) | W] = 2 · 1{W = 1}`, each with variance `1`.

The efficient variance of the arm mean `E[Y(1)]` is therefore `1 / (1/4) + 1 = 5`, and that of
the average effect is `1 / (1/4) + 1 / (3/4) + 1 = 19/3`.

## Main definitions

* `twoPointLaw`, `twoPointOutcome`, `twoPointRegression`: the population.

## Main results

* `twoPoint_isPropensityScore`, `twoPoint_ignorable`, `twoPoint_isOutcomeRegression`,
  `twoPoint_isOutcomeRegression_sq`: the hypotheses hold.
* `twoPoint_integral_armEIF_sq`: the efficient variance of `E[Y(1)]` is `5`.
* `twoPoint_integral_ateEIF_sq`: the efficient variance of the average effect is `19/3`.
* `twoPoint_isLUB_submodelBounds`: the efficiency bound `5` of `E[Y(1)]` is the supremum of the
  Cramér-Rao bounds of the score submodels of the population.

## References

* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66 (1998).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory MissingData PointTreatment Filter

/-- The law of the `i`th coin: `P(true) = 1/4` for the treatment coordinate `1`, and `1/2` for
the covariate `0` and the noise `2`. -/
noncomputable def twoPointCoin (i : Fin 3) : Measure Bool :=
  boolLaw (if i = 1 then 1 / 4 else 1 / 2)

instance (i : Fin 3) : IsProbabilityMeasure (twoPointCoin i) := by
  unfold twoPointCoin
  split_ifs <;> exact isProbabilityMeasure_boolLaw (by norm_num) (by norm_num)

/-- The law of the population: three independent coins. -/
noncomputable def twoPointLaw : Measure (Fin 3 → Bool) := Measure.pi twoPointCoin

instance : IsProbabilityMeasure twoPointLaw := by
  unfold twoPointLaw; infer_instance

/-- The sign `σ(true) = 1`, `σ(false) = -1`. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- The outcome regression of the population: `m(a, w) = 2 · 1{a = 1, w = 1}`. -/
def twoPointRegression (a w : Bool) : ℝ := if a && w then 2 else 0

/-- The potential outcomes of the population: `Y(a) = m(a, W) + σ(U)`. -/
def twoPointOutcome (a : Bool) (ω : Fin 3 → Bool) : ℝ :=
  twoPointRegression a (ω 0) + boolSign (ω 2)

theorem iIndepFun_twoPoint : iIndepFun (fun i (ω : Fin 3 → Bool) => ω i) twoPointLaw :=
  iIndepFun_pi (μ := twoPointCoin) (X := fun _ => id) fun _ => aemeasurable_id

theorem measurable_coord (i : Fin 3) : Measurable fun ω : Fin 3 → Bool => ω i :=
  measurable_pi_apply i

theorem measurable_twoPointOutcome (a : Bool) : Measurable (twoPointOutcome a) :=
  Measurable.of_discrete

/-- Integrals of a function of one coordinate are integrals under that coin. -/
theorem integral_twoPoint_coord (i : Fin 3) (g : Bool → ℝ) :
    ∫ ω, g (ω i) ∂twoPointLaw = ∫ b, g b ∂(twoPointCoin i) := by
  rw [← (measurePreserving_eval twoPointCoin i).map_eq,
    integral_map (measurable_coord i).aemeasurable Integrable.of_finite.aestronglyMeasurable]
  rfl

theorem integral_twoPoint_coord_eq (i : Fin 3) (g : Bool → ℝ) :
    ∫ ω, g (ω i) ∂twoPointLaw = (if i = 1 then 1 / 4 else 1 / 2) * g true +
      (1 - (if i = 1 then 1 / 4 else 1 / 2)) * g false := by
  rw [integral_twoPoint_coord, twoPointCoin]
  split_ifs <;> exact integral_boolLaw (by norm_num) (by norm_num) g

theorem integral_boolSign : ∫ ω, boolSign (ω 2) ∂twoPointLaw = 0 := by
  rw [integral_twoPoint_coord_eq]; simp [boolSign]; norm_num

/-- The treatment is independent of the covariate and the noise. -/
theorem indepFun_twoPoint_treatment :
    IndepFun (fun ω : Fin 3 → Bool => ω 1) (fun ω => (ω 0, ω 2)) twoPointLaw :=
  (iIndepFun_twoPoint.indepFun_prodMk measurable_coord 0 2 1 (by decide) (by decide)).symm

/-- **The propensity score of the population is the constant `1/4`.** -/
theorem twoPoint_isPropensityScore :
    IsPropensityScore twoPointLaw (fun ω => ω 1) (fun ω => ω 0) (fun _ => 1 / 4) := by
  have h := isPropensityScore_const_of_indepFun (measurable_coord 0) (measurable_coord 1)
    (indepFun_twoPoint_treatment.comp measurable_id measurable_fst)
  have hp : twoPointLaw.real ((fun ω : Fin 3 → Bool => ω 1) ⁻¹' {true}) = 1 / 4 := by
    have := integral_respInd (μ := twoPointLaw) (measurable_coord 1)
    rw [← this]
    have h1 := integral_twoPoint_coord_eq 1 (fun b => if b = true then (1 : ℝ) else 0)
    simp only [respInd_apply] at h1 ⊢
    rw [h1]; norm_num
  rwa [hp] at h

/-- **Ignorability holds in the population**: the treatment is independent of
`(W, Y(0), Y(1))`. -/
theorem twoPoint_ignorable :
    Ignorable twoPointLaw (fun ω => ω 1) (measurable_coord 0) twoPointOutcome := by
  refine ignorable_of_indepFun (measurable_coord 0) (measurable_coord 1)
    measurable_twoPointOutcome ?_
  have hg : Measurable fun p : Bool × Bool =>
      (p.1, (twoPointRegression false p.1 + boolSign p.2,
        twoPointRegression true p.1 + boolSign p.2)) := Measurable.of_discrete
  exact indepFun_twoPoint_treatment.comp measurable_id hg

theorem twoPoint_obsOutcome (ω : Fin 3 → Bool) :
    obsOutcome (fun ω => ω 1) twoPointOutcome ω =
      twoPointRegression (ω 1) (ω 0) + boolSign (ω 2) := rfl

/-- **The outcome regression of the population** is `m(a, w) = 2 · 1{a = 1, w = 1}`: the noise
`U` is independent of `(W, A)` and has mean zero. -/
theorem twoPoint_isOutcomeRegression :
    IsOutcomeRegression twoPointLaw (fun ω => ω 1) (fun ω => ω 0)
      (obsOutcome (fun ω => ω 1) twoPointOutcome) twoPointRegression := by
  refine ⟨fun _ => Measurable.of_discrete, ?_⟩
  set mWA := MeasurableSpace.comap (fun ω : Fin 3 → Bool => (ω 0, ω 1))
    (inferInstance : MeasurableSpace (Bool × Bool))
  have hle : mWA ≤ MeasurableSpace.pi := ((measurable_coord 0).prodMk (measurable_coord 1)).comap_le
  have hind : IndepFun (fun ω : Fin 3 → Bool => ω 2) (fun ω => (ω 0, ω 1)) twoPointLaw :=
    (iIndepFun_twoPoint.indepFun_prodMk measurable_coord 0 1 2 (by decide) (by decide)).symm
  have hsU : StronglyMeasurable[MeasurableSpace.comap (fun ω : Fin 3 → Bool => ω 2)
      (inferInstance : MeasurableSpace Bool)] fun ω => boolSign (ω 2) :=
    ((Measurable.of_discrete (f := boolSign)).comp
      (comap_measurable fun ω : Fin 3 → Bool => ω 2)).stronglyMeasurable
  have hU := condExp_indep_eq (measurable_coord 2).comap_le hle hsU hind
  have hm : StronglyMeasurable[mWA] fun ω : Fin 3 → Bool => twoPointRegression (ω 1) (ω 0) := by
    have : (fun ω : Fin 3 → Bool => twoPointRegression (ω 1) (ω 0)) =
        (fun p : Bool × Bool => twoPointRegression p.2 p.1) ∘ fun ω => (ω 0, ω 1) := rfl
    rw [this]
    exact (Measurable.of_discrete.comp (comap_measurable _)).stronglyMeasurable
  have hsplit : obsOutcome (fun ω => ω 1) twoPointOutcome =
      (fun ω : Fin 3 → Bool => twoPointRegression (ω 1) (ω 0)) + fun ω => boolSign (ω 2) := rfl
  rw [hsplit]
  refine (condExp_add Integrable.of_finite Integrable.of_finite mWA).trans ?_
  rw [condExp_of_stronglyMeasurable hle hm Integrable.of_finite]
  filter_upwards [hU] with ω h
  simp only [Pi.add_apply, h, integral_boolSign, add_zero]

/-- **The residual of the population has conditional variance `1`.** -/
theorem twoPoint_isOutcomeRegression_sq :
    IsOutcomeRegression twoPointLaw (fun ω => ω 1) (fun ω => ω 0)
      (fun ω => (obsOutcome (fun ω => ω 1) twoPointOutcome ω -
        twoPointRegression (ω 1) (ω 0)) ^ 2) (fun _ _ => 1) := by
  refine ⟨fun _ => measurable_const, ?_⟩
  have h1 : (fun ω : Fin 3 → Bool => (obsOutcome (fun ω => ω 1) twoPointOutcome ω -
      twoPointRegression (ω 1) (ω 0)) ^ 2) = fun _ => (1 : ℝ) := by
    funext ω; rw [twoPoint_obsOutcome]; cases ω 2 <;> simp [boolSign]
  rw [h1, condExp_const ((measurable_coord 0).prodMk (measurable_coord 1)).comap_le]

theorem twoPoint_strictOverlapAE :
    StrictOverlapAE (fun _ : Bool => (1 : ℝ) / 4) (twoPointLaw.map fun ω => ω 0) (1 / 4) := by
  have h := (strictOverlap_const (𝒲 := Bool) (p := 1 / 4) (by norm_num)
    (by norm_num)).strictOverlapAE (twoPointLaw.map fun ω => ω 0)
  have hmin : min ((1 : ℝ) / 4) (1 - 1 / 4) = 1 / 4 := by norm_num
  rwa [hmin] at h

theorem variance_twoPoint_double :
    Var[fun ω : Fin 3 → Bool => twoPointRegression true (ω 0); twoPointLaw] = 1 := by
  rw [variance_eq_integral Measurable.of_discrete.aemeasurable]
  have hmean : ∫ ω, twoPointRegression true (ω 0) ∂twoPointLaw = 1 := by
    rw [integral_twoPoint_coord_eq 0 (twoPointRegression true)]; norm_num [twoPointRegression]
  rw [hmean, integral_twoPoint_coord_eq 0 (fun b => (twoPointRegression true b - 1) ^ 2)]
  norm_num [twoPointRegression]

/-- **The efficient variance of the treated arm mean in the population is `5`**: the formula
`E[v(1, W) / e(W)] + Var(E[Y(1) | W])` evaluates to `1 / (1/4) + 1`. -/
theorem twoPoint_integral_armEIF_sq :
    ∫ ω, armEIF (fun _ => 1 / 4) twoPointRegression true (armMean twoPointLaw twoPointOutcome true)
      (obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0) ω) ^ 2 ∂twoPointLaw = 5 := by
  have hpos := le_armProb_of_ae (twoPoint_strictOverlapAE.ae_comp
    (measurable_coord 0).aemeasurable)
  rw [twoPoint_ignorable.integral_armEIF_sq (measurable_coord 0) (measurable_coord 1)
    measurable_twoPointOutcome (fun _ => MemLp.of_discrete) twoPoint_isPropensityScore
    twoPoint_isOutcomeRegression twoPoint_isOutcomeRegression_sq true (by norm_num)
    (hpos true)]
  have hc : twoPointLaw[twoPointOutcome true | MeasurableSpace.comap (fun ω => ω 0)
      inferInstance] =ᵐ[twoPointLaw] fun ω => twoPointRegression true (ω 0) := by
    have hmi := twoPoint_ignorable.meanIgnorable (measurable_coord 0) (measurable_coord 1)
      measurable_twoPointOutcome true Integrable.of_finite
    have hid := twoPoint_isOutcomeRegression.ae_eq_condExp (measurable_coord 0)
      (measurable_coord 1) (fun _ => Integrable.of_finite) twoPoint_isPropensityScore true hmi
      ((hpos true).mono fun _ h => lt_of_lt_of_le (by norm_num) h)
    exact hid.symm
  rw [variance_congr hc, variance_twoPoint_double]
  simp only [armProb_true]
  norm_num

/-- **The efficient variance of the average effect in the population is `19/3`**: the formula
`E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])` evaluates to
`1 / (1/4) + 1 / (3/4) + 1`. -/
theorem twoPoint_integral_ateEIF_sq :
    ∫ ω, ateEIF (fun _ => 1 / 4) twoPointRegression (ate twoPointLaw twoPointOutcome)
      (obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0) ω) ^ 2 ∂twoPointLaw = 19 / 3 := by
  rw [twoPoint_ignorable.integral_ateEIF_sq (measurable_coord 0) (measurable_coord 1)
    measurable_twoPointOutcome (fun _ => MemLp.of_discrete) twoPoint_isPropensityScore
    twoPoint_isOutcomeRegression twoPoint_isOutcomeRegression_sq twoPoint_strictOverlapAE]
  have hc : cate twoPointLaw (fun ω => ω 0) twoPointOutcome =ᵐ[twoPointLaw]
      fun ω => twoPointRegression true (ω 0) := by
    have heq : indivEffect twoPointOutcome = fun ω => twoPointRegression true (ω 0) := by
      funext ω
      simp [indivEffect, twoPointOutcome, twoPointRegression]
    have hm : StronglyMeasurable[MeasurableSpace.comap (fun ω : Fin 3 → Bool => ω 0)
        (inferInstance : MeasurableSpace Bool)] fun ω => twoPointRegression true (ω 0) :=
      ((Measurable.of_discrete (f := twoPointRegression true)).comp
        (comap_measurable fun ω : Fin 3 → Bool => ω 0)).stronglyMeasurable
    rw [cate, heq, condExp_of_stronglyMeasurable (measurable_coord 0).comap_le hm
      Integrable.of_finite]
  rw [variance_congr hc, variance_twoPoint_double]
  norm_num

/-- **The efficiency bound of `E[Y(1)]` in the population is `5`**: it is the least upper bound
of the Cramér-Rao bounds `d² / E[s(O)²]` of the score submodels through the population. -/
theorem twoPoint_isLUB_submodelBounds :
    IsLUB {r | ∃ s, IsBoundedScore twoPointLaw
        (obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0)) s ∧
      0 < ∫ ω, s (obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0) ω) ^ 2 ∂twoPointLaw ∧
      ∃ d, HasDerivAt (fun t ↦ regressionFunctional (scoreTilt twoPointLaw
          (fun ω ↦ s (obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0) ω)) t)
          (arm (fun ω => ω 1) true) (fun ω => ω 0) (obsOutcome (fun ω => ω 1) twoPointOutcome))
        d 0 ∧
      r = d ^ 2 / ∫ ω, s (obsData (fun ω => ω 1) twoPointOutcome (fun ω => ω 0) ω) ^ 2
        ∂twoPointLaw} 5 := by
  have hpos := le_armProb_of_ae (twoPoint_strictOverlapAE.ae_comp
    (measurable_coord 0).aemeasurable)
  have h := isLUB_submodelBounds_arm (measurable_coord 0) (measurable_coord 1)
    measurable_twoPointOutcome (fun _ => MemLp.of_discrete) twoPoint_isPropensityScore
    twoPoint_isOutcomeRegression true
    (twoPoint_ignorable.meanIgnorable (measurable_coord 0) (measurable_coord 1)
      measurable_twoPointOutcome true Integrable.of_finite) (by norm_num) (hpos true)
    (by rw [twoPoint_integral_armEIF_sq]; norm_num)
  rwa [twoPoint_integral_armEIF_sq] at h

end Efficiency
end CausalInference
