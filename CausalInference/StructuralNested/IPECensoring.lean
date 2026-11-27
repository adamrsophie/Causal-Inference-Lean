/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.IPEExtensions
public import CausalInference.Survival.RecensoringCounterexamples

/-!
# Iterative parameter estimation with censoring, slope one, and an estimated Weibull shape

This file continues `IPE` and `IPEExtensions` in three directions.

**Censoring and recensoring.** TSD 16 describes the IPE algorithm in Section 3.2.3 and Appendix A
(transform the switchers' times with `exp ψ`, refit a parametric failure time model, iterate)
without any censoring step. Its Section 3.3.2 states that recensoring is required for the RPSFTM and
IPE methods to avoid bias, and Appendix A gives the recensoring time `min (C, exp ψ C)` for patients
in groups at risk of switching. TSD 24 (Section 4.2.1.1) adds that Branson and Whitehead (2002)
described an abridged version of recensoring, later shown to be suboptimal, and that Zhang and Chen
(2016) proposed a modified IPE applying recensoring correctly; neither document prints a formula for
the censored update. The update defined here is therefore our own formalization. At the current
value `ψ` the control arm is replaced by its recensored record
`(min (U(ψ), D*(ψ)), 1{U(ψ) ≤ D*(ψ)})` with `D*(ψ) = min (C, exp ψ C)` (`CensoredTrial.recensored`),
and the experimental arm (treated throughout) by its observed record censored again at
`D*(ψ) / exp ψ`, the same recensoring time on its own time scale (`expRecord`); for `ψ ≤ 0` this is
the observed record (`expRecord_of_nonpos`), so only the arm at risk of switching is recensored. For
any functional `Φ` of the law of a censored record (a survival probability at a fixed time, a
restricted mean within the recensored follow-up, the target of a parametric fit) the estimating
function `censoredEstFn Φ` compares `Φ` on the two records, the experimental one rescaled by
`exp ψ`. At the true parameter the two records have the same law (`armLaw_records_eq`, from
`armLaw_recensored_eq`), so the truth is a root for every `Φ` (`censoredEstFn_trueParam`). For the
exponential fit to censored data (follow-up per event) the update `ipeCensMap` has the truth as a
fixed point (`isFixedPt_ipeCensMap_trueParam`). Without recensoring (control times transformed,
original event indicator kept) it does not: in the staggered entry trial the update gives
`log (93/272)` at the truth `log (1/2)` (`StaggeredCensoring.naive_not_fixed`).

**Slope one almost everywhere.** If the control patients with positive time off the experimental
treatment have probability zero, `logMap`, `ipeMap` and `weibullMap k` are translations
`ψ ↦ ψ + f 0`, so their fixed point set is empty or all of `ℝ` (`fixedPt_empty_or_univ_of_shift`).
With the truth a fixed point, the fixed point is unique if and only if those patients have positive
probability (`unique_fixedPt_ipeMap_iff`, `unique_fixedPt_logMap_iff`,
`unique_fixedPt_weibullMap_iff`, all instances of `unique_fixedPt_iff_of_shift`).

**An estimated Weibull shape.** For any rule `κ` choosing a positive shape at each value, the
truth is a fixed point of `ψ ↦ weibullMap (κ ψ) ψ`, and the only one under positive time off
treatment, since a fixed point `q` of that map is a fixed point of `weibullMap (κ q)`, whose only
fixed point is the truth (`isFixedPt_weibullMap_rule`). The population profile equation for the
common shape of the two-arm Weibull fit with arm covariate is `shapeScore` (derivation in its
docstring); it is strictly decreasing in the shape (`shapeScore_strictAntiOn`), by the
inequality `x^k (x^δ - exp (δ L)) (log x - L) ≥ 0` integrated at `L = E[X^k log X] / E[X^k]`,
so the fitted shape is unique when it exists (`shapeScore_root_unique`), and the truth is the
unique fixed point with the fitted shape (`isFixedPt_weibullMap_fittedShape`).

## Main results

* `CensoredTrial.censoredEstFn_trueParam`, `CensoredTrial.isFixedPt_ipeCensMap_trueParam`,
  `IPECounterexample.StaggeredCensoring.naive_not_fixed`.
* `SwitchingTrial.unique_fixedPt_ipeMap_iff`, `SwitchingTrial.unique_fixedPt_logMap_iff`,
  `SwitchingTrial.unique_fixedPt_weibullMap_iff`.
* `SwitchingTrial.shapeScore_strictAntiOn`, `SwitchingTrial.isFixedPt_weibullMap_rule`,
  `SwitchingTrial.isFixedPt_weibullMap_fittedShape`.

## Sources

* NICE DSU Technical Support Document 16, Sections 3.2.3 and 3.3.2 and Appendix A.
* NICE DSU Technical Support Document 24, Section 4.2.1.1.
* M. Branson, J. Whitehead, Statistics in Medicine 21 (2002), 2449 to 2463.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology

namespace CausalInference

namespace StructuralNested

namespace CensoredTrial

variable {Ω : Type*} {M : CensoredTrial Ω}

/-! ### The records compared by the censored update -/

variable (M) in
/-- **The experimental arm is on treatment throughout**: its treatment path is all of time. -/
def ExpFullyTreated : Prop := ∀ ω, M.R ω = true → M.A ω = univ

variable (M) in
/-- **The experimental record at `ψ`**, computed from the observed data: the observed follow-up
and event indicator of the experimental arm, censored again at `D*(ψ) / exp ψ`, the recensoring
time brought back to the observed time scale of a fully treated patient:
`(min (x, D*(ψ) / exp ψ), δ ∧ x ≤ D*(ψ) / exp ψ)`. -/
noncomputable def expRecord (ψ : ℝ) (ω : Ω) : ℝ × Bool :=
  (min (M.obsTime ω) (M.recensTime ψ ω / Real.exp ψ),
    M.event ω && decide (M.obsTime ω ≤ M.recensTime ψ ω / Real.exp ψ))

/-- The rescaled recensoring time `D*(ψ) / exp ψ` is at most the administrative censoring time. -/
theorem recensTime_div_le (ψ : ℝ) (ω : Ω) : M.recensTime ψ ω / Real.exp ψ ≤ M.C ω := by
  rw [div_le_iff₀ (Real.exp_pos ψ), mul_comm]
  exact min_le_right _ _

/-- The experimental record is the survival time censored at `D*(ψ) / exp ψ`. -/
theorem expRecord_eq (ψ : ℝ) (ω : Ω) :
    M.expRecord ψ ω = censorAt (M.T ω) (M.recensTime ψ ω / Real.exp ψ) := by
  have hd := recensTime_div_le (M := M) ψ ω
  simp only [expRecord, censorAt, obsTime, event]
  rcases le_or_gt (M.T ω) (M.recensTime ψ ω / Real.exp ψ) with h | h
  · have hTC : M.T ω ≤ M.C ω := h.trans hd
    simp [h, hTC]
  · have hm : M.recensTime ψ ω / Real.exp ψ ≤ min (M.T ω) (M.C ω) := le_min h.le hd
    rw [min_eq_right hm, min_eq_right h.le]
    simp only [not_le.2 h, decide_false, Prod.mk.injEq, true_and]
    rcases le_or_gt (M.T ω) (M.C ω) with h' | h'
    · simp [h', h]
    · simp [not_le.2 h']

/-- **For a beneficial or null effect the experimental record is the observed record.** For
`ψ ≤ 0` and `C ≥ 0`, `D*(ψ) / exp ψ = C`, so `expRecord ψ` is the observed follow-up and event
indicator: only the arm at risk of switching is recensored, as TSD 16 (Appendix A) describes. -/
theorem expRecord_of_nonpos (hwf : M.WellFormed) {ψ : ℝ} (hψ : ψ ≤ 0) (ω : Ω) :
    M.expRecord ψ ω = (M.obsTime ω, M.event ω) := by
  have e : M.recensTime ψ ω / Real.exp ψ = M.C ω := by
    rw [recensTime, recensoringTime_of_nonpos hψ (hwf.C_nonneg ω),
      mul_div_cancel_left₀ _ (Real.exp_pos ψ).ne']
  have h : M.obsTime ω ≤ M.C ω := min_le_right _ _
  simp only [expRecord, e, min_eq_left h, h, decide_true, Bool.and_true]

/-- **At the true parameter the rescaled experimental record is the recensored record.** Under
the path model at `ψ` and a fully treated experimental arm, for an experimental patient
`(exp ψ x', δ') = (min (U, D*), 1{U ≤ D*})`, where `(x', δ')` is the experimental record. -/
theorem scale_expRecord_eq (hwf : M.WellFormed) {ψ : ℝ} (h : M.PathModel ψ)
    (hfull : M.ExpFullyTreated) {ω : Ω} (hω : M.R ω = true) :
    (Real.exp ψ * (M.expRecord ψ ω).1, (M.expRecord ψ ω).2) = M.recensored ψ ω := by
  have he := Real.exp_pos ψ
  rw [expRecord_eq, recensored_eq hwf h, h ω, hfull ω hω, untreatedTime_univ]
  simp only [censorAt]
  rw [mul_min_of_nonneg _ _ he.le, mul_div_cancel₀ _ he.ne']
  simp only [le_div_iff₀ he, mul_comm (M.T ω)]

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The records agree in law at the true parameter.** Under the path model at `ψ₀`, a fully
treated experimental arm, randomization with respect to `(U, C)`, measurable `R`, `U`, `C`, and
both arms of positive probability, the law of the recensored control record equals the law of
the rescaled experimental record `(exp ψ₀ x', δ')`. -/
theorem armLaw_records_eq [IsFiniteMeasure μ] (hwf : M.WellFormed) {ψ₀ : ℝ}
    (h : M.PathModel ψ₀) (hfull : M.ExpFullyTreated) (hR : Measurable M.R)
    (hU : Measurable M.U) (hC : Measurable M.C) (hrand : M.RandomizedCensored μ)
    (h1 : μ (M.toSwitchingTrial.arm true) ≠ 0) (h0 : μ (M.toSwitchingTrial.arm false) ≠ 0) :
    (μ[|M.toSwitchingTrial.arm false]).map (M.recensored ψ₀) =
      (μ[|M.toSwitchingTrial.arm true]).map
        (fun ω ↦ (Real.exp ψ₀ * (M.expRecord ψ₀ ω).1, (M.expRecord ψ₀ ω).2)) := by
  rw [← armLaw_recensored_eq hwf h hR hU hC hrand h1 h0]
  refine (Measure.map_congr ?_).symm
  filter_upwards [ae_cond_mem (SwitchingTrial.measurableSet_arm (M := M.toSwitchingTrial) hR
    true)] with ω hω
  exact scale_expRecord_eq hwf h hfull hω

variable (M μ) in
/-- **The censored estimating function of a functional `Φ`.** For any functional `Φ` of the law
of a censored record (a survival probability at a fixed time, a restricted mean, the target of a
parametric fit), the difference between its value on the recensored control record at `ψ` and
on the rescaled experimental record at `ψ`. -/
noncomputable def censoredEstFn (Φ : Measure (ℝ × Bool) → ℝ) (ψ : ℝ) : ℝ :=
  Φ ((μ[|M.toSwitchingTrial.arm false]).map (M.recensored ψ)) -
    Φ ((μ[|M.toSwitchingTrial.arm true]).map
      (fun ω ↦ (Real.exp ψ * (M.expRecord ψ ω).1, (M.expRecord ψ ω).2)))

/-- **The true parameter is a root for every functional.** Under the hypotheses of
`armLaw_records_eq`, `censoredEstFn Φ ψ₀ = 0` for every `Φ`. -/
theorem censoredEstFn_trueParam [IsFiniteMeasure μ] (hwf : M.WellFormed) {ψ₀ : ℝ}
    (h : M.PathModel ψ₀) (hfull : M.ExpFullyTreated) (hR : Measurable M.R)
    (hU : Measurable M.U) (hC : Measurable M.C) (hrand : M.RandomizedCensored μ)
    (h1 : μ (M.toSwitchingTrial.arm true) ≠ 0) (h0 : μ (M.toSwitchingTrial.arm false) ≠ 0)
    (Φ : Measure (ℝ × Bool) → ℝ) : M.censoredEstFn μ Φ ψ₀ = 0 := by
  rw [censoredEstFn, armLaw_records_eq hwf h hfull hR hU hC hrand h1 h0, sub_self]

/-! ### The censored exponential update -/

variable (M μ) in
/-- **Follow-up per event** of a censored record `X = (time, event)` in arm `r`:
`E[time | R = r] / P(event | R = r)`. It is the reciprocal of the maximum likelihood rate of an
exponential model fitted to censored data in that arm (events divided by total follow-up), in
the population. -/
noncomputable def perEvent (X : Ω → ℝ × Bool) (r : Bool) : ℝ :=
  M.toSwitchingTrial.armMean μ (fun ω ↦ (X ω).1) r /
    (μ[|M.toSwitchingTrial.arm r]).real {ω | (X ω).2 = true}

variable (M μ) in
/-- **The censored update with recensoring.** At the current value `ψ`, the control arm is
replaced by its recensored record (untreated scale, recensored at `D*(ψ)`), the experimental arm
by its record censored at `D*(ψ) / exp ψ` (observed scale), and the arms are compared by the time
ratio of an exponential accelerated failure time fit to censored data, the ratio of follow-up
per event: `ipeCensMap ψ = log (perEvent (control record) / perEvent (experimental record))`.
For `ψ ≤ 0` the experimental record is the observed record (`expRecord_of_nonpos`). -/
noncomputable def ipeCensMap (ψ : ℝ) : ℝ :=
  Real.log (M.perEvent μ (M.recensored ψ) false / M.perEvent μ (M.expRecord ψ) true)

variable (M μ) in
/-- **The censored update without recensoring**: the control arm is replaced by the transformed
follow-up with the original event indicator (`CensoredTrial.naive`), the experimental arm keeps
its observed follow-up and event indicator. -/
noncomputable def ipeNaiveMap (ψ : ℝ) : ℝ :=
  Real.log (M.perEvent μ (M.naive ψ) false /
    M.perEvent μ (fun ω ↦ (M.obsTime ω, M.event ω)) true)

/-- **The true parameter is a fixed point of the censored update.** Under the path model at
`ψ₀`, a fully treated experimental arm, randomization with respect to `(U, C)`, measurable `R`,
`U`, `C`, integrable `C`, both arms of positive probability, and an experimental record with
positive probability of an event and nonzero mean time, `ipeCensMap ψ₀ = ψ₀`. Independent
censoring is not needed. -/
theorem isFixedPt_ipeCensMap_trueParam [IsFiniteMeasure μ] (hwf : M.WellFormed) {ψ₀ : ℝ}
    (h : M.PathModel ψ₀) (hfull : M.ExpFullyTreated) (hR : Measurable M.R)
    (hU : Measurable M.U) (hC : Measurable M.C) (hrand : M.RandomizedCensored μ)
    (hCi : Integrable M.C μ) (h1 : μ (M.toSwitchingTrial.arm true) ≠ 0)
    (h0 : μ (M.toSwitchingTrial.arm false) ≠ 0)
    (hev : (μ[|M.toSwitchingTrial.arm true]).real {ω | (M.expRecord ψ₀ ω).2 = true} ≠ 0)
    (hX : M.toSwitchingTrial.armMean μ (fun ω ↦ (M.expRecord ψ₀ ω).1) true ≠ 0) :
    IsFixedPt (M.ipeCensMap μ) ψ₀ := by
  set g : ℝ × ℝ → ℝ × Bool := fun p ↦ censorAt p.1 (recensoringTime ψ₀ p.2) with hgdef
  have hg : Measurable g := measurable_censorAt.comp
    (measurable_fst.prodMk ((measurable_recensoringTime ψ₀).comp measurable_snd))
  have hrec : M.recensored ψ₀ = fun ω ↦ g (M.U ω, M.C ω) := funext (recensored_eq hwf h)
  have hUnn : ∀ ω, 0 ≤ M.U ω := fun ω ↦ by
    rw [h ω]
    exact (mul_nonneg (le_min zero_le_one (Real.exp_pos _).le) (hwf.T_nonneg ω)).trans
      (untreatedTime_mem_Icc (hwf.measurableSet_path ω) ψ₀ (hwf.T_nonneg ω)).1
  have hG1i : Integrable (fun ω ↦ (g (M.U ω, M.C ω)).1) μ := by
    refine Integrable.mono' hCi ((measurable_fst.comp hg).comp (hU.prodMk hC)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    have e : (g (M.U ω, M.C ω)).1 = min (M.U ω) (recensoringTime ψ₀ (M.C ω)) := rfl
    rw [e, Real.norm_eq_abs, abs_of_nonneg (le_min (hUnn ω)
      (recensoringTime_nonneg ψ₀ (hwf.C_nonneg ω)))]
    exact (min_le_right _ _).trans (recensoringTime_le_self _ _)
  have hind1 : IndepFun (fun ω ↦ (g (M.U ω, M.C ω)).1) M.R μ :=
    (hrand.comp measurable_id (measurable_fst.comp hg)).symm
  have hmean : ∀ r, μ (M.toSwitchingTrial.arm r) ≠ 0 →
      M.toSwitchingTrial.armMean μ (fun ω ↦ (g (M.U ω, M.C ω)).1) r =
        ∫ ω, (g (M.U ω, M.C ω)).1 ∂μ := fun r hr ↦
    Mediation.condMean_preimage_singleton_of_indepFun hind1 hR hG1i hr
  have hprob : ∀ r, μ (M.toSwitchingTrial.arm r) ≠ 0 →
      (μ[|M.toSwitchingTrial.arm r]).real {ω | (g (M.U ω, M.C ω)).2 = true} =
        μ.real {ω | (g (M.U ω, M.C ω)).2 = true} := fun r hr ↦ by
    have hm : Measurable fun ω ↦ (g (M.U ω, M.C ω)).2 :=
      (measurable_snd.comp hg).comp (hU.prodMk hC)
    have e := congrArg (fun ν : Measure Bool ↦ (ν {true}).toReal)
      (map_cond_arm_of_randomizedCensored hR hU hC hrand (measurable_snd.comp hg) hr)
    dsimp only [Function.comp_def] at e
    rw [Measure.map_apply hm (measurableSet_singleton _),
      Measure.map_apply hm (measurableSet_singleton _)] at e
    exact e
  have hmem := ae_cond_mem (μ := μ)
    (SwitchingTrial.measurableSet_arm (M := M.toSwitchingTrial) hR true)
  have hexp1 : M.toSwitchingTrial.armMean μ (fun ω ↦ (M.expRecord ψ₀ ω).1) true * Real.exp ψ₀ =
      M.toSwitchingTrial.armMean μ (fun ω ↦ (g (M.U ω, M.C ω)).1) true := by
    rw [SwitchingTrial.armMean, SwitchingTrial.armMean, ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [hmem] with ω hω
    have e := congrArg Prod.fst (scale_expRecord_eq hwf h hfull hω)
    rw [hrec] at e
    rw [← e, mul_comm]
  have hexp2 : (μ[|M.toSwitchingTrial.arm true]).real {ω | (M.expRecord ψ₀ ω).2 = true} =
      (μ[|M.toSwitchingTrial.arm true]).real {ω | (g (M.U ω, M.C ω)).2 = true} := by
    refine measureReal_congr ?_
    filter_upwards [hmem] with ω hω
    have e := congrArg Prod.snd (scale_expRecord_eq hwf h hfull hω)
    rw [hrec] at e
    change (M.expRecord ψ₀ ω).2 = true ↔ (g (M.U ω, M.C ω)).2 = true
    rw [← e]
  have hE : ∫ ω, (g (M.U ω, M.C ω)).1 ∂μ =
      M.toSwitchingTrial.armMean μ (fun ω ↦ (M.expRecord ψ₀ ω).1) true * Real.exp ψ₀ := by
    rw [← hmean true h1, hexp1]
  have hP : μ.real {ω | (g (M.U ω, M.C ω)).2 = true} =
      (μ[|M.toSwitchingTrial.arm true]).real {ω | (M.expRecord ψ₀ ω).2 = true} := by
    rw [← hprob true h1, hexp2]
  rw [IsFixedPt, ipeCensMap, perEvent, perEvent]
  simp only [hrec]
  rw [hmean false h0, hprob false h0, hE, hP]
  rw [show ∀ a b c : ℝ, b ≠ 0 → c ≠ 0 → (b * a / c) / (b / c) = a from fun a b c hb hc ↦ by
    field_simp, Real.log_exp]
  all_goals assumption

end CensoredTrial

/-! ### Slope one almost everywhere: the converse of the slope condition -/

/-- **A translation has no fixed point or every point is fixed.** If `f ψ = ψ + f 0` for every
`ψ`, then either no point is a fixed point of `f` (when `f 0 ≠ 0`) or every point is (when
`f 0 = 0`). -/
theorem fixedPt_empty_or_univ_of_shift {f : ℝ → ℝ} (hshift : ∀ ψ, f ψ = ψ + f 0) :
    (∀ ψ, ¬ IsFixedPt f ψ) ∨ ∀ ψ, IsFixedPt f ψ := by
  by_cases h0 : f 0 = 0
  · exact Or.inr fun ψ ↦ by rw [IsFixedPt, hshift, h0, add_zero]
  · refine Or.inl fun ψ hψ ↦ h0 ?_
    have := hshift ψ
    rw [hψ.eq] at this
    linarith

/-- **Uniqueness of a fixed point is decided by a dichotomy.** Let `p` be a fixed point of
`f : ℝ → ℝ`. If a condition `P` gives uniqueness, and its failure makes `f` a translation,
`f ψ = ψ + f 0`, then `p` is the unique fixed point exactly when `P` holds (otherwise every `ψ`
is a fixed point). -/
theorem unique_fixedPt_iff_of_shift {f : ℝ → ℝ} {p : ℝ} {P : Prop} (hp : IsFixedPt f p)
    (huniq : P → ∀ q, IsFixedPt f q → q = p) (hshift : ¬ P → ∀ ψ, f ψ = ψ + f 0) :
    (∀ q, IsFixedPt f q → q = p) ↔ P := by
  refine ⟨fun h ↦ by_contra fun hP ↦ ?_, huniq⟩
  have hs := hshift hP
  have h0 : f 0 = 0 := by have := hs p; rw [hp.eq] at this; linarith
  have hq : IsFixedPt f (p + 1) := by rw [IsFixedPt, hs, h0, add_zero]
  have := h (p + 1) hq
  linarith

namespace SwitchingTrial

variable {Ω : Type*} [MeasurableSpace Ω] {M : SwitchingTrial Ω} {μ : Measure Ω}

/-- If the control patients with positive time off the experimental treatment have probability
zero, almost every control patient (in the conditional law of the control arm) has `T^c = 0`. -/
theorem ae_Tc_eq_zero [IsFiniteMeasure μ] (hR : Measurable M.R) (hwf : M.WellFormed)
    (hno : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) = 0) : ∀ᵐ ω ∂μ[|M.arm false], M.Tc ω = 0 := by
  have h : μ[|M.arm false] {ω | 0 < M.Tc ω} = 0 := by
    rw [cond_apply (M.measurableSet_arm hR false), hno, mul_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with ω hω
  have h1 : ¬ 0 < M.Tc ω := hω
  have h2 : 0 ≤ M.Tc ω := sub_nonneg.2 (hwf.te_le ω)
  linarith

/-- Under `T^c = 0` almost everywhere in the control arm, `U(ψ) = exp ψ T` almost everywhere
there. -/
theorem ae_counterfactual_eq [IsFiniteMeasure μ] (hR : Measurable M.R) (hwf : M.WellFormed)
    (hno : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) = 0) (ψ : ℝ) :
    ∀ᵐ ω ∂μ[|M.arm false], M.counterfactual ψ ω = Real.exp ψ * M.T ω := by
  filter_upwards [ae_Tc_eq_zero hR hwf hno] with ω hω
  have : M.Te ω = M.T ω := by simp only [Tc] at hω; linarith
  rw [counterfactual, hω, this, zero_add]

/-- **Slope one for the log-time update, almost everywhere.** If the control patients with
positive time off the experimental treatment have probability zero, `logMap ψ = ψ + logMap 0`
for every `ψ`. -/
theorem logMap_eq_add_of_ae [IsFiniteMeasure μ] (hR : Measurable M.R) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ)
    (h0 : μ (M.arm false) ≠ 0) (hno : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) = 0) (ψ : ℝ) :
    M.logMap μ ψ = ψ + M.logMap μ 0 := by
  have e : M.logControl μ ψ = M.armMean μ (fun ω ↦ ψ + Real.log (M.T ω)) false := by
    refine integral_congr_ae ?_
    filter_upwards [ae_counterfactual_eq hR hwf hno ψ] with ω hω
    rw [hω, Real.log_mul (Real.exp_pos _).ne' (hTpos ω).ne', Real.log_exp]
  rw [logMap_eq, logMap_eq, e, armMean_const_add hlogT h0, logControl, counterfactual_zero]
  ring

/-- **Slope one for the ratio of means update, almost everywhere.** If the control patients with
positive time off the experimental treatment have probability zero, and `E[T^e | R = 0]`,
`E[T | R = 1]` are nonzero, `ipeMap ψ = ψ + ipeMap 0` for every `ψ`. -/
theorem ipeMap_eq_add_of_ae [IsFiniteMeasure μ] (hR : Measurable M.R) (hwf : M.WellFormed)
    (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h0 : μ (M.arm false) ≠ 0)
    (hno : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) = 0) (hb : M.armMean μ M.Te false ≠ 0)
    (hc : M.armMean μ M.T true ≠ 0) (ψ : ℝ) : M.ipeMap μ ψ = ψ + M.ipeMap μ 0 := by
  have ha : M.armMean μ M.Tc false = 0 := by
    rw [armMean, integral_congr_ae (g := fun _ ↦ (0 : ℝ)) (ae_Tc_eq_zero hR hwf hno),
      integral_zero]
  have key : ∀ x, M.ipeMap μ x = Real.log (Real.exp x * (M.armMean μ M.Te false /
      M.armMean μ M.T true)) := fun x ↦ by
    rw [ipeMap_eq hT hTe h0, ipeRatio, ha, zero_add, mul_div_assoc]
  rw [key, key, Real.exp_zero, one_mul, Real.log_mul (Real.exp_pos _).ne' (div_ne_zero hb hc),
    Real.log_exp]

/-- **Slope one for the Weibull update, almost everywhere.** For a shape `k > 0`, if the control
patients with positive time off the experimental treatment have probability zero,
`weibullMap k ψ = ψ + weibullMap k 0` for every `ψ`. -/
theorem weibullMap_eq_add_of_ae [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 < k) (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0)
    (hno : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) = 0) (ψ : ℝ) :
    M.weibullMap μ k ψ = ψ + M.weibullMap μ k 0 := by
  have e : M.powControl μ k ψ = Real.exp (ψ * k) * M.powControl μ k 0 := by
    rw [powControl, powControl, counterfactual_zero, SwitchingTrial.armMean,
      SwitchingTrial.armMean, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_counterfactual_eq hR hwf hno ψ] with ω hω
    rw [hω, Real.mul_rpow (Real.exp_pos _).le (hTpos ω).le, ← Real.exp_mul]
  have hA := powControl_pos hTm hTem hwf hTpos hk.le hTk h0 0
  rw [weibullMap_eq hTm hTem hwf hTpos hk.le hTk h1 h0,
    weibullMap_eq hTm hTem hwf hTpos hk.le hTk h1 h0, e,
    Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp]
  field_simp
  ring

/-- Positive probability of control patients with positive time off treatment gives
`E[T^c | R = 0] > 0`. -/
theorem armMean_Tc_pos_of_pos [IsFiniteMeasure μ] (hR : Measurable M.R) (hwf : M.WellFormed)
    (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h0 : μ (M.arm false) ≠ 0)
    (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) : 0 < M.armMean μ M.Tc false := by
  have := integral_lt_of_le_of_lt (ν := μ[|M.arm false]) (f := fun _ ↦ (0 : ℝ)) (g := M.Tc)
    (integrable_const _) (Mediation.integrable_cond_of_integrable (integrable_Tc hT hTe) h0)
    (fun ω ↦ sub_nonneg.2 (hwf.te_le ω)) (cond_Tc_pos_ne_zero hR hpos) fun ω hω ↦ hω
  rw [integral_zero] at this
  exact this

/-- **Uniqueness of the ratio of means fixed point is equivalent to positive time off
treatment.** Under the common treatment effect `ψ₀`, randomization, a fully treated
experimental arm, `0 ≤ T^e ≤ T`, `T > 0`, integrable `T`, `T^e` and both arms of positive
probability: `ψ₀` is the unique fixed point of `ipeMap` if and only if the control patients
with positive time off the experimental treatment have positive probability. -/
theorem unique_fixedPt_ipeMap_iff [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated)
    (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    (∀ q, IsFixedPt (M.ipeMap μ) q → q = ψ₀) ↔ μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0 := by
  have hc : 0 < M.armMean μ M.T true := armMean_pos hTpos hT h1
  refine unique_fixedPt_iff_of_shift
    (isFixedPt_ipeMap_trueParam hR h hrand hfull hT hTe h1 h0 hc.ne') (fun hpos q hq ↦ ?_)
    (fun hno ↦ ?_)
  · exact (isFixedPt_ipeMap_iff_trueParam hR h hrand hfull hwf.te_nonneg hT hTe h1 h0
      (armMean_Tc_pos_of_pos hR hwf hT hTe h0 hpos) q).1 hq
  · have hno' : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) = 0 := not_not.1 hno
    have ha : M.armMean μ M.Tc false = 0 := by
      rw [armMean, integral_congr_ae (g := fun _ ↦ (0 : ℝ)) (ae_Tc_eq_zero hR hwf hno'),
        integral_zero]
    have hb : 0 < M.armMean μ M.Te false := by
      have := armMean_pos (r := false) hTpos hT h0
      rw [armMean_Tc hT hTe h0] at ha
      linarith
    exact ipeMap_eq_add_of_ae hR hwf hT hTe h0 hno' hb.ne' hc.ne'

/-- **Uniqueness of the log-time fixed point is equivalent to positive time off treatment.**
Under the hypotheses of `isFixedPt_logMap_trueParam`, `ψ₀` is the unique fixed point of `logMap`
if and only if the control patients with positive time off the experimental treatment have
positive probability. -/
theorem unique_fixedPt_logMap_iff [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    (∀ q, IsFixedPt (M.logMap μ) q → q = ψ₀) ↔ μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0 :=
  unique_fixedPt_iff_of_shift
    (isFixedPt_logMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hlogT h1 h0)
    (fun hpos ↦ (tendsto_iterate_logMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hlogT h1 h0
      hpos).1)
    (fun hno ↦ logMap_eq_add_of_ae hR hwf hTpos hlogT h0 (not_not.1 hno))

/-- **Uniqueness of the Weibull fixed point is equivalent to positive time off treatment.** Under
the hypotheses of `isFixedPt_weibullMap_trueParam`, `ψ₀` is the unique fixed point of
`weibullMap k` if and only if the control patients with positive time off the experimental
treatment have positive probability. -/
theorem unique_fixedPt_weibullMap_iff [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 < k) (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    (∀ q, IsFixedPt (M.weibullMap μ k) q → q = ψ₀) ↔
      μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0 :=
  unique_fixedPt_iff_of_shift
    (isFixedPt_weibullMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hk hTk h1 h0)
    (fun hpos ↦ (tendsto_iterate_weibullMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hk hTk
      h1 h0 hpos).1)
    (fun hno ↦ weibullMap_eq_add_of_ae hR hTm hTem hwf hTpos hk hTk h1 h0 (not_not.1 hno))

end SwitchingTrial

/-! ### The Weibull fit with an estimated shape -/

/-- Pointwise inequality behind the monotonicity of the tilted mean of `log X`: for `x > 0`,
`δ > 0` and any `L`, `x^k (x^δ - exp (δ L)) (log x - L) ≥ 0`, expanded. -/
theorem rpow_tilt_ineq {x : ℝ} (hx : 0 < x) (k : ℝ) {δ : ℝ} (hδ : 0 < δ) (L : ℝ) :
    Real.exp (δ * L) * (x ^ k * Real.log x) - Real.exp (δ * L) * L * x ^ k ≤
      x ^ (k + δ) * Real.log x - L * x ^ (k + δ) := by
  have ha : 0 ≤ x ^ k := (Real.rpow_pos_of_pos hx k).le
  have hxd : x ^ δ = Real.exp (δ * Real.log x) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  have hbd : 0 ≤ (x ^ δ - Real.exp (δ * L)) * (Real.log x - L) := by
    rcases le_total L (Real.log x) with h | h
    · refine mul_nonneg (sub_nonneg.2 ?_) (sub_nonneg.2 h)
      rw [hxd]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hδ.le)
    · refine mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 ?_) (sub_nonpos.2 h)
      rw [hxd]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hδ.le)
  have e : x ^ (k + δ) = x ^ k * x ^ δ := Real.rpow_add hx k δ
  have := mul_nonneg ha hbd
  have hid : x ^ k * x ^ δ * Real.log x - L * (x ^ k * x ^ δ) -
      (Real.exp (δ * L) * (x ^ k * Real.log x) - Real.exp (δ * L) * L * x ^ k) =
      x ^ k * ((x ^ δ - Real.exp (δ * L)) * (Real.log x - L)) := by ring
  rw [e]
  linarith

/-- **The shape score of one arm.** For a positive time `X` with law `ν` (one arm), the
derivative in `k` of the Weibull log likelihood per observation, with the arm's scale profiled
out (`λ^k = E[X^k]`): `1/k + E[log X] - E[X^k log X] / E[X^k]`. -/
noncomputable def shapeScoreArm {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (X : Ω → ℝ)
    (k : ℝ) : ℝ :=
  1 / k + ∫ ω, Real.log (X ω) ∂ν -
    (∫ ω, X ω ^ k * Real.log (X ω) ∂ν) / ∫ ω, X ω ^ k ∂ν

/-- **The shape score of one arm is strictly decreasing** on `k > 0`, for a positive time `X`
under a probability measure with `X^k` and `X^k log X` integrable for every `k > 0`. -/
theorem shapeScoreArm_strictAntiOn {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {X : Ω → ℝ} (hX : ∀ ω, 0 < X ω)
    (hI : ∀ k : ℝ, 0 < k → Integrable (fun ω ↦ X ω ^ k) ν ∧
      Integrable (fun ω ↦ X ω ^ k * Real.log (X ω)) ν) :
    StrictAntiOn (shapeScoreArm ν X) (Ioi 0) := by
  intro k hk k' hk' hlt
  have hk0 : (0 : ℝ) < k := hk
  have hk0' : (0 : ℝ) < k' := hk'
  have hD : ∀ j : ℝ, 0 < j → 0 < ∫ ω, X ω ^ j ∂ν := fun j hj ↦ by
    rw [integral_pos_iff_support_of_nonneg (fun ω ↦ (Real.rpow_pos_of_pos (hX ω) j).le)
      (hI j hj).1]
    have : Function.support (fun ω ↦ X ω ^ j) = univ :=
      eq_univ_of_forall fun ω ↦ (Real.rpow_pos_of_pos (hX ω) j).ne'
    rw [this, measure_univ]; exact one_pos
  set N := ∫ ω, X ω ^ k * Real.log (X ω) ∂ν
  set D := ∫ ω, X ω ^ k ∂ν
  set N' := ∫ ω, X ω ^ k' * Real.log (X ω) ∂ν
  set D' := ∫ ω, X ω ^ k' ∂ν
  have hDp := hD k hk0
  have hD'p := hD k' hk0'
  set L := N / D
  set c := Real.exp ((k' - k) * L)
  have hpt : ∀ ω, c * (X ω ^ k * Real.log (X ω)) - c * L * X ω ^ k ≤
      X ω ^ k' * Real.log (X ω) - L * X ω ^ k' := fun ω ↦ by
    have := rpow_tilt_ineq (hX ω) k (sub_pos.2 hlt) L
    rwa [add_sub_cancel] at this
  have hmono := integral_mono (((hI k hk0).2.const_mul c).sub ((hI k hk0).1.const_mul (c * L)))
    ((hI k' hk0').2.sub ((hI k' hk0').1.const_mul L)) hpt
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub ((hI k hk0).2.const_mul c) ((hI k hk0).1.const_mul (c * L)),
    integral_sub (hI k' hk0').2 ((hI k' hk0').1.const_mul L), integral_const_mul,
    integral_const_mul, integral_const_mul] at hmono
  have hzero : c * N - c * L * D = 0 := by
    rw [mul_assoc c L D, show L * D = N from div_mul_cancel₀ N hDp.ne', sub_self]
  have hratio : L ≤ N' / D' := by
    rw [le_div_iff₀ hD'p]; linarith
  have hinv : 1 / k' < 1 / k := one_div_lt_one_div_of_lt hk0 hlt
  simp only [shapeScoreArm]
  linarith

namespace SwitchingTrial

variable {Ω : Type*} [MeasurableSpace Ω] {M : SwitchingTrial Ω} {μ : Measure Ω}

variable (M μ) in
/-- **The population profile equation for the common Weibull shape.** In the two-arm Weibull
fit with the arm as covariate (one scale per arm, a common shape `k`) to the experimental times
`T` and the transformed control times `U(ψ)`, the log likelihood per observation is
`log k - k log λ_r + (k - 1) log x - (x / λ_r)^k`. Its maximum in the scale of arm `r` is at
`λ_r^k = E[X^k | R = r]`; substituting, the derivative in `k` of the expected log likelihood is
the arm score `1/k + E[log X | R = r] - E[X^k log X | R = r] / E[X^k | R = r]`, and the fit pools
the arms with their probabilities:
`shapeScore ψ k = P(R = 1) score_1(k) + P(R = 0) score_0(k)`, with `X = T` in arm `1` and
`X = U(ψ)` in arm `0`. -/
noncomputable def shapeScore (ψ k : ℝ) : ℝ :=
  μ.real (M.arm true) * shapeScoreArm (μ[|M.arm true]) M.T k +
    μ.real (M.arm false) * shapeScoreArm (μ[|M.arm false]) (M.counterfactual ψ) k

/-- **The pooled shape score is strictly decreasing** on `k > 0`, so the fitted shape (its root)
is unique when it exists. The hypotheses are `T > 0`, `0 ≤ T^e ≤ T`, both arms of positive
probability, and integrability of `X^k` and `X^k log X` in each arm for every `k > 0`. -/
theorem shapeScore_strictAntiOn [IsFiniteMeasure μ] (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (ψ : ℝ)
    (hI1 : ∀ k : ℝ, 0 < k → Integrable (fun ω ↦ M.T ω ^ k) (μ[|M.arm true]) ∧
      Integrable (fun ω ↦ M.T ω ^ k * Real.log (M.T ω)) (μ[|M.arm true]))
    (hI0 : ∀ k : ℝ, 0 < k → Integrable (fun ω ↦ M.counterfactual ψ ω ^ k) (μ[|M.arm false]) ∧
      Integrable (fun ω ↦ M.counterfactual ψ ω ^ k * Real.log (M.counterfactual ψ ω))
        (μ[|M.arm false])) :
    StrictAntiOn (M.shapeScore μ ψ) (Ioi 0) := by
  have := cond_isProbabilityMeasure (μ := μ) h1
  have := cond_isProbabilityMeasure (μ := μ) h0
  have a1 := shapeScoreArm_strictAntiOn (ν := μ[|M.arm true]) hTpos hI1
  have a0 := shapeScoreArm_strictAntiOn (ν := μ[|M.arm false])
    (counterfactual_pos hwf hTpos ψ) hI0
  have p1 : 0 < μ.real (M.arm true) :=
    ENNReal.toReal_pos h1 (measure_ne_top _ _)
  have p0 : 0 < μ.real (M.arm false) :=
    ENNReal.toReal_pos h0 (measure_ne_top _ _)
  intro k hk k' hk' hlt
  have e1 := a1 hk hk' hlt
  have e0 := a0 hk hk' hlt
  simp only [shapeScore]
  linarith [mul_lt_mul_of_pos_left e1 p1, mul_lt_mul_of_pos_left e0 p0]

/-- **The fitted shape is unique.** Under the hypotheses of `shapeScore_strictAntiOn`, two
positive roots of the pooled shape score are equal. -/
theorem shapeScore_root_unique [IsFiniteMeasure μ] (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (ψ : ℝ)
    (hI1 : ∀ k : ℝ, 0 < k → Integrable (fun ω ↦ M.T ω ^ k) (μ[|M.arm true]) ∧
      Integrable (fun ω ↦ M.T ω ^ k * Real.log (M.T ω)) (μ[|M.arm true]))
    (hI0 : ∀ k : ℝ, 0 < k → Integrable (fun ω ↦ M.counterfactual ψ ω ^ k) (μ[|M.arm false]) ∧
      Integrable (fun ω ↦ M.counterfactual ψ ω ^ k * Real.log (M.counterfactual ψ ω))
        (μ[|M.arm false]))
    {k k' : ℝ} (hk : 0 < k) (hk' : 0 < k') (h : M.shapeScore μ ψ k = 0)
    (h' : M.shapeScore μ ψ k' = 0) : k = k' :=
  (shapeScore_strictAntiOn hwf hTpos h1 h0 ψ hI1 hI0).injOn hk hk' (h.trans h'.symm)

open Classical in
variable (M μ) in
/-- **The fitted shape at the current value `ψ`**: the positive root of the pooled shape score
when one exists, and the exponential shape `1` otherwise (when the likelihood has no maximizer
in the shape). -/
noncomputable def fittedShape (ψ : ℝ) : ℝ :=
  if h : ∃ k, 0 < k ∧ M.shapeScore μ ψ k = 0 then h.choose else 1

/-- The fitted shape is positive. -/
theorem fittedShape_pos (ψ : ℝ) : 0 < M.fittedShape μ ψ := by
  rw [fittedShape]
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_pos

/-- When a positive root of the shape score exists, the fitted shape is a root. -/
theorem shapeScore_fittedShape {ψ : ℝ} (h : ∃ k, 0 < k ∧ M.shapeScore μ ψ k = 0) :
    M.shapeScore μ ψ (M.fittedShape μ ψ) = 0 := by
  simp only [fittedShape, h, dite_true]
  exact h.choose_spec.2

/-- **The true parameter is a fixed point whatever the shape rule.** For any rule `κ` choosing a
positive shape at each value (`κ ψ > 0`), with `T^{κ ψ}` integrable for every `ψ`, under the
hypotheses of `isFixedPt_weibullMap_trueParam`, `ψ₀` is a fixed point of
`ψ ↦ weibullMap (κ ψ) ψ`. If moreover the control patients with positive time off the
experimental treatment have positive probability, it is the only fixed point. -/
theorem isFixedPt_weibullMap_rule [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (κ : ℝ → ℝ) (hκ : ∀ ψ, 0 < κ ψ)
    (hTκ : ∀ ψ, Integrable (fun ω ↦ M.T ω ^ κ ψ) μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) :
    IsFixedPt (fun ψ ↦ M.weibullMap μ (κ ψ) ψ) ψ₀ ∧
      (μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0 →
        ∀ q, IsFixedPt (fun ψ ↦ M.weibullMap μ (κ ψ) ψ) q → q = ψ₀) := by
  refine ⟨isFixedPt_weibullMap_trueParam hR hTm hTem h hrand hfull hwf hTpos (hκ ψ₀) (hTκ ψ₀)
    h1 h0, fun hpos q hq ↦ ?_⟩
  exact (tendsto_iterate_weibullMap_trueParam hR hTm hTem h hrand hfull hwf hTpos (hκ q) (hTκ q)
    h1 h0 hpos).1 q hq

/-- **The fitted shape.** With the shape fitted at each value by the population profile
equation (`fittedShape`), under the hypotheses of `isFixedPt_weibullMap_trueParam` and `T^k`
integrable for every `k > 0`, `ψ₀` is a fixed point of `ψ ↦ weibullMap (fittedShape ψ) ψ`, and
the only one when the control patients with positive time off the experimental treatment have
positive probability. -/
theorem isFixedPt_weibullMap_fittedShape [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (hTk : ∀ k : ℝ, 0 < k → Integrable (fun ω ↦ M.T ω ^ k) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    IsFixedPt (fun ψ ↦ M.weibullMap μ (M.fittedShape μ ψ) ψ) ψ₀ ∧
      (μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0 →
        ∀ q, IsFixedPt (fun ψ ↦ M.weibullMap μ (M.fittedShape μ ψ) ψ) q → q = ψ₀) :=
  isFixedPt_weibullMap_rule hR hTm hTem h hrand hfull hwf hTpos (M.fittedShape μ)
    fittedShape_pos (fun ψ ↦ hTk _ (fittedShape_pos ψ)) h1 h0

end SwitchingTrial

/-! ### Countermodel: the update without recensoring -/

namespace IPECounterexample

namespace StaggeredCensoring

open CensoredTrial RecensoringCounterexample RecensoringCounterexample.Staggered
open CausalInference.Mediation.Counterexample RPSFTMCounterexample

/-- The experimental arm of the staggered entry trial is on treatment throughout. -/
theorem fullyTreated : trial.ExpFullyTreated := fun ω hω ↦ by
  simp [trial, path, show ω.1 = true from hω]

/-- The experimental record at `ψ₀` is the observed follow-up and event indicator. -/
theorem expRecord_eq_obs (ω : Ω₀) :
    trial.expRecord ψ₀ ω = censorAt (trial.T ω) (trial.C ω) := by
  rw [expRecord_eq, recensTime_eq, exp_ψ₀]
  congr 1; ring

/-- **Counterexample: without recensoring the true parameter is not a fixed point.** In the
staggered entry trial of `RecensoringCounterexample.Staggered` (common effect with time ratio
`1/2`, randomization with respect to `(U, C)`, independent censoring, experimental arm treated
throughout), the update without recensoring gives `ipeNaiveMap ψ₀ = log (93/272)`, not
`ψ₀ = log (1/2)`: the control follow-up per event is `93/20`, the experimental one `68/5`. With
recensoring, `ipeCensMap ψ₀ = ψ₀`. -/
theorem naive_not_fixed :
    trial.ipeNaiveMap μ₀ ψ₀ = Real.log (93 / 272) ∧ Real.log (93 / 272) ≠ ψ₀ ∧
      IsFixedPt (trial.ipeCensMap μ₀) ψ₀ := by
  have hc := condReal_arm trial.toSwitchingTrial (fun _ ↦ rfl)
  have hm := armMean_μ₀ trial.toSwitchingTrial (fun _ ↦ rfl)
  have hn : ∀ ω, trial.naive ψ₀ ω = censorAt (trial.U ω) (trial.naiveCensTime ψ₀ ω) :=
    naive_eq wellFormed pathModel
  refine ⟨?_, ?_, ?_⟩
  · simp only [ipeNaiveMap, perEvent, hm, hc, hn, naiveCensTime_eq, censorAt, obsTime, event]
    simp only [μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator,
      mem_inter_iff, SwitchingTrial.arm, mem_preimage, mem_singleton_iff, mem_ofPred_eq, trial,
      CensoredTrial.toSwitchingTrial]
    norm_num
  · intro h
    have := Real.log_injOn_pos (by norm_num : (93 / 272 : ℝ) ∈ Ioi 0)
      (by norm_num : (1 / 2 : ℝ) ∈ Ioi 0) (h.trans rfl)
    norm_num at this
  · refine isFixedPt_ipeCensMap_trueParam wellFormed pathModel fullyTreated
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _)
      randomizedCensored Integrable.of_finite
      (μ₀_ne_zero_of_mem (ω := (true, true, true)) rfl)
      (μ₀_ne_zero_of_mem (ω := (false, true, true)) rfl) ?_ ?_
    · simp only [hc, expRecord_eq_obs, censorAt]
      simp only [μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator,
        mem_inter_iff, SwitchingTrial.arm, mem_preimage, mem_singleton_iff, mem_ofPred_eq, trial,
        CensoredTrial.toSwitchingTrial]
      norm_num
    · simp only [hm, expRecord_eq_obs, censorAt]
      simp only [trial]
      norm_num

end StaggeredCensoring

end IPECounterexample

end StructuralNested

end CausalInference
