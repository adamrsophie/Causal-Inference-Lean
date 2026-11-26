/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Sharp regression discontinuity: identification at the cutoff

Treatment is assigned by the sharp rule `D = 1{X ≥ c}` for a running variable `X` and a cutoff
`c : ℝ`. To avoid conditioning on the null event `X = c`, everything is stated through
conditional mean functions of the running variable: `m1 x` and `m0 x` are versions of
`E[Y(1) | X = x]` and `E[Y(0) | X = x]`, and the observed regression function is
`observedRegression c m1 m0 x = if c ≤ x then m1 x else m0 x`.

## Main results

* `CausalInference.RD.sharp_rd_identification`: if `m1` is right-continuous at `c` and `m0` is
  left-continuous at `c`, the right limit minus the left limit of the observed regression at `c`
  equals `m1 c - m0 c`, the average treatment effect at the cutoff.
* `CausalInference.RD.condExp_observed_eq_observedRegression`: the measure-theoretic bridge;
  if `m1 ∘ X` and `m0 ∘ X` are versions of `E[Y1 | σ(X)]` and `E[Y0 | σ(X)]`, then
  `observedRegression c m1 m0 ∘ X` is a version of `E[Y | σ(X)]` for the observed outcome
  `Y = if c ≤ X then Y1 else Y0`.
  `CausalInference.RD.condExp_observed_eq_observedRegression_of_measurable` adds Borel
  measurability of the observed regression when `m1` and `m0` are measurable.
* `CausalInference.RD.tendsto_right_unique_of_ae_eq` and
  `CausalInference.RD.tendsto_left_unique_of_ae_eq`: under the support conditions
  `CausalInference.RD.RightSupport` and `CausalInference.RD.LeftSupport` (positive mass of the
  running variable in every one-sided neighborhood of `c`), one-sided limits at `c` do not depend
  on the version of a conditional mean function.
* `CausalInference.RD.sharp_rd_identification_of_condExp`: the identification statement for an
  arbitrary version of `E[Y | σ(X)]`, so the observed jump is a functional of the law of
  `(X, Y)`.
* `CausalInference.RD.sharp_rd_counterexample`: with `m0` discontinuous at the cutoff, the
  observed jump differs from `m1 c - m0 c` and from the right limit of `m1 - m0`
  (`CausalInference.RD.not_tendsto_counterexampleM0` checks the discontinuity).
* `CausalInference.RD.sharp_rd_support_counterexample`: without right support, one law of
  `(X, Y1, Y0)` is compatible with two admissible pairs `(m1, m0)` with different cutoff effects.

## Sources

J. Hahn, P. Todd, W. Van der Klaauw (2001), Identification and estimation of treatment effects
with a regression-discontinuity design, Econometrica 69(1).
G. W. Imbens, T. Lemieux (2008), Regression discontinuity designs: a guide to practice,
Journal of Econometrics 142(2).
-/

@[expose] public section

open Filter Topology

namespace CausalInference

namespace RD

/-- The observed regression function of a sharp regression discontinuity design with cutoff `c`:
`x ↦ E[Y | X = x]` equals `m1 x = E[Y(1) | X = x]` at and above the cutoff and
`m0 x = E[Y(0) | X = x]` below it. This definition encodes two assumptions at once: consistency
(the observed outcome is the potential outcome of the treatment received) and the sharp rule
`D = 1{X ≥ c}` (every unit at or above the cutoff is treated, every unit below is not). -/
noncomputable def observedRegression (c : ℝ) (m1 m0 : ℝ → ℝ) (x : ℝ) : ℝ :=
  if c ≤ x then m1 x else m0 x

theorem observedRegression_of_le {c x : ℝ} (m1 m0 : ℝ → ℝ) (h : c ≤ x) :
    observedRegression c m1 m0 x = m1 x := ite_eq_left h

theorem observedRegression_of_lt {c x : ℝ} (m1 m0 : ℝ → ℝ) (h : x < c) :
    observedRegression c m1 m0 x = m0 x := ite_eq_right (not_le.mpr h)

/-- The right limit of the observed regression at the cutoff is `m1 c` as soon as `m1` is
right-continuous at `c`. The filter is `𝓝[>] c` (points strictly above `c`); since the observed
regression agrees with `m1` on `[c, ∞)`, `𝓝[≥] c` would give the same limit. -/
theorem tendsto_observedRegression_right {c : ℝ} {m1 : ℝ → ℝ} (m0 : ℝ → ℝ)
    (h1 : Tendsto m1 (𝓝[>] c) (𝓝 (m1 c))) :
    Tendsto (observedRegression c m1 m0) (𝓝[>] c) (𝓝 (m1 c)) :=
  tendsto_nhdsWithin_congr (fun _ hx => (observedRegression_of_le m1 m0 (le_of_lt hx)).symm) h1

/-- The left limit of the observed regression at the cutoff is `m0 c` as soon as `m0` is
left-continuous at `c`. The filter must be `𝓝[<] c` (points strictly below `c`) and not
`𝓝[≤] c`: at `x = c` itself the observed regression equals `m1 c`, not `m0 c`. -/
theorem tendsto_observedRegression_left {c : ℝ} (m1 : ℝ → ℝ) {m0 : ℝ → ℝ}
    (h0 : Tendsto m0 (𝓝[<] c) (𝓝 (m0 c))) :
    Tendsto (observedRegression c m1 m0) (𝓝[<] c) (𝓝 (m0 c)) :=
  tendsto_nhdsWithin_congr (fun _ hx => (observedRegression_of_lt m1 m0 hx).symm) h0

/-- **Sharp regression discontinuity identification** (Hahn, Todd and Van der Klaauw 2001).
Assume `m1` (a version of `E[Y(1) | X = x]`) is right-continuous at the cutoff `c` and `m0`
(a version of `E[Y(0) | X = x]`) is left-continuous at `c`. If `yPlus` and `yMinus` are the right
and left limits at `c` of the observed regression function, then `yPlus - yMinus = m1 c - m0 c`,
the average treatment effect at the cutoff. Existence of both limits follows from
`tendsto_observedRegression_right` and `tendsto_observedRegression_left`. This is a statement
about the supplied functions; since conditional mean functions are determined only almost
everywhere for the law of the running variable, the statement in terms of the observed law,
which needs mass of the running variable on both sides of `c`, is
`sharp_rd_identification_of_condExp`. -/
theorem sharp_rd_identification {c : ℝ} {m1 m0 : ℝ → ℝ}
    (h1 : Tendsto m1 (𝓝[>] c) (𝓝 (m1 c))) (h0 : Tendsto m0 (𝓝[<] c) (𝓝 (m0 c)))
    {yPlus yMinus : ℝ}
    (hPlus : Tendsto (observedRegression c m1 m0) (𝓝[>] c) (𝓝 yPlus))
    (hMinus : Tendsto (observedRegression c m1 m0) (𝓝[<] c) (𝓝 yMinus)) :
    yPlus - yMinus = m1 c - m0 c := by
  rw [tendsto_nhds_unique hPlus (tendsto_observedRegression_right m0 h1),
    tendsto_nhds_unique hMinus (tendsto_observedRegression_left m1 h0)]

/-! ### Counterexample: a discontinuous `m0` breaks identification -/

/-- Counterexample mean function for the untreated potential outcome: `1` strictly below `0` and
`0` at and above `0`, so it is not left-continuous at the cutoff `0`. -/
noncomputable def counterexampleM0 (x : ℝ) : ℝ := if x < 0 then 1 else 0

/-- **Counterexample.** Take cutoff `0`, `m1 = 0` and `m0 = counterexampleM0`, which jumps at
the cutoff. The observed regression has right limit `0` and left limit `1` at `0`, so every
observed jump (right limit minus left limit) is `-1`, while the effect at the cutoff
`m1 0 - m0 0` is `0`. Hence the left-continuity hypothesis on `m0` in
`sharp_rd_identification` cannot be dropped. The failure does not depend on the value of `m0` at
the single point `0`: the last conjunct says that the effect `m1 x - m0 x` tends to `0` as `x`
decreases to the cutoff, so the observed jump `-1` also differs from the limit of the effect just
above the cutoff, a quantity that is the same for every version of `m1` and `m0` that agrees with
them off the point `0`. -/
theorem sharp_rd_counterexample :
    Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[<] 0) (𝓝 1) ∧
    (∀ yPlus yMinus : ℝ,
      Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[>] 0) (𝓝 yPlus) →
      Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[<] 0) (𝓝 yMinus) →
      yPlus - yMinus ≠ (fun _ : ℝ => (0 : ℝ)) 0 - counterexampleM0 0) ∧
    Tendsto (fun x => (fun _ : ℝ => (0 : ℝ)) x - counterexampleM0 x) (𝓝[>] 0) (𝓝 0) := by
  have hR : Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[>] 0) (𝓝 0) :=
    tendsto_observedRegression_right _ tendsto_const_nhds
  have hL : Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[<] 0) (𝓝 1) :=
    tendsto_nhdsWithin_congr (fun x hx => by
      simp [observedRegression_of_lt _ _ (Set.mem_Iio.mp hx), counterexampleM0,
        Set.mem_Iio.mp hx]) tendsto_const_nhds
  refine ⟨hR, hL, fun yPlus yMinus hPlus hMinus => ?_, ?_⟩
  · rw [tendsto_nhds_unique hPlus hR, tendsto_nhds_unique hMinus hL]
    norm_num [counterexampleM0]
  · refine tendsto_nhdsWithin_congr (fun x hx => ?_) tendsto_const_nhds
    simp [counterexampleM0, not_lt.mpr (le_of_lt (Set.mem_Ioi.mp hx))]

/-! ### Measure-theoretic bridge -/

open MeasureTheory

/-- The counterexample `m0` is indeed not left-continuous at the cutoff `0`: otherwise
`sharp_rd_identification` would contradict `sharp_rd_counterexample`. -/
theorem not_tendsto_counterexampleM0 :
    ¬ Tendsto counterexampleM0 (𝓝[<] 0) (𝓝 (counterexampleM0 0)) := fun h0 =>
  sharp_rd_counterexample.2.2.1 0 1 sharp_rd_counterexample.1 sharp_rd_counterexample.2.1
    (sharp_rd_identification tendsto_const_nhds h0 sharp_rd_counterexample.1
      sharp_rd_counterexample.2.1)

/-- **Bridge to conditional expectations.** On a probability space with running variable `X`,
integrable potential outcomes `Y1`, `Y0`, and observed outcome `Y = if c ≤ X then Y1 else Y0`
(consistency under the sharp rule), if `m1 ∘ X` and `m0 ∘ X` are versions of the conditional
expectations of `Y1` and `Y0` given the sigma-algebra generated by `X`, then
`observedRegression c m1 m0 ∘ X` is a version of the conditional expectation of `Y` given `X`.
So the observed regression function of this file is a genuine version of `E[Y | X = x]`. -/
theorem condExp_observed_eq_observedRegression {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {Y1 Y0 : Ω → ℝ}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) (c : ℝ) {m1 m0 : ℝ → ℝ}
    (h1 : μ[Y1 | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m1 ∘ X)
    (h0 : μ[Y0 | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m0 ∘ X) :
    μ[fun ω => if c ≤ X ω then Y1 ω else Y0 ω | MeasurableSpace.comap X inferInstance]
      =ᵐ[μ] observedRegression c m1 m0 ∘ X := by
  set s : Set Ω := X ⁻¹' Set.Ici c
  have hs : MeasurableSet[MeasurableSpace.comap X inferInstance] s :=
    ⟨Set.Ici c, measurableSet_Ici, rfl⟩
  have hY : (fun ω => if c ≤ X ω then Y1 ω else Y0 ω) = s.indicator Y1 + sᶜ.indicator Y0 := by
    funext ω
    by_cases h : c ≤ X ω <;> simp [s, Set.indicator, h]
  have hsm : MeasurableSet s := hX measurableSet_Ici
  rw [hY]
  filter_upwards [condExp_add (hY1.indicator hsm) (hY0.indicator hsm.compl) _,
    condExp_indicator hY1 hs, condExp_indicator hY0 hs.compl, h1, h0] with ω hadd hi1 hi0 e1 e0
  rw [hadd, Pi.add_apply, hi1, hi0]
  by_cases h : c ≤ X ω
  · simp [s, Set.indicator, h, e1, observedRegression]
  · simp [s, Set.indicator, h, e0, observedRegression]

/-- The observed regression function of the sharp design is Borel measurable as soon as `m1` and
`m0` are. -/
theorem measurable_observedRegression (c : ℝ) {m1 m0 : ℝ → ℝ} (hm1 : Measurable m1)
    (hm0 : Measurable m0) : Measurable (observedRegression c m1 m0) :=
  Measurable.ite measurableSet_Ici hm1 hm0

/-- **Bridge to conditional expectations, measurable version.** Under the hypotheses of
`condExp_observed_eq_observedRegression`, and if moreover `m1` and `m0` are Borel measurable,
the observed regression function `observedRegression c m1 m0` is Borel measurable and its
composition with `X` is a version of the conditional expectation of the observed outcome given
`X`. So it is a regular version of `E[Y | X = x]` in the usual sense (a Borel function of the
running variable). -/
theorem condExp_observed_eq_observedRegression_of_measurable {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {Y1 Y0 : Ω → ℝ} (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) (c : ℝ)
    {m1 m0 : ℝ → ℝ} (hm1 : Measurable m1) (hm0 : Measurable m0)
    (h1 : μ[Y1 | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m1 ∘ X)
    (h0 : μ[Y0 | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m0 ∘ X) :
    Measurable (observedRegression c m1 m0) ∧
      μ[fun ω => if c ≤ X ω then Y1 ω else Y0 ω | MeasurableSpace.comap X inferInstance]
        =ᵐ[μ] observedRegression c m1 m0 ∘ X :=
  ⟨measurable_observedRegression c hm1 hm0,
    condExp_observed_eq_observedRegression hX hY1 hY0 c h1 h0⟩

/-! ### Support of the running variable and law-level identification

A conditional mean function of the running variable is determined only almost everywhere for
the law of `X`. Its one-sided limits at the cutoff are functionals of the law only when `X` puts
mass arbitrarily close to `c` on the relevant side. -/

/-- Right support at the cutoff: the running variable `X` puts positive mass on every interval
`(c, c + ε)` with `ε > 0`. -/
def RightSupport {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) :
    Prop :=
  ∀ ε > 0, μ (X ⁻¹' Set.Ioo c (c + ε)) ≠ 0

/-- Left support at the cutoff: the running variable `X` puts positive mass on every interval
`(c - ε, c)` with `ε > 0`. -/
def LeftSupport {Ω : Type*} {_ : MeasurableSpace Ω} (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) :
    Prop :=
  ∀ ε > 0, μ (X ⁻¹' Set.Ioo (c - ε) c) ≠ 0

/-- **Right limits do not depend on the version.** If `f ∘ X = g ∘ X` almost everywhere, the
running variable has right support at `c`, and `f` and `g` have right limits `a` and `b` at `c`,
then `a = b`. -/
theorem tendsto_right_unique_of_ae_eq {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} {c a b : ℝ} {f g : ℝ → ℝ} (hfg : f ∘ X =ᵐ[μ] g ∘ X)
    (hsupp : RightSupport μ X c) (hf : Tendsto f (𝓝[>] c) (𝓝 a))
    (hg : Tendsto g (𝓝[>] c) (𝓝 b)) : a = b := by
  by_contra hab
  have hev : ∀ᶠ x in 𝓝[>] c, f x - g x ≠ 0 :=
    (hf.sub hg).eventually (eventually_ne_nhds (sub_ne_zero.mpr hab))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine hsupp (u - c) (sub_pos.mpr hu) (measure_mono_null ?_ (ae_iff.mp hfg))
  intro ω hω
  have hω' : X ω ∈ Set.Ioo c u := by simpa using hω
  exact fun h => hsub hω' (sub_eq_zero.mpr h)

/-- **Left limits do not depend on the version.** If `f ∘ X = g ∘ X` almost everywhere, the
running variable has left support at `c`, and `f` and `g` have left limits `a` and `b` at `c`,
then `a = b`. -/
theorem tendsto_left_unique_of_ae_eq {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} {c a b : ℝ} {f g : ℝ → ℝ} (hfg : f ∘ X =ᵐ[μ] g ∘ X)
    (hsupp : LeftSupport μ X c) (hf : Tendsto f (𝓝[<] c) (𝓝 a))
    (hg : Tendsto g (𝓝[<] c) (𝓝 b)) : a = b := by
  by_contra hab
  have hev : ∀ᶠ x in 𝓝[<] c, f x - g x ≠ 0 :=
    (hf.sub hg).eventually (eventually_ne_nhds (sub_ne_zero.mpr hab))
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  refine hsupp (c - l) (sub_pos.mpr hl) (measure_mono_null ?_ (ae_iff.mp hfg))
  intro ω hω
  have hω' : X ω ∈ Set.Ioo l c := by simpa using hω
  exact fun h => hsub hω' (sub_eq_zero.mpr h)

/-- **Sharp regression discontinuity identification from the observed law.** On a probability
space with measurable running variable `X`, integrable potential outcomes `Y1`, `Y0`, and observed
outcome `Y = if c ≤ X then Y1 else Y0`, assume:
* `m1 ∘ X` and `m0 ∘ X` are versions of `E[Y1 | σ(X)]` and `E[Y0 | σ(X)]`, with `m1`
  right-continuous at `c` and `m0` left-continuous at `c`;
* the running variable has mass on both sides arbitrarily close to `c` (`RightSupport` and
  `LeftSupport`).
Let `r` be any function with `r ∘ X` a version of `E[Y | σ(X)]` and with right and left limits
`yPlus` and `yMinus` at `c`. Then `yPlus - yMinus = m1 c - m0 c`. Since `r` is an arbitrary
version, the jump on the left side is a functional of the joint law of `(X, Y)`. -/
theorem sharp_rd_identification_of_condExp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {Y1 Y0 : Ω → ℝ}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) {c : ℝ} {m1 m0 : ℝ → ℝ}
    (h1 : μ[Y1 | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m1 ∘ X)
    (h0 : μ[Y0 | MeasurableSpace.comap X inferInstance] =ᵐ[μ] m0 ∘ X)
    (hm1 : Tendsto m1 (𝓝[>] c) (𝓝 (m1 c))) (hm0 : Tendsto m0 (𝓝[<] c) (𝓝 (m0 c)))
    (hright : RightSupport μ X c) (hleft : LeftSupport μ X c) {r : ℝ → ℝ}
    (hr : r ∘ X =ᵐ[μ]
      μ[fun ω => if c ≤ X ω then Y1 ω else Y0 ω | MeasurableSpace.comap X inferInstance])
    {yPlus yMinus : ℝ} (hPlus : Tendsto r (𝓝[>] c) (𝓝 yPlus))
    (hMinus : Tendsto r (𝓝[<] c) (𝓝 yMinus)) :
    yPlus - yMinus = m1 c - m0 c := by
  have hae := hr.trans (condExp_observed_eq_observedRegression hX hY1 hY0 c h1 h0)
  rw [tendsto_right_unique_of_ae_eq hae hright hPlus (tendsto_observedRegression_right m0 hm1),
    tendsto_left_unique_of_ae_eq hae hleft hMinus (tendsto_observedRegression_left m1 hm0)]

/-! ### Counterexample: the support condition cannot be dropped -/

/-- The law of the running variable in the support counterexample: uniform on `(-1, 0)`, so it
has left support but no right support at the cutoff `0`. -/
noncomputable def supportCounterexampleLaw : Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Ioo (-1) 0)

/-- Treated mean function of the second admissible model in the support counterexample: `0`
below the cutoff `0` and `1` at and above it. It is right-continuous at `0`. -/
noncomputable def supportCounterexampleM1 (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

/-- **Counterexample: identification fails without support on both sides.** Take the cutoff
`0`, the probability space `ℝ` with the uniform law on `(-1, 0)`, running variable `X = id`, and
potential outcomes `Y1 = Y0 = 0`. The running variable has left support but not right support at
`0`. Both pairs `(m1, m0) = (0, 0)` and `(m1, m0) = (supportCounterexampleM1, 0)` are versions of
`E[Y1 | σ(X)]` and `E[Y0 | σ(X)]` and satisfy the one-sided continuity hypotheses of
`sharp_rd_identification_of_condExp`, yet their effects at the cutoff are `0` and `1`. So one and
the same joint law of `(X, Y1, Y0)` is compatible with two different cutoff effects, and the
right support hypothesis cannot be dropped. -/
theorem sharp_rd_support_counterexample :
    IsProbabilityMeasure supportCounterexampleLaw ∧
    LeftSupport supportCounterexampleLaw id 0 ∧ ¬ RightSupport supportCounterexampleLaw id 0 ∧
    supportCounterexampleLaw[(0 : ℝ → ℝ) | MeasurableSpace.comap id inferInstance]
      =ᵐ[supportCounterexampleLaw] (fun _ : ℝ => (0 : ℝ)) ∘ id ∧
    supportCounterexampleLaw[(0 : ℝ → ℝ) | MeasurableSpace.comap id inferInstance]
      =ᵐ[supportCounterexampleLaw] supportCounterexampleM1 ∘ id ∧
    Tendsto supportCounterexampleM1 (𝓝[>] 0) (𝓝 (supportCounterexampleM1 0)) ∧
    (fun _ : ℝ => (0 : ℝ)) 0 - (fun _ : ℝ => (0 : ℝ)) 0 = 0 ∧
    supportCounterexampleM1 0 - (fun _ : ℝ => (0 : ℝ)) 0 = 1 := by
  refine ⟨⟨?_⟩, ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num [supportCounterexampleM1]⟩
  · simp [supportCounterexampleLaw, Real.volume_Ioo]
  · intro ε hε
    rw [supportCounterexampleLaw, Set.preimage_id,
      Measure.restrict_apply measurableSet_Ioo, Set.Ioo_inter_Ioo, Real.volume_Ioo]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, min_self, zero_sub, neg_pos, max_lt_iff]
    exact ⟨by linarith, by norm_num⟩
  · intro h
    refine h 1 one_pos ?_
    rw [supportCounterexampleLaw, Set.preimage_id,
      Measure.restrict_apply measurableSet_Ioo, Set.Ioo_inter_Ioo, Real.volume_Ioo]
    simp
  · rw [condExp_zero]
    rfl
  · rw [condExp_zero, supportCounterexampleLaw,
      Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun x hx => ?_
    simp [supportCounterexampleM1, not_le.mpr hx.2]
  · refine tendsto_nhdsWithin_congr (fun x hx => ?_) tendsto_const_nhds
    simp [supportCounterexampleM1, le_of_lt (Set.mem_Ioi.mp hx)]

end RD

end CausalInference
