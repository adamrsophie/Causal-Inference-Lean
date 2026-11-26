/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

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
* `CausalInference.RD.sharp_rd_counterexample`: with `m0` discontinuous at the cutoff, the
  observed jump differs from `m1 c - m0 c` (`CausalInference.RD.not_tendsto_counterexampleM0`
  checks the discontinuity).

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
`tendsto_observedRegression_right` and `tendsto_observedRegression_left`. -/
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
`sharp_rd_identification` cannot be dropped. -/
theorem sharp_rd_counterexample :
    Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[<] 0) (𝓝 1) ∧
    ∀ yPlus yMinus : ℝ,
      Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[>] 0) (𝓝 yPlus) →
      Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[<] 0) (𝓝 yMinus) →
      yPlus - yMinus ≠ (fun _ : ℝ => (0 : ℝ)) 0 - counterexampleM0 0 := by
  have hR : Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[>] 0) (𝓝 0) :=
    tendsto_observedRegression_right _ tendsto_const_nhds
  have hL : Tendsto (observedRegression 0 (fun _ => 0) counterexampleM0) (𝓝[<] 0) (𝓝 1) :=
    tendsto_nhdsWithin_congr (fun x hx => by
      simp [observedRegression_of_lt _ _ (Set.mem_Iio.mp hx), counterexampleM0,
        Set.mem_Iio.mp hx]) tendsto_const_nhds
  refine ⟨hR, hL, fun yPlus yMinus hPlus hMinus => ?_⟩
  rw [tendsto_nhds_unique hPlus hR, tendsto_nhds_unique hMinus hL]
  norm_num [counterexampleM0]

/-! ### Measure-theoretic bridge -/

open MeasureTheory

/-- The counterexample `m0` is indeed not left-continuous at the cutoff `0`: otherwise
`sharp_rd_identification` would contradict `sharp_rd_counterexample`. -/
theorem not_tendsto_counterexampleM0 :
    ¬ Tendsto counterexampleM0 (𝓝[<] 0) (𝓝 (counterexampleM0 0)) := fun h0 =>
  sharp_rd_counterexample.2.2 0 1 sharp_rd_counterexample.1 sharp_rd_counterexample.2.1
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

end RD

end CausalInference
