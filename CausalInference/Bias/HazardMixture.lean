/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.EffectMeasures
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Hazards of mixtures of exponential laws: frailty selection in continuous time

**Time scale: continuous.** Time is `t : ℝ` and the laws are given by their survival functions
on the real line. Statements are made for all real `t` where they hold there; their survival
reading is for `t ≥ 0`. The discrete-time survival layer is `CausalInference.Survival`.

A population is a finite mixture of strata `i` with weights `p i` (nonnegative, summing to one;
`EffectMeasure.IsWeights`), and within stratum `i` the event time is exponential with constant
hazard `r i`. The population survival is `S(t) = ∑ i, p i exp (-r i t)` (`mixSurvival`), the
population hazard is `h = -S' / S` (`mixHazard`, `mixHazard_eq_neg_deriv_div`), and the
population cumulative hazard is `H = -log S` (`mixCumHazard`, with `H' = h`).

## Main results

* `mixHazard_eq_sum_survivorWeight`: `h(t)` is the average of the stratum hazards over the
  survivors at `t` (`survivorWeight`); the continuous analogue of `hazard2_eq_weighted` in
  `CausalInference.Bias.HazardRatio`.
* `hasDerivAt_mixHazard_eq_neg_var`: `h'(t)` is minus the variance of the stratum hazard
  among the survivors at `t` (via Lagrange's identity `two_mul_weighted_var`).
* `mixHazard_antitone`, `mixHazard_strictAnti`: constant but heterogeneous hazards give a
  nonincreasing population hazard, strictly decreasing as soon as two strata of positive
  weight have different hazards.
* Treatment multiplying every stratum hazard by `ψ` (a conditional hazard ratio `ψ`, constant
  in time, with the stratifier independent of treatment): `mixSurvival_mul`,
  `mixHazard_mul`, `mixCumHazard_mul` (`S₁(t) = S₀(ψ t)`, `h₁(t) = ψ h₀(ψ t)`).
* `mixCumHazard_attenuation_of_nonneg`, `mixCumHazard_ratio_mem_of_nonneg`: for `ψ > 1`, rates
  nonnegative on the strata of positive weight, two strata of positive weight with different
  rates, and `t > 0`, the marginal cumulative hazard ratio `H₁(t) / H₀(t)` lies strictly between
  `1` and `ψ`. A cured stratum (rate `0`) is allowed
  (`HazardMixtureExample.cured_cumHazard_ratio_mem`). `mixCumHazard_attenuation` and
  `mixCumHazard_ratio_mem` are the special cases with every rate positive.
* The protective mirror: `mixCumHazard_attenuation_of_lt_one`,
  `mixCumHazard_ratio_mem_of_lt_one` (for `0 < ψ < 1`, `ψ < H₁(t) / H₀(t) < 1`) and
  `lt_mixHazard_ratio_of_lt_one` (`ψ < h₁(t) / h₀(t)`).
* `mixHazard_ratio_lt_of_nonneg`, `mixHazard_ratio_lt`, `mixHazard_ratio_zero`,
  `tendsto_mixHazard_ratio`: the marginal instantaneous hazard ratio `h₁(t) / h₀(t)` is below
  `ψ > 1` for `t > 0`, and, with every rate positive, equals `ψ` at `t = 0` and tends to `ψ` as
  `t → 0`.
* `HazardMixtureExample.marginal_hazardRatio_lt_one`: the marginal instantaneous hazard ratio
  is not confined to the interval between `1` and `ψ`. Strata of equal weight with hazards
  `1/1000` and `1`, `ψ = 2`: at `t = 5` the marginal hazard ratio is below `1`, while the
  cumulative hazard ratio is between `1` and `2`. So "attenuation toward the null" holds for
  the cumulative hazard ratio but not for the instantaneous one, which can cross the null.

All results are about population quantities. The NICE DSU text speaks of estimates from
pooled data; the formal results here say what those estimates target, not how they are
computed. Only finite mixtures are treated; a general frailty distribution is not.

## Sources

* NICE DSU Technical Support Document 2, S. Dias, N. J. Welton, A. J. Sutton, A. E. Ades
  (2011, last updated 2016), Section 3.1: in populations with constant but heterogeneous rates
  the average hazard must decrease over time, as those with higher hazard rates reach their
  end points earlier and exit from the risk set.
* NICE DSU Technical Support Document 3, S. Dias, A. J. Sutton, N. J. Welton, A. E. Ades
  (2011, last updated 2012), Section 1.1.5 (aggregation bias): pooling over a covariate that
  modifies the baseline risk but not the treatment effect biases the treatment effect toward
  the null, a particular danger in survival analysis.
* The discrete two-period version of the selection mechanism is
  `CausalInference.Bias.HazardRatio` (Hernán and Robins, *Causal Inference: What If*,
  Technical Point 8.1).
-/

@[expose] public section

open Finset Filter Topology

namespace CausalInference

namespace Bias

namespace HazardMixture

open EffectMeasure

variable {ι : Type*} [Fintype ι]

/-- The survival function of a finite mixture of exponential laws: component `i` has weight
`p i` and constant hazard `r i`, and `S(t) = ∑ i, p i * exp (-(r i * t))`. It is the survival
function of a law on `[0, ∞]` when the weights form a distribution and every `r i ≥ 0` (a
stratum with `r i = 0` never has the event); the results that need this say so. -/
noncomputable def mixSurvival (p r : ι → ℝ) (t : ℝ) : ℝ := ∑ i, p i * Real.exp (-(r i * t))

/-- The density of the mixture, `f(t) = ∑ i, p i * r i * exp (-(r i * t))`, which is `-S'(t)`
(`hasDerivAt_mixSurvival`). -/
noncomputable def mixDensity (p r : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * r i * Real.exp (-(r i * t))

/-- The auxiliary sum `∑ i, p i * r i ^ 2 * exp (-(r i * t))`, which is `-f'(t)`. -/
noncomputable def mixSecond (p r : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * r i ^ 2 * Real.exp (-(r i * t))

/-- The population hazard of the mixture, `h(t) = f(t) / S(t)`. With weights summing to one
the survival is positive (`mixSurvival_pos`), so this is a genuine ratio, equal to
`-S'(t) / S(t)`. -/
noncomputable def mixHazard (p r : ι → ℝ) (t : ℝ) : ℝ := mixDensity p r t / mixSurvival p r t

/-- The population cumulative hazard of the mixture, `H(t) = -log S(t)`. -/
noncomputable def mixCumHazard (p r : ι → ℝ) (t : ℝ) : ℝ := -Real.log (mixSurvival p r t)

/-- The derivative of one stratum term: `(c exp (-a t))' = -c a exp (-a t)`. -/
theorem hasDerivAt_expTerm (c a t : ℝ) :
    HasDerivAt (fun t => c * Real.exp (-(a * t))) (-(c * a * Real.exp (-(a * t)))) t := by
  have := (((hasDerivAt_id t).const_mul a).neg.exp).const_mul c
  convert this using 1
  · funext x; simp
  · simp; ring

/-- `S' = -f`: the density is minus the derivative of the survival function. -/
theorem hasDerivAt_mixSurvival (p r : ι → ℝ) (t : ℝ) :
    HasDerivAt (mixSurvival p r) (-mixDensity p r t) t := by
  have := HasDerivAt.sum (u := univ) fun i _ => hasDerivAt_expTerm (p i) (r i) t
  unfold mixSurvival mixDensity
  convert this using 1
  · ext t; simp
  · simp [Finset.sum_neg_distrib]

/-- `f' = -Q` with `Q = mixSecond`. -/
theorem hasDerivAt_mixDensity (p r : ι → ℝ) (t : ℝ) :
    HasDerivAt (mixDensity p r) (-mixSecond p r t) t := by
  have := HasDerivAt.sum (u := univ) fun i _ => hasDerivAt_expTerm (p i * r i) (r i) t
  unfold mixDensity mixSecond
  convert this using 1
  · ext t; simp
  · simp only [Finset.sum_neg_distrib, neg_inj]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Weights summing to one have a positive entry. -/
theorem exists_pos_of_isWeights {p : ι → ℝ} (hp : IsWeights p) : ∃ i, 0 < p i := by
  by_contra h
  push Not at h
  have : ∑ i, p i ≤ 0 := Finset.sum_nonpos fun i _ => h i
  linarith [hp.2]

/-- The survival of the mixture is positive at every time. -/
theorem mixSurvival_pos {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) (t : ℝ) :
    0 < mixSurvival p r t := by
  obtain ⟨i, hi⟩ := exists_pos_of_isWeights hp
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hp.1 j) (Real.exp_pos _).le)
    ⟨i, mem_univ _, mul_pos hi (Real.exp_pos _)⟩

/-- Everybody is alive at time `0`: `S(0) = 1`. -/
theorem mixSurvival_zero {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) : mixSurvival p r 0 = 1 := by
  simp [mixSurvival, hp.2]

/-- The hazard is `-S'/S`, as the derivative of the survival function says. -/
theorem mixHazard_eq_neg_deriv_div {p : ι → ℝ} (r : ι → ℝ) (t : ℝ) :
    mixHazard p r t = -deriv (mixSurvival p r) t / mixSurvival p r t := by
  rw [(hasDerivAt_mixSurvival p r t).deriv, neg_neg, mixHazard]

/-- The derivative of the population hazard:
`h'(t) = -(S(t) * Q(t) - f(t) ^ 2) / S(t) ^ 2` with `Q = mixSecond`. -/
theorem hasDerivAt_mixHazard {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) (t : ℝ) :
    HasDerivAt (mixHazard p r)
      (-(mixSurvival p r t * mixSecond p r t - mixDensity p r t ^ 2) / mixSurvival p r t ^ 2)
      t := by
  have := (hasDerivAt_mixDensity p r t).div (hasDerivAt_mixSurvival p r t)
    (mixSurvival_pos hp r t).ne'
  convert this using 1
  · rfl
  · ring

/-- Lagrange's identity for weighted sums:
`2 ((∑ a) (∑ a x²) - (∑ a x)²) = ∑ i, ∑ j, a i a j (x i - x j)²`. -/
theorem two_mul_weighted_var (a x : ι → ℝ) :
    2 * ((∑ i, a i) * (∑ i, a i * x i ^ 2) - (∑ i, a i * x i) ^ 2) =
      ∑ i, ∑ j, a i * a j * (x i - x j) ^ 2 := by
  have e : ∀ i j, a i * a j * (x i - x j) ^ 2 =
      a i * x i ^ 2 * a j + a i * (a j * x j ^ 2) - 2 * (a i * x i * (a j * x j)) := by
    intros; ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

/-- The distribution of the components among the survivors at time `t`:
`w t i = p i * exp (-(r i * t)) / S(t)`, the probability of component `i` given `T > t`. -/
noncomputable def survivorWeight (p r : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  p i * Real.exp (-(r i * t)) / mixSurvival p r t

/-- The survivor weights form a probability distribution at every time. -/
theorem isWeights_survivorWeight {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) (t : ℝ) :
    IsWeights (survivorWeight p r t) := by
  have hS := mixSurvival_pos hp r t
  refine ⟨fun i => div_nonneg (mul_nonneg (hp.1 i) (Real.exp_pos _).le) hS.le, ?_⟩
  simp only [survivorWeight]
  rw [← Finset.sum_div, div_eq_one_iff_eq hS.ne']
  rfl

/-- The population hazard is the average of the component hazards over the survivors at `t`:
`h(t) = ∑ i, w t i * r i`. This is the continuous-time form of `hazard2_eq_weighted` in
`CausalInference.Bias.HazardRatio`. -/
theorem mixHazard_eq_sum_survivorWeight (p r : ι → ℝ) (t : ℝ) :
    mixHazard p r t = ∑ i, survivorWeight p r t i * r i := by
  simp only [mixHazard, mixDensity, survivorWeight, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Lagrange's identity for the numerator of `h'`, with the unnormalized survivor weights
`p i exp (-r i t)`. -/
theorem two_mul_hazardNumerator (p r : ι → ℝ) (t : ℝ) :
    2 * (mixSurvival p r t * mixSecond p r t - mixDensity p r t ^ 2) =
      ∑ i, ∑ j, p i * Real.exp (-(r i * t)) * (p j * Real.exp (-(r j * t))) *
        (r i - r j) ^ 2 := by
  have h1 : mixSecond p r t = ∑ i, p i * Real.exp (-(r i * t)) * r i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : mixDensity p r t = ∑ i, p i * Real.exp (-(r i * t)) * r i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  exact two_mul_weighted_var _ r

/-- **The population hazard decreases at the rate of the survivors' variance of the rates**:
`h'(t) = -(∑ i, w t i * r i ^ 2 - (∑ i, w t i * r i) ^ 2)`, minus the variance of the component
hazard under the survivor weights `w t`. -/
theorem hasDerivAt_mixHazard_eq_neg_var {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) (t : ℝ) :
    HasDerivAt (mixHazard p r)
      (-(∑ i, survivorWeight p r t i * r i ^ 2 - (∑ i, survivorWeight p r t i * r i) ^ 2))
      t := by
  convert hasDerivAt_mixHazard hp r t using 1
  have hS := (mixSurvival_pos hp r t).ne'
  have e1 : ∑ i, survivorWeight p r t i * r i ^ 2 = mixSecond p r t / mixSurvival p r t := by
    simp only [mixSecond, survivorWeight, div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, ← mixHazard_eq_sum_survivorWeight, mixHazard]
  field_simp

/-- `S Q - f ^ 2 ≥ 0`: the unnormalized survivors' variance of the rates is nonnegative. -/
theorem hazardNumerator_nonneg {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) (t : ℝ) :
    0 ≤ mixSurvival p r t * mixSecond p r t - mixDensity p r t ^ 2 := by
  have h := two_mul_hazardNumerator p r t
  have : 0 ≤ ∑ i, ∑ j, p i * Real.exp (-(r i * t)) * (p j * Real.exp (-(r j * t))) *
      (r i - r j) ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    have := hp.1 i; have := hp.1 j; positivity
  linarith

/-- `S Q - f ^ 2 > 0` when two strata of positive weight have different rates. -/
theorem hazardNumerator_pos {p r : ι → ℝ} (t : ℝ) (hp : IsWeights p) {i j : ι} (hi : 0 < p i)
    (hj : 0 < p j) (hij : r i ≠ r j) :
    0 < mixSurvival p r t * mixSecond p r t - mixDensity p r t ^ 2 := by
  have h := two_mul_hazardNumerator p r t
  have hterm : ∀ k l, 0 ≤ p k * Real.exp (-(r k * t)) * (p l * Real.exp (-(r l * t))) *
      (r k - r l) ^ 2 := fun k l => by have := hp.1 k; have := hp.1 l; positivity
  have hle := (Finset.single_le_sum (fun l _ => hterm i l) (mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hterm k l) (mem_univ i))
  have hne : r i - r j ≠ 0 := sub_ne_zero.2 hij
  have : 0 < p i * Real.exp (-(r i * t)) * (p j * Real.exp (-(r j * t))) * (r i - r j) ^ 2 := by
    positivity
  linarith

/-- **Constant but heterogeneous hazards give a nonincreasing population hazard** (NICE DSU
TSD 2, Section 3.1). -/
theorem mixHazard_antitone {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) :
    Antitone (mixHazard p r) := by
  refine antitone_of_hasDerivAt_nonpos (hasDerivAt_mixHazard hp r) fun t => ?_
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (hazardNumerator_nonneg hp r t))
    (sq_nonneg _)

/-- **The population hazard is strictly decreasing** as soon as two components of positive
weight have different hazards (NICE DSU TSD 2, Section 3.1: those with higher hazard rates
reach their end points earlier and exit from the risk set). -/
theorem mixHazard_strictAnti {p r : ι → ℝ} (hp : IsWeights p) {i j : ι} (hi : 0 < p i)
    (hj : 0 < p j) (hij : r i ≠ r j) : StrictAnti (mixHazard p r) := by
  refine strictAnti_of_hasDerivAt_neg (hasDerivAt_mixHazard hp r) fun t => ?_
  have := hazardNumerator_pos t hp hi hj hij
  have := mixSurvival_pos hp r t
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-! ### Proportional hazards within strata, and the marginal comparison -/

/-- The density is positive when every component hazard is positive. -/
theorem mixDensity_pos {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ i, 0 < r i) (t : ℝ) :
    0 < mixDensity p r t := by
  obtain ⟨i, hi⟩ := exists_pos_of_isWeights hp
  exact Finset.sum_pos' (fun j _ => by have := hp.1 j; have := hr j; positivity)
    ⟨i, mem_univ _, by have := hr i; positivity⟩

/-- The population hazard is positive when every component hazard is positive. -/
theorem mixHazard_pos {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ i, 0 < r i) (t : ℝ) :
    0 < mixHazard p r t :=
  div_pos (mixDensity_pos hp hr t) (mixSurvival_pos hp r t)

/-- Multiplying every component hazard by `ψ` (treated stratum hazard `ψ * r i`, control
stratum hazard `r i`) rescales time in the population survival: `S₁(t) = S₀(ψ t)`. -/
theorem mixSurvival_mul (p r : ι → ℝ) (ψ t : ℝ) :
    mixSurvival p (fun i => ψ * r i) t = mixSurvival p r (ψ * t) :=
  Finset.sum_congr rfl fun i _ => by ring_nf

/-- The population hazard of the treated arm: `h₁(t) = ψ * h₀(ψ t)`. -/
theorem mixHazard_mul (p r : ι → ℝ) (ψ t : ℝ) :
    mixHazard p (fun i => ψ * r i) t = ψ * mixHazard p r (ψ * t) := by
  have hD : mixDensity p (fun i => ψ * r i) t = ψ * mixDensity p r (ψ * t) := by
    simp only [mixDensity, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  rw [mixHazard, mixHazard, hD, mixSurvival_mul, mul_div_assoc]

/-- The population cumulative hazard of the treated arm: `H₁(t) = H₀(ψ t)`. -/
theorem mixCumHazard_mul (p r : ι → ℝ) (ψ t : ℝ) :
    mixCumHazard p (fun i => ψ * r i) t = mixCumHazard p r (ψ * t) := by
  rw [mixCumHazard, mixCumHazard, mixSurvival_mul]

/-- `H(0) = 0`. -/
theorem mixCumHazard_zero {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) :
    mixCumHazard p r 0 = 0 := by
  rw [mixCumHazard, mixSurvival_zero hp, Real.log_one, neg_zero]

/-- The cumulative hazard is an antiderivative of the hazard: `H' = h`. -/
theorem hasDerivAt_mixCumHazard {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) (t : ℝ) :
    HasDerivAt (mixCumHazard p r) (mixHazard p r t) t := by
  have := ((hasDerivAt_mixSurvival p r t).log (mixSurvival_pos hp r t).ne').neg
  convert this using 1
  · rfl
  · rw [neg_div, neg_neg]
    rfl

/-- The density is positive when the rates are nonnegative on the support of the weights and
one stratum of positive weight has a positive rate. -/
theorem mixDensity_pos_of_support {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ k, 0 < p k → 0 ≤ r k) {i : ι} (hi : 0 < p i) (hri : 0 < r i) (t : ℝ) :
    0 < mixDensity p r t := by
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, mem_univ _, by positivity⟩
  rcases (hp.1 j).eq_or_lt with h | h
  · rw [← h]; simp
  · have := hr j h; positivity

/-- Two distinct nonnegative rates on positive-weight strata give a positive density: one of the
two rates is positive. -/
theorem mixDensity_pos_of_ne {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ k, 0 < p k → 0 ≤ r k)
    {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j) (t : ℝ) :
    0 < mixDensity p r t := by
  rcases (hr i hi).eq_or_lt with h | h
  · exact mixDensity_pos_of_support hp hr hj (lt_of_le_of_ne (hr j hj) (h ▸ hij)) t
  · exact mixDensity_pos_of_support hp hr hi h t

/-- The population hazard is positive under the hypotheses of `mixDensity_pos_of_ne`. -/
theorem mixHazard_pos_of_ne {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ k, 0 < p k → 0 ≤ r k)
    {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j) (t : ℝ) :
    0 < mixHazard p r t :=
  div_pos (mixDensity_pos_of_ne hp hr hi hj hij t) (mixSurvival_pos hp r t)

/-- **Attenuation of the cumulative hazard ratio, rates on the support** (NICE DSU TSD 3,
Section 1.1.5, aggregation bias). Within every stratum `i` of a factor independent of treatment
the hazards are constant, `r i` without and `ψ * r i` with treatment, so the conditional hazard
ratio is `ψ > 1` at every time. Assume the rates are nonnegative on the strata of positive weight
(a stratum of rate `0` is a cured stratum) and two strata of positive weight have different
rates. Then at every `t > 0` the marginal cumulative hazards satisfy
`0 < H₀(t) < H₁(t) < ψ * H₀(t)`: the marginal cumulative hazard ratio lies strictly between `1`
and `ψ`. Rates on strata of weight zero are unrestricted. -/
theorem mixCumHazard_attenuation_of_nonneg {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ k, 0 < p k → 0 ≤ r k) {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j)
    {ψ : ℝ} (hψ : 1 < ψ) {t : ℝ} (ht : 0 < t) :
    0 < mixCumHazard p r t ∧ mixCumHazard p r t < mixCumHazard p (fun k => ψ * r k) t ∧
      mixCumHazard p (fun k => ψ * r k) t < ψ * mixCumHazard p r t := by
  have hH := hasDerivAt_mixCumHazard hp r
  have hmono : StrictMono (mixCumHazard p r) :=
    strictMono_of_hasDerivAt_pos hH fun s =>
      div_pos (mixDensity_pos_of_ne hp hr hi hj hij s) (mixSurvival_pos hp r s)
  have hanti := mixHazard_strictAnti hp hi hj hij
  have h0 := mixCumHazard_zero hp r
  have hψt : t < ψ * t := by nlinarith
  rw [mixCumHazard_mul]
  refine ⟨h0 ▸ hmono ht, hmono hψt, ?_⟩
  -- `g s = ψ H₀(s) - H₀(ψ s)` vanishes at `0` and increases on `(0, t)`.
  set g : ℝ → ℝ := fun s => ψ * mixCumHazard p r s - mixCumHazard p r (ψ * s) with hg
  have hg' : ∀ s, HasDerivAt g (ψ * mixHazard p r s - ψ * mixHazard p r (ψ * s)) s := by
    intro s
    have h2 := (hH (ψ * s)).comp s ((hasDerivAt_id s).const_mul ψ)
    convert ((hH s).const_mul ψ).sub h2 using 1
    · rfl
    · simp only [mul_one]; ring
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g _ ht
    (fun s _ => (hg' s).continuousAt.continuousWithinAt) fun s _ => hg' s
  have hc0 : 0 < c := hc.1
  have hpos : 0 < ψ * mixHazard p r c - ψ * mixHazard p r (ψ * c) := by
    have : mixHazard p r (ψ * c) < mixHazard p r c := hanti (by nlinarith)
    nlinarith
  have hg0 : g 0 = 0 := by simp only [hg, mul_zero, h0, sub_zero]
  rw [hg0, sub_zero, sub_zero, eq_div_iff ht.ne'] at hslope
  have : 0 < g t := by rw [← hslope]; positivity
  simp only [hg] at this
  linarith

/-- **Attenuation of the cumulative hazard ratio** with positive rates in every stratum: the
special case of `mixCumHazard_attenuation_of_nonneg`. Under the hypotheses at every `t > 0`,
`0 < H₀(t) < H₁(t) < ψ * H₀(t)`. -/
theorem mixCumHazard_attenuation {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ i, 0 < r i)
    {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j) {ψ : ℝ} (hψ : 1 < ψ) {t : ℝ}
    (ht : 0 < t) :
    0 < mixCumHazard p r t ∧ mixCumHazard p r t < mixCumHazard p (fun k => ψ * r k) t ∧
      mixCumHazard p (fun k => ψ * r k) t < ψ * mixCumHazard p r t :=
  mixCumHazard_attenuation_of_nonneg hp (fun k _ => (hr k).le) hi hj hij hψ ht

/-- The cumulative hazard ratio form of `mixCumHazard_attenuation_of_nonneg`:
`1 < H₁(t) / H₀(t) < ψ` for `t > 0`, with nonnegative rates on the support and two distinct
supported rates. -/
theorem mixCumHazard_ratio_mem_of_nonneg {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ k, 0 < p k → 0 ≤ r k) {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j)
    {ψ : ℝ} (hψ : 1 < ψ) {t : ℝ} (ht : 0 < t) :
    1 < mixCumHazard p (fun k => ψ * r k) t / mixCumHazard p r t ∧
      mixCumHazard p (fun k => ψ * r k) t / mixCumHazard p r t < ψ := by
  obtain ⟨h0, h1, h2⟩ := mixCumHazard_attenuation_of_nonneg hp hr hi hj hij hψ ht
  exact ⟨(one_lt_div h0).2 h1, (div_lt_iff₀ h0).2 h2⟩

/-- The cumulative hazard ratio form of `mixCumHazard_attenuation`:
`1 < H₁(t) / H₀(t) < ψ` for `t > 0`. -/
theorem mixCumHazard_ratio_mem {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ i, 0 < r i)
    {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j) {ψ : ℝ} (hψ : 1 < ψ) {t : ℝ}
    (ht : 0 < t) :
    1 < mixCumHazard p (fun k => ψ * r k) t / mixCumHazard p r t ∧
      mixCumHazard p (fun k => ψ * r k) t / mixCumHazard p r t < ψ :=
  mixCumHazard_ratio_mem_of_nonneg hp (fun k _ => (hr k).le) hi hj hij hψ ht

/-- **The marginal instantaneous hazard ratio is below the conditional one**, rates on the
support: under the hypotheses of `mixCumHazard_attenuation_of_nonneg`, `h₁(t) / h₀(t) < ψ` at
every `t > 0`. It need not stay above `1`: `HazardMixtureExample.marginal_hazardRatio_lt_one`. -/
theorem mixHazard_ratio_lt_of_nonneg {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ k, 0 < p k → 0 ≤ r k) {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j)
    {ψ : ℝ} (hψ : 1 < ψ) {t : ℝ} (ht : 0 < t) :
    mixHazard p (fun k => ψ * r k) t / mixHazard p r t < ψ := by
  rw [mixHazard_mul, div_lt_iff₀ (mixHazard_pos_of_ne hp hr hi hj hij t)]
  have : mixHazard p r (ψ * t) < mixHazard p r t :=
    mixHazard_strictAnti hp hi hj hij (by nlinarith)
  nlinarith

/-- **The marginal instantaneous hazard ratio is below the conditional one**: under the
hypotheses of `mixCumHazard_attenuation`, `h₁(t) / h₀(t) < ψ` at every `t > 0`. The ratio
equals `ψ` at `t = 0` (`mixHazard_ratio_zero`). It need not stay above `1`:
`HazardMixtureExample.marginal_hazardRatio_lt_one`. -/
theorem mixHazard_ratio_lt {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ i, 0 < r i)
    {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j) {ψ : ℝ} (hψ : 1 < ψ) {t : ℝ}
    (ht : 0 < t) :
    mixHazard p (fun k => ψ * r k) t / mixHazard p r t < ψ :=
  mixHazard_ratio_lt_of_nonneg hp (fun k _ => (hr k).le) hi hj hij hψ ht

omit [Fintype ι] in
/-- Treating `ψ * r` as the baseline and `ψ⁻¹` as the multiplier gives back `r`. -/
theorem inv_mul_mul_rate {r : ι → ℝ} {ψ : ℝ} (hψ : ψ ≠ 0) :
    (fun k => ψ⁻¹ * (ψ * r k)) = r := by
  funext k; field_simp

/-- **The protective mirror of the attenuation**: for a conditional hazard ratio `0 < ψ < 1`,
nonnegative rates on the support and two distinct supported rates, at every `t > 0`,
`0 < H₁(t)`, `ψ * H₀(t) < H₁(t)` and `H₁(t) < H₀(t)`: the marginal cumulative hazard ratio lies
strictly between `ψ` and `1`, again attenuated toward the null. It is
`mixCumHazard_attenuation_of_nonneg` applied to the baseline rates `ψ * r` and the multiplier
`ψ⁻¹ > 1`. -/
theorem mixCumHazard_attenuation_of_lt_one {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ k, 0 < p k → 0 ≤ r k) {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j)
    {ψ : ℝ} (hψ0 : 0 < ψ) (hψ1 : ψ < 1) {t : ℝ} (ht : 0 < t) :
    0 < mixCumHazard p (fun k => ψ * r k) t ∧
      ψ * mixCumHazard p r t < mixCumHazard p (fun k => ψ * r k) t ∧
      mixCumHazard p (fun k => ψ * r k) t < mixCumHazard p r t := by
  have hr' : ∀ k, 0 < p k → 0 ≤ ψ * r k := fun k hk => mul_nonneg hψ0.le (hr k hk)
  have hij' : ψ * r i ≠ ψ * r j := fun h => hij (mul_left_cancel₀ hψ0.ne' h)
  obtain ⟨h0, h1, h2⟩ := mixCumHazard_attenuation_of_nonneg hp hr' hi hj hij'
    (one_lt_inv₀ hψ0 |>.2 hψ1) ht
  rw [inv_mul_mul_rate hψ0.ne'] at h1 h2
  refine ⟨h0, ?_, h1⟩
  have := mul_lt_mul_of_pos_left h2 hψ0
  rwa [← mul_assoc, mul_inv_cancel₀ hψ0.ne', one_mul] at this

/-- The ratio form of `mixCumHazard_attenuation_of_lt_one`: `ψ < H₁(t) / H₀(t) < 1` for
`0 < ψ < 1` and `t > 0`. -/
theorem mixCumHazard_ratio_mem_of_lt_one {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ k, 0 < p k → 0 ≤ r k) {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j)
    {ψ : ℝ} (hψ0 : 0 < ψ) (hψ1 : ψ < 1) {t : ℝ} (ht : 0 < t) :
    ψ < mixCumHazard p (fun k => ψ * r k) t / mixCumHazard p r t ∧
      mixCumHazard p (fun k => ψ * r k) t / mixCumHazard p r t < 1 := by
  obtain ⟨h0, h1, h2⟩ := mixCumHazard_attenuation_of_lt_one hp hr hi hj hij hψ0 hψ1 ht
  have hH : 0 < mixCumHazard p r t := h0.trans h2
  exact ⟨(lt_div_iff₀ hH).2 h1, (div_lt_one hH).2 h2⟩

/-- **The protective mirror for the instantaneous hazard ratio**: for `0 < ψ < 1`, nonnegative
rates on the support and two distinct supported rates, `ψ < h₁(t) / h₀(t)` at every `t > 0`. -/
theorem lt_mixHazard_ratio_of_lt_one {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ k, 0 < p k → 0 ≤ r k) {i j : ι} (hi : 0 < p i) (hj : 0 < p j) (hij : r i ≠ r j)
    {ψ : ℝ} (hψ0 : 0 < ψ) (hψ1 : ψ < 1) {t : ℝ} (ht : 0 < t) :
    ψ < mixHazard p (fun k => ψ * r k) t / mixHazard p r t := by
  have hr' : ∀ k, 0 < p k → 0 ≤ ψ * r k := fun k hk => mul_nonneg hψ0.le (hr k hk)
  have hij' : ψ * r i ≠ ψ * r j := fun h => hij (mul_left_cancel₀ hψ0.ne' h)
  have h := mixHazard_ratio_lt_of_nonneg hp hr' hi hj hij' (one_lt_inv₀ hψ0 |>.2 hψ1) ht
  rw [inv_mul_mul_rate hψ0.ne'] at h
  rw [div_lt_iff₀ (mixHazard_pos_of_ne hp hr' hi hj hij' t)] at h
  rw [lt_div_iff₀ (mixHazard_pos_of_ne hp hr hi hj hij t)]
  have := mul_lt_mul_of_pos_left h hψ0
  rwa [← mul_assoc, mul_inv_cancel₀ hψ0.ne', one_mul] at this

/-- At time `0` the marginal hazard ratio equals the conditional one: `h₁(0) / h₀(0) = ψ`. -/
theorem mixHazard_ratio_zero {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ i, 0 < r i) (ψ : ℝ) :
    mixHazard p (fun k => ψ * r k) 0 / mixHazard p r 0 = ψ := by
  rw [mixHazard_mul, mul_zero, mul_div_assoc, div_self (mixHazard_pos hp hr 0).ne', mul_one]

/-- The marginal hazard ratio tends to the conditional one as `t → 0`. -/
theorem tendsto_mixHazard_ratio {p r : ι → ℝ} (hp : IsWeights p) (hr : ∀ i, 0 < r i) (ψ : ℝ) :
    Tendsto (fun t => mixHazard p (fun k => ψ * r k) t / mixHazard p r t) (𝓝 0) (𝓝 ψ) := by
  have hc : ∀ q : ι → ℝ, Continuous (mixHazard p q) := fun q =>
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_mixHazard hp q t).continuousAt
  have := ((hc fun k => ψ * r k).continuousAt (x := 0)).div ((hc r).continuousAt (x := 0))
    (mixHazard_pos hp hr 0).ne'
  have h := this.tendsto
  rw [Pi.div_apply, mixHazard_ratio_zero hp hr ψ] at h
  exact h

namespace HazardMixtureExample

/-- Two strata of equal weight. -/
noncomputable def exWeight (_ : Bool) : ℝ := 1 / 2

/-- Baseline (control) hazards: `1/1000` in the stratum `true`, `1` in the stratum `false`. -/
noncomputable def exRate (b : Bool) : ℝ := if b then 1 / 1000 else 1

/-- The example weights form a distribution. -/
theorem isWeights_exWeight : IsWeights exWeight :=
  ⟨fun _ => by norm_num [exWeight], by norm_num [exWeight, Fintype.sum_bool]⟩

/-- The example hazards are positive. -/
theorem exRate_pos (b : Bool) : 0 < exRate b := by cases b <;> norm_num [exRate]

/-- `exp 5 < 150`. -/
theorem exp_five_lt : Real.exp 5 < 150 := by
  have h := Real.exp_nat_mul 1 5
  norm_num at h
  rw [h]
  have := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  calc Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := by gcongr
    _ < 150 := by norm_num

/-- `20000 < exp 10`. -/
theorem lt_exp_ten : 20000 < Real.exp 10 := by
  have h := Real.exp_nat_mul 1 10
  norm_num at h
  rw [h]
  have := Real.exp_one_gt_d9
  calc (20000 : ℝ) < 2.7182818283 ^ 10 := by norm_num
    _ < Real.exp 1 ^ 10 := by gcongr

/-- The population hazard of the control arm at time `t`, written out. -/
theorem exHazard_eq (t : ℝ) :
    mixHazard exWeight exRate t =
      (1 / 1000 * Real.exp (-(1 / 1000 * t)) + Real.exp (-t)) /
        (Real.exp (-(1 / 1000 * t)) + Real.exp (-t)) := by
  have hpos : 0 < Real.exp (-(1 / 1000 * t)) + Real.exp (-t) := by positivity
  simp only [mixHazard, mixDensity, mixSurvival, exWeight, exRate, Fintype.sum_bool,
    ite_true, Bool.false_eq_true, ite_false, one_mul]
  field_simp

/-- **The marginal hazard ratio can leave the interval between `1` and the conditional hazard
ratio** (counterexample to the reading of NICE DSU TSD 3, Section 1.1.5, for instantaneous
hazard ratios). Two strata of equal weight with constant control hazards `1/1000` and `1`;
treatment doubles the hazard in each stratum, so the conditional hazard ratio is `2` at every
time. At `t = 5` the marginal hazard ratio `h₁(5) / h₀(5) = 2 h₀(10) / h₀(5)` is below `1`:
the marginal comparison shows a smaller hazard in the treated arm although treatment doubles
the hazard in every stratum. The marginal cumulative hazard ratio at `t = 5` stays strictly
between `1` and `2` (`mixCumHazard_ratio_mem`). -/
theorem marginal_hazardRatio_lt_one :
    (∀ b, 2 * exRate b / exRate b = 2) ∧
      mixHazard exWeight (fun k => 2 * exRate k) 5 / mixHazard exWeight exRate 5 < 1 ∧
      1 < mixCumHazard exWeight (fun k => 2 * exRate k) 5 / mixCumHazard exWeight exRate 5 ∧
      mixCumHazard exWeight (fun k => 2 * exRate k) 5 / mixCumHazard exWeight exRate 5 < 2 := by
  have hne : exRate true ≠ exRate false := by norm_num [exRate]
  have hw : (0 : ℝ) < exWeight true := by norm_num [exWeight]
  have hw' : (0 : ℝ) < exWeight false := by norm_num [exWeight]
  refine ⟨fun b => by have := (exRate_pos b).ne'; field_simp, ?_,
    mixCumHazard_ratio_mem isWeights_exWeight exRate_pos hw hw' hne (by norm_num)
      (by norm_num)⟩
  rw [mixHazard_mul, div_lt_one (mixHazard_pos isWeights_exWeight exRate_pos 5), exHazard_eq,
    exHazard_eq]
  norm_num
  set E10 := Real.exp (-(1 / 100 : ℝ))
  set F10 := Real.exp (-(10 : ℝ)) with hF10d
  set E5 := Real.exp (-(1 / 200 : ℝ))
  set F5 := Real.exp (-(5 : ℝ)) with hF5d
  have hE10 : 99 / 100 ≤ E10 := by
    have := Real.add_one_le_exp (-(1 / 100 : ℝ)); linarith
  have hE10' : E10 ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hE5 : 0 < E5 := Real.exp_pos _
  have hE5' : E5 ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hF10 : 0 < F10 := Real.exp_pos _
  have hF10' : F10 ≤ 1 / 20000 := by
    rw [hF10d, Real.exp_neg, inv_eq_one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) lt_exp_ten.le
  have hF5 : 1 / 150 ≤ F5 := by
    rw [hF5d, Real.exp_neg, inv_eq_one_div]
    exact div_le_div_of_nonneg_left zero_le_one (Real.exp_pos _) exp_five_lt.le
  have hF5' : F5 ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hL : 2 * (1 / 1000 * E10 + F10) * (E5 + F5) ≤ 2 * (1 / 1000 + 1 / 20000) * 2 := by
    have h1 : 1 / 1000 * E10 + F10 ≤ 1 / 1000 + 1 / 20000 := by linarith
    have h2 : E5 + F5 ≤ 2 := by linarith
    have h3 : 0 ≤ 1 / 1000 * E10 + F10 := by positivity
    nlinarith
  have hR : 1 / 150 * (99 / 100) ≤ (1 / 1000 * E5 + F5) * (E10 + F10) := by
    have h1 : 1 / 150 * (99 / 100) ≤ F5 * E10 := mul_le_mul hF5 hE10 (by norm_num) (by linarith)
    nlinarith
  linarith

/-- Baseline hazards with a cured stratum: `0` in the stratum `true`, `1` in the stratum
`false`. -/
noncomputable def curedRate (b : Bool) : ℝ := if b then 0 else 1

/-- **Attenuation with a cured stratum.** Two strata of equal weight, one cured (rate `0`) and
one with rate `1`; treatment doubles the rate in each stratum. At every `t > 0` the marginal
cumulative hazard ratio lies strictly between `1` and `2`, and for the protective multiplier
`1/2` strictly between `1/2` and `1`. The positive-rate theorems do not apply here; the versions
with nonnegative rates on the support do. -/
theorem cured_cumHazard_ratio_mem {t : ℝ} (ht : 0 < t) :
    (1 < mixCumHazard exWeight (fun k => 2 * curedRate k) t / mixCumHazard exWeight curedRate t ∧
      mixCumHazard exWeight (fun k => 2 * curedRate k) t / mixCumHazard exWeight curedRate t
        < 2) ∧
    (1 / 2 < mixCumHazard exWeight (fun k => 1 / 2 * curedRate k) t /
        mixCumHazard exWeight curedRate t ∧
      mixCumHazard exWeight (fun k => 1 / 2 * curedRate k) t / mixCumHazard exWeight curedRate t
        < 1) := by
  have hr : ∀ k, 0 < exWeight k → 0 ≤ curedRate k := fun k _ => by
    cases k <;> norm_num [curedRate]
  have hw : (0 : ℝ) < exWeight true := by norm_num [exWeight]
  have hw' : (0 : ℝ) < exWeight false := by norm_num [exWeight]
  have hne : curedRate true ≠ curedRate false := by norm_num [curedRate]
  exact ⟨mixCumHazard_ratio_mem_of_nonneg isWeights_exWeight hr hw hw' hne (by norm_num) ht,
    mixCumHazard_ratio_mem_of_lt_one isWeights_exWeight hr hw hw' hne (by norm_num)
      (by norm_num) ht⟩

end HazardMixtureExample

end HazardMixture

end Bias

end CausalInference
