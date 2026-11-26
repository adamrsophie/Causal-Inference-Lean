/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Real

/-!
# Synthetic control: deterministic and algebraic core

We formalize the synthetic control method of Abadie and Gardeazabal (2003) and Abadie, Diamond
and Hainmueller (2010), "Synthetic control methods for comparative case studies", as an
optimization and design object. Everything here is deterministic: no sampling model, no
design-based or asymptotic inference.

Setting: one treated unit and a finite donor pool `J`. Fit losses are indexed by a finite type
`K` (the pre-treatment periods, or covariates); the effect path and the identification results
are indexed by a type `Tpost` of post-treatment periods. Donor weights are plain vectors
`w : J → ℝ`; the simplex constraint (`w j ≥ 0`, `∑ j, w j = 1`) is imposed by taking
`w : Convexity.StdSimplex ℝ J`, Mathlib's standard simplex, and using its weights.

## Main definitions

* `SyntheticControl.synth w Y t`: the synthetic control outcome `∑ j, w j * Y j t`.
* `SyntheticControl.fitLoss v Y₁ Y w`: the `v`-weighted fit loss
  `∑ k, v k * (Y₁ k - ∑ j, w j * Y j k) ^ 2`, used both for pre-treatment outcomes and for
  covariates (the diagonal version of the `V` matrix of Abadie and Gardeazabal).
* `SyntheticControl.preLoss Y₁ Y w`: the unweighted pre-treatment fit loss.
* `SyntheticControl.effectHat Y₁ Y w t`: the estimated effect path `Y₁ t - ∑ j, w j * Y j t`.

## Main results

* `synth_mem_convexHull`, `le_synth`, `synth_le`, `exists_le_synth`, `exists_synth_le`:
  with simplex weights the synthetic outcome is a convex combination of donor outcomes, so it
  lies between the smallest and largest donor outcome (no extrapolation).
* `fitLoss_nonneg`, `fitLoss_eq_zero_iff`, `preLoss_eq_zero_iff`: the loss is nonnegative and
  vanishes exactly under exact fit.
* `convexOn_fitLoss`: the loss is convex in the weight vector.
* `exists_isMinOn_preLoss`: a loss minimizer over the simplex exists.
* `effectHat_sub_effect`: the bias identity for the estimated effect.
* `effectHat_eq_effect`: exact identification when the treated unit's untreated outcome equals
  the weighted donor combination in the post period.
-/

@[expose] public section

open Convexity

namespace CausalInference

namespace SyntheticControl

variable {J K T : Type*} [Fintype J]

/-- The synthetic control outcome at time `t`: the `w`-weighted combination
`∑ j, w j * Y j t` of donor outcomes. -/
def synth (w : J → ℝ) (Y : J → T → ℝ) (t : T) : ℝ :=
  ∑ j, w j * Y j t

/-- The estimated effect path: the treated unit's observed outcome minus the synthetic control,
`Y₁ t - ∑ j, w j * Y j t`. -/
def effectHat (Y₁ : T → ℝ) (Y : J → T → ℝ) (w : J → ℝ) (t : T) : ℝ :=
  Y₁ t - synth w Y t

/-! ### No extrapolation -/

/-- With simplex weights, the synthetic outcome path lies in the convex hull of the donor
outcome paths. -/
theorem synth_path_mem_convexHull (w : StdSimplex ℝ J) (Y : J → T → ℝ) :
    synth (⇑w.weights) Y ∈ convexHull ℝ (Set.range Y) := by
  have h : synth (⇑w.weights) Y = ∑ j, w.weights j • Y j := by
    ext t
    simp [synth, Finset.sum_apply]
  rw [h]
  exact (convex_convexHull ℝ _).sum_mem (fun j _ => w.weights_nonneg j) w.total_of_fintype
    (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))

/-- With simplex weights, the synthetic outcome at time `t` lies in the convex hull of the
donor outcomes at time `t`. -/
theorem synth_mem_convexHull (w : StdSimplex ℝ J) (Y : J → T → ℝ) (t : T) :
    synth (⇑w.weights) Y t ∈ convexHull ℝ (Set.range fun j => Y j t) :=
  (convex_convexHull ℝ _).sum_mem (fun j _ => w.weights_nonneg j) w.total_of_fintype
    (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))

/-- With simplex weights, a lower bound for all donor outcomes at time `t` is a lower bound for
the synthetic outcome. -/
theorem le_synth (w : StdSimplex ℝ J) (Y : J → T → ℝ) (t : T) {m : ℝ}
    (hm : ∀ j, m ≤ Y j t) : m ≤ synth (⇑w.weights) Y t := by
  calc m = ∑ j, w.weights j * m := by rw [← Finset.sum_mul, w.total_of_fintype, one_mul]
    _ ≤ synth (⇑w.weights) Y t :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hm j) (w.weights_nonneg j)

/-- With simplex weights, an upper bound for all donor outcomes at time `t` is an upper bound
for the synthetic outcome. -/
theorem synth_le (w : StdSimplex ℝ J) (Y : J → T → ℝ) (t : T) {M : ℝ}
    (hM : ∀ j, Y j t ≤ M) : synth (⇑w.weights) Y t ≤ M := by
  calc synth (⇑w.weights) Y t ≤ ∑ j, w.weights j * M :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hM j) (w.weights_nonneg j)
    _ = M := by rw [← Finset.sum_mul, w.total_of_fintype, one_mul]

/-- With simplex weights, some donor outcome at time `t` is at most the synthetic outcome:
the synthetic outcome is at least the donor minimum. -/
theorem exists_le_synth (w : StdSimplex ℝ J) (Y : J → T → ℝ) (t : T) :
    ∃ j, Y j t ≤ synth (⇑w.weights) Y t := by
  have : Nonempty J := w.nonempty
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ (fun j => Y j t) Finset.univ_nonempty
  exact ⟨j, le_synth w Y t fun i => hj i (Finset.mem_univ i)⟩

/-- With simplex weights, some donor outcome at time `t` is at least the synthetic outcome:
the synthetic outcome is at most the donor maximum. -/
theorem exists_synth_le (w : StdSimplex ℝ J) (Y : J → T → ℝ) (t : T) :
    ∃ j, synth (⇑w.weights) Y t ≤ Y j t := by
  have : Nonempty J := w.nonempty
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => Y j t) Finset.univ_nonempty
  exact ⟨j, synth_le w Y t fun i => hj i (Finset.mem_univ i)⟩

/-! ### Fit loss -/

variable [Fintype K]

/-- The `v`-weighted fit loss of weights `w` on a finite index `K` (pre-treatment periods or
covariates): `∑ k, v k * (Y₁ k - ∑ j, w j * Y j k) ^ 2`. With `v` the diagonal of the matrix `V`
of Abadie and Gardeazabal this is their covariate-weighted criterion. -/
def fitLoss (v : K → ℝ) (Y₁ : K → ℝ) (Y : J → K → ℝ) (w : J → ℝ) : ℝ :=
  ∑ k, v k * (Y₁ k - synth w Y k) ^ 2

/-- The pre-treatment fit loss `∑ t, (Y₁ t - ∑ j, w j * Y j t) ^ 2` over a finite type of
pre-treatment periods: the fit loss with unit weights. -/
def preLoss (Y₁ : K → ℝ) (Y : J → K → ℝ) (w : J → ℝ) : ℝ :=
  fitLoss (fun _ => 1) Y₁ Y w

/-- The pre-treatment loss written out as an unweighted sum of squared residuals. -/
theorem preLoss_eq (Y₁ : K → ℝ) (Y : J → K → ℝ) (w : J → ℝ) :
    preLoss Y₁ Y w = ∑ k, (Y₁ k - synth w Y k) ^ 2 := by
  simp [preLoss, fitLoss]

/-- With nonnegative weights `v`, the fit loss is nonnegative. -/
theorem fitLoss_nonneg {v : K → ℝ} (hv : ∀ k, 0 ≤ v k) (Y₁ : K → ℝ) (Y : J → K → ℝ)
    (w : J → ℝ) : 0 ≤ fitLoss v Y₁ Y w :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hv k) (sq_nonneg _)

/-- With strictly positive weights `v`, the fit loss vanishes if and only if the fit is exact at
every index. -/
theorem fitLoss_eq_zero_iff {v : K → ℝ} (hv : ∀ k, 0 < v k) (Y₁ : K → ℝ) (Y : J → K → ℝ)
    (w : J → ℝ) : fitLoss v Y₁ Y w = 0 ↔ ∀ k, Y₁ k = synth w Y k := by
  rw [fitLoss, Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hv k).le (sq_nonneg _)]
  refine forall_congr' fun k => ?_
  simp [(hv k).ne', sub_eq_zero]

/-- The pre-treatment loss is nonnegative. -/
theorem preLoss_nonneg (Y₁ : K → ℝ) (Y : J → K → ℝ) (w : J → ℝ) : 0 ≤ preLoss Y₁ Y w :=
  fitLoss_nonneg (fun _ => zero_le_one) Y₁ Y w

/-- The pre-treatment loss vanishes if and only if the synthetic control reproduces the treated
unit's outcome in every pre-treatment period. -/
theorem preLoss_eq_zero_iff (Y₁ : K → ℝ) (Y : J → K → ℝ) (w : J → ℝ) :
    preLoss Y₁ Y w = 0 ↔ ∀ k, Y₁ k = synth w Y k :=
  fitLoss_eq_zero_iff (fun _ => zero_lt_one) Y₁ Y w

/-- With nonnegative weights `v`, the fit loss is a convex function of the weight vector on all
of `J → ℝ` (hence on the simplex). -/
theorem convexOn_fitLoss {v : K → ℝ} (hv : ∀ k, 0 ≤ v k) (Y₁ : K → ℝ) (Y : J → K → ℝ) :
    ConvexOn ℝ Set.univ (fitLoss v Y₁ Y) := by
  refine ⟨convex_univ, fun w _ w' _ a b ha hb hab => ?_⟩
  simp only [fitLoss, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have hres : Y₁ k - synth (a • w + b • w') Y k
      = a * (Y₁ k - synth w Y k) + b * (Y₁ k - synth w' Y k) := by
    simp only [synth, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    linear_combination (-Y₁ k) * hab
  rw [hres]
  have hsq : (a * (Y₁ k - synth w Y k) + b * (Y₁ k - synth w' Y k)) ^ 2
      ≤ a * (Y₁ k - synth w Y k) ^ 2 + b * (Y₁ k - synth w' Y k) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [sq_nonneg (synth w Y k - synth w' Y k), mul_nonneg ha hb]
  nlinarith [mul_le_mul_of_nonneg_left hsq (hv k)]

/-- The pre-treatment loss is a convex function of the weight vector. -/
theorem convexOn_preLoss (Y₁ : K → ℝ) (Y : J → K → ℝ) :
    ConvexOn ℝ Set.univ (preLoss Y₁ Y) :=
  convexOn_fitLoss (fun _ => zero_le_one) Y₁ Y

/-- Existence of synthetic control weights: for a nonempty donor pool there are simplex weights
minimizing the `v`-weighted fit loss over the whole simplex. The proof uses compactness of the
simplex and continuity of the loss. -/
theorem exists_isMinOn_fitLoss [Nonempty J] (v : K → ℝ) (Y₁ : K → ℝ) (Y : J → K → ℝ) :
    ∃ w : StdSimplex ℝ J, ∀ w' : StdSimplex ℝ J,
      fitLoss v Y₁ Y (⇑w.weights) ≤ fitLoss v Y₁ Y (⇑w'.weights) := by
  have hc : Continuous fun w : StdSimplex ℝ J => fitLoss v Y₁ Y (⇑w.weights) := by
    simp only [fitLoss, synth]
    fun_prop
  obtain ⟨w, -, hw⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  exact ⟨w, fun w' => hw (Set.mem_univ w')⟩

/-- Existence of a minimizer of the pre-treatment loss over the simplex. -/
theorem exists_isMinOn_preLoss [Nonempty J] (Y₁ : K → ℝ) (Y : J → K → ℝ) :
    ∃ w : StdSimplex ℝ J, ∀ w' : StdSimplex ℝ J,
      preLoss Y₁ Y (⇑w.weights) ≤ preLoss Y₁ Y (⇑w'.weights) :=
  exists_isMinOn_fitLoss _ Y₁ Y

/-! ### Bias identity and exact identification

In the post-treatment periods `Tpost`, `Y1₁` and `Y0₁` are the treated unit's treated and
untreated potential outcomes, `Yobs₁` its observed outcome, `Y0` the donors' untreated potential
outcomes and `Yobs` the donors' observed outcomes. The true effect path is `Y1₁ t - Y0₁ t`. -/

variable {Tpost : Type*}

/-- **Bias identity.** If the treated unit's observed post-treatment outcome is its treated
potential outcome and the donors' observed outcomes are their untreated potential outcomes,
then for any weights the estimated effect minus the true effect equals the counterfactual
mismatch `Y0₁ t - ∑ j, w j * Y0 j t`. No fit assumption is made. -/
theorem effectHat_sub_effect (Yobs₁ Y1₁ Y0₁ : Tpost → ℝ) (Yobs Y0 : J → Tpost → ℝ) (w : J → ℝ)
    (hcons : ∀ t, Yobs₁ t = Y1₁ t) (hdonor : ∀ j t, Yobs j t = Y0 j t) (t : Tpost) :
    effectHat Yobs₁ Yobs w t - (Y1₁ t - Y0₁ t) = Y0₁ t - synth w Y0 t := by
  have hY : Yobs = Y0 := funext fun j => funext fun t => hdonor j t
  rw [effectHat, hcons, hY]
  ring

/-- **Exact identification (deterministic).** Under the observation hypotheses of
`effectHat_sub_effect`, if at the post-treatment time `t` the treated unit's untreated potential
outcome equals the same weighted combination of the donors' untreated potential outcomes, then
the estimated effect equals the true effect `Y1₁ t - Y0₁ t`. The matching hypothesis `hmatch`
concerns unobservable counterfactuals and is the substantive assumption of the method. -/
theorem effectHat_eq_effect (Yobs₁ Y1₁ Y0₁ : Tpost → ℝ) (Yobs Y0 : J → Tpost → ℝ) (w : J → ℝ)
    (hcons : ∀ t, Yobs₁ t = Y1₁ t) (hdonor : ∀ j t, Yobs j t = Y0 j t) (t : Tpost)
    (hmatch : Y0₁ t = synth w Y0 t) :
    effectHat Yobs₁ Yobs w t = Y1₁ t - Y0₁ t := by
  have h := effectHat_sub_effect Yobs₁ Y1₁ Y0₁ Yobs Y0 w hcons hdonor t
  linarith

end SyntheticControl

end CausalInference
