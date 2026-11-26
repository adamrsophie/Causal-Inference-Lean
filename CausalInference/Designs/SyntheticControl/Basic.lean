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
are indexed by a type `Tpost` of post-treatment periods. The full panel is indexed by
`Tpre ⊕ Tpost`, with observation consistency in both periods (`PanelConsistent`). Donor weights
are plain vectors `w : J → ℝ`; the simplex constraint (`w j ≥ 0`, `∑ j, w j = 1`) is imposed by
taking `w : Convexity.StdSimplex ℝ J`, Mathlib's standard simplex, and using its weights, or,
at the level of sets, by `w ∈ weightSimplex J`. (Mathlib's set `stdSimplex` is deprecated at
the pinned revision; `weightSimplex J` is the range of the weight map of `StdSimplex ℝ J`.)

## Main definitions

* `SyntheticControl.synth w Y t`: the synthetic control outcome `∑ j, w j * Y j t`.
* `SyntheticControl.fitLoss v Y₁ Y w`: the `v`-weighted fit loss
  `∑ k, v k * (Y₁ k - ∑ j, w j * Y j k) ^ 2`, used both for pre-treatment outcomes and for
  covariates (the diagonal version of the `V` matrix of Abadie and Gardeazabal).
* `SyntheticControl.preLoss Y₁ Y w`: the unweighted pre-treatment fit loss.
* `SyntheticControl.effectHat Y₁ Y w t`: the estimated effect path `Y₁ t - ∑ j, w j * Y j t`.
* `SyntheticControl.weightSimplex J`: the simplex of donor weight vectors as a set.
* `SyntheticControl.PanelConsistent`: observation consistency on the panel `Tpre ⊕ Tpost`.

## Main results

* `synth_mem_convexHull`, `le_synth`, `synth_le`, `exists_le_synth`, `exists_synth_le`:
  with simplex weights the synthetic outcome is a convex combination of donor outcomes, so it
  lies between the smallest and largest donor outcome (no extrapolation).
* `fitLoss_nonneg`, `fitLoss_eq_zero_iff`, `preLoss_eq_zero_iff`: the loss is nonnegative and,
  for strictly positive index weights `v`, vanishes exactly under exact fit;
  `fitLoss_eq_zero_iff_of_nonneg`: for nonnegative `v` it vanishes exactly under exact fit at
  the indices of positive weight.
* `convexOn_fitLoss`, `convexOn_weightSimplex_fitLoss`: the loss is convex in the weight vector.
* `exists_isMinOn_preLoss`, `exists_mem_weightSimplex_isMinOn_fitLoss`: a loss minimizer over
  the simplex exists; `convex_setOf_isMinOn_fitLoss`: the minimizers form a convex set.
* `exists_preLoss_eq_zero_iff`: simplex weights with zero pre-treatment loss exist if and only
  if the treated pre-treatment path lies in the convex hull of the donor paths.
* `effectHat_sub_effect`: the bias identity for the estimated effect.
* `effectHat_eq_effect`: exact identification when the treated unit's untreated outcome equals
  the weighted donor combination in the post period.
* `PanelConsistent.preLoss_eq_zero_iff`, `PanelConsistent.effectHat_sub_effect`: on the panel,
  zero observed pre-treatment loss is exact fit of the untreated outcomes, and the bias
  identity holds in every post-treatment period.
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

/-- With nonnegative weights `v`, the fit loss vanishes if and only if the fit is exact at every
index of positive weight; indices with `v k = 0` are unconstrained. -/
theorem fitLoss_eq_zero_iff_of_nonneg {v : K → ℝ} (hv : ∀ k, 0 ≤ v k) (Y₁ : K → ℝ)
    (Y : J → K → ℝ) (w : J → ℝ) :
    fitLoss v Y₁ Y w = 0 ↔ ∀ k, 0 < v k → Y₁ k = synth w Y k := by
  rw [fitLoss, Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hv k) (sq_nonneg _)]
  refine forall_congr' fun k => ?_
  rcases (hv k).eq_or_lt with h | h
  · simp [← h]
  · simp [h, h.ne', sub_eq_zero]

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

/-! ### The simplex as a set of weight vectors

Mathlib's set `stdSimplex ℝ J` is deprecated in favor of the bundled type `StdSimplex ℝ J`; the
set of weight vectors it describes is the range of the weight map of the bundled type. -/

variable (J) in
/-- The standard simplex of donor weights as a subset of `J → ℝ`: the weight vectors of points
of the bundled simplex `StdSimplex ℝ J`, that is, the nonnegative vectors summing to one. -/
def weightSimplex : Set (J → ℝ) :=
  Set.range fun w : StdSimplex ℝ J => ⇑w.weights

/-- A vector lies in the weight simplex if and only if it is nonnegative and sums to one. -/
theorem mem_weightSimplex {w : J → ℝ} :
    w ∈ weightSimplex J ↔ (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 := by
  rw [weightSimplex, StdSimplex.range_toFun_comp_weights]
  simp

omit [Fintype J] in
/-- The weight vector of a point of the bundled simplex lies in the weight simplex. -/
theorem weights_mem_weightSimplex (w : StdSimplex ℝ J) : ⇑w.weights ∈ weightSimplex J :=
  Set.mem_range_self w

omit [Fintype J] in
/-- The weight simplex is convex. -/
theorem convex_weightSimplex [Finite J] : Convex ℝ (weightSimplex J) := by
  have := Fintype.ofFinite J
  intro w hw w' hw' a b ha hb hab
  rw [mem_weightSimplex] at hw hw' ⊢
  refine ⟨fun j => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hw.1 j)) (mul_nonneg hb (hw'.1 j))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, hw'.2, hab]

/-- Existence of synthetic control weights, set form: for a nonempty donor pool the
`v`-weighted fit loss attains its minimum over the weight simplex. -/
theorem exists_mem_weightSimplex_isMinOn_fitLoss [Nonempty J] (v : K → ℝ) (Y₁ : K → ℝ)
    (Y : J → K → ℝ) :
    ∃ w ∈ weightSimplex J, IsMinOn (fitLoss v Y₁ Y) (weightSimplex J) w := by
  obtain ⟨w, hw⟩ := exists_isMinOn_fitLoss v Y₁ Y
  refine ⟨_, weights_mem_weightSimplex w, ?_⟩
  rintro _ ⟨w', rfl⟩
  exact hw w'

/-- With nonnegative weights `v`, the fit loss is convex on the weight simplex. -/
theorem convexOn_weightSimplex_fitLoss {v : K → ℝ} (hv : ∀ k, 0 ≤ v k) (Y₁ : K → ℝ)
    (Y : J → K → ℝ) : ConvexOn ℝ (weightSimplex J) (fitLoss v Y₁ Y) :=
  (convexOn_fitLoss hv Y₁ Y).subset (Set.subset_univ _) convex_weightSimplex

/-- With nonnegative weights `v`, the set of minimizers of the fit loss over the weight simplex
is convex. -/
theorem convex_setOf_isMinOn_fitLoss {v : K → ℝ} (hv : ∀ k, 0 ≤ v k) (Y₁ : K → ℝ)
    (Y : J → K → ℝ) :
    Convex ℝ {w | w ∈ weightSimplex J ∧ IsMinOn (fitLoss v Y₁ Y) (weightSimplex J) w} := by
  intro w hw w' hw' a b ha hb hab
  have hc := convexOn_weightSimplex_fitLoss hv Y₁ Y
  have hmem := convex_weightSimplex hw.1 hw'.1 ha hb hab
  refine ⟨hmem, fun x hx => ?_⟩
  have hle := hc.2 hw.1 hw'.1 ha hb hab
  have h1 : fitLoss v Y₁ Y w ≤ fitLoss v Y₁ Y x := hw.2 hx
  have h2 : fitLoss v Y₁ Y w' ≤ fitLoss v Y₁ Y x := hw'.2 hx
  simp only [smul_eq_mul] at hle
  have hx' : a * fitLoss v Y₁ Y x + b * fitLoss v Y₁ Y x = fitLoss v Y₁ Y x := by
    rw [← add_mul, hab, one_mul]
  change fitLoss v Y₁ Y (a • w + b • w') ≤ fitLoss v Y₁ Y x
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-! ### Exact-fit feasibility -/

/-- **Exact-fit feasibility.** Some simplex weights reproduce the treated unit's pre-treatment
path exactly (zero pre-treatment loss) if and only if that path lies in the convex hull of the
donors' pre-treatment paths. -/
theorem exists_preLoss_eq_zero_iff (Y₁ : K → ℝ) (Y : J → K → ℝ) :
    (∃ w ∈ weightSimplex J, preLoss Y₁ Y w = 0) ↔ Y₁ ∈ convexHull ℝ (Set.range Y) := by
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, h⟩
    have hY : Y₁ = synth (⇑w.weights) Y := funext ((preLoss_eq_zero_iff _ _ _).mp h)
    rw [hY]
    exact synth_path_mem_convexHull w Y
  · intro h
    have hA : convexHull ℝ (Set.range Y)
        ⊆ {x | ∃ w ∈ weightSimplex J, x = synth w Y} := by
      refine convexHull_min ?_ ?_
      · rintro _ ⟨j, rfl⟩
        classical
        refine ⟨Pi.single j 1, mem_weightSimplex.mpr ⟨fun i => ?_, by simp⟩, ?_⟩
        · by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        · ext k
          simp [synth, Pi.single_apply]
      · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ a b ha hb hab
        refine ⟨a • w + b • w', convex_weightSimplex hw hw' ha hb hab, ?_⟩
        ext k
        simp only [synth, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
          Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    obtain ⟨w, hw, hY⟩ := hA h
    exact ⟨w, hw, (preLoss_eq_zero_iff _ _ _).mpr fun k => congrFun hY k⟩

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

/-! ### The panel: pre- and post-treatment periods together

Time is indexed by `Tpre ⊕ Tpost`: `Sum.inl t` is a pre-treatment period and `Sum.inr t` a
post-treatment period. `Y0₁` is the treated unit's untreated potential outcome path, `Y1₁` its
treated potential outcome in the post-treatment periods, `Y0` the donors' untreated potential
outcome paths, and `Yobs₁`, `Yobs` the observed paths. -/

variable {Tpre : Type*}

/-- **Observation consistency on the panel.** Before treatment the treated unit is observed
untreated (no anticipation); after treatment it is observed treated; the donors are never
treated, so they are observed untreated in every period. -/
structure PanelConsistent (Yobs₁ : Tpre ⊕ Tpost → ℝ) (Yobs : J → Tpre ⊕ Tpost → ℝ)
    (Y1₁ : Tpost → ℝ) (Y0₁ : Tpre ⊕ Tpost → ℝ) (Y0 : J → Tpre ⊕ Tpost → ℝ) : Prop where
  /-- Before treatment the treated unit's observed outcome is its untreated outcome. -/
  pre : ∀ t, Yobs₁ (.inl t) = Y0₁ (.inl t)
  /-- After treatment the treated unit's observed outcome is its treated outcome. -/
  post : ∀ t, Yobs₁ (.inr t) = Y1₁ t
  /-- The donors' observed outcomes are their untreated outcomes. -/
  donor : ∀ j s, Yobs j s = Y0 j s

namespace PanelConsistent

variable {Yobs₁ : Tpre ⊕ Tpost → ℝ} {Yobs : J → Tpre ⊕ Tpost → ℝ} {Y1₁ : Tpost → ℝ}
  {Y0₁ : Tpre ⊕ Tpost → ℝ} {Y0 : J → Tpre ⊕ Tpost → ℝ}

/-- Under panel consistency, zero pre-treatment loss on the observed data is the same as exact
pre-treatment fit of the untreated potential outcomes. -/
theorem preLoss_eq_zero_iff [Fintype Tpre] (h : PanelConsistent Yobs₁ Yobs Y1₁ Y0₁ Y0)
    (w : J → ℝ) :
    preLoss (fun t : Tpre => Yobs₁ (.inl t)) (fun j t => Yobs j (.inl t)) w = 0
      ↔ ∀ t : Tpre, Y0₁ (.inl t) = synth w Y0 (.inl t) := by
  rw [SyntheticControl.preLoss_eq_zero_iff]
  simp only [synth, h.pre, h.donor]

/-- **Bias identity on the panel.** Under panel consistency, in every post-treatment period the
estimated effect computed from observed data minus the true effect `Y1₁ t - Y0₁ (inr t)` is the
counterfactual mismatch `Y0₁ (inr t) - ∑ j, w j * Y0 j (inr t)`. -/
theorem effectHat_sub_effect (h : PanelConsistent Yobs₁ Yobs Y1₁ Y0₁ Y0) (w : J → ℝ)
    (t : Tpost) :
    effectHat Yobs₁ Yobs w (.inr t) - (Y1₁ t - Y0₁ (.inr t))
      = Y0₁ (.inr t) - synth w Y0 (.inr t) := by
  have hY : Yobs = Y0 := funext fun j => funext fun s => h.donor j s
  rw [effectHat, h.post, hY]
  ring

end PanelConsistent

end SyntheticControl

end CausalInference
