/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolution
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Regularity of the sample family

The asymptotic theory of regular estimators is stated for a family `F` at a point `θ₀` under the
hypotheses `IsRegularAt θ₀`, `IsScoreRegular θ₀ r` and the identity `∂_θ ℓ(θ; z) = s(θ; z)` on the
ball. This file shows that these hypotheses pass from `F` to the family `F.pi n` of an i.i.d.
sample of size `n`, so that results proved for a general family apply to samples with no new
verification.

## Main results

* `CausalInference.abs_iteratedDeriv_prod_le`: the Leibniz bound for the first two derivatives of
  a finite product of `C²` functions.
* `CausalInference.ParametricFamily.pi_isRegularAt`: `F.pi n` is regular at a regular point of
  `F`. The density envelope `|f(θ₀; ·)| + ε b₁` comes from the mean value theorem.
* `CausalInference.ParametricFamily.pi_fisherInfo_of_isRegularAt`: its information is `n I(θ₀)`.
* `CausalInference.ParametricFamily.pi_score_hasDerivAt_of_isOpen`: where the support is constant
  the sample score and the second derivative of the sample log likelihood are sums over the
  coordinates.
* `CausalInference.ParametricFamily.pi_isScoreRegular`: `F.pi n` satisfies `IsScoreRegular θ₀ r'`
  for some `0 < r' ≤ r`, with the derivative identity, given measurability of the sample score at
  `θ₀` and of the second derivatives of the sample log likelihood. On a discrete space these hold
  (`pi_isScoreRegular_of_discrete`).

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal ContDiff

namespace CausalInference

/-! ### Bounds for a product of smooth functions -/

section ProductBounds

/-- A function with derivative bounded by `B` on the ball `ball c ε`, where it is `C²`, is
bounded there by `|g c| + ε B`. -/
lemma abs_le_of_contDiffOn_ball {g : ℝ → ℝ} {c ε B : ℝ} (hg : ContDiffOn ℝ 2 g (ball c ε))
    (hB : ∀ u ∈ ball c ε, |deriv g u| ≤ B) {u : ℝ} (hu : u ∈ ball c ε) :
    |g u| ≤ |g c| + ε * B := by
  have hc : c ∈ ball c ε := mem_ball_self (pos_of_mem_ball hu)
  have hd : ∀ v ∈ ball c ε, DifferentiableAt ℝ g v := fun v hv ↦
    (hg.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hv)
  have h := (convex_ball c ε).norm_image_sub_le_of_norm_deriv_le hd
    (fun v hv ↦ by rw [Real.norm_eq_abs]; exact hB v hv) hc hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB c hc)
  have hd' : |u - c| ≤ ε := (mem_ball_iff_norm.1 hu).le
  calc |g u| ≤ |g c| + |g u - g c| := by
        have := abs_sub_abs_le_abs_sub (g u) (g c); linarith
    _ ≤ |g c| + B * |u - c| := by linarith
    _ ≤ |g c| + ε * B := by nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The choice of an envelope by derivative order: `b₀` for the function, `b₁` for the first
derivative and `b₂` for the second. -/
def envelopeByOrder {α : Type*} (b₀ b₁ b₂ : α → ℝ) (m : ℕ) : α → ℝ :=
  if m = 0 then b₀ else if m = 1 then b₁ else b₂

/-- **Leibniz bound for a product.** If each `g j` is `C²` on an open set `s` and its derivatives
of order `0, 1, 2` are bounded at `u ∈ s` by `B 0 j, B 1 j, B 2 j`, then for `k ≤ 2` the `k`-th
derivative of `∏ j, g j` at `u` is bounded by `∑_p N(p) ∏_j B (count j p) j`, the sum over the
multisets `p` of size `k` and `N(p)` the number of their orderings. -/
lemma abs_iteratedDeriv_prod_le {g : ι → ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hg : ∀ j, ContDiffOn ℝ 2 (g j) s) {u : ℝ} (hu : u ∈ s) {B : ℕ → ι → ℝ}
    (hB : ∀ m ≤ 2, ∀ j, |iteratedDeriv m (g j) u| ≤ B m j) {k : ℕ} (hk : k ≤ 2) :
    |iteratedDeriv k (fun v ↦ ∏ j, g j v) u| ≤
      ∑ p ∈ (univ : Finset ι).sym k, ((p : Multiset ι).countPerms : ℝ) *
        ∏ j, B (Multiset.count j p) j := by
  have h := norm_iteratedFDerivWithin_prod_le (u := univ) (f := g) (N := 2)
    (fun j _ ↦ hg j) hs.uniqueDiffOn hu (n := k) (by exact_mod_cast hk)
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen hs hu, Real.norm_eq_abs] at h
  refine h.trans (Finset.sum_le_sum fun p hp ↦ ?_)
  have hcard : ∀ j, Multiset.count j p ≤ 2 := fun j ↦
    ((Multiset.count_le_card j (p : Multiset ι)).trans p.2.le).trans hk
  gcongr with j
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen hs hu, Real.norm_eq_abs]
  exact hB _ (hcard j) j

end ProductBounds

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S} [SigmaFinite F.ν] {θ₀ : ℝ}

/-- **The sample family is regular at a regular point.** If `F` is regular at `θ₀`
(`IsRegularAt`), so is the family `F.pi n` of an i.i.d. sample of size `n`. The support of the
likelihood is constant near `θ₀`, the likelihood is `C²` on the same ball, and its first two
derivatives have the envelopes given by the Leibniz rule
(`CausalInference.abs_iteratedDeriv_prod_le`) from the envelopes `b₁`, `b₂` of `F` and the
envelope `|f(θ₀; ·)| + ε b₁` of the density on the ball of radius `ε` (mean value theorem). The
score is square integrable by `pi_fisherInfo`. -/
theorem pi_isRegularAt (n : ℕ) (hreg : F.IsRegularAt θ₀) : (F.pi n).IsRegularAt θ₀ := by
  have hΘ := hreg.mem_nhds
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hΘ
  obtain ⟨ε, hε, hball, hC2, b₁, b₂, hb₁, hb₂, hbd⟩ := hreg.smooth_dominated
  obtain ⟨b₀, hb₀def⟩ : ∃ b₀ : S → ℝ, b₀ = fun y ↦ |F.density θ₀ y| + ε * b₁ y := ⟨_, rfl⟩
  have hb₀ : Integrable b₀ F.ν := by
    rw [hb₀def]; exact (F.integrable_density θ₀ hθ₀).abs.add (hb₁.const_mul ε)
  obtain ⟨Bf, hBfdef⟩ : ∃ Bf : ℕ → S → ℝ, Bf = envelopeByOrder b₀ b₁ b₂ := ⟨_, rfl⟩
  have hBf : ∀ m, Integrable (Bf m) F.ν := by
    intro m
    simp only [hBfdef, envelopeByOrder]
    split_ifs
    · exact hb₀
    · exact hb₁
    · exact hb₂
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → (Fin n → S) → ℝ, E = fun k x ↦
      ∑ p ∈ (univ : Finset (Fin n)).sym k,
        ((p : Multiset (Fin n)).countPerms : ℝ) * ∏ j, Bf (Multiset.count j p) (x j) :=
    ⟨_, rfl⟩
  have hE : ∀ k, Integrable (E k) (Measure.pi fun _ : Fin n ↦ F.ν) := fun k ↦ by
    rw [hEdef]
    exact integrable_finsetSum _ fun p _ ↦
      (Integrable.fintype_prod (f := fun j ↦ Bf (Multiset.count j (p : Multiset (Fin n))))
        fun _ ↦ hBf _).const_mul ((p : Multiset (Fin n)).countPerms : ℝ)
  have hgood : ∀ᵐ x ∂(Measure.pi fun _ : Fin n ↦ F.ν), ∀ j,
      ContDiffOn ℝ 2 (fun u ↦ F.density u (x j)) (ball θ₀ ε) ∧
        ∀ u ∈ ball θ₀ ε, |F.densityDeriv u (x j)| ≤ b₁ (x j) ∧
          |F.densityDeriv2 u (x j)| ≤ b₂ (x j) :=
    ae_all_iff.2 fun j ↦ (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ F.ν)
      (i := j)).eventually (hC2.and hbd)
  have hB : ∀ x : Fin n → S, (∀ j, ContDiffOn ℝ 2 (fun u ↦ F.density u (x j)) (ball θ₀ ε) ∧
      ∀ u ∈ ball θ₀ ε, |F.densityDeriv u (x j)| ≤ b₁ (x j) ∧
        |F.densityDeriv2 u (x j)| ≤ b₂ (x j)) → ∀ u ∈ ball θ₀ ε, ∀ m ≤ 2, ∀ j,
      |iteratedDeriv m (fun v ↦ F.density v (x j)) u| ≤ Bf m (x j) := by
    intro x hx u hu m hm j
    interval_cases m
    · simp only [iteratedDeriv_zero, hBfdef, envelopeByOrder, hb₀def]
      exact abs_le_of_contDiffOn_ball (hx j).1 (fun v hv ↦ ((hx j).2 v hv).1) hu
    · simp only [iteratedDeriv_one, hBfdef, envelopeByOrder]
      exact ((hx j).2 u hu).1
    · rw [iteratedDeriv_succ, iteratedDeriv_one]
      simp only [hBfdef, envelopeByOrder]
      exact ((hx j).2 u hu).2
  refine ⟨?_, ⟨ε, hε, hball, ?_, E 1, E 2, hE 1, hE 2, ?_⟩,
    (pi_fisherInfo n hΘ hreg.derivInterchange.self_of_nhds hreg.ae_differentiableAt
      hreg.memLp_score).1⟩
  · filter_upwards [hreg.support, hΘ] with u hu huΘ x
    exact pi_density_pos_iff hθ₀ huΘ hu n x
  · filter_upwards [hgood] with x hx
    simp only [pi_density]
    exact contDiffOn_prod fun j _ ↦ (hx j).1
  · filter_upwards [hgood] with x hx u hu
    have hb := hB x hx u hu
    constructor
    · have e : (F.pi n).densityDeriv u x =
          iteratedDeriv 1 (fun v ↦ ∏ j, F.density v (x j)) u := by
        rw [iteratedDeriv_one]; rfl
      rw [e]
      rw [hEdef]
      exact abs_iteratedDeriv_prod_le isOpen_ball (fun j ↦ (hx j).1) hu
        (B := fun m j ↦ Bf m (x j)) hb (by norm_num)
    · have e : (F.pi n).densityDeriv2 u x =
          iteratedDeriv 2 (fun v ↦ ∏ j, F.density v (x j)) u := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]; rfl
      rw [e]
      rw [hEdef]
      exact abs_iteratedDeriv_prod_le isOpen_ball (fun j ↦ (hx j).1) hu
        (B := fun m j ↦ Bf m (x j)) hb le_rfl

/-- **The information of the sample family at a regular point** is `n I(θ₀)`. -/
theorem pi_fisherInfo_of_isRegularAt (n : ℕ) (hreg : F.IsRegularAt θ₀) :
    (F.pi n).fisherInfo θ₀ = n * F.fisherInfo θ₀ :=
  (pi_fisherInfo n hreg.mem_nhds hreg.derivInterchange.self_of_nhds hreg.ae_differentiableAt
    hreg.memLp_score).2

/-- The information of a sample of size `n ≥ 1` is positive when that of one observation is. -/
theorem pi_fisherInfo_pos {n : ℕ} (hn : 0 < n) (hreg : F.IsRegularAt θ₀)
    (hI : 0 < F.fisherInfo θ₀) : 0 < (F.pi n).fisherInfo θ₀ := by
  rw [pi_fisherInfo_of_isRegularAt n hreg]
  exact mul_pos (Nat.cast_pos.2 hn) hI

/-- **The score of a sample, pointwise.** Let `U` be open and let every coordinate `x i` have
positive density on `U`, a log density with derivative `s(u; x i)` and a score with derivative
`∂²ℓ(u; x i)` at every `u ∈ U`. Then at `θ ∈ U` the log likelihood of the sample has derivative
equal to the sample score, the sample score is `∑ i, s(θ; x i)`, it has derivative equal to the
second derivative of the sample log likelihood, and that second derivative is
`∑ i, ∂²ℓ(θ; x i)`. -/
theorem pi_score_hasDerivAt_of_isOpen {n : ℕ} {x : Fin n → S} {U : Set ℝ} (hU : IsOpen U)
    (hpos : ∀ i, ∀ u ∈ U, 0 < F.density u (x i))
    (hd : ∀ i, ∀ u ∈ U, HasDerivAt (fun v ↦ F.logLik v (x i)) (F.score u (x i)) u)
    (hh : ∀ i, ∀ u ∈ U, HasDerivAt (fun v ↦ F.score v (x i)) (F.hessLogLik u (x i)) u)
    {θ : ℝ} (hθ : θ ∈ U) :
    HasDerivAt (fun u ↦ (F.pi n).logLik u x) ((F.pi n).score θ x) θ ∧
      (F.pi n).score θ x = ∑ i, F.score θ (x i) ∧
      HasDerivAt (fun u ↦ (F.pi n).score u x) ((F.pi n).hessLogLik θ x) θ ∧
      (F.pi n).hessLogLik θ x = ∑ i, F.hessLogLik θ (x i) := by
  have hlog : ∀ v ∈ U, (F.pi n).logLik v x = ∑ i, F.logLik v (x i) := fun v hv ↦ by
    simp only [logLik, pi_density]
    exact Real.log_prod (fun i _ ↦ (hpos i v hv).ne')
  have hdens : ∀ i, ∀ u ∈ U, DifferentiableAt ℝ (fun v ↦ F.density v (x i)) u := by
    intro i u hu
    refine (hd i u hu).differentiableAt.exp.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hu] with v hv
    simp only [logLik]
    rw [Real.exp_log (hpos i v hv)]
  have hsc : ∀ u ∈ U, (F.pi n).score u x = ∑ i, F.score u (x i) := fun u hu ↦
    pi_score (fun i ↦ hpos i u hu) (fun i ↦ hdens i u hu)
  have hL : ∀ u ∈ U, HasDerivAt (fun v ↦ (F.pi n).logLik v x) ((F.pi n).score u x) u := by
    intro u hu
    rw [hsc u hu]
    refine (HasDerivAt.fun_sum (u := univ) fun i _ ↦ hd i u hu).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hu] with v hv
    exact hlog v hv
  have hS : HasDerivAt (fun u ↦ (F.pi n).score u x) (∑ i, F.hessLogLik θ (x i)) θ := by
    refine (HasDerivAt.fun_sum (u := univ) fun i _ ↦ hh i θ hθ).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hθ] with v hv
    exact hsc v hv
  have hH : (F.pi n).hessLogLik θ x = ∑ i, F.hessLogLik θ (x i) := by
    have e : (fun u ↦ deriv (fun v ↦ (F.pi n).logLik v x) u) =ᶠ[𝓝 θ]
        fun u ↦ (F.pi n).score u x := by
      filter_upwards [hU.mem_nhds hθ] with u hu
      exact (hL u hu).deriv
    rw [hessLogLik, e.deriv_eq, hS.deriv]
  exact ⟨hL θ hθ, hsc θ hθ, hH ▸ hS, hH⟩

/-- **Smoothness of the score passes to the sample family.** Let `F` be regular at `θ₀`, satisfy
`IsScoreRegular θ₀ r`, and let the log density have derivative equal to the score on the closed
ball of radius `r`. If the sample score at `θ₀` and the second derivatives of the sample log
likelihood on that ball are measurable, then for some radius `0 < r' ≤ r` the sample family
satisfies `IsScoreRegular θ₀ r'` and the same derivative identity. The radius shrinks to stay
inside the neighborhood on which the support is constant. The second derivative of the sample log
likelihood is the sum over the coordinates, with envelope `∑ i, H (x i)`.

The measurability hypotheses are assumed because they concern the sample score as a function
defined everywhere, while the hypotheses on `F` control it only almost everywhere. They hold on a
discrete space (`pi_isScoreRegular_of_discrete`). -/
theorem pi_isScoreRegular (n : ℕ) (hreg : F.IsRegularAt θ₀) {r : ℝ} (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hms : Measurable ((F.pi n).score θ₀))
    (hmh : ∀ θ ∈ closedBall θ₀ r, Measurable ((F.pi n).hessLogLik θ)) :
    ∃ r' ∈ Set.Ioc 0 r, (F.pi n).IsScoreRegular θ₀ r' ∧
      ∀ᵐ x ∂(F.pi n).law θ₀, ∀ θ ∈ closedBall θ₀ r',
        HasDerivAt (fun u ↦ (F.pi n).logLik u x) ((F.pi n).score θ x) θ := by
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hreg.mem_nhds
  have := isProbabilityMeasure_law hθ₀
  obtain ⟨ρ, hρ, hsupp⟩ := Metric.eventually_nhds_iff_ball.1 hreg.support
  have hr := hs.pos
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = min r ρ := ⟨_, rfl⟩
  have hR0 : 0 < R := hRdef ▸ lt_min hr hρ
  have hRr : R ≤ r := hRdef ▸ min_le_left r ρ
  have hUr : ball θ₀ R ⊆ closedBall θ₀ r :=
    (ball_subset_ball hRr).trans ball_subset_closedBall
  have hUρ : ball θ₀ R ⊆ ball θ₀ ρ := ball_subset_ball (hRdef ▸ min_le_right r ρ)
  have hcU : closedBall θ₀ (R / 2) ⊆ ball θ₀ R := closedBall_subset_ball (by linarith)
  have hcr : closedBall θ₀ (R / 2) ⊆ closedBall θ₀ r :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨H, hH, hHb⟩ := hs.dominated
  have hgood1 : ∀ᵐ z ∂F.law θ₀, 0 < F.density θ₀ z ∧
      (∀ θ ∈ closedBall θ₀ r, HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ) ∧
      (∀ θ ∈ closedBall θ₀ r, HasDerivAt (fun u ↦ F.score u z) (F.hessLogLik θ z) θ) ∧
      ContinuousOn (fun u ↦ F.hessLogLik u z) (closedBall θ₀ r) ∧
      ∀ θ ∈ closedBall θ₀ r, |F.hessLogLik θ z| ≤ H z := by
    filter_upwards [F.ae_law_pos, hdl, hs.hasDerivAt_score, hs.continuousOn_hessLogLik, hHb]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hgood : ∀ᵐ x ∂(F.pi n).law θ₀, ∀ i, 0 < F.density θ₀ (x i) ∧
      (∀ θ ∈ closedBall θ₀ r, HasDerivAt (fun u ↦ F.logLik u (x i)) (F.score θ (x i)) θ) ∧
      (∀ θ ∈ closedBall θ₀ r,
        HasDerivAt (fun u ↦ F.score u (x i)) (F.hessLogLik θ (x i)) θ) ∧
      ContinuousOn (fun u ↦ F.hessLogLik u (x i)) (closedBall θ₀ r) ∧
      ∀ θ ∈ closedBall θ₀ r, |F.hessLogLik θ (x i)| ≤ H (x i) := by
    rw [pi_law n hθ₀]
    exact ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ F.law θ₀)
      (i := i)).eventually hgood1
  have hkey : ∀ᵐ x ∂(F.pi n).law θ₀, ∀ θ ∈ ball θ₀ R,
      HasDerivAt (fun u ↦ (F.pi n).logLik u x) ((F.pi n).score θ x) θ ∧
        HasDerivAt (fun u ↦ (F.pi n).score u x) ((F.pi n).hessLogLik θ x) θ ∧
        (F.pi n).hessLogLik θ x = ∑ i, F.hessLogLik θ (x i) := by
    filter_upwards [hgood] with x hx θ hθ
    obtain ⟨h1, -, h3, h4⟩ := pi_score_hasDerivAt_of_isOpen isOpen_ball
      (fun i u hu ↦ ((hsupp u (hUρ hu)) (x i)).2 (hx i).1)
      (fun i u hu ↦ (hx i).2.1 u (hUr hu)) (fun i u hu ↦ (hx i).2.2.1 u (hUr hu)) hθ
    exact ⟨h1, h3, h4⟩
  refine ⟨R / 2, ⟨by positivity, by linarith⟩, ⟨by positivity, hms,
    fun θ hθ ↦ hmh θ (hcr hθ), ?_, ?_, ⟨fun x ↦ ∑ i, H (x i), ?_, ?_⟩⟩, ?_⟩
  · filter_upwards [hkey] with x hx θ hθ
    exact (hx θ (hcU hθ)).2.1
  · filter_upwards [hkey, hgood] with x hx hx'
    exact (continuousOn_finsetSum univ fun i _ ↦ (hx' i).2.2.2.1.mono hcr).congr
      fun θ hθ ↦ (hx θ (hcU hθ)).2.2
  · rw [pi_law n hθ₀]
    exact integrable_finsetSum _ fun i _ ↦
      (measurePreserving_eval (fun _ : Fin n ↦ F.law θ₀) i).integrable_comp_of_integrable hH
  · filter_upwards [hkey, hgood] with x hx hx' θ hθ
    rw [(hx θ (hcU hθ)).2.2]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ ↦ (hx' i).2.2.2.2 θ (hcr hθ))
  · filter_upwards [hkey] with x hx θ hθ
    exact (hx θ (hcU hθ)).1

/-- On a discrete sample space the measurability hypotheses of `pi_isScoreRegular` hold. -/
theorem pi_isScoreRegular_of_discrete (n : ℕ) [DiscreteMeasurableSpace (Fin n → S)]
    (hreg : F.IsRegularAt θ₀) {r : ℝ} (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ) :
    ∃ r' ∈ Set.Ioc 0 r, (F.pi n).IsScoreRegular θ₀ r' ∧
      ∀ᵐ x ∂(F.pi n).law θ₀, ∀ θ ∈ closedBall θ₀ r',
        HasDerivAt (fun u ↦ (F.pi n).logLik u x) ((F.pi n).score θ x) θ :=
  pi_isScoreRegular n hreg hs hdl .of_discrete fun _ _ ↦ .of_discrete

end ParametricFamily

end CausalInference
