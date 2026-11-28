/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LogisticFitNormality

/-!
# Any two logistic maximum likelihood fits agree with probability tending to one

Let `O` be an i.i.d. sample of records with law `P_{ξ₀}` of the logistic family, with a design
bounded and of full rank under the regressor law, and let `K` be a compact neighborhood of `ξ₀`.
A **maximizer sequence** is any `θ̂ : ℕ → Ω → ℝ^κ` such that for every `n`, almost surely,
`θ̂_n ∈ K` maximizes the likelihood of the first `n` records over `K`. No measurability and no
particular choice among several maximizers is assumed.

* **Consistency of every maximizer sequence** (`tendstoInMeasure_logisticFamily_of_isMaxOn`):
  `θ̂_n → ξ₀` in probability, by the consistency theorem for maximum likelihood estimators.
* **The score vanishes at an interior maximizer** (`logisticScoreSum_eq_zero_of_isMaxOn`), so
  it vanishes at `θ̂_n` with probability tending to one
  (`withProbTendingToOne_logisticScoreSum_eq_zero_of_isMaxOn`).
* **Two maximizers near `ξ₀` coincide** (`eq_zero_of_logisticLogLik_le_add`): if the score
  vanishes at `m`, the empirical information at `ξ₀` is within `n e` of `n M` entrywise with
  `λ ‖v‖² ≤ vᵀ M v`, and `ℓ_n(m + u) ≥ ℓ_n(m)`, then the quadratic expansion
  `ℓ_n(m + u) - ℓ_n(m) ≈ -(n/2) uᵀ M u` forces `u = 0` once `‖m - ξ₀‖`, `‖u‖` and `e` are small.
* **Agreement** (`withProbTendingToOne_eq_of_isMaxOn_logistic`): any two maximizer sequences
  are equal with probability tending to one; in particular any maximizer sequence equals the fit
  `glmMLE` with probability tending to one (`withProbTendingToOne_glmMLE_eq_of_isMaxOn`).

The total variation form of the Bernstein and von Mises conclusion passes between centerings
that agree with probability tending to one (`IsBernsteinVonMises.congr_withProbTendingToOne`,
from `TendstoInMeasure.congr_withProbTendingToOne`); no measurability is needed.

## Main results

* `WithProbTendingToOne.mono_eventually`, `withProbTendingToOne_of_forall_ae`,
  `IsBernsteinVonMises.congr_withProbTendingToOne`.
* `logisticScoreSum_eq_zero_of_isMaxOn`, `tendstoInMeasure_logisticFamily_of_isMaxOn`,
  `withProbTendingToOne_logisticScoreSum_eq_zero_of_isMaxOn`.
* `eq_zero_of_logisticLogLik_le_add`, `withProbTendingToOne_eq_of_isMaxOn_logistic`,
  `withProbTendingToOne_glmMLE_eq_of_isMaxOn`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

/-! ### Transfer along events of probability tending to one -/

section Transfer

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Families of events eventually containing events of probability tending to one have
probability tending to one. -/
theorem WithProbTendingToOne.mono_eventually {A B : ℕ → Set Ω} (hA : WithProbTendingToOne μ A)
    (hAB : ∀ᶠ n in atTop, A n ⊆ B n) : WithProbTendingToOne μ B :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hA
    (Eventually.of_forall fun _ ↦ bot_le)
    (hAB.mono fun _ h ↦ measure_mono (compl_subset_compl.2 h))

/-- Events that are almost sure for every `n` have probability tending to one. -/
theorem withProbTendingToOne_of_forall_ae {p : ℕ → Ω → Prop} (h : ∀ n, ∀ᵐ ω ∂μ, p n ω) :
    WithProbTendingToOne μ fun n ↦ {ω | p n ω} := by
  have h0 : ∀ n, μ {ω | p n ω}ᶜ = 0 := fun n ↦ by
    have := h n
    rw [ae_iff] at this
    simpa [compl_def] using this
  simp only [WithProbTendingToOne, h0]
  exact tendsto_const_nhds

/-- **The Bernstein and von Mises conclusion passes to a centering that agrees with probability
tending to one.** -/
theorem PosteriorLimit.IsBernsteinVonMises.congr_withProbTendingToOne {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {Pn : ℕ → Ω → Measure E}
    {θ₁ θ₂ : ℕ → Ω → E} {N : Measure E} (h : PosteriorLimit.IsBernsteinVonMises μ Pn θ₁ N)
    (hA : WithProbTendingToOne μ fun n ↦ {ω | θ₁ n ω = θ₂ n ω}) :
    PosteriorLimit.IsBernsteinVonMises μ Pn θ₂ N where
  isProbabilityMeasure := h.isProbabilityMeasure
  isProbabilityMeasure_limit := h.isProbabilityMeasure_limit
  tendsto := h.tendsto.congr_withProbTendingToOne hA fun n ω hω ↦ by
    simp only [mem_ofPred_eq] at hω
    rw [hω]

end Transfer

namespace PosteriorLimit

open PopulationAdjustment PopulationAdjustment.BayesStandardization

variable {C κ : Type*} [Fintype κ]

/-! ### The score at an interior maximizer -/

/-- **The score vanishes at an interior maximizer of the likelihood**: if `ξ` maximizes the
logistic likelihood over `K` and `K` is a neighborhood of `ξ`, the score sum at `ξ` is zero. -/
theorem logisticScoreSum_eq_zero_of_isMaxOn {z : C → κ → ℝ} {n : ℕ} {x : Fin n → C × ℝ}
    {K : Set (κ → ℝ)} {ξ : κ → ℝ} (hmax : IsMaxOn (glmLikelihood logisticDens z x) K ξ)
    (hK : K ∈ 𝓝 ξ) : logisticScoreSum z x ξ = 0 := by
  refine logisticScoreSum_eq_zero_of_isLocalMax ?_
  have hloc := hmax.isLocalMax hK
  filter_upwards [hloc] with ξ' hξ'
  rw [glmLikelihood_logisticDens_eq_exp, glmLikelihood_logisticDens_eq_exp] at hξ'
  exact Real.exp_le_exp.1 hξ'

/-- **Two maximizers near the truth coincide.** Let the design of every record be bounded by
`B`, let `λ ‖v‖² ≤ vᵀ M v` for all `v`, let the empirical information at `ξ₀` be within
`n e` of `n M` entrywise, let the score vanish at `m`, and let `ℓ_n(m + u) ≥ ℓ_n(m)`. If
`(qB)³ (‖m - ξ₀‖ + ‖u‖) + q² e / 2 < λ / 2` with `q = card κ`, then `u = 0`. Proof: the quadratic
expansion `abs_logisticLogLik_quad_le` gives `(n/2) λ ‖u‖² ≤ n ((qB)³ (‖m - ξ₀‖ + ‖u‖) +
q² e / 2) ‖u‖²`. -/
theorem eq_zero_of_logisticLogLik_le_add {z : C → κ → ℝ} {B : ℝ} {n : ℕ}
    (hn : 0 < n) {x : Fin n → C × ℝ} (hB : ∀ i j, |z (x i).1 j| ≤ B) (ξ₀ : κ → ℝ)
    {M : Matrix κ κ ℝ} {lam : ℝ} (hQ : ∀ v, lam * ‖v‖ ^ 2 ≤ quadForm M v) {e : ℝ}
    (hS : ∀ j k, |logisticEmpInfo z x ξ₀ j k - n * M j k| ≤ n * e)
    {m : EuclideanSpace ℝ κ} (hscore : logisticScoreSum z x (WithLp.ofLp m) = 0)
    {u : EuclideanSpace ℝ κ}
    (hle : logisticLogLik z x (WithLp.ofLp m) ≤ logisticLogLik z x (WithLp.ofLp (m + u)))
    (hsmall : (Fintype.card κ * B) ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) +
      Fintype.card κ ^ 2 * e / 2 < lam / 2) : u = 0 := by
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨j₀⟩⟩
  · ext j
    exact isEmptyElim j
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ⟨0, hn⟩ j₀)
  have h := abs_logisticLogLik_quad_le hB0 hB ξ₀ M hS hscore u
  set c := (Fintype.card κ * B) ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) +
    Fintype.card κ ^ 2 * e / 2 with hc
  have h1 := (le_abs_self _).trans h
  have h2 := hQ u
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : (n : ℝ) * (lam / 2 - c) * ‖u‖ ^ 2 ≤ 0 := by nlinarith
  have hpos : 0 < (n : ℝ) * (lam / 2 - c) := mul_pos hn' (by linarith)
  have h4 : ‖u‖ ^ 2 ≤ 0 := by
    by_contra hcon
    have := mul_pos hpos (lt_of_not_ge hcon)
    linarith
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h4 (sq_nonneg _)))

/-! ### Consistency and the score equations for every maximizer sequence -/

variable [MeasurableSpace C] {R : Measure C} [IsProbabilityMeasure R] {z : C → κ → ℝ}
  {hz : ∀ j, Measurable fun c ↦ z c j}
  {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
  {O : ℕ → Ξ → C × ℝ} {K : Set (κ → ℝ)} {ξ₀ : κ → ℝ} {B : ℝ}

omit [IsProbabilityMeasure P] in
/-- A maximizer sequence of the logistic likelihood over `K` is a maximum likelihood estimator
of the logistic family of records. -/
lemma isMLE_logisticFamily_of_isMaxOn {θh : ℕ → Ξ → κ → ℝ}
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω)) :
    (glmFamily logisticKernel R z hz).IsMLE P K O θh := by
  intro n
  filter_upwards [hmax n] with ω hω
  have hl : ∀ ξ, (glmFamily logisticKernel R z hz).likelihood O n ω ξ =
      glmLikelihood logisticDens z (fun i : Fin n ↦ O i ω) ξ := fun ξ ↦ by
    simp only [ParametricFamily.likelihood, glmLikelihood]
    exact Finset.prod_range fun i ↦ logisticDens (z (O i ω).1 ⬝ᵥ ξ) (O i ω).2
  refine ⟨hω.1, fun ξ hξ ↦ ?_⟩
  rw [hl, hl]
  exact hω.2 hξ

/-- **Consistency of every logistic maximizer sequence.** For an i.i.d. sample with law `P_{ξ₀}`
of the logistic family, a design bounded and of full rank under `R`, a compact `K ∋ ξ₀` and any
`θ̂` that almost surely maximizes the likelihood of the first `n` records over `K` for every
`n`, `θ̂_n → ξ₀` in probability. -/
theorem tendstoInMeasure_logisticFamily_of_isMaxOn (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) {θh : ℕ → Ξ → κ → ℝ}
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω)) :
    TendstoInMeasure P θh atTop (fun _ ↦ ξ₀) := by
  set F := glmFamily logisticKernel R z hz
  have := ParametricFamily.isProbabilityMeasure_law (F := F) (Set.mem_univ ξ₀)
  obtain ⟨Bk, hBk⟩ := hK.isBounded.exists_norm_le
  set H : C × ℝ → ℝ := fun q ↦ Real.log 2 + 1 * (Bk * ∑ j, |z q.1 j|) with hHdef
  have hzi : ∀ j, Integrable (fun q : C × ℝ ↦ |z q.1 j|) (F.law ξ₀) := fun j ↦
    (integrable_of_ae_abs_le ((hz j).comp measurable_fst)
      ((ae_abs_design_le hB).mono fun _ hq ↦ hq j)).abs
  have hH : Integrable H (F.law ξ₀) :=
    (integrable_const _).add (((integrable_finsetSum _ fun j _ ↦ hzi j).const_mul Bk).const_mul 1)
  refine ParametricFamily.tendstoInMeasure_of_isMLE hO hlaw hK (Set.subset_univ _) hξ₀
    (glmFamily_pointIdentified logisticKernel_identifies hfull K)
    (ae_of_all _ fun q ↦ ((continuous_logisticDens q.2).comp
      (continuous_const.dotProduct continuous_id)).continuousOn)
    (ae_of_all _ fun q θ _ ↦ logisticDens_pos _ _) hH (ae_of_all _ fun q θ hθ ↦ ?_)
    (isMLE_logisticFamily_of_isMaxOn hmax)
  change |Real.log (logisticDens (z q.1 ⬝ᵥ θ) q.2)| ≤ H q
  refine (abs_log_logisticDens_le _ _).trans (add_le_add_right (mul_le_mul_of_nonneg_left ?_
    zero_le_one) _)
  exact (abs_dotProduct_le_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (hBk θ hθ) (Finset.sum_nonneg fun j _ ↦ abs_nonneg _))

omit [MeasurableSpace C] [IsProbabilityMeasure P] in
/-- **The score vanishes at every maximizer sequence with probability tending to one**, when
`K` is a neighborhood of `ξ₀` and the sequence converges to `ξ₀` in probability. -/
theorem withProbTendingToOne_logisticScoreSum_eq_zero_of_isMaxOn (hKξ₀ : K ∈ 𝓝 ξ₀)
    {θh : ℕ → Ξ → κ → ℝ}
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω))
    (hcons : TendstoInMeasure P θh atTop (fun _ ↦ ξ₀)) :
    WithProbTendingToOne P fun n ↦
      {ω | logisticScoreSum z (fun i : Fin n ↦ O i ω) (θh n ω) = 0} := by
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 hKξ₀
  refine ((hcons.withProbTendingToOne_dist_lt hr).inter
    (withProbTendingToOne_of_forall_ae hmax)).mono fun n ω h ↦ ?_
  obtain ⟨h1, h2⟩ := h
  simp only [mem_ofPred_eq] at h1 h2 ⊢
  refine logisticScoreSum_eq_zero_of_isMaxOn h2.2 (Metric.mem_nhds_iff.2
    ⟨r - dist (θh n ω) ξ₀, sub_pos.2 h1, fun y hy ↦ hrK ?_⟩)
  rw [Metric.mem_ball] at hy ⊢
  linarith [dist_triangle y (θh n ω) ξ₀]

/-! ### Agreement of maximizer sequences -/

omit [IsProbabilityMeasure P] in
/-- The design marginal of the sample is the regressor law. -/
lemma map_fst_eq_of_map_eq_logisticFamily (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀) :
    P.map (fun ω ↦ (O 0 ω).1) = R := by
  rw [show (fun ω ↦ (O 0 ω).1) = Prod.fst ∘ O 0 from rfl,
    ← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hO.aemeasurable 0),
    hlaw, map_fst_logisticFamily_law]

/-- **Any two logistic maximizer sequences agree with probability tending to one.** For an
i.i.d. sample with law `P_{ξ₀}` of the logistic family, a design bounded and of full rank under
`R`, a compact neighborhood `K` of `ξ₀` and two sequences `θ₁, θ₂` that almost surely maximize
the likelihood of the first `n` records over `K` for every `n`, the events `{θ₁_n = θ₂_n}` have
probability tending to one. Neither sequence need be measurable. -/
theorem withProbTendingToOne_eq_of_isMaxOn_logistic (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hKξ₀ : K ∈ 𝓝 ξ₀) {θ₁ θ₂ : ℕ → Ξ → κ → ℝ}
    (h₁ : ∀ n, ∀ᵐ ω ∂P, θ₁ n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θ₁ n ω))
    (h₂ : ∀ n, ∀ᵐ ω ∂P, θ₂ n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θ₂ n ω)) :
    WithProbTendingToOne P fun n ↦ {ω | θ₁ n ω = θ₂ n ω} := by
  have hzm : Measurable z := measurable_pi_iff.2 hz
  have hR := map_fst_eq_of_map_eq_logisticFamily hO hlaw
  have hξ₀ := mem_of_mem_nhds hKξ₀
  have hc₁ := tendstoInMeasure_logisticFamily_of_isMaxOn hO hlaw hB hfull hK hξ₀ h₁
  have hc₂ := tendstoInMeasure_logisticFamily_of_isMaxOn hO hlaw hB hfull hK hξ₀ h₂
  have hI := posDef_logisticInfo hzm hB hfull ξ₀
  obtain ⟨lam, hlam, hQ⟩ := exists_mul_sq_norm_le_quadForm hI
  set B' := max B 0 with hB'def
  have hB' : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B' := hB.mono fun c hc j ↦ (hc j).trans (le_max_left _ _)
  set q : ℝ := (Fintype.card κ : ℝ) with hq
  set a := (q * B') ^ 3 with hadef
  have ha : 0 ≤ a := by positivity
  set δ := lam / (12 * (a + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  set e := lam / (2 * (q ^ 2 + 1)) with hedef
  have he : 0 < e := by positivity
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 hKξ₀
  have hcE : ∀ {θ : ℕ → Ξ → κ → ℝ}, TendstoInMeasure P θ atTop (fun _ ↦ ξ₀) →
      TendstoInMeasure P (fun n ω ↦ WithLp.toLp 2 (θ n ω)) atTop (fun _ ↦ WithLp.toLp 2 ξ₀) :=
    fun hθ ↦ hθ.comp_continuousAt (PiLp.continuous_toLp 2 _).continuousAt
  have A1 := hc₁.withProbTendingToOne_dist_lt hr
  have A2 := (hcE hc₁).withProbTendingToOne_dist_lt hδ
  have A3 := (hcE hc₂).withProbTendingToOne_dist_lt hδ
  have A4 := withProbTendingToOne_abs_logisticEmpInfo_sub_le hO hR hzm hB ξ₀ he
  have hset : MeasurableSet {x : C × ℝ | ∀ j, |z x.1 j| ≤ B'} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_le (continuous_abs.measurable.comp ((hz j).comp measurable_fst))
        measurable_const
  have hBO : ∀ᵐ x ∂(P.map (O 0)), ∀ j, |z x.1 j| ≤ B' := by
    rw [ae_map_iff (hO.aemeasurable 0) hset]
    rw [← hR] at hB'
    exact ae_of_ae_map (hO.aemeasurable 0).fst hB'
  have A5 := WithProbTendingToOne.of_ae (hO.ae_forall hBO)
  have A6 := withProbTendingToOne_of_forall_ae h₁
  have A7 := withProbTendingToOne_of_forall_ae h₂
  refine (((((A1.inter A2).inter A3).inter A4).inter A5).inter (A6.inter A7)).mono_eventually ?_
  filter_upwards [eventually_ge_atTop 1] with n hn ω hω
  obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6, g7⟩ := hω
  simp only [mem_ofPred_eq] at g1 g2 g3 g4 g5 g6 g7 ⊢
  set x : Fin n → C × ℝ := fun i ↦ O i ω with hxdef
  set m : EuclideanSpace ℝ κ := WithLp.toLp 2 (θ₁ n ω) with hmdef
  set u : EuclideanSpace ℝ κ := WithLp.toLp 2 (θ₂ n ω) - m with hudef
  have hnhds : K ∈ 𝓝 (θ₁ n ω) := Metric.mem_nhds_iff.2 ⟨r - dist (θ₁ n ω) ξ₀, sub_pos.2 g1,
    fun y hy ↦ hrK (by
      rw [Metric.mem_ball] at hy ⊢
      linarith [dist_triangle y (θ₁ n ω) ξ₀])⟩
  have hscore : logisticScoreSum z x (WithLp.ofLp m) = 0 :=
    logisticScoreSum_eq_zero_of_isMaxOn g6.2 hnhds
  have hmu : WithLp.ofLp (m + u) = θ₂ n ω := by simp [hudef]
  have hle : logisticLogLik z x (WithLp.ofLp m) ≤ logisticLogLik z x (WithLp.ofLp (m + u)) := by
    rw [hmu]
    have h := g7.2 g6.1
    simp only [mem_ofPred_eq] at h
    rw [glmLikelihood_logisticDens_eq_exp, glmLikelihood_logisticDens_eq_exp] at h
    exact Real.exp_le_exp.1 h
  have hm : ‖m - WithLp.toLp 2 ξ₀‖ < δ := by rw [← dist_eq_norm]; exact g2
  have hm2 : ‖WithLp.toLp 2 (θ₂ n ω) - WithLp.toLp 2 ξ₀‖ < δ := by
    rw [← dist_eq_norm]; exact g3
  have hu : ‖u‖ < 2 * δ := by
    have : u = (WithLp.toLp 2 (θ₂ n ω) - WithLp.toLp 2 ξ₀) - (m - WithLp.toLp 2 ξ₀) := by
      simp [hudef]
    rw [this]
    linarith [norm_sub_le (WithLp.toLp 2 (θ₂ n ω) - WithLp.toLp 2 ξ₀) (m - WithLp.toLp 2 ξ₀)]
  have hsmall : (Fintype.card κ * B') ^ 3 * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) +
      Fintype.card κ ^ 2 * e / 2 < lam / 2 := by
    have h1 : a * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) ≤ a * (3 * δ) :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    have h2 : a * (3 * δ) < lam / 4 := by
      have e1 : a * (3 * δ) = lam / 4 * (a / (a + 1)) := by
        simp only [hδdef]
        field_simp
        ring
      rw [e1]
      exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).2 (by linarith))
    have h3 : q ^ 2 * e / 2 < lam / 4 := by
      have e1 : q ^ 2 * e / 2 = lam / 4 * (q ^ 2 / (q ^ 2 + 1)) := by
        simp only [hedef]
        field_simp
        ring
      rw [e1]
      exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).2 (by linarith))
    change a * (‖m - WithLp.toLp 2 ξ₀‖ + ‖u‖) + q ^ 2 * e / 2 < lam / 2
    linarith
  have hu0 := eq_zero_of_logisticLogLik_le_add hn (x := x) (fun i j ↦ g5 i j) ξ₀ hQ
    (fun j k ↦ g4 j k) hscore hle hsmall
  have h12 : WithLp.toLp 2 (θ₂ n ω) = WithLp.toLp 2 (θ₁ n ω) := by
    rw [hudef, sub_eq_zero] at hu0
    exact hu0
  have := congrArg WithLp.ofLp h12
  simpa using this.symm

/-- **Every logistic maximizer sequence agrees with the fit `glmMLE`** with probability tending
to one, under the hypotheses of `withProbTendingToOne_eq_of_isMaxOn_logistic`. -/
theorem withProbTendingToOne_glmMLE_eq_of_isMaxOn (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hKξ₀ : K ∈ 𝓝 ξ₀) {θh : ℕ → Ξ → κ → ℝ}
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω)) :
    WithProbTendingToOne P fun n ↦ {ω | glmMLE logisticDens z K O n ω = θh n ω} :=
  withProbTendingToOne_eq_of_isMaxOn_logistic hO hlaw hB hfull hK hKξ₀
    (fun n ↦ ae_of_all _ fun ω ↦ glmMLE_isMaxOn z hK ⟨ξ₀, mem_of_mem_nhds hKξ₀⟩ O n ω) hmax

end PosteriorLimit

end CausalInference
