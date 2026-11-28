/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencySharpReparam
public import CausalInference.PopulationAdjustment.WeightedMomentOrderSetting

/-!
# Lower dimensional features under one exponential moment

The consistency theorem for features in a proper affine subspace
(`sampleBalancedArmMean_isConsistent_trial_reparam`) assumes exponential moments of all orders of
the coordinates `ψ(X)`. Here one order suffices: `κ > 2 p ‖β*‖`, where `β*` minimizes the
population dual objective of the coordinates and `p` is their dimension
(`sampleBalancedArmMean_isConsistent_trial_reparam_of_isMinOn`).

**The full dimensional condition fails for collinear features.** For the two features
`(X, 2X)` (`collinearFeatures`) the unit direction `v = (1, -1/2)` (sup norm) is orthogonal to
every feature value, so `vᵀ(φ(x) - t)` is the constant `-vᵀt`; for `v` or `-v` it is at most `0`,
and the margin set `{δ ≤ vᵀ(φ - t)}` is empty for every `δ > 0`
(`not_margin_collinearFeatures`). Hence no target is in the interior of the closed convex hull of
the support of the feature law, for every law of `X` (`not_mem_interior_collinearFeatures`), and
the full dimensional theorems do not apply to the collinear instance, while the reparametrized
one does (`collinearInst_consistent_of_isMinOn`).

## Main results

* `sampleBalancedArmMean_isConsistent_trial_reparam_of_isMinOn`.
* `collinearFeatures_orthogonal`, `not_margin_collinearFeatures`,
  `not_mem_interior_collinearFeatures`, `not_mem_interior_collinearInst`.
* `collinearInst_consistent_of_isMinOn`: the collinear instance through the theorem of one order.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-! ### Consistency for lower dimensional features -/

section Trial

variable {Ω₁ Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p q : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency for features in a proper affine subspace under one exponential moment.** Let
`T`, `O`, `φ = c + M ψ` (almost surely under the covariate law, `N M = 1`), the reported targets
`tₙ ∈ c + range M` with `tₙ → c + M t`, and the arm `a` hypotheses with `m = a₀ + bᵀψ` be as in
`sampleBalancedArmMean_isConsistent_trial_reparam`. Assume the interior condition at `t` for the
law of the coordinates `ψ(X) ∈ ℝ^p`, a minimizer `β*` of their population dual objective
`E[exp(βᵀ(ψ(X) - t))]` and `E[exp(κ ‖ψ(X) - t‖)] < ∞` for one `κ > 2 p ‖β*‖`. Then the weighted
arm mean with the features `φ` at `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_trial_reparam_of_isMinOn (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin q → ℝ} (hφ : Measurable φ) {ψ : 𝒳 → Fin p → ℝ} (hψ : Measurable ψ)
    {M : Matrix (Fin q) (Fin p) ℝ} {N : Matrix (Fin p) (Fin q) ℝ} (hNM : N * M = 1)
    {c : Fin q → ℝ} (hrep : ∀ᵐ x ∂T.covLaw, φ x = c + M *ᵥ ψ x) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map ψ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw ψ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖ψ x - t‖)) T.covLaw)
    (hκ : 2 * p * ‖βs‖ < κ)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin q → ℝ} (hG : ∀ n, Measurable (G n))
    (hGE : ∀ n w, ∃ u, G n w = c + M *ᵥ u)
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => c + M *ᵥ t))
    (hq : 0 < T.μ.real (T.A ⁻¹' {a})) {m : 𝒳 → ℝ} (hm : T.IsCondMean a m)
    (hres2 : Integrable (fun ω => (T.Y a ω - m (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 | MeasurableSpace.comap T.X inferInstance]
      ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ ψ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  set G' : ℕ → 𝒲 → Fin p → ℝ := fun n w => N *ᵥ (G n w - c) with hG'
  have hGG : ∀ n w, G n w = c + M *ᵥ G' n w := fun n w => by
    obtain ⟨u, hu⟩ := hGE n w
    rw [hG']; simp only
    rw [hu, add_sub_cancel_left,
      show N *ᵥ (M *ᵥ u) = u by rw [mulVec_mulVec, hNM, one_mulVec]]
  have hcont : Continuous fun y : Fin q → ℝ => N *ᵥ (y - c) :=
    (Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const))
  have hG'm : ∀ n, Measurable (G' n) := fun n => hcont.measurable.comp (hG n)
  have htm' : TendstoInMeasure P (fun n ω => G' n (W ω)) atTop (fun _ => t) := by
    have h := htm.comp_continuousAt hcont.continuousAt
    rwa [add_sub_cancel_left, mulVec_mulVec, hNM, one_mulVec] at h
  have h := sampleBalancedArmMean_isConsistent_trial_of_isMinOn hX hA hYo a hYa hrand hO hOm
    hlaw hψ hint hmin hexp hκ hW hWO hG'm htm' hq hm hres2 hvar haff
  have hset : MeasurableSet {x | φ x = c + M *ᵥ ψ x} :=
    measurableSet_eq_fun hφ (measurable_const.add
      ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp hψ))
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hrec : ∀ᵐ z ∂(P.map (O 0)), φ (z : 𝒳 × Bool × ℝ).1 = c + M *ᵥ ψ z.1 := by
    rw [hlaw, Trial.ipdLaw]
    refine (ae_map_iff (p := fun z : 𝒳 × Bool × ℝ => φ z.1 = c + M *ᵥ ψ z.1) hf.aemeasurable
      (hset.preimage measurable_fst)).2 ?_
    exact (ae_map_iff (p := fun x => φ x = c + M *ᵥ ψ x) hX.aemeasurable hset).1 hrep
  have hae := hO.ae_forall (p := fun z : 𝒳 × Bool × ℝ => φ z.1 = c + M *ᵥ ψ z.1) hrec
  refine TendstoInMeasure.congr' (Eventually.of_forall fun n => hae.mono fun ω hω => ?_)
    EventuallyEq.rfl h
  change sampleBalancedArmMean ψ (G' n (W ω)) O a n ω =
    sampleBalancedArmMean φ (G n (W ω)) O a n ω
  rw [hGG n (W ω), sampleBalancedArmMean_affine hNM c O _ a n ω hω]

end Trial

/-! ### The interior condition fails for collinear features -/

section Collinear

/-- The unit direction `(1, -1/2)` orthogonal to the line of the collinear features. -/
noncomputable def collinearNormal : Fin 2 → ℝ := ![1, -1 / 2]

theorem norm_collinearNormal : ‖collinearNormal‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
  · fin_cases i <;> norm_num [collinearNormal]
  · have := norm_le_pi_norm collinearNormal 0
    simpa [collinearNormal] using this

/-- **The collinear features lie on a line**: `(1, -1/2)ᵀ(x, 2x) = 0`. -/
theorem collinearFeatures_orthogonal (x : Fin 1 → ℝ) :
    collinearNormal ⬝ᵥ collinearFeatures x = 0 := by
  simp [collinearNormal, collinearFeatures, dotProduct, Fin.sum_univ_two]; ring

theorem measurable_collinearFeatures : Measurable collinearFeatures := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact measurable_pi_apply 0
  · exact measurable_const.mul (measurable_pi_apply 0)

/-- **The margin condition fails for the collinear features, for every law and every target.**
For `δ > 0`, one of the unit directions `±(1, -1/2)` has `vᵀ(φ(x) - t) = ∓(1, -1/2)ᵀt ≤ 0` for
every `x`, so its margin set is empty and has probability `0 < δ`. -/
theorem not_margin_collinearFeatures {ν : Measure (Fin 1 → ℝ)} (t : Fin 2 → ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ¬ ∀ v : Fin 2 → ℝ, ‖v‖ = 1 → δ ≤ ν.real {x | δ ≤ v ⬝ᵥ (collinearFeatures x - t)} := by
  intro h
  have hconst : ∀ (s : ℝ) (x : Fin 1 → ℝ),
      (s • collinearNormal) ⬝ᵥ (collinearFeatures x - t) = -(s * (collinearNormal ⬝ᵥ t)) :=
    fun s x => by
      rw [smul_dotProduct, dotProduct_sub, collinearFeatures_orthogonal, smul_eq_mul]; ring
  have hempty : ∀ s : ℝ, s * (collinearNormal ⬝ᵥ t) ≥ 0 →
      {x | δ ≤ (s • collinearNormal) ⬝ᵥ (collinearFeatures x - t)} = ∅ := fun s hs => by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, hconst]
    linarith
  have hn : ∀ s : ℝ, |s| = 1 → ‖s • collinearNormal‖ = 1 := fun s hs => by
    rw [norm_smul, norm_collinearNormal, Real.norm_eq_abs, hs, mul_one]
  rcases le_total 0 (collinearNormal ⬝ᵥ t) with h0 | h0
  · have := h (1 • collinearNormal) (hn 1 (by norm_num))
    rw [hempty 1 (by linarith), measureReal_empty] at this
    linarith
  · have := h ((-1 : ℝ) • collinearNormal) (hn (-1) (by norm_num))
    rw [hempty (-1) (by linarith), measureReal_empty] at this
    linarith

/-- **No target is in the interior for collinear features.** For every probability law `ν` of a
scalar covariate and every target `t ∈ ℝ²`, `t` is not in the interior of the closed convex hull of
the support of the law of the collinear features `(X, 2X)`. -/
theorem not_mem_interior_collinearFeatures {𝒟 : Type*} [MeasurableSpace 𝒟] {ν : Measure 𝒟}
    [IsProbabilityMeasure ν] {X : 𝒟 → Fin 1 → ℝ} (hX : Measurable X) (t : Fin 2 → ℝ) :
    t ∉ interior (closedConvexHull ℝ (ν.map (collinearFeatures ∘ X)).support) := by
  intro ht
  obtain ⟨δ, hδ, h⟩ := exists_margin_of_mem_interior_map (measurable_collinearFeatures.comp hX) ht
  refine not_margin_collinearFeatures (ν := ν.map X) t hδ fun v hv => ?_
  have hs : MeasurableSet {x : Fin 1 → ℝ | δ ≤ v ⬝ᵥ (collinearFeatures x - t)} :=
    measurableSet_le measurable_const
      ((continuous_const.dotProduct continuous_id).measurable.comp
        (measurable_collinearFeatures.sub_const t))
  rw [map_measureReal_apply hX hs]
  exact h v hv

/-- **The collinear instance violates the full dimensional interior condition.** For the coin
trial over the three point law, the target `(0, 0)` of the instance
`sharpInst_collinear_consistent` is not in the interior of the closed convex hull of the support
of the law of the collinear features, so the full dimensional consistency theorems do not apply
to it. -/
theorem not_mem_interior_collinearInst :
    (0 : Fin 2 → ℝ) ∉ interior (closedConvexHull ℝ
      ((sharpInstTrial threePointLaw sharpInstOutcome).covLaw.map collinearFeatures).support) := by
  rw [sharpInstTrial_covLaw]
  exact not_mem_interior_collinearFeatures (ν := threePointLaw) measurable_id 0

/-- **The collinear instance through the theorem of one exponential moment.** In the coin trial
over the three point law with `Y(true) = 1 + 2X`, balanced on the collinear features `(X, 2X)` at
the reported targets `(1 / (n + 1), 2 / (n + 1)) → (0, 0)`, every hypothesis of
`sampleBalancedArmMean_isConsistent_trial_reparam_of_isMinOn` holds with the coordinate `ψ = X`,
the target `0` of the coordinate (its mean, so `β* = 0`) and the order `κ = 1`; the weighted arm
mean converges in probability to `1`. -/
theorem collinearInst_consistent_of_isMinOn :
    IsConsistent (fun n ω => sampleBalancedArmMean collinearFeatures
      ![1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1))]
      (sharpInstSample threePointLaw sharpInstOutcome) true n ω) 1
      (sharpInstLaw threePointLaw sharpInstOutcome) := by
  have hf := measurable_sharpInstOutcome
  have hfi : Integrable (sharpInstOutcome true) threePointLaw :=
    integrable_threePointLaw (hf true)
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses hf true hfi
  have hcov := sharpInstTrial_covLaw (lam := threePointLaw) (f := sharpInstOutcome)
  have hi : ∀ k, Integrable (fun x : Fin 1 → ℝ => id x k) threePointLaw := fun k =>
    integrable_threePointLaw (measurable_pi_apply k)
  have hmean : ∀ k, ∫ x, id x k ∂threePointLaw = (0 : Fin 1 → ℝ) k := fun k => by
    have := congrFun integral_id_threePointLaw k
    have h2 : (∫ y, y ∂threePointLaw) k = ∫ y, y k ∂threePointLaw := eval_integral hi k
    simp only [id]; rw [← h2]; exact this
  have hmin := isMinOn_sharpDualObjective_zero_of_integral_eq measurable_id hi hmean
  have htn : Tendsto (fun n : ℕ => featureLineVec (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (featureLineVec 0)) := tendsto_pi_nhds.2 fun _ => by
    simpa [featureLineVec] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htn' : Tendsto (fun n : ℕ => (0 : Fin 2 → ℝ) +
      collinearDirection *ᵥ featureLineVec (1 / ((n : ℝ) + 1))) atTop
      (𝓝 ((0 : Fin 2 → ℝ) + collinearDirection *ᵥ featureLineVec 0)) :=
    tendsto_const_nhds.add
      ((Continuous.matrix_mulVec continuous_const continuous_id).continuousAt.tendsto.comp htn)
  have hval : ∀ n : ℕ, ![1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1))] =
      (0 : Fin 2 → ℝ) + collinearDirection *ᵥ featureLineVec (1 / ((n : ℝ) + 1)) := fun n => by
    rw [← collinearFeatures_eq]; rfl
  have h := sampleBalancedArmMean_isConsistent_trial_reparam_of_isMinOn hX hA hYo true hYa hrand
    (isIIDSample_sharpInstSample hf) (measurable_sharpInstSample hf) (map_sharpInstSample hf 0)
    measurable_collinearFeatures measurable_id collinearLeftInverse_mul (c := 0)
    (ae_of_all _ collinearFeatures_eq) (t := 0)
    (by rw [Measure.map_id, hcov]; exact zero_mem_interior_threePointLaw)
    (by rw [hcov]; exact hmin) (κ := 1) (by rw [hcov]; exact integrable_exp_threePointLaw 1 0)
    (by simp) (W := fun _ => ()) measurable_const (indepFun_const_left _ _)
    (G := fun n _ => (0 : Fin 2 → ℝ) + collinearDirection *ᵥ featureLineVec (1 / ((n : ℝ) + 1)))
    (fun _ => measurable_const) (fun n _ => ⟨_, rfl⟩)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => htn')) hq hm hres2 hvar (a0 := 1) (b := featureLineVec 2)
    sharpInstOutcome_true
  simp only [← hval] at h
  simpa using h

end Collinear

end PopulationAdjustment

end CausalInference
