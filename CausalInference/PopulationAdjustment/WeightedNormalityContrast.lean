/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityLimit
public import CausalInference.PopulationAdjustment.WeightedConsistencyContrast
public import CausalInference.Estimation.DeltaMethod

/-!
# Asymptotic normality of the weighted comparisons

The anchored and unanchored weighted comparisons of `WeightedConsistencyContrast` on a link scale
`g`. The index part is a smooth function of the weighted arm means of the same sample, so the
delta method and the asymptotically linear representations of
`sampleBalancedArmMean_isAsymptoticallyLinear` give its influence function:
`g'(m_false) IF_false - g'(m_true) IF_true` for the anchored comparison
(`weightedIndexContrast_isAsymptoticallyLinear`) and `-g'(m_true) IF_true` for the unanchored one.

The aggregate part comes from another study. It is an independent estimate that is
asymptotically normal on the link scale at the same rate, `√n (d - d̂ₙ) → N(0, w)`; the limit law
of the comparison is then normal with the sum of the two variances
(`tendstoInDistribution_add_of_indepFun`, proved through characteristic functions). A reported
aggregate value without sampling error is the case `w = 0`.

## Main definitions

* `weightedAnchoredInfluence`: the influence function of the anchored index part.

## Main results

* `tendstoInDistribution_add_of_indepFun`: the sum of independent normal limits.
* `weightedIndexContrast_isAsymptoticallyLinear`.
* `anchoredBalancedEstimate_tendstoInDistribution`.
* `unanchoredBalancedEstimate_tendstoInDistribution`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

/-- **Sums of independent normal limits.** If `Xₙ → N(0, v)` and `Zₙ → N(0, w)` in law and `Xₙ`
is independent of `Zₙ` for every `n`, then `Xₙ + Zₙ → N(0, v + w)` in law. -/
theorem tendstoInDistribution_add_of_indepFun {Ω Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] {P : Measure Ω}
    [IsProbabilityMeasure P] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P₃ : Measure Ω₃}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] [IsProbabilityMeasure P₃]
    {X Z : ℕ → Ω → ℝ} {Y₁ : Ω₁ → ℝ} {Y₂ : Ω₂ → ℝ} {Y : Ω₃ → ℝ} {v w : ℝ≥0}
    (hX : TendstoInDistribution X atTop Y₁ (fun _ => P) P₁)
    (hZ : TendstoInDistribution Z atTop Y₂ (fun _ => P) P₂) (hind : ∀ n, IndepFun (X n) (Z n) P)
    (hY₁ : HasLaw Y₁ (gaussianReal 0 v) P₁) (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    (hY : HasLaw Y (gaussianReal 0 (v + w)) P₃) :
    TendstoInDistribution (fun n ω => X n ω + Z n ω) atTop Y (fun _ => P) P₃ := by
  refine TendstoInDistribution.of_tendsto_charFun
    (fun n => (hX.forall_aemeasurable n).add (hZ.forall_aemeasurable n)) hY.aemeasurable
    fun s => ?_
  have hprod : ∀ n, charFun (P.map fun ω => X n ω + Z n ω) s =
      charFun (P.map (X n)) s * charFun (P.map (Z n)) s := fun n => by
    rw [(hind n).charFun_map_fun_add_eq_mul (hX.forall_aemeasurable n)
      (hZ.forall_aemeasurable n)]
    rfl
  simp_rw [hprod]
  have hl := (hX.tendsto_charFun s).mul (hZ.tendsto_charFun s)
  rw [hY₁.map_eq, hY₂.map_eq] at hl
  rw [hY.map_eq]
  convert hl using 2
  simp only [charFun_gaussianReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- The influence function `g'(m_false) IF_false - g'(m_true) IF_true` of the anchored index
part `g(m̂_false) - g(m̂_true)`, with `gf'` and `gt'` the derivatives of `g` at the two limits. -/
noncomputable def weightedAnchoredInfluence (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (gf' gt' : ℝ) (z : 𝒳 × Bool × ℝ) : ℝ :=
  gf' * weightedArmInfluence ν φ t false z - gt' * weightedArmInfluence ν φ t true z

/-- **The anchored index part is asymptotically linear**: under the hypotheses of
`sampleBalancedArmMean_isAsymptoticallyLinear` for both arms and a link `g` differentiable at the
two limits, `g(m̂_false) - g(m̂_true)` has the influence function `weightedAnchoredInfluence`. -/
theorem weightedIndexContrast_isAsymptoticallyLinear [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : ∀ a, 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) {g : ℝ → ℝ} {gf' gt' : ℝ}
    (hgf : HasDerivAt g gf'
      (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)))
    (hgt : HasDerivAt g gt'
      (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t))) :
    IsAsymptoticallyLinear (fun n ω => g (sampleBalancedArmMean φ t O false n ω) -
        g (sampleBalancedArmMean φ t O true n ω))
      (g (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)) -
        g (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
      (weightedAnchoredInfluence (P.map (O 0)) φ t gf' gt') O P :=
  ((sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin false (hq false)
    hy).comp_hasDerivAt hO hgf).sub
    ((sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin true (hq true)
      hy).comp_hasDerivAt hO hgt)

omit [MeasurableSpace Ω] in
/-- A measurable function of two sample measurable estimators is sample measurable. -/
theorem isSampleMeasurable_comp₂ {θ₁ θ₂ : ℕ → Ω → ℝ} (h₁ : IsSampleMeasurable θ₁ O)
    (h₂ : IsSampleMeasurable θ₂ O) {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) :
    IsSampleMeasurable (fun n ω => f (θ₁ n ω) (θ₂ n ω)) O := fun n => by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁ n
  obtain ⟨g₂, hg₂, e₂⟩ := h₂ n
  refine ⟨fun x => f (g₁ x) (g₂ x), hf.comp (hg₁.prodMk hg₂), ?_⟩
  funext ω
  simp only [e₁, e₂]

/-- **Asymptotic normality of the anchored weighted comparison** on the link scale `g`. The
aggregate estimate `d̂ₙ = dBC n` of the comparator contrast `d` is independent of the index
records and asymptotically normal, `√n (d - d̂ₙ) → N(0, w)`. Then
`√n (Δ̂ₙ - Δ) → N(0, E[IF²] + w)` in law, with `Δ = g(m_false) - g(m_true) - d` and the index
influence function `IF = weightedAnchoredInfluence`. -/
theorem anchoredBalancedEstimate_tendstoInDistribution [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : ∀ a, 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) {g : ℝ → ℝ}
    (hg : Measurable g) {gf' gt' : ℝ}
    (hgf : HasDerivAt g gf'
      (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)))
    (hgt : HasDerivAt g gt'
      (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
    {dBC : ℕ → Ω → ℝ} {d : ℝ}
    (hindep : ∀ n, IndepFun (fun ω (i : Fin n) => O i ω) (dBC n) P)
    {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure P₃] {Y₁ : Ω₁ → ℝ} {Y₂ : Ω₂ → ℝ}
    {Y : Ω₃ → ℝ} {w : ℝ≥0}
    (hY₁ : HasLaw Y₁ (gaussianReal 0
      (P[fun ω => weightedAnchoredInfluence (P.map (O 0)) φ t gf' gt' (O 0 ω) ^ 2]).toNNReal) P₁)
    (hagg : TendstoInDistribution (fun (n : ℕ) ω => √n * (d - dBC n ω)) atTop Y₂
      (fun _ => P) P₂) (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    (hY : HasLaw Y (gaussianReal 0
      ((P[fun ω => weightedAnchoredInfluence (P.map (O 0)) φ t gf' gt' (O 0 ω) ^ 2]).toNNReal +
        w)) P₃) :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (anchoredBalancedEstimate g φ t O dBC n ω -
      (g (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)) -
        g (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)) - d)))
      atTop Y (fun _ => P) P₃ := by
  set mF := tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)
  set mT := tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)
  have hAL := weightedIndexContrast_isAsymptoticallyLinear hO hφ hB hδ hmargin hq hy hgf hgt
  have hSM : IsSampleMeasurable (fun n ω => g (sampleBalancedArmMean φ t O false n ω) -
      g (sampleBalancedArmMean φ t O true n ω)) O :=
    isSampleMeasurable_comp₂ (isSampleMeasurable_sampleBalancedArmMean hφ t O false)
      (isSampleMeasurable_sampleBalancedArmMean hφ t O true) (f := fun x y => g x - g y)
      (show Measurable fun q : ℝ × ℝ => g q.1 - g q.2 from
        (hg.comp measurable_fst).sub (hg.comp measurable_snd))
  have hX := hAL.tendstoInDistribution_of_isSampleMeasurable hO hSM hY₁
  have hind : ∀ n : ℕ, IndepFun (fun ω => √(n : ℝ) * ((g (sampleBalancedArmMean φ t O false n ω) -
      g (sampleBalancedArmMean φ t O true n ω)) - (g mF - g mT)))
      (fun ω => √n * (d - dBC n ω)) P := fun n => by
    obtain ⟨f, hf, e⟩ := hSM n
    have := (hindep n).comp (φ := fun x => √n * (f x - (g mF - g mT)))
      (ψ := fun r => √n * (d - r)) ((hf.sub_const _).const_mul _)
      ((measurable_const.sub measurable_id).const_mul _)
    convert this using 2 with ω
    · simp only [Function.comp_apply]
      rw [show (g (sampleBalancedArmMean φ t O false n ω) -
        g (sampleBalancedArmMean φ t O true n ω)) = f fun i => O i ω from congrFun e ω]
    · rfl
  have h := tendstoInDistribution_add_of_indepFun hX hagg hind hY₁ hY₂ hY
  convert h using 3 with n ω
  rw [anchoredBalancedEstimate_eq]
  ring

/-- **Asymptotic normality of the unanchored weighted comparison** on the link scale `g`. The
aggregate estimate `m̂Bₙ` of the comparator mean `mB` is independent of the index records with
`√n (g(m̂Bₙ) - g(mB)) → N(0, w)`. Then `√n (Δ̂ₙ - Δ) → N(0, g'(m_true)² σ²_true + w)` in law,
with `Δ = g(mB) - g(m_true)` and `σ²_true = weightedArmVariance`. -/
theorem unanchoredBalancedEstimate_tendstoInDistribution [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) {g : ℝ → ℝ}
    (hg : Measurable g) {gt' : ℝ}
    (hgt : HasDerivAt g gt'
      (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
    {mB : ℕ → Ω → ℝ} {mB₀ : ℝ}
    (hindep : ∀ n, IndepFun (fun ω (i : Fin n) => O i ω) (mB n) P)
    {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] [IsProbabilityMeasure P₃] {Y₁ : Ω₁ → ℝ} {Y₂ : Ω₂ → ℝ}
    {Y : Ω₃ → ℝ} {w : ℝ≥0}
    (hY₁ : HasLaw Y₁ (gaussianReal 0
      (gt' ^ 2 * weightedArmVariance (P.map (O 0)) φ t true).toNNReal) P₁)
    (hagg : TendstoInDistribution (fun (n : ℕ) ω => √n * (g (mB n ω) - g mB₀)) atTop Y₂
      (fun _ => P) P₂) (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    (hY : HasLaw Y (gaussianReal 0
      ((gt' ^ 2 * weightedArmVariance (P.map (O 0)) φ t true).toNNReal + w)) P₃) :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (unanchoredBalancedEstimate g φ t O mB n ω -
      (g mB₀ - g (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))))
      atTop Y (fun _ => P) P₃ := by
  set mT := tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)
  have hAL := (sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin true hq
    hy).comp_hasDerivAt hO hgt.neg
  have hSM : IsSampleMeasurable (fun n ω => -g (sampleBalancedArmMean φ t O true n ω)) O :=
    isSampleMeasurable_comp₂ (isSampleMeasurable_sampleBalancedArmMean hφ t O true)
      (isSampleMeasurable_sampleBalancedArmMean hφ t O true)
      (f := fun x _ => -g x)
      (show Measurable fun q : ℝ × ℝ => -g q.1 from (hg.comp measurable_fst).neg)
  have hvar : P[fun ω => (-gt' * weightedArmInfluence (P.map (O 0)) φ t true (O 0 ω)) ^ 2] =
      gt' ^ 2 * weightedArmVariance (P.map (O 0)) φ t true := by
    have hm := (sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin true hq
      hy).measurable
    rw [weightedArmVariance,
      integral_map (hO.aemeasurable 0) (hm.pow_const 2).aestronglyMeasurable,
      ← integral_const_mul]
    congr 1; funext ω; ring
  rw [← hvar] at hY₁ hY
  have hX := hAL.tendstoInDistribution_of_isSampleMeasurable hO hSM hY₁
  have hind : ∀ n : ℕ, IndepFun
      (fun ω => √(n : ℝ) * (-g (sampleBalancedArmMean φ t O true n ω) - -g mT))
      (fun ω => √n * (g (mB n ω) - g mB₀)) P := fun n => by
    obtain ⟨f, hf, e⟩ := hSM n
    have := (hindep n).comp (φ := fun x => √n * (f x - -g mT))
      (ψ := fun r => √n * (g r - g mB₀)) ((hf.sub_const _).const_mul _)
      ((hg.sub_const _).const_mul _)
    convert this using 2 with ω
    · simp only [Function.comp_apply]
      rw [show -g (sampleBalancedArmMean φ t O true n ω) = f fun i => O i ω from congrFun e ω]
    · rfl
  have h := tendstoInDistribution_add_of_indepFun hX hagg hind hY₁ hY₂ hY
  convert h using 3 with n ω
  simp only [unanchoredBalancedEstimate, Pi.neg_apply]
  ring

end PopulationAdjustment

end CausalInference
