/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.AnchoredPredictor

/-!
# Shared effect modifiers in the smallest anchored network

One trial of `a` against the common comparator `c` reports individual data; one trial of `b`
against `c` reports aggregate data: the average conditional effect `d` of `b` relative to `c`
over its covariate law `f`, with covariate means `x̄ = ∫ x df` (`covMean`). Both follow the
anchored predictor (`anchoredPredictor`) with common prognostic effects `β₁`.

* **The aggregate contrast** (`linkConditional_anchoredPredictor`): if `g(m_c) = α + xᵀβ₁` and
  `g(m_b) = α + xᵀβ₁ + γ_b + xᵀβ₂`, then `∫ τ_cb df = γ_b + x̄ᵀβ₂`.
* **Identification under shared effect modifiers** (`sharedEffectModifiers_identifiable`): with
  full column rank designs (`designMatrix`) in the two arms of the individual data trial and one
  interaction vector `β₂` for `a` and `b`, any two parameter values that reproduce the data have
  the same `β₂`, `γ_a`, `γ_b` and `γ_b - γ_a`, and `γ_b = d - x̄ᵀβ₂`.
* **One aggregate trial leaves the interactions of `b` free**
  (`sharedEffectModifiers_untestable`): the aggregate trial constrains `(γ_b, β₂,b)` only through
  `γ_b + x̄ᵀβ₂,b = d`; so when `x̄ ≠ 0` two parameter points, one with the interactions `β₂` and
  one with `β₂ + x̄`, reproduce the reported effect and differ in the coefficient `γ_b - γ_a`,
  the conditional effect at the covariate value `0`. This is a statement about coefficients: the
  effects of the two points in a target population with covariate means `x̄_Q` differ by
  `x̄ᵀ(x̄_Q - x̄)`, which is zero when the target is the aggregate trial population.
* **A second aggregate trial tests it** (`sharedEffectModifiers_overidentifying`): with two
  aggregate trials of `b` against `c` with covariate means `x̄ ≠ x̄'`, the assumption implies
  `d - d' = β₂ᵀ(x̄ - x̄')`, and a model with different interactions violates it.

Each theorem is instantiated on one covariate (`sharedEffectModifiers_example`,
`sharedEffectModifiers_test_example`).

## Main definitions

* `designMatrix`, `covMean`.

## Main results

* `design_injective`, `linkConditional_anchoredPredictor`, `sharedEffectModifiers_identifiable`,
  `sharedEffectModifiers_untestable`, `sharedEffectModifiers_overidentifying`,
  `sharedEffectModifiers_example`, `sharedEffectModifiers_test_example`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory EffectMeasure

variable {p : ℕ}

/-- The design matrix with intercept of `n` design points: row `i` is `(1, x_i)`. -/
def designMatrix {n : ℕ} (x : Fin n → Fin p → ℝ) : Matrix (Fin n) (Fin (p + 1)) ℝ :=
  Matrix.of fun i => Fin.cons 1 (x i)

/-- The design matrix applied to `(α, β)` is the predictor `α + xᵢᵀβ`. -/
theorem designMatrix_mulVec {n : ℕ} (x : Fin n → Fin p → ℝ) (α : ℝ) (β : Fin p → ℝ) (i : Fin n) :
    (designMatrix x).mulVec (Fin.cons α β : Fin (p + 1) → ℝ) i = anchoredPredictor α β 0 0 (x i) :=
  by simp [designMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, anchoredPredictor]

/-- **A full column rank design identifies the coefficients**: two coefficient vectors with the
same predictor at every design point coincide. -/
theorem design_injective {n : ℕ} {x : Fin n → Fin p → ℝ}
    (hrank : LinearIndependent ℝ (designMatrix x).col) {α α' : ℝ} {β β' : Fin p → ℝ}
    (h : ∀ i, anchoredPredictor α β 0 0 (x i) = anchoredPredictor α' β' 0 0 (x i)) :
    α = α' ∧ β = β' := by
  have e : (designMatrix x).mulVec (Fin.cons α β : Fin (p + 1) → ℝ) =
      (designMatrix x).mulVec (Fin.cons α' β' : Fin (p + 1) → ℝ) :=
    funext fun i => by rw [designMatrix_mulVec, designMatrix_mulVec, h i]
  exact Fin.cons_inj.1 (Matrix.mulVec_injective_iff.2 hrank e)

/-- The active arm predictor is a predictor with intercept `α + γ` and slope `β₁ + β₂`. -/
theorem anchoredPredictor_eq_intercept (α : ℝ) (β₁ : Fin p → ℝ) (γ : ℝ) (β₂ x : Fin p → ℝ) :
    anchoredPredictor α β₁ γ β₂ x = anchoredPredictor (α + γ) (β₁ + β₂) 0 0 x := by
  simp only [anchoredPredictor, Pi.add_apply, Pi.zero_apply, mul_add, Finset.sum_add_distrib,
    mul_zero, Finset.sum_const_zero]
  ring

/-- The covariate means `x̄_k = ∫ x_k df` of a covariate law on `ℝ^p`. -/
noncomputable def covMean (f : Measure (Fin p → ℝ)) : Fin p → ℝ := fun k => ∫ x, x k ∂f

/-- **The aggregate contrast under the anchored predictor.** If the covariates have integrable
coordinates under the probability law `f`, `g(m_c(x)) = α + xᵀβ₁` and
`g(m_b(x)) = α + xᵀβ₁ + γ_b + xᵀβ₂`, the average conditional effect of `b` relative to `c` is
`γ_b + x̄ᵀβ₂`. -/
theorem linkConditional_anchoredPredictor {g : ℝ → ℝ} {f : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure f] (hf : ∀ k, Integrable (fun x => x k) f) {mb mc : (Fin p → ℝ) → ℝ}
    {α γb : ℝ} {β₁ β₂ : Fin p → ℝ} (hb : ∀ x, g (mb x) = anchoredPredictor α β₁ γb β₂ x)
    (hc : ∀ x, g (mc x) = anchoredPredictor α β₁ 0 0 x) :
    linkConditional g f mc mb = γb + covMean f ⬝ᵥ β₂ := by
  have e : ∀ x, linkContrast g mc mb x = γb + ∑ j, x j * β₂ j := fun x => by
    simp only [linkContrast, hb, hc, anchoredPredictor, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero]
    ring
  simp only [linkConditional, e]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (hf j).mul_const _),
    integral_const, integral_finsetSum _ fun j _ => (hf j).mul_const _]
  simp only [integral_mul_const, probReal_univ, smul_eq_mul, one_mul, covMean, dotProduct]

/-- **Identification under shared effect modifiers in the smallest network.** The individual data
trial gives `m_c` and `m_a` at design points `x_c`, `x_a` with full column rank designs; the
aggregate data trial gives the average conditional effect `d` of `b` relative to `c` over a law `f`
with integrable coordinates. If two parameter values with common prognostic effects and one
interaction vector for `a` and `b` reproduce these data, they have the same `β₂`, `γ_a` and `γ_b`,
hence the same `γ_b - γ_a`, and `γ_b = d - x̄ᵀβ₂`. -/
theorem sharedEffectModifiers_identifiable {g : ℝ → ℝ} {nc na : ℕ} {xc : Fin nc → Fin p → ℝ}
    {xa : Fin na → Fin p → ℝ} (hrc : LinearIndependent ℝ (designMatrix xc).col)
    (hra : LinearIndependent ℝ (designMatrix xa).col) {mc ma : (Fin p → ℝ) → ℝ}
    {f : Measure (Fin p → ℝ)} [IsProbabilityMeasure f] (hf : ∀ k, Integrable (fun x => x k) f)
    {d α γa α₂ γb α' γa' α₂' γb' : ℝ} {β₁ β₂ β₁' β₂' : Fin p → ℝ}
    {mb mc₂ mb' mc₂' : (Fin p → ℝ) → ℝ}
    (hc : ∀ i, g (mc (xc i)) = anchoredPredictor α β₁ 0 0 (xc i))
    (ha : ∀ i, g (ma (xa i)) = anchoredPredictor α β₁ γa β₂ (xa i))
    (hb : ∀ x, g (mb x) = anchoredPredictor α₂ β₁ γb β₂ x)
    (hc₂ : ∀ x, g (mc₂ x) = anchoredPredictor α₂ β₁ 0 0 x) (hd : linkConditional g f mc₂ mb = d)
    (hc' : ∀ i, g (mc (xc i)) = anchoredPredictor α' β₁' 0 0 (xc i))
    (ha' : ∀ i, g (ma (xa i)) = anchoredPredictor α' β₁' γa' β₂' (xa i))
    (hb' : ∀ x, g (mb' x) = anchoredPredictor α₂' β₁' γb' β₂' x)
    (hc₂' : ∀ x, g (mc₂' x) = anchoredPredictor α₂' β₁' 0 0 x)
    (hd' : linkConditional g f mc₂' mb' = d) :
    β₂ = β₂' ∧ γa = γa' ∧ γb = γb' ∧ γb - γa = γb' - γa' ∧ γb = d - covMean f ⬝ᵥ β₂ := by
  obtain ⟨hα, hβ₁⟩ := design_injective hrc fun i => (hc i).symm.trans (hc' i)
  obtain ⟨hαγ, hβ⟩ := design_injective (α := α + γa) (β := β₁ + β₂) (α' := α' + γa')
    (β' := β₁' + β₂') hra fun i => by
      rw [← anchoredPredictor_eq_intercept, ← anchoredPredictor_eq_intercept, ← ha i, ← ha' i]
  have hβ₂ : β₂ = β₂' := by rw [hβ₁] at hβ; exact add_left_cancel hβ
  have hγa : γa = γa' := by linarith
  have e := linkConditional_anchoredPredictor hf hb hc₂
  have e' := linkConditional_anchoredPredictor hf hb' hc₂'
  rw [hd] at e
  rw [hd', ← hβ₂] at e'
  have hγb : γb = γb' := by linarith
  exact ⟨hβ₂, hγa, hγb, by rw [hγa, hγb], by linarith⟩

/-- `v ⬝ᵥ v > 0` for a nonzero real vector. -/
theorem dotProduct_self_pos_of_ne {v : Fin p → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
    (Ne.symm (mt dotProduct_self_eq_zero.1 hv))

/-- **One aggregate trial leaves the interactions of `b` free.** Under the anchored predictor
for the aggregate trial of `b` against `c`, a parameter `(γ_b, β₂,b)` reproduces the reported
effect `d` exactly when `γ_b + x̄ᵀβ₂,b = d`. Hence for any `β₂` the point `(d - x̄ᵀβ₂, β₂)` and
the point `(d - x̄ᵀ(β₂ + x̄), β₂ + x̄)` both reproduce `d`, and when `x̄ ≠ 0` they give different
values of the coefficient `γ_b - γ_a`, which is the conditional effect at the covariate value
`0`. The statement is about coefficients only: in a target population with covariate means
`x̄_Q` the effects of the two points differ by `x̄ᵀ(x̄_Q - x̄)`, which is zero when the target is
the aggregate trial population. -/
theorem sharedEffectModifiers_untestable {g : ℝ → ℝ} {f : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure f] (hf : ∀ k, Integrable (fun x => x k) f) {α : ℝ} {β₁ : Fin p → ℝ}
    {mc : (Fin p → ℝ) → ℝ} (hc : ∀ x, g (mc x) = anchoredPredictor α β₁ 0 0 x) (d γa : ℝ)
    (β₂ : Fin p → ℝ) :
    (∀ (γb : ℝ) (β₂b : Fin p → ℝ) (mb : (Fin p → ℝ) → ℝ),
      (∀ x, g (mb x) = anchoredPredictor α β₁ γb β₂b x) →
        (linkConditional g f mc mb = d ↔ γb + covMean f ⬝ᵥ β₂b = d)) ∧
      (∀ mb : (Fin p → ℝ) → ℝ,
        (∀ x, g (mb x) = anchoredPredictor α β₁ (d - covMean f ⬝ᵥ β₂) β₂ x) →
          linkConditional g f mc mb = d) ∧
      (∀ mb : (Fin p → ℝ) → ℝ, (∀ x, g (mb x) =
          anchoredPredictor α β₁ (d - covMean f ⬝ᵥ (β₂ + covMean f)) (β₂ + covMean f) x) →
          linkConditional g f mc mb = d) ∧
      (covMean f ≠ 0 →
        (d - covMean f ⬝ᵥ β₂) - γa ≠ (d - covMean f ⬝ᵥ (β₂ + covMean f)) - γa) := by
  refine ⟨fun γb β₂b mb hb => ?_, fun mb hb => ?_, fun mb hb => ?_, fun hx => ?_⟩
  · rw [linkConditional_anchoredPredictor hf hb hc]
  · rw [linkConditional_anchoredPredictor hf hb hc]; ring
  · rw [linkConditional_anchoredPredictor hf hb hc]; ring
  · have := dotProduct_self_pos_of_ne hx
    rw [dotProduct_add]
    linarith

/-- **A second aggregate trial tests shared effect modifiers.** With two aggregate trials of `b`
against `c` with covariate laws `f`, `f'` (baselines `α`, `α'`), shared effect modifiers give
`d - d' = β₂ᵀ(x̄ - x̄')`; when `x̄ ≠ x̄'` the model with interactions `β₂ + (x̄ - x̄')` for `b`
violates this restriction. -/
theorem sharedEffectModifiers_overidentifying {g : ℝ → ℝ} {f f' : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure f] [IsProbabilityMeasure f'] (hf : ∀ k, Integrable (fun x => x k) f)
    (hf' : ∀ k, Integrable (fun x => x k) f') {α α' γb : ℝ} {β₁ β₂ : Fin p → ℝ}
    {mc mc' : (Fin p → ℝ) → ℝ} (hc : ∀ x, g (mc x) = anchoredPredictor α β₁ 0 0 x)
    (hc' : ∀ x, g (mc' x) = anchoredPredictor α' β₁ 0 0 x) :
    (∀ mb mb' : (Fin p → ℝ) → ℝ, (∀ x, g (mb x) = anchoredPredictor α β₁ γb β₂ x) →
      (∀ x, g (mb' x) = anchoredPredictor α' β₁ γb β₂ x) →
        linkConditional g f mc mb - linkConditional g f' mc' mb' =
          β₂ ⬝ᵥ (covMean f - covMean f')) ∧
      (covMean f ≠ covMean f' → ∀ mb mb' : (Fin p → ℝ) → ℝ,
        (∀ x, g (mb x) = anchoredPredictor α β₁ γb (β₂ + (covMean f - covMean f')) x) →
        (∀ x, g (mb' x) = anchoredPredictor α' β₁ γb (β₂ + (covMean f - covMean f')) x) →
          linkConditional g f mc mb - linkConditional g f' mc' mb' ≠
            β₂ ⬝ᵥ (covMean f - covMean f')) := by
  refine ⟨fun mb mb' hb hb' => ?_, fun hne mb mb' hb hb' => ?_⟩
  · rw [linkConditional_anchoredPredictor hf hb hc, linkConditional_anchoredPredictor hf' hb' hc',
      dotProduct_sub, dotProduct_comm (covMean f) β₂, dotProduct_comm (covMean f') β₂]
    ring
  · rw [linkConditional_anchoredPredictor hf hb hc, linkConditional_anchoredPredictor hf' hb' hc']
    have := dotProduct_self_pos_of_ne (sub_ne_zero.2 hne)
    simp only [dotProduct_add, dotProduct_sub, sub_dotProduct] at this ⊢
    rw [dotProduct_comm (covMean f) β₂, dotProduct_comm (covMean f') β₂]
    intro h
    nlinarith [dotProduct_comm (covMean f) (covMean f'), this]

/-! ### An instance on one covariate -/

/-- The design points `0` and `1` on one covariate. -/
def twoPointDesign : Fin 2 → Fin 1 → ℝ := ![fun _ => 0, fun _ => 1]

/-- The design with points `0` and `1` has full column rank. -/
theorem linearIndependent_twoPointDesign :
    LinearIndependent ℝ (designMatrix twoPointDesign).col := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp [Fin.sum_univ_succ, designMatrix, twoPointDesign, Matrix.col, Function.swap,
    Fin.cons_zero] at h0 h1
  intro i
  fin_cases i <;> simp <;> linarith

/-- **The smallest network on one covariate.** On the identity scale with one covariate, the
individual data trial observes `m_c(x) = x` and `m_a(x) = 2x + 1` at the design points `0, 1`, and
the aggregate trial of `b` against `c` has its covariate concentrated at `1`, with `m_c(x) = x`
and reported effect `d = 3`. The parameter `α = 0`, `β₁ = 1`, `γ_a = 1`, `β₂ = 1`, `γ_b = 2`
reproduces these data, and by identification every parameter with shared effect modifiers that
reproduces them has `γ_b - γ_a = 1`. Without shared effect modifiers the point `γ_b = 1`,
`β₂,b = 2` also reproduces `d = 3`, with `γ_b - γ_a = 0`. -/
theorem sharedEffectModifiers_example :
    let f : Measure (Fin 1 → ℝ) := Measure.dirac fun _ => 1
    let mc : (Fin 1 → ℝ) → ℝ := fun x => x 0
    let ma : (Fin 1 → ℝ) → ℝ := fun x => 2 * x 0 + 1
    (∀ i, mc (twoPointDesign i) = anchoredPredictor 0 (fun _ => 1) 0 0 (twoPointDesign i)) ∧
      (∀ i, ma (twoPointDesign i) =
        anchoredPredictor 0 (fun _ => 1) 1 (fun _ => 1) (twoPointDesign i)) ∧
      linkConditional id f mc (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1)) = 3 ∧
      (∀ (α' γa' α₂' γb' : ℝ) (β₁' β₂' : Fin 1 → ℝ) (mb' mc₂' : (Fin 1 → ℝ) → ℝ),
        (∀ i, mc (twoPointDesign i) = anchoredPredictor α' β₁' 0 0 (twoPointDesign i)) →
        (∀ i, ma (twoPointDesign i) = anchoredPredictor α' β₁' γa' β₂' (twoPointDesign i)) →
        (∀ x, mb' x = anchoredPredictor α₂' β₁' γb' β₂' x) →
        (∀ x, mc₂' x = anchoredPredictor α₂' β₁' 0 0 x) →
        linkConditional id f mc₂' mb' = 3 → γb' - γa' = 1) ∧
      linkConditional id f mc (anchoredPredictor 0 (fun _ => 1) 1 (fun _ => 2)) = 3 := by
  intro f mc ma
  have hf : ∀ k, Integrable (fun x : Fin 1 → ℝ => x k) f := fun _ => integrable_dirac (by simp)
  have hcm : covMean f = fun _ => 1 := funext fun k => by simp [covMean, f]
  have hmc : ∀ x, id (mc x) = anchoredPredictor 0 (fun _ => 1) 0 0 x := fun x => by
    simp [mc, anchoredPredictor]
  have hc : ∀ i, mc (twoPointDesign i) =
      anchoredPredictor 0 (fun _ => 1) 0 0 (twoPointDesign i) := fun i => hmc _
  have ha : ∀ i, ma (twoPointDesign i) =
      anchoredPredictor 0 (fun _ => 1) 1 (fun _ => 1) (twoPointDesign i) := fun i => by
    simp [ma, anchoredPredictor]; ring
  have hd : linkConditional id f mc (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1)) = 3 := by
    rw [linkConditional_anchoredPredictor (g := id)
      (mb := anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1)) hf (fun _ => rfl) hmc, hcm]
    simp [dotProduct]; norm_num
  refine ⟨hc, ha, hd, fun α' γa' α₂' γb' β₁' β₂' mb' mc₂' hc' ha' hb' hc₂' hd' => ?_, ?_⟩
  · have := sharedEffectModifiers_identifiable (g := id) (mc := mc) (ma := ma)
      (mb := anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1)) (mb' := mb') (mc₂' := mc₂')
      linearIndependent_twoPointDesign linearIndependent_twoPointDesign hf hc ha (fun _ => rfl)
      hmc hd hc' ha' hb' hc₂' hd'
    linarith [this.2.2.2.1]
  · have := (sharedEffectModifiers_untestable (g := id) hf hmc 3 1 (fun _ => 1)).2.2.1
      (anchoredPredictor 0 (fun _ => 1) 1 (fun _ => 2))
    rw [hcm] at this
    refine this fun x => ?_
    simp [anchoredPredictor, dotProduct]
    norm_num

/-- **Testing shared effect modifiers with a second aggregate trial, on one covariate.** On the
identity scale with `m_c(x) = x`, two aggregate trials of `b` against `c` have their covariate
concentrated at `1` and at `0`. With shared interactions `β₂ = 1` and `γ_b = 2` the difference of
the two reported effects is `β₂ (x̄ - x̄') = 1`; with interactions `2` for `b` it is not. With one
aggregate trial at `x̄ = 1 ≠ 0`, the shared point and the unshared point of
`sharedEffectModifiers_untestable` give different values of `γ_b - γ_a`. -/
theorem sharedEffectModifiers_test_example :
    let f : Measure (Fin 1 → ℝ) := Measure.dirac fun _ => 1
    let f' : Measure (Fin 1 → ℝ) := Measure.dirac fun _ => 0
    let mc : (Fin 1 → ℝ) → ℝ := fun x => x 0
    linkConditional id f mc (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1)) -
        linkConditional id f' mc (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1)) = 1 ∧
      linkConditional id f mc (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 2)) -
        linkConditional id f' mc (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 2)) ≠ 1 ∧
      (3 - covMean f ⬝ᵥ (fun _ => 1)) - 1 ≠
        (3 - covMean f ⬝ᵥ ((fun _ => 1) + covMean f)) - 1 := by
  intro f f' mc
  have hf : ∀ k, Integrable (fun x : Fin 1 → ℝ => x k) f := fun _ => integrable_dirac (by simp)
  have hf' : ∀ k, Integrable (fun x : Fin 1 → ℝ => x k) f' := fun _ => integrable_dirac (by simp)
  have hcm : covMean f = fun _ => 1 := funext fun k => by simp [covMean, f]
  have hcm' : covMean f' = fun _ => 0 := funext fun k => by simp [covMean, f']
  have hmc : ∀ x, id (mc x) = anchoredPredictor 0 (fun _ => 1) 0 0 x := fun x => by
    simp [mc, anchoredPredictor]
  have hne : covMean f ≠ covMean f' := by
    rw [hcm, hcm']; intro h; simpa using congrFun h 0
  have T := sharedEffectModifiers_overidentifying (g := id) (γb := 2) (β₂ := fun _ => 1) hf hf'
    hmc hmc
  have hsub : (fun _ : Fin 1 => (1 : ℝ)) + (covMean f - covMean f') = fun _ => 2 := by
    rw [hcm, hcm']; funext; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [T.1 (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1))
      (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 1)) (fun _ => rfl) (fun _ => rfl), hcm, hcm']
    simp [dotProduct]
  · have h2 := T.2 hne (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 2))
      (anchoredPredictor 0 (fun _ => 1) 2 (fun _ => 2)) (fun x => by rw [hsub]; rfl)
      (fun x => by rw [hsub]; rfl)
    rw [hcm, hcm'] at h2
    simpa [dotProduct] using h2
  · have := (sharedEffectModifiers_untestable (g := id) hf hmc 3 1 (fun _ => 1)).2.2.2
      (by rw [hcm]; intro h; simpa using congrFun h 0)
    exact this

end IndirectComparison

end CausalInference
