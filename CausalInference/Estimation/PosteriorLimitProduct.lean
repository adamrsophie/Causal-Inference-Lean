/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitTotalVariation
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Products of posteriors

For two independent experiments with posteriors `Π₁, Π₂`, the joint posterior is the product
`Π₁ ⊗ Π₂`. This file shows that the Bernstein and von Mises conclusion passes to products.

* **Total variation of products.** For probability laws,
  `‖μ₁ ⊗ ν₁ - μ₂ ⊗ ν₂‖_TV ≤ ‖μ₁ - μ₂‖_TV + ‖ν₁ - ν₂‖_TV` (`tvDist_prod_le`). The proof bounds
  one factor at a time: on a Hahn set `s` of `(μ₁ ⊗ ν, μ₂ ⊗ ν)`, the total variation is twice the
  excess on `s`, which is the `ν` average of the excesses on the sections of `s`.
* **Bernstein and von Mises for products** (`IsBernsteinVonMises.prod`): if
  `‖Π₁,n - N₁(θ̂₁,n, n⁻¹ ·)‖ → 0` in probability under `P₁` and similarly for the second
  experiment, then under `P₁ ⊗ P₂` the product posteriors satisfy the same with the limit
  `N₁ ⊗ N₂` and the centering `(θ̂₁,n, θ̂₂,n)`.
* **Joint convergence in law** of statistics of the two experiments under `P₁ ⊗ P₂`
  (`TendstoInDistribution.prodMk_of_prod`): the law of the pair is the product of the laws,
  and the product of probability laws is continuous for weak convergence.

## Main results

* `tvDist_prod_le`, `IsBernsteinVonMises.prod`, `TendstoInDistribution.prodMk_of_prod`,
  `TendstoInMeasure.comp_fst_prod`, `TendstoInMeasure.comp_snd_prod`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

/-! ### Total variation of products -/

section TotalVariation

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- The measure of a set under a product law, as the average of the measures of its sections
over the second factor. -/
lemma measureReal_prod_eq_integral {μ : Measure E} {ν : Measure F} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {s : Set (E × F)} (hs : MeasurableSet s) :
    (μ.prod ν).real s = ∫ y, μ.real ((fun x ↦ (x, y)) ⁻¹' s) ∂ν := by
  rw [measureReal_def, Measure.prod_apply_symm hs]
  simp only [measureReal_def]
  rw [integral_toReal (measurable_measure_prodMk_right hs).aemeasurable
    (ae_of_all _ fun _ ↦ measure_lt_top _ _)]

/-- The section measures of a measurable set are integrable over a probability law. -/
lemma integrable_measureReal_section {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] {s : Set (E × F)} (hs : MeasurableSet s) :
    Integrable (fun y ↦ μ.real ((fun x ↦ (x, y)) ⁻¹' s)) ν :=
  Integrable.of_bound (measurable_measure_prodMk_right hs).ennreal_toReal.aestronglyMeasurable 1
    (ae_of_all _ fun _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)

/-- **Total variation of products with a common second factor.** For probability laws,
`‖μ₁ ⊗ ν - μ₂ ⊗ ν‖_TV ≤ ‖μ₁ - μ₂‖_TV`. -/
theorem tvDist_prod_left_le (μ₁ μ₂ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν] :
    tvDist (μ₁.prod ν) (μ₂.prod ν) ≤ tvDist μ₁ μ₂ := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition (μ₁.prod ν) (μ₂.prod ν)
  have hs := h.measurableSet
  have hb : ∀ y, μ₂.real ((fun x ↦ (x, y)) ⁻¹' s) - μ₁.real ((fun x ↦ (x, y)) ⁻¹' s) ≤
      tvDist μ₁ μ₂ / 2 := fun y ↦ by
    have := abs_measureReal_sub_le_half_tvDist (μ := μ₂) (ν := μ₁)
      (measurable_prodMk_right (y := y) hs)
    rw [tvDist_comm] at this
    exact (le_abs_self _).trans this
  have hI : ∫ y, (μ₂.real ((fun x ↦ (x, y)) ⁻¹' s) - μ₁.real ((fun x ↦ (x, y)) ⁻¹' s)) ∂ν ≤
      tvDist μ₁ μ₂ / 2 := by
    calc _ ≤ ∫ _y, tvDist μ₁ μ₂ / 2 ∂ν :=
          integral_mono ((integrable_measureReal_section hs).sub
            (integrable_measureReal_section hs)) (integrable_const _) hb
      _ = tvDist μ₁ μ₂ / 2 := by simp
  rw [integral_sub (integrable_measureReal_section hs) (integrable_measureReal_section hs),
    ← measureReal_prod_eq_integral hs, ← measureReal_prod_eq_integral hs] at hI
  rw [h.tvDist_eq, probReal_compl_eq_one_sub hs, probReal_compl_eq_one_sub hs]
  linarith

/-- **Total variation of products with a common first factor.** For probability laws,
`‖μ ⊗ ν₁ - μ ⊗ ν₂‖_TV ≤ ‖ν₁ - ν₂‖_TV`. -/
theorem tvDist_prod_right_le (μ : Measure E) (ν₁ ν₂ : Measure F) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    tvDist (μ.prod ν₁) (μ.prod ν₂) ≤ tvDist ν₁ ν₂ := by
  rw [← tvDist_map_eq_of_leftInverse measurable_swap measurable_swap
    (fun p : E × F ↦ Prod.swap_swap p), Measure.prod_swap, Measure.prod_swap]
  exact tvDist_prod_left_le ν₁ ν₂ μ

/-- **Total variation of products.** For probability laws,
`‖μ₁ ⊗ ν₁ - μ₂ ⊗ ν₂‖_TV ≤ ‖μ₁ - μ₂‖_TV + ‖ν₁ - ν₂‖_TV`. -/
theorem tvDist_prod_le (μ₁ μ₂ : Measure E) (ν₁ ν₂ : Measure F) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    tvDist (μ₁.prod ν₁) (μ₂.prod ν₂) ≤ tvDist μ₁ μ₂ + tvDist ν₁ ν₂ :=
  (tvDist_triangle _ (μ₂.prod ν₁) _).trans
    (add_le_add (tvDist_prod_left_le μ₁ μ₂ ν₁) (tvDist_prod_right_le μ₂ ν₁ ν₂))

end TotalVariation

/-! ### Convergence in probability on a product sample space -/

section Lift

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {E : Type*} [PseudoMetricSpace E]

omit [IsProbabilityMeasure P₁] in
/-- Convergence in probability of a statistic of the first experiment holds under the product
sampling law. -/
theorem _root_.MeasureTheory.TendstoInMeasure.comp_fst_prod {f : ℕ → Ω₁ → E} {g : Ω₁ → E}
    (h : TendstoInMeasure P₁ f atTop g) :
    TendstoInMeasure (P₁.prod P₂) (fun n ω ↦ f n ω.1) atTop (fun ω ↦ g ω.1) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ zero_le) fun n ↦ ?_
  have := Measure.le_map_apply (μ := P₁.prod P₂) measurable_fst.aemeasurable
    {x | ε ≤ dist (f n x) (g x)}
  rwa [Measure.map_fst_prod, measure_univ, one_smul] at this

/-- Convergence in probability of a statistic of the second experiment holds under the product
sampling law. -/
theorem _root_.MeasureTheory.TendstoInMeasure.comp_snd_prod {f : ℕ → Ω₂ → E} {g : Ω₂ → E}
    (h : TendstoInMeasure P₂ f atTop g) :
    TendstoInMeasure (P₁.prod P₂) (fun n ω ↦ f n ω.2) atTop (fun ω ↦ g ω.2) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ zero_le) fun n ↦ ?_
  have := Measure.le_map_apply (μ := P₁.prod P₂) measurable_snd.aemeasurable
    {x | ε ≤ dist (f n x) (g x)}
  rwa [Measure.map_snd_prod, measure_univ, one_smul] at this

/-- A nonnegative sequence bounded by a sum of two sequences tending to zero in probability tends
to zero in probability. -/
lemma tendstoInMeasure_zero_of_le_add {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {a b c : ℕ → Ω → ℝ} (ha : TendstoInMeasure P a atTop (fun _ ↦ 0))
    (hb : TendstoInMeasure P b atTop (fun _ ↦ 0)) (hc0 : ∀ n ω, 0 ≤ c n ω)
    (hc : ∀ n ω, c n ω ≤ a n ω + b n ω) : TendstoInMeasure P c atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_dist] at ha hb ⊢
  intro ε hε
  have hsum := (ha (ε / 2) (half_pos hε)).add (hb (ε / 2) (half_pos hε))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun n ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, Set.mem_union] at hω ⊢
  rw [abs_of_nonneg (hc0 n ω)] at hω
  by_contra hne
  rw [not_or, not_le, not_le] at hne
  have h1 := (le_abs_self (a n ω)).trans_lt hne.1
  have h2 := (le_abs_self (b n ω)).trans_lt hne.2
  linarith [hc n ω]

end Lift

/-! ### The Bernstein and von Mises conclusion for products -/

section Product

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **The Bernstein and von Mises conclusion for independent posteriors.** If the posteriors
`Π₁,n` of the first experiment satisfy `‖Π₁,n - N₁(θ̂₁,n, n⁻¹ ·)‖_TV → 0` in probability under
`P₁`, and those of the second experiment satisfy the same under `P₂`, then the product
posteriors `Π₁,n ⊗ Π₂,n` satisfy `‖Π₁,n ⊗ Π₂,n - (N₁ ⊗ N₂)(θ̂_n, n⁻¹ ·)‖_TV → 0` in probability
under `P₁ ⊗ P₂`, with `θ̂_n = (θ̂₁,n, θ̂₂,n)`. -/
theorem IsBernsteinVonMises.prod {Pn₁ : ℕ → Ω₁ → Measure E} {θh₁ : ℕ → Ω₁ → E}
    {N₁ : Measure E} {Pn₂ : ℕ → Ω₂ → Measure F} {θh₂ : ℕ → Ω₂ → F} {N₂ : Measure F}
    (h₁ : IsBernsteinVonMises P₁ Pn₁ θh₁ N₁) (h₂ : IsBernsteinVonMises P₂ Pn₂ θh₂ N₂) :
    IsBernsteinVonMises (P₁.prod P₂) (fun n ω ↦ (Pn₁ n ω.1).prod (Pn₂ n ω.2))
      (fun n ω ↦ (θh₁ n ω.1, θh₂ n ω.2)) (N₁.prod N₂) where
  isProbabilityMeasure n ω := by
    have := h₁.isProbabilityMeasure n ω.1
    have := h₂.isProbabilityMeasure n ω.2
    infer_instance
  isProbabilityMeasure_limit := by
    have := h₁.isProbabilityMeasure_limit
    have := h₂.isProbabilityMeasure_limit
    infer_instance
  tendsto := by
    have := h₁.isProbabilityMeasure_limit
    have := h₂.isProbabilityMeasure_limit
    refine tendstoInMeasure_zero_of_le_add h₁.tendsto.comp_fst_prod h₂.tendsto.comp_snd_prod
      (fun _ _ ↦ tvDist_nonneg) fun n ω ↦ ?_
    have := h₁.isProbabilityMeasure n ω.1
    have := h₂.isProbabilityMeasure n ω.2
    have hmap : (N₁.prod N₂).map (fun z ↦ (θh₁ n ω.1, θh₂ n ω.2) + (√(n : ℝ))⁻¹ • z) =
        (N₁.map fun z ↦ θh₁ n ω.1 + (√(n : ℝ))⁻¹ • z).prod
          (N₂.map fun z ↦ θh₂ n ω.2 + (√(n : ℝ))⁻¹ • z) := by
      rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
      rfl
    rw [hmap]
    exact tvDist_prod_le _ _ _ _

end Product

/-! ### Joint convergence in law of independent statistics -/

section Joint

variable {Ω₁ Ω₂ Ω₁' Ω₂' : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  {mΩ₁' : MeasurableSpace Ω₁'} {mΩ₂' : MeasurableSpace Ω₂'}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {Q₁ : Measure Ω₁'} {Q₂ : Measure Ω₂'} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {E F : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [TopologicalSpace.PseudoMetrizableSpace E]
  [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F] [TopologicalSpace.PseudoMetrizableSpace F]

/-- **Joint convergence in law of statistics of two independent experiments.** If
`X₁,n ⇒ Z₁` under `P₁` and `X₂,n ⇒ Z₂` under `P₂`, then under `P₁ ⊗ P₂` the pair
`(X₁,n, X₂,n)` converges in law to `(Z₁, Z₂)` under `Q₁ ⊗ Q₂`, whose law is the product of the
two limit laws. -/
theorem _root_.MeasureTheory.TendstoInDistribution.prodMk_of_prod {X₁ : ℕ → Ω₁ → E}
    {X₂ : ℕ → Ω₂ → F} {Z₁ : Ω₁' → E} {Z₂ : Ω₂' → F}
    (h₁ : TendstoInDistribution X₁ atTop Z₁ (fun _ ↦ P₁) Q₁)
    (h₂ : TendstoInDistribution X₂ atTop Z₂ (fun _ ↦ P₂) Q₂) :
    TendstoInDistribution (fun n ω ↦ (X₁ n ω.1, X₂ n ω.2)) atTop (fun ω' ↦ (Z₁ ω'.1, Z₂ ω'.2))
      (fun _ ↦ P₁.prod P₂) (Q₁.prod Q₂) where
  forall_aemeasurable n :=
    ((h₁.forall_aemeasurable n).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst)).prodMk
      ((h₂.forall_aemeasurable n).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd))
  aemeasurable_limit :=
    (h₁.aemeasurable_limit.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      (h₂.aemeasurable_limit.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  tendsto := by
    have hc := (ProbabilityMeasure.continuous_prod (α := E) (β := F)).tendsto
      ((⟨Q₁.map Z₁, inferInstance⟩ : ProbabilityMeasure E),
        (⟨Q₂.map Z₂, inferInstance⟩ : ProbabilityMeasure F))
    have h := hc.comp (h₁.tendsto.prodMk_nhds h₂.tendsto)
    have hseq : (fun n ↦ (⟨(P₁.prod P₂).map (fun ω ↦ (X₁ n ω.1, X₂ n ω.2)), inferInstance⟩ :
        ProbabilityMeasure (E × F))) = (fun μ : ProbabilityMeasure E × ProbabilityMeasure F ↦
          μ.1.prod μ.2) ∘ fun n ↦ ((⟨P₁.map (X₁ n), inferInstance⟩ : ProbabilityMeasure E),
            (⟨P₂.map (X₂ n), inferInstance⟩ : ProbabilityMeasure F)) := by
      funext n
      exact Subtype.ext (Measure.map_prod_map_of_aemeasurable P₁ P₂ (h₁.forall_aemeasurable n)
        (h₂.forall_aemeasurable n)).symm
    have hlim : (⟨(Q₁.prod Q₂).map (fun ω' ↦ (Z₁ ω'.1, Z₂ ω'.2)), inferInstance⟩ :
        ProbabilityMeasure (E × F)) = ProbabilityMeasure.prod
          (⟨Q₁.map Z₁, inferInstance⟩ : ProbabilityMeasure E) ⟨Q₂.map Z₂, inferInstance⟩ :=
      Subtype.ext (Measure.map_prod_map_of_aemeasurable Q₁ Q₂ h₁.aemeasurable_limit
        h₂.aemeasurable_limit).symm
    rw [hseq, hlim]
    exact h

end Joint

end PosteriorLimit

end CausalInference
