/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.Model
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The aggregate mean is strictly monotone in a shift of the linear predictor

For a covariate law `F`, an inverse link `g⁻¹` and a function `h` of the covariates, the
aggregate mean as a function of a scalar shift is `Θ(c) = ∫ g⁻¹(c + h(x)) F(dx)`
(`shiftMean`). An aggregate arm mean of the multilevel model is `Θ` at the cell intercept
`μ_j + γ_k`, with `h(x) = xᵀ(β₁ + β₂,k)` (`armMean_eq_shiftMean`).

## Main results

* `shiftMean_strictMono`: for a strictly increasing `g⁻¹` with `g⁻¹(c + h)` integrable for every
  `c`, `Θ` is strictly increasing.
* `shiftMean_continuous`: for a continuous monotone `g⁻¹` and measurable `h`, `Θ` is continuous.
* `range_shiftMean`: for a continuous strictly increasing `g⁻¹`, the range of `Θ` is the range of
  `g⁻¹`; `range_shiftMean_Ioo` names it `(ℓ, u)` from the limits of `g⁻¹`.
* `existsUnique_shiftMean_eq`: every value in the range of `g⁻¹` is the aggregate mean of exactly
  one shift.
* `intercept_eq_of_armMean_eq`: two models with the same slope vector `β₁ + β₂,k` and the same
  aggregate arm mean have the same cell intercept `μ + γ_k`.
* `not_injective_shiftMean_const`: without strict monotonicity of `g⁻¹` the aggregate mean does
  not determine the shift: for the constant inverse link `0` every shift gives the mean `0`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **aggregate mean as a function of a shift** `Θ(c) = ∫ g⁻¹(c + h(x)) F(dx)`. -/
noncomputable def shiftMean (F : Measure 𝒳) (ginv : ℝ → ℝ) (h : 𝒳 → ℝ) (c : ℝ) : ℝ :=
  ∫ x, ginv (c + h x) ∂F

variable {F : Measure 𝒳} {ginv : ℝ → ℝ} {h : 𝒳 → ℝ}

/-- The integral of an everywhere positive integrable function under a probability law is
positive. -/
theorem integral_pos_of_forall_pos [IsProbabilityMeasure F] {f : 𝒳 → ℝ} (hf : Integrable f F)
    (hpos : ∀ x, 0 < f x) : 0 < ∫ x, f x ∂F := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hf,
    show Function.support f = Set.univ from Set.eq_univ_of_forall fun x => (hpos x).ne']
  simp

/-- **The aggregate mean is strictly increasing in the shift.** -/
theorem shiftMean_strictMono [IsProbabilityMeasure F] (hmono : StrictMono ginv)
    (hint : ∀ c, Integrable (fun x => ginv (c + h x)) F) : StrictMono (shiftMean F ginv h) := by
  intro c₁ c₂ hc
  have := integral_pos_of_forall_pos ((hint c₂).sub (hint c₁))
    fun x => sub_pos.2 (hmono (by linarith : c₁ + h x < c₂ + h x))
  simp only [Pi.sub_apply] at this
  rw [integral_sub (hint c₂) (hint c₁)] at this
  simp only [shiftMean]
  linarith

/-- **The aggregate mean is continuous in the shift**, by dominated convergence with the bound
`|g⁻¹(c' - 1 + h)| + |g⁻¹(c' + 1 + h)|` near `c'`. -/
theorem shiftMean_continuous (hmono : Monotone ginv) (hcont : Continuous ginv)
    (hh : Measurable h) (hint : ∀ c, Integrable (fun x => ginv (c + h x)) F) :
    Continuous (shiftMean F ginv h) := by
  rw [continuous_iff_continuousAt]
  intro c'
  refine continuousAt_of_dominated
    (bound := fun x => |ginv (c' - 1 + h x)| + |ginv (c' + 1 + h x)|)
    (Eventually.of_forall fun c => (hcont.measurable.comp (hh.const_add c)).aestronglyMeasurable)
    ?_ ((hint _).abs.add (hint _).abs) (ae_of_all _ fun x => ?_)
  · filter_upwards [Ioo_mem_nhds (by linarith : c' - 1 < c') (by linarith : c' < c' + 1)]
      with c hc
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs]
    exact (abs_le_max_abs_abs (hmono (by linarith [hc.1])) (hmono (by linarith [hc.2]))).trans
      (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))
  · exact (hcont.comp (continuous_id.add continuous_const)).continuousAt

/-- The aggregate mean exceeds every value below the range of `g⁻¹`: for `y < g⁻¹(z)` some
shift has `y < Θ(c)`. -/
theorem exists_lt_shiftMean [IsProbabilityMeasure F] (hmono : Monotone ginv)
    (hginv : Measurable ginv) (hh : Measurable h)
    (hint : ∀ c, Integrable (fun x => ginv (c + h x)) F) {y z : ℝ} (hy : y < ginv z) :
    ∃ c, y < shiftMean F ginv h c := by
  set G : ℕ → 𝒳 → ℝ := fun n x => min (ginv (n + h x)) (ginv z)
  have hGm : ∀ n, AEStronglyMeasurable (G n) F := fun n =>
    ((hginv.comp (hh.const_add _)).min measurable_const).aestronglyMeasurable
  have hb : ∀ n, ∀ x, ‖G n x‖ ≤ |ginv (0 + h x)| + |ginv z| := fun n x => by
    rw [Real.norm_eq_abs, abs_le]
    have h1 : min (ginv (0 + h x)) (ginv z) ≤ G n x :=
      min_le_min (hmono (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])) le_rfl
    have h2 : -(|ginv (0 + h x)| + |ginv z|) ≤ min (ginv (0 + h x)) (ginv z) :=
      le_min (by linarith [neg_abs_le (ginv (0 + h x)), abs_nonneg (ginv z)])
        (by linarith [neg_abs_le (ginv z), abs_nonneg (ginv (0 + h x))])
    exact ⟨h2.trans h1, (min_le_right _ _).trans ((le_abs_self _).trans
      (le_add_of_nonneg_left (abs_nonneg _)))⟩
  have hlim : Tendsto (fun n => ∫ x, G n x ∂F) atTop (𝓝 (∫ _, ginv z ∂F)) := by
    refine tendsto_integral_of_dominated_convergence _ hGm ((hint 0).abs.add (integrable_const _))
      (fun n => ae_of_all _ (hb n)) (ae_of_all _ fun x => tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop ⌈z - h x⌉₊] with n hn
    have : z ≤ n + h x := by linarith [Nat.le_ceil (z - h x), (Nat.cast_le (α := ℝ)).2 hn]
    exact (min_eq_right (hmono this)).symm
  rw [integral_const, probReal_univ, one_smul] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hy)).exists
  refine ⟨n, hn.trans_le (integral_mono ?_ (hint n) fun x => min_le_left _ _)⟩
  exact ((hint 0).abs.add (integrable_const _)).mono' (hGm n) (ae_of_all _ (hb n))

/-- The aggregate mean falls below every value above the range of `g⁻¹`, by
`exists_lt_shiftMean` for the reflected link `z ↦ -g⁻¹(-z)`. -/
theorem exists_shiftMean_lt [IsProbabilityMeasure F] (hmono : Monotone ginv)
    (hginv : Measurable ginv) (hh : Measurable h)
    (hint : ∀ c, Integrable (fun x => ginv (c + h x)) F) {y z : ℝ} (hy : ginv z < y) :
    ∃ c, shiftMean F ginv h c < y := by
  have hrefl : ∀ c, shiftMean F (fun z => -ginv (-z)) (fun x => -h x) c =
      -shiftMean F ginv h (-c) := fun c => by
    simp only [shiftMean, ← integral_neg]
    congr 1
    ext x
    rw [show -(c + -h x) = -c + h x by ring]
  obtain ⟨c, hc⟩ := exists_lt_shiftMean (F := F) (ginv := fun z => -ginv (-z)) (h := fun x => -h x)
    (fun a b hab => neg_le_neg (hmono (neg_le_neg hab))) (hginv.comp measurable_neg).neg hh.neg
    (fun c => ((hint (-c)).neg).congr (ae_of_all _ fun x => by
      simp only [Pi.neg_apply]
      rw [show -(c + -h x) = -c + h x by ring]))
    (y := -y) (z := -z) (by simp only [neg_neg]; linarith)
  exact ⟨-c, by rw [hrefl] at hc; linarith⟩

/-- **The range of the aggregate mean is the range of the inverse link.** For a continuous
strictly increasing `g⁻¹` and measurable `h` with `g⁻¹(c + h)` integrable for every `c`, a value
is an aggregate mean of some shift exactly when it is a value of `g⁻¹`. -/
theorem range_shiftMean [IsProbabilityMeasure F] (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hh : Measurable h)
    (hint : ∀ c, Integrable (fun x => ginv (c + h x)) F) :
    Set.range (shiftMean F ginv h) = Set.range ginv := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    by_contra hy
    have key : (∀ z, ginv z < shiftMean F ginv h c) ∨ (∀ z, shiftMean F ginv h c < ginv z) := by
      by_contra hne
      simp only [not_or, not_forall, not_lt] at hne
      obtain ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩ := hne
      exact hy (intermediate_value_univ z₂ z₁ hcont ⟨hz₂, hz₁⟩)
    rcases key with hk | hk
    · have := integral_pos_of_forall_pos ((integrable_const (shiftMean F ginv h c)).sub (hint c))
        fun x => sub_pos.2 (hk _)
      simp only [Pi.sub_apply] at this
      rw [integral_sub (integrable_const _) (hint c), integral_const, probReal_univ,
        one_smul] at this
      simp only [shiftMean] at this
      linarith
    · have := integral_pos_of_forall_pos ((hint c).sub (integrable_const (shiftMean F ginv h c)))
        fun x => sub_pos.2 (hk _)
      simp only [Pi.sub_apply] at this
      rw [integral_sub (hint c) (integrable_const _), integral_const, probReal_univ,
        one_smul] at this
      simp only [shiftMean] at this
      linarith
  · rintro ⟨z, rfl⟩
    obtain ⟨c₂, hc₂⟩ := exists_lt_shiftMean hmono.monotone hcont.measurable hh hint
      (show ginv z < ginv (z + 1) from hmono (lt_add_one z))
    obtain ⟨c₁, hc₁⟩ := exists_shiftMean_lt hmono.monotone hcont.measurable hh hint
      (show ginv (z - 1) < ginv z from hmono (by linarith))
    exact intermediate_value_univ c₁ c₂ (shiftMean_continuous hmono.monotone hcont hh hint)
      ⟨hc₁.le, hc₂.le⟩

/-- **The range is `(ℓ, u)`** when `g⁻¹` maps into `(ℓ, u)` with limits `ℓ` at `-∞` and `u` at
`+∞` (the logit and probit links with `(ℓ, u) = (0, 1)`). -/
theorem range_shiftMean_Ioo [IsProbabilityMeasure F] (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hh : Measurable h)
    (hint : ∀ c, Integrable (fun x => ginv (c + h x)) F) {ℓ u : ℝ}
    (hmem : ∀ z, ginv z ∈ Set.Ioo ℓ u) (hbot : Tendsto ginv atBot (𝓝 ℓ))
    (htop : Tendsto ginv atTop (𝓝 u)) :
    Set.range (shiftMean F ginv h) = Set.Ioo ℓ u := by
  rw [range_shiftMean hmono hcont hh hint]
  refine Set.Subset.antisymm (Set.range_subset_iff.2 hmem) fun y hy => ?_
  obtain ⟨z₁, hz₁⟩ := (hbot.eventually (gt_mem_nhds hy.1)).exists
  obtain ⟨z₂, hz₂⟩ := (htop.eventually (lt_mem_nhds hy.2)).exists
  exact intermediate_value_univ z₁ z₂ hcont ⟨hz₁.le, hz₂.le⟩

/-- **An aggregate mean determines the shift**: every value `θ` in the range of `g⁻¹` is
`Θ(c)` for exactly one `c`. -/
theorem existsUnique_shiftMean_eq [IsProbabilityMeasure F] (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hh : Measurable h)
    (hint : ∀ c, Integrable (fun x => ginv (c + h x)) F) {θ : ℝ} (hθ : θ ∈ Set.range ginv) :
    ∃! c, shiftMean F ginv h c = θ := by
  rw [← range_shiftMean hmono hcont hh hint] at hθ
  obtain ⟨c, hc⟩ := hθ
  exact ⟨c, hc, fun c' hc' => (shiftMean_strictMono hmono hint).injective (hc'.trans hc.symm)⟩

/-- **The failure without strict monotonicity**: for the constant inverse link `0` every shift
gives the aggregate mean `0`, so the mean does not determine the shift (`Θ(0) = Θ(1)`). -/
theorem not_injective_shiftMean_const :
    shiftMean F (fun _ => (0 : ℝ)) h 0 = shiftMean F (fun _ => (0 : ℝ)) h 1 := by
  simp [shiftMean]

/-! ### Arm means of the multilevel model -/

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-- An aggregate arm mean is the shift mean at the cell intercept `α + γ_k` with
`h(x) = xᵀ(β₁ + β₂,k)`. -/
theorem armMean_eq_shiftMean (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (α : ℝ)
    (F : Measure (Fin p → ℝ)) (k : K) :
    M.armMean ginv α F k = shiftMean F ginv (fun x => x ⬝ᵥ (M.β₁ + M.β₂ k)) (α + M.γ k) := by
  simp only [armMean, surface, shiftMean, eta_eq_affine]

/-- **One aggregate mean pins one cell intercept.** For a strictly increasing `g⁻¹` and a
probability law `F` under which `g⁻¹(c + xᵀ(β₁ + β₂,k))` is integrable for every `c`, two models
with the same slope vector `β₁ + β₂,k` and the same aggregate mean of arm `k` have the same cell
intercept `α + γ_k`. -/
theorem intercept_eq_of_armMean_eq {ginv : ℝ → ℝ} (hmono : StrictMono ginv)
    {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F] {M M' : MultilevelModel J K p}
    {α α' : ℝ} {k : K} (hslope : M.β₁ + M.β₂ k = M'.β₁ + M'.β₂ k)
    (hint : ∀ c, Integrable (fun x => ginv (c + x ⬝ᵥ (M.β₁ + M.β₂ k))) F)
    (h : M.armMean ginv α F k = M'.armMean ginv α' F k) : α + M.γ k = α' + M'.γ k := by
  rw [armMean_eq_shiftMean, armMean_eq_shiftMean, ← hslope] at h
  exact (shiftMean_strictMono hmono hint).injective h

end MultilevelModel

end NetworkMetaRegression

end CausalInference
