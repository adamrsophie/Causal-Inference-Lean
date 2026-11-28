/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.AnchoredPredictor
public import CausalInference.Transport.ScaleAlignment
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurable functions with shift invariant increments are affine

**The local Cauchy equation.** Let `I` be a set of reals and `H : ℝ → ℝ`. Say that the
increments of `H` on `I` depend only on the shift when
`H(η₁ + γ) - H(η₁) = H(η₂ + γ) - H(η₂)` whenever `η₁, η₁ + γ, η₂, η₂ + γ ∈ I`. If `I` is order
connected and `H` is measurable on `I` (the function equal to `H` on `I` and to `0` outside is
measurable), then `H` is affine on `I` (`affine_on_ordConnected_of_sub_eq`); the converse holds
with no regularity (`forall_sub_eq_iff_affine_of_measurable`). The proof first treats a compact
interval `[a, b]`, `a < b` (`affine_on_Icc_of_sub_eq`): `ψ(r) = H(a + r (b - a)) - H(a)` is
additive on `[0, 1]`, so `Φ(s) = ⌊s⌋ ψ(1) + ψ(fract s)` is an additive map `ℝ → ℝ`; it is
measurable, hence continuous (`AddMonoidHom.continuous_of_measurable`) and linear, and
`Φ = ψ` on `[0, 1)`. Segments of `I` through two fixed points then share one line. On the whole
line the condition is that `H(v) - H(u)` is a function of `v - u` (`exists_sub_eq_iff_affine`).

**The bridge to the differentiable case.** A function continuous on a measurable set is
measurable on it (`measurable_indicator_of_continuousOn`); in particular a function
differentiable on `(a, b)` is measurable there. So the characterization
`Transport.forall_sub_eq_iff_affine`, which assumes differentiability on `(a, b)`, holds under
continuity on `(a, b)` (`forall_sub_eq_iff_affine_of_continuousOn`) and, more generally, under
measurability on any order connected set.

**The anchored comparison on a misaligned scale.** A model on the link `g` with mean function
`g⁻¹` gives the arms the predictors of an `AnchoredModel`; an effect reported on the scale `h`
compares the means through `ψ = h ∘ g⁻¹`. If `ψ` is measurable and not affine on an order
connected set `I` on which `g ∘ g⁻¹` is the identity, there are an anchored model with shared
effect modifiers and two covariate values `x₁`, `x₂` with all predictors in `I` such that, with
both trials concentrated at `x₁` and the target at `x₂`, the anchored comparison recovers the
target average conditional effect on the model scale `g` but not on the reporting scale `h`
(`exists_anchoredEstimand_ne_of_not_affine`). Two cases with numbers, for an identity link on
risks `(1/5, 2/5)` at `x₁` and `(2/5, 3/5)` at `x₂`, with common risk difference `1/5`: reported
as a log risk ratio, the anchored comparison is `log 2` and the target `log (3/2)`
(`anchoredEstimand_log_example`); reported as a log odds ratio, `log (8/3)` and `log (9/4)`
(`anchoredEstimand_logit_example`). Neither `log` on `(0, 1]` nor the logit on `(0, 1)` is
affine (`log_not_affine_on_Ioc`, `logit_not_affine_on_Ioo`).

## Main results

* `affine_on_Icc_of_sub_eq`, `affine_on_ordConnected_of_sub_eq`,
  `forall_sub_eq_iff_affine_of_measurable`, `exists_sub_eq_iff_affine`.
* `measurable_indicator_of_continuousOn`, `forall_sub_eq_iff_affine_of_continuousOn`.
* `exists_anchoredEstimand_ne_of_not_affine`.
* `log_not_affine_on_Ioc`, `logit_not_affine_on_Ioo`, `anchoredEstimand_log_example`,
  `anchoredEstimand_logit_example`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory Set EffectMeasure

/-! ### The local Cauchy equation -/

/-- **Shift invariant increments on a compact interval make a measurable function affine.** If
`a < b`, `H` is measurable on `[a, b]` and `H(η₁ + γ) - H(η₁) = H(η₂ + γ) - H(η₂)` whenever the
four points lie in `[a, b]`, then `H` is affine on `[a, b]`. -/
theorem affine_on_Icc_of_sub_eq {H : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hH : Measurable ((Icc a b).indicator H))
    (hinc : ∀ η₁ η₂ γ, η₁ ∈ Icc a b → η₁ + γ ∈ Icc a b → η₂ ∈ Icc a b → η₂ + γ ∈ Icc a b →
      H (η₁ + γ) - H η₁ = H (η₂ + γ) - H η₂) :
    ∃ k l : ℝ, ∀ η ∈ Icc a b, H η = k * η + l := by
  set L := b - a with hL
  have hL0 : 0 < L := sub_pos.2 hab
  set ψ : ℝ → ℝ := fun r => H (a + r * L) - H a with hψ
  have mem : ∀ r, 0 ≤ r → r ≤ 1 → a + r * L ∈ Icc a b := fun r h0 h1 =>
    ⟨by nlinarith, by nlinarith⟩
  have hadd : ∀ r₁ r₂, 0 ≤ r₁ → 0 ≤ r₂ → r₁ + r₂ ≤ 1 → ψ (r₁ + r₂) = ψ r₁ + ψ r₂ := by
    intro r₁ r₂ h₁ h₂ h₁₂
    have e := hinc a (a + r₁ * L) (r₂ * L) ⟨le_rfl, hab.le⟩ (mem r₂ h₂ (by linarith))
      (mem r₁ h₁ (by linarith))
      (by rw [show a + r₁ * L + r₂ * L = a + (r₁ + r₂) * L by ring]
          exact mem _ (by linarith) h₁₂)
    simp only [hψ]
    rw [show a + (r₁ + r₂) * L = a + r₁ * L + r₂ * L by ring]
    linarith
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  -- a measurable function agreeing with `ψ` on `[0, 1]`
  set ψ' : ℝ → ℝ := fun r => (Icc a b).indicator H (a + r * L) - H a with hψ'
  have hψ'm : Measurable ψ' :=
    (hH.comp (by fun_prop : Measurable fun r : ℝ => a + r * L)).sub_const _
  have hψ'eq : ∀ s : ℝ, ψ' (Int.fract s) = ψ (Int.fract s) := fun s => by
    simp only [hψ', hψ, indicator_of_mem (mem _ (Int.fract_nonneg s) (Int.fract_lt_one s).le)]
  have hΦadd : ∀ s t : ℝ, ((⌊s + t⌋ : ℤ) : ℝ) * ψ 1 + ψ' (Int.fract (s + t)) =
      (((⌊s⌋ : ℤ) : ℝ) * ψ 1 + ψ' (Int.fract s)) + (((⌊t⌋ : ℤ) : ℝ) * ψ 1 + ψ' (Int.fract t)) := by
    intro s t
    rw [hψ'eq, hψ'eq, hψ'eq]
    have fs0 := Int.fract_nonneg s
    have ft0 := Int.fract_nonneg t
    have fs1 := Int.fract_lt_one s
    have ft1 := Int.fract_lt_one t
    rcases lt_or_ge (Int.fract s + Int.fract t) 1 with hlt | hge
    · rw [Int.floor_add_eq_add_iff.2 hlt, Int.fract_add_eq_add_iff.2 hlt,
        hadd _ _ fs0 ft0 hlt.le]
      push_cast
      ring
    · rw [Int.floor_add_eq_add_add_one_iff.2 hge, Int.fract_add_eq_add_sub_one_iff.2 hge]
      have e1 := hadd (Int.fract s + Int.fract t - 1) (1 - Int.fract t) (by linarith)
        (by linarith) (by linarith)
      have e2 := hadd (Int.fract t) (1 - Int.fract t) ft0 (by linarith) (by linarith)
      rw [show Int.fract s + Int.fract t - 1 + (1 - Int.fract t) = Int.fract s by ring] at e1
      rw [show Int.fract t + (1 - Int.fract t) = 1 by ring] at e2
      push_cast
      linarith
  let K : ℝ →+ ℝ :=
    { toFun := fun s => ((⌊s⌋ : ℤ) : ℝ) * ψ 1 + ψ' (Int.fract s)
      map_zero' := by
        have h := hψ'eq 0
        rw [Int.fract_zero] at h
        simp [h, hψ0]
      map_add' := hΦadd }
  have hKm : Measurable K :=
    ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp Int.measurable_floor |>.mul_const _).add
      (hψ'm.comp measurable_fract)
  have hK : Continuous K := Measure.AddMonoidHom.continuous_of_measurable K hKm
  have hlin : ∀ r, 0 ≤ r → r ≤ 1 → ψ r = r * ψ 1 := by
    intro r h0 h1
    have hK1 : K 1 = ψ 1 := by
      change ((⌊(1 : ℝ)⌋ : ℤ) : ℝ) * ψ 1 + ψ' (Int.fract 1) = ψ 1
      rw [hψ'eq]
      simp [hψ0]
    rcases h1.lt_or_eq with h1 | rfl
    · have := map_real_smul K hK r 1
      simp only [smul_eq_mul, mul_one, hK1] at this
      change ((⌊r⌋ : ℤ) : ℝ) * ψ 1 + ψ' (Int.fract r) = r * ψ 1 at this
      rwa [hψ'eq, Int.floor_eq_zero_iff.2 ⟨h0, h1⟩, Int.fract_eq_self.2 ⟨h0, h1⟩, Int.cast_zero,
        zero_mul, zero_add] at this
    · ring
  refine ⟨ψ 1 / L, H a - ψ 1 / L * a, fun t ht => ?_⟩
  have hr0 : 0 ≤ (t - a) / L := div_nonneg (by linarith [ht.1]) hL0.le
  have hr1 : (t - a) / L ≤ 1 := (div_le_one hL0).2 (by linarith [ht.2])
  have e := hlin _ hr0 hr1
  have h1 : ψ 1 = H (a + L) - H a := by simp [hψ]
  simp only [hψ] at e
  rw [div_mul_cancel₀ _ hL0.ne', add_sub_cancel] at e
  rw [h1]
  field_simp at e ⊢
  linear_combination e

/-- **Shift invariant increments on an order connected set make a measurable function affine.**
If `I` is order connected, `H` is measurable on `I` and the increments of `H` on `I` depend only
on the shift, then `H` is affine on `I`. -/
theorem affine_on_ordConnected_of_sub_eq {H : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hH : Measurable (I.indicator H))
    (hinc : ∀ η₁ η₂ γ, η₁ ∈ I → η₁ + γ ∈ I → η₂ ∈ I → η₂ + γ ∈ I →
      H (η₁ + γ) - H η₁ = H (η₂ + γ) - H η₂) :
    ∃ k l : ℝ, ∀ η ∈ I, H η = k * η + l := by
  by_cases h2 : ∃ a ∈ I, ∃ b ∈ I, a < b
  · obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := h2
    refine ⟨(H b₀ - H a₀) / (b₀ - a₀), H a₀ - (H b₀ - H a₀) / (b₀ - a₀) * a₀, fun t ht => ?_⟩
    have hlo : min a₀ t ∈ I := by rcases min_choice a₀ t with h | h <;> rw [h] <;> assumption
    have hhi : max b₀ t ∈ I := by rcases max_choice b₀ t with h | h <;> rw [h] <;> assumption
    have hsub : Icc (min a₀ t) (max b₀ t) ⊆ I := hI.out hlo hhi
    have hlohi : min a₀ t < max b₀ t :=
      (min_le_left a₀ t).trans_lt (hab₀.trans_le (le_max_left b₀ t))
    have hmeas : Measurable ((Icc (min a₀ t) (max b₀ t)).indicator H) := by
      have e : (Icc (min a₀ t) (max b₀ t)).indicator H =
          (Icc (min a₀ t) (max b₀ t)).indicator (I.indicator H) := by
        rw [indicator_indicator, inter_eq_left.2 hsub]
      rw [e]
      exact hH.indicator measurableSet_Icc
    obtain ⟨c, d, hcd⟩ := affine_on_Icc_of_sub_eq hlohi hmeas
      fun η₁ η₂ γ h1 h1' h2 h2' => hinc η₁ η₂ γ (hsub h1) (hsub h1') (hsub h2) (hsub h2')
    have ma : a₀ ∈ Icc (min a₀ t) (max b₀ t) :=
      ⟨min_le_left _ _, hab₀.le.trans (le_max_left _ _)⟩
    have mb : b₀ ∈ Icc (min a₀ t) (max b₀ t) :=
      ⟨(min_le_left _ _).trans hab₀.le, le_max_left _ _⟩
    have mt : t ∈ Icc (min a₀ t) (max b₀ t) := ⟨min_le_right _ _, le_max_right _ _⟩
    rw [hcd a₀ ma, hcd b₀ mb, hcd t mt]
    have hne : b₀ - a₀ ≠ 0 := sub_ne_zero.2 hab₀.ne'
    field_simp
    ring
  · push Not at h2
    rcases I.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
    · exact ⟨0, 0, fun t ht => ht.elim⟩
    · refine ⟨0, H t₀, fun t ht => ?_⟩
      have e : t = t₀ := le_antisymm (h2 t₀ ht₀ t ht) (h2 t ht t₀ ht₀)
      rw [e]
      ring

/-- **The characterization on an order connected set.** For `H` measurable on an order
connected set `I`, the increments of `H` on `I` depend only on the shift exactly when `H` is
affine on `I`. The direction from affine needs no measurability. -/
theorem forall_sub_eq_iff_affine_of_measurable {H : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hH : Measurable (I.indicator H)) :
    (∀ η₁ η₂ γ, η₁ ∈ I → η₁ + γ ∈ I → η₂ ∈ I → η₂ + γ ∈ I →
      H (η₁ + γ) - H η₁ = H (η₂ + γ) - H η₂) ↔ ∃ k l : ℝ, ∀ η ∈ I, H η = k * η + l := by
  refine ⟨affine_on_ordConnected_of_sub_eq hI hH, ?_⟩
  rintro ⟨k, l, h⟩ η₁ η₂ γ h1 h1' h2 h2'
  rw [h _ h1, h _ h1', h _ h2, h _ h2']
  ring

/-- **The measurable Cauchy equation on the line.** For a measurable `H : ℝ → ℝ`, the increment
`H(v) - H(u)` is a function of `v - u` exactly when `H` is affine. -/
theorem exists_sub_eq_iff_affine {H : ℝ → ℝ} (hH : Measurable H) :
    (∃ F : ℝ → ℝ, ∀ u v, H v - H u = F (v - u)) ↔ ∃ k l : ℝ, ∀ t, H t = k * t + l := by
  have hm : Measurable ((univ : Set ℝ).indicator H) := by rwa [indicator_univ]
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨k, l, h⟩ := affine_on_ordConnected_of_sub_eq ordConnected_univ hm
      fun η₁ η₂ γ _ _ _ _ => by
        rw [hF η₁ (η₁ + γ), hF η₂ (η₂ + γ), add_sub_cancel_left, add_sub_cancel_left]
    exact ⟨k, l, fun t => h t trivial⟩
  · rintro ⟨k, l, h⟩
    exact ⟨fun d => k * d, fun u v => by rw [h, h]; ring⟩

/-! ### The bridge to the differentiable case -/

/-- **A function continuous on a measurable set is measurable on it.** -/
theorem measurable_indicator_of_continuousOn {ψ : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : ContinuousOn ψ s) : Measurable (s.indicator ψ) := by
  classical
  have := h.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hs
  convert this using 1
  funext x
  simp only [indicator, piecewise]

/-- **The characterization under continuity.** For `ψ` continuous on `(a, b)`, the difference
`ψ(η + γ) - ψ(η)` does not depend on `η` (for all points in `(a, b)`) exactly when `ψ` is affine
on `(a, b)`. With `DifferentiableOn.continuousOn` this contains
`Transport.forall_sub_eq_iff_affine`. -/
theorem forall_sub_eq_iff_affine_of_continuousOn {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContinuousOn ψ (Ioo a b)) :
    (∀ η₁ η₂ γ, η₁ ∈ Ioo a b → η₁ + γ ∈ Ioo a b → η₂ ∈ Ioo a b → η₂ + γ ∈ Ioo a b →
      ψ (η₁ + γ) - ψ η₁ = ψ (η₂ + γ) - ψ η₂) ↔ ∃ k l, ∀ η ∈ Ioo a b, ψ η = k * η + l :=
  forall_sub_eq_iff_affine_of_measurable ordConnected_Ioo
    (measurable_indicator_of_continuousOn measurableSet_Ioo hψ)

/-! ### The anchored comparison on a misaligned scale -/

/-- The conditional mean `g⁻¹(η_t(x))` of the arm `t` of an anchored model with mean function
`ginv`. -/
noncomputable def AnchoredModel.condMean {ι : Type*} {p : ℕ} (M : AnchoredModel ι p)
    (ginv : ℝ → ℝ) (t : ι) (x : Fin p → ℝ) : ℝ :=
  ginv (M.predictor t x)

/-- The anchored model on one covariate for the treatments `0, 1, 2` with predictors
`η_0(x) = η_1(x) = x` and `η_2(x) = x + γ`: no interactions, so every set of treatments shares
its effect modifiers. -/
def shiftModel (γ : ℝ) : AnchoredModel (Fin 3) 1 := ⟨0, fun _ => 1, ![0, 0, γ], fun _ => 0⟩

theorem shiftModel_predictor (γ : ℝ) (t : Fin 3) (x : Fin 1 → ℝ) :
    (shiftModel γ).predictor t x = x 0 + ![0, 0, γ] t := by
  simp [shiftModel, AnchoredModel.predictor, anchoredPredictor]

theorem shiftModel_isAnchoredAt (γ : ℝ) : (shiftModel γ).IsAnchoredAt 0 := ⟨rfl, rfl⟩

theorem shiftModel_shared (γ : ℝ) (S : Set (Fin 3)) : (shiftModel γ).SharedEffectModifiers S :=
  fun _ _ _ _ => rfl

/-- The anchored comparison of the shift model with both trials at `x₁`, on a scale `h`, is the
difference `h(g⁻¹(x₁ + γ)) - h(g⁻¹(x₁))`; the target effect at `x₂` is the same difference at
`x₂`. -/
private theorem shiftModel_values (γ : ℝ) (ginv h : ℝ → ℝ) (x₁ x₂ : Fin 1 → ℝ) :
    anchoredEstimand (Measure.dirac x₁)
        (linkContrast h ((shiftModel γ).condMean ginv 1) ((shiftModel γ).condMean ginv 0))
        (linkContrast h ((shiftModel γ).condMean ginv 2) ((shiftModel γ).condMean ginv 0)) =
      h (ginv (x₁ 0 + γ)) - h (ginv (x₁ 0)) ∧
    linkConditional h (Measure.dirac x₂) ((shiftModel γ).condMean ginv 1)
        ((shiftModel γ).condMean ginv 2) = h (ginv (x₂ 0 + γ)) - h (ginv (x₂ 0)) := by
  simp only [anchoredEstimand, linkConditional, linkContrast, integral_dirac,
    AnchoredModel.condMean, shiftModel_predictor]
  simp

/-- **The anchored comparison on a misaligned scale does not recover the target.** Let `g` be a
link with `g(g⁻¹(η)) = η` on an order connected set `I`, and let `ψ = h ∘ g⁻¹` be measurable and
not affine on `I`. Then there are a shift `γ` and covariate values `x₁, x₂` such that the
anchored model `shiftModel γ` (anchored at `0`, every set of treatments sharing its effect
modifiers) has all its predictors at `x₁` and `x₂` in `I`, and, with the trials of `1` and of
`2` against `0` concentrated at `x₁` and the target at `x₂`:

* on the model scale `g`, the anchored comparison is the target average conditional effect of
  `2` against `1`, both equal to `γ = γ_2 - γ_1`;
* on the reporting scale `h`, the anchored comparison differs from the target average
  conditional effect. -/
theorem exists_anchoredEstimand_ne_of_not_affine {I : Set ℝ} (hI : I.OrdConnected)
    {g ginv h : ℝ → ℝ} (hinv : ∀ η ∈ I, g (ginv η) = η)
    (hψ : Measurable (I.indicator fun η => h (ginv η)))
    (hna : ¬ ∃ k l : ℝ, ∀ η ∈ I, h (ginv η) = k * η + l) :
    ∃ (γ : ℝ) (x₁ x₂ : Fin 1 → ℝ),
      (∀ t, (shiftModel γ).predictor t x₁ ∈ I ∧ (shiftModel γ).predictor t x₂ ∈ I) ∧
      anchoredEstimand (Measure.dirac x₁)
          (linkContrast g ((shiftModel γ).condMean ginv 1) ((shiftModel γ).condMean ginv 0))
          (linkContrast g ((shiftModel γ).condMean ginv 2) ((shiftModel γ).condMean ginv 0)) =
        (shiftModel γ).γ 2 - (shiftModel γ).γ 1 ∧
      linkConditional g (Measure.dirac x₂) ((shiftModel γ).condMean ginv 1)
          ((shiftModel γ).condMean ginv 2) = (shiftModel γ).γ 2 - (shiftModel γ).γ 1 ∧
      anchoredEstimand (Measure.dirac x₁)
          (linkContrast h ((shiftModel γ).condMean ginv 1) ((shiftModel γ).condMean ginv 0))
          (linkContrast h ((shiftModel γ).condMean ginv 2) ((shiftModel γ).condMean ginv 0)) ≠
        linkConditional h (Measure.dirac x₂) ((shiftModel γ).condMean ginv 1)
          ((shiftModel γ).condMean ginv 2) := by
  rw [← forall_sub_eq_iff_affine_of_measurable hI hψ] at hna
  push Not at hna
  obtain ⟨η₁, η₂, γ, h1, h1', h2, h2', hne⟩ := hna
  have hγ : (shiftModel γ).γ 2 - (shiftModel γ).γ 1 = γ := by simp [shiftModel]
  refine ⟨γ, fun _ => η₁, fun _ => η₂, fun t => ?_, ?_, ?_, ?_⟩
  · rw [shiftModel_predictor, shiftModel_predictor]
    fin_cases t <;> simp [h1, h1', h2, h2']
  · rw [(shiftModel_values γ ginv g _ (fun _ => η₂)).1, hγ, hinv _ h1, hinv _ h1']
    ring
  · rw [(shiftModel_values γ ginv g (fun _ => η₁) _).2, hγ, hinv _ h2, hinv _ h2']
    ring
  · rw [(shiftModel_values γ ginv h _ (fun _ => η₂)).1,
      (shiftModel_values γ ginv h (fun _ => η₁) _).2]
    exact hne

/-! ### The log and logit reporting scales -/

/-- The increments of `log` over the risk pairs `(1/5, 2/5)` and `(2/5, 3/5)` differ:
`log 2 ≠ log (3/2)`. -/
theorem log_sub_example :
    Real.log (2 / 5) - Real.log (1 / 5) = Real.log 2 ∧
      Real.log (3 / 5) - Real.log (2 / 5) = Real.log (3 / 2) ∧ Real.log 2 ≠ Real.log (3 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  · rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  · intro h
    have := Real.log_injOn_pos (by norm_num : (2 : ℝ) ∈ Ioi 0)
      (by norm_num : (3 / 2 : ℝ) ∈ Ioi 0) h
    norm_num at this

/-- The logit of the risks `1/5`, `2/5` and `3/5`. -/
theorem logit_values :
    logit (1 / 5) = Real.log (1 / 4) ∧ logit (2 / 5) = Real.log (2 / 3) ∧
      logit (3 / 5) = Real.log (3 / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [logit, odds]

/-- The increments of the logit over the risk pairs `(1/5, 2/5)` and `(2/5, 3/5)` differ:
`log (8/3) ≠ log (9/4)`. -/
theorem logit_sub_example :
    logit (2 / 5) - logit (1 / 5) = Real.log (8 / 3) ∧
      logit (3 / 5) - logit (2 / 5) = Real.log (9 / 4) ∧ Real.log (8 / 3) ≠ Real.log (9 / 4) := by
  obtain ⟨l1, l2, l3⟩ := logit_values
  refine ⟨?_, ?_, ?_⟩
  · rw [l1, l2, ← Real.log_div (by norm_num) (by norm_num)]; norm_num
  · rw [l2, l3, ← Real.log_div (by norm_num) (by norm_num)]; norm_num
  · intro h
    have := Real.log_injOn_pos (by norm_num : (8 / 3 : ℝ) ∈ Ioi 0)
      (by norm_num : (9 / 4 : ℝ) ∈ Ioi 0) h
    norm_num at this

/-- **The logarithm is not affine on the risks `(0, 1]`.** -/
theorem log_not_affine_on_Ioc : ¬ ∃ k l : ℝ, ∀ η ∈ Ioc (0 : ℝ) 1, Real.log η = k * η + l := by
  rintro ⟨k, l, hkl⟩
  have e := (forall_sub_eq_iff_affine_of_measurable ordConnected_Ioc
    (Real.measurable_log.indicator measurableSet_Ioc)).2 ⟨k, l, hkl⟩ (1 / 5) (2 / 5) (1 / 5)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
  obtain ⟨h1, h2, hne⟩ := log_sub_example
  norm_num at e h1 h2
  exact hne (h1.symm.trans (e.trans h2))

/-- **The logit is not affine on the risks `(0, 1)`.** -/
theorem logit_not_affine_on_Ioo : ¬ ∃ k l : ℝ, ∀ η ∈ Ioo (0 : ℝ) 1, logit η = k * η + l := by
  rintro ⟨k, l, hkl⟩
  have e := (forall_sub_eq_iff_affine_of_measurable ordConnected_Ioo
    (measurable_logit.indicator measurableSet_Ioo)).2 ⟨k, l, hkl⟩ (1 / 5) (2 / 5) (1 / 5)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
  obtain ⟨h1, h2, hne⟩ := logit_sub_example
  norm_num at e h1 h2
  exact hne (h1.symm.trans (e.trans h2))

/-- **An identity link reported as a log risk ratio.** In `shiftModel (1/5)` with the identity
link, the risks are `(1/5, 1/5, 2/5)` at `x₁ = 1/5` and `(2/5, 2/5, 3/5)` at `x₂ = 2/5`, all in
`(0, 1)`. With both trials at `x₁` and the target at `x₂`, the anchored comparison of `2`
against `1` on the identity scale is the target risk difference `1/5`; on the log scale the
anchored comparison is `log 2` and the target log risk ratio is `log (3/2)`. -/
theorem anchoredEstimand_log_example :
    let M := shiftModel (1 / 5)
    let x₁ : Fin 1 → ℝ := fun _ => 1 / 5
    let x₂ : Fin 1 → ℝ := fun _ => 2 / 5
    (∀ t, M.condMean id t x₁ ∈ Ioo (0 : ℝ) 1 ∧ M.condMean id t x₂ ∈ Ioo (0 : ℝ) 1) ∧
      anchoredEstimand (Measure.dirac x₁) (linkContrast id (M.condMean id 1) (M.condMean id 0))
          (linkContrast id (M.condMean id 2) (M.condMean id 0)) = 1 / 5 ∧
      linkConditional id (Measure.dirac x₂) (M.condMean id 1) (M.condMean id 2) = 1 / 5 ∧
      anchoredEstimand (Measure.dirac x₁)
          (linkContrast Real.log (M.condMean id 1) (M.condMean id 0))
          (linkContrast Real.log (M.condMean id 2) (M.condMean id 0)) = Real.log 2 ∧
      linkConditional Real.log (Measure.dirac x₂) (M.condMean id 1) (M.condMean id 2) =
        Real.log (3 / 2) ∧
      Real.log 2 ≠ Real.log (3 / 2) := by
  intro M x₁ x₂
  obtain ⟨h1, h2, hne⟩ := log_sub_example
  have v := shiftModel_values (1 / 5) id Real.log x₁ x₂
  have w := shiftModel_values (1 / 5) id id x₁ x₂
  simp only [id, x₁, x₂] at v w
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, hne⟩
  · simp only [AnchoredModel.condMean, M, shiftModel_predictor, id, x₁, x₂]
    fin_cases t <;> norm_num
  · rw [w.1]; norm_num
  · rw [w.2]; norm_num
  · rw [v.1]; norm_num at h1 ⊢; exact h1
  · rw [v.2]; norm_num at h2 ⊢; exact h2

/-- **An identity link reported as a log odds ratio.** In the model of
`anchoredEstimand_log_example`, on the logit scale the anchored comparison is `log (8/3)` and
the target log odds ratio is `log (9/4)`, while on the identity scale both are `1/5`. -/
theorem anchoredEstimand_logit_example :
    let M := shiftModel (1 / 5)
    let x₁ : Fin 1 → ℝ := fun _ => 1 / 5
    let x₂ : Fin 1 → ℝ := fun _ => 2 / 5
    anchoredEstimand (Measure.dirac x₁) (linkContrast logit (M.condMean id 1) (M.condMean id 0))
        (linkContrast logit (M.condMean id 2) (M.condMean id 0)) = Real.log (8 / 3) ∧
      linkConditional logit (Measure.dirac x₂) (M.condMean id 1) (M.condMean id 2) =
        Real.log (9 / 4) ∧
      Real.log (8 / 3) ≠ Real.log (9 / 4) := by
  intro M x₁ x₂
  obtain ⟨h1, h2, hne⟩ := logit_sub_example
  have v := shiftModel_values (1 / 5) id logit x₁ x₂
  simp only [id, x₁, x₂] at v
  refine ⟨?_, ?_, hne⟩
  · rw [v.1]; norm_num at h1 ⊢; exact h1
  · rw [v.2]; norm_num at h2 ⊢; exact h2

end IndirectComparison

end CausalInference
