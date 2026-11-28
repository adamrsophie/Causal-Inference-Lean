/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HeterogeneityUnequalConsistency
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Meta-analysis: the Gaussian model with unequal variances

**The Gaussian random effects model.** Let the pairs `(bᵢ, εᵢ)` be independent across studies
with `(bᵢ, εᵢ) ~ N(0, τ²) ⊗ N(0, vᵢ)`, `τ² ≥ 0`, `a ≤ vᵢ ≤ A`, `0 < a`. Then the estimates
`Yᵢ = θ + bᵢ + εᵢ` satisfy every hypothesis of `IsUnequalVarianceStudies`, with the fourth moment
bound `E (Yᵢ - θ)⁴ ≤ (A + τ²)² E Z⁴` for `Z ~ N(0, 1)` (`isUnequalVarianceStudies_gaussian`): the
law of `bᵢ + εᵢ` is `N(0, vᵢ + τ²)`, the image of `N(0, 1)` under `z ↦ √(vᵢ + τ²) z`. Hence the
DerSimonian and Laird estimators and the pooled estimates are consistent
(`isConsistent_dl_gaussian_unequalVar`).

**A concrete model.** On `Ω = ℕ → ℝ × ℝ` with the product measure
`⊗ᵢ (N(0, τ²) ⊗ N(0, vᵢ))` and the alternating variances `vᵢ = 1` for even `i`, `vᵢ = 2` for
odd `i` (`alternatingVar`), the coordinates form such a model, and the conclusions hold
(`isConsistent_dl_alternatingVar`).

## Main results

* `hasLaw_add_of_gaussian_prod`, `integral_pow_four_le_of_hasLaw_gaussian`,
  `isUnequalVarianceStudies_gaussian`, `isConsistent_dl_gaussian_unequalVar`.
* `alternatingVar`, `isConsistent_dl_alternatingVar`.

## References

* R. DerSimonian and N. Laird, *Meta-analysis in clinical trials*, Controlled Clinical Trials 7
  (1986).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If `(B, E) ~ N(0, τ²) ⊗ N(0, s)` with `τ², s ≥ 0`, then `B + E ~ N(0, s + τ²)`. -/
theorem hasLaw_add_of_gaussian_prod {B E : Ω → ℝ} {τ2 s : ℝ} (hτ : 0 ≤ τ2) (hs : 0 ≤ s)
    (hlaw : HasLaw (fun ω => (B ω, E ω))
      ((gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 s.toNNReal)) P) :
    HasLaw (fun ω => B ω + E ω) (gaussianReal 0 (s + τ2).toNNReal) P := by
  have hF : HasLaw (fun p : ℝ × ℝ => p.1 + p.2) (gaussianReal 0 (s + τ2).toNNReal)
      ((gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 s.toNNReal)) := by
    refine ⟨by fun_prop, ?_⟩
    change (gaussianReal 0 τ2.toNNReal) ∗ (gaussianReal 0 s.toNNReal) = _
    rw [gaussianReal_conv_gaussianReal, add_zero, add_comm s, Real.toNNReal_add hτ hs]
  exact hF.comp hlaw

/-- **The fourth moment in the Gaussian model**: if `X ~ N(0, σ²)` with `0 ≤ σ² ≤ S`, then
`E X⁴ ≤ S² E Z⁴` for `Z ~ N(0, 1)`. -/
theorem integral_pow_four_le_of_hasLaw_gaussian {X : Ω → ℝ} {σ2 S : ℝ} (hσ : 0 ≤ σ2)
    (hσS : σ2 ≤ S) (hlaw : HasLaw X (gaussianReal 0 σ2.toNNReal) P) :
    ∫ ω, X ω ^ 4 ∂P ≤ S ^ 2 * ∫ z, z ^ 4 ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun z => √σ2 * z) = gaussianReal 0 σ2.toNNReal := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp [Real.sq_sqrt hσ, Real.coe_toNNReal _ hσ]
  have h1 : ∫ ω, X ω ^ 4 ∂P = ∫ x, x ^ 4 ∂gaussianReal 0 σ2.toNNReal :=
    hlaw.integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  have h2 : ∫ x, x ^ 4 ∂gaussianReal 0 σ2.toNNReal = σ2 ^ 2 * ∫ z, z ^ 4 ∂gaussianReal 0 1 := by
    rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
    have he : (fun z : ℝ => (√σ2 * z) ^ 4) = fun z => σ2 ^ 2 * z ^ 4 := by
      funext z
      rw [mul_pow, show (√σ2) ^ 4 = (√σ2 ^ 2) ^ 2 by ring, Real.sq_sqrt hσ]
    rw [he, integral_const_mul]
  rw [h1, h2]
  have hz : 0 ≤ ∫ z, z ^ 4 ∂gaussianReal 0 1 := integral_nonneg fun z => by positivity
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσ hσS 2) hz

/-- **The Gaussian random effects model with unequal variances satisfies the hypotheses**: let
the pairs `(bᵢ, εᵢ)` be independent with `(bᵢ, εᵢ) ~ N(0, τ²) ⊗ N(0, vᵢ)`, `τ² ≥ 0`,
`a ≤ vᵢ ≤ A`, `0 < a`. Then `Yᵢ = θ + bᵢ + εᵢ` is a sequence of independent studies with unequal
variances, with the fourth moment bound `M = (A + τ²)² E Z⁴`, `Z ~ N(0, 1)`. -/
theorem isUnequalVarianceStudies_gaussian {b ε : ℕ → Ω → ℝ} {v : ℕ → ℝ} {τ2 a A : ℝ}
    (hind : iIndepFun (fun i ω => (b i ω, ε i ω)) P)
    (hlaw : ∀ i, HasLaw (fun ω => (b i ω, ε i ω))
      ((gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 (v i).toNNReal)) P)
    (hτ : 0 ≤ τ2) (ha : 0 < a) (hva : ∀ i, a ≤ v i) (hvA : ∀ i, v i ≤ A) (θ : ℝ) :
    IsUnequalVarianceStudies P (fun i ω => θ + b i ω + ε i ω) θ τ2 v a A
      ((A + τ2) ^ 2 * ∫ z, z ^ 4 ∂gaussianReal 0 1) := by
  have hP : IsProbabilityMeasure P := (hlaw 0).isProbabilityMeasure
  have hv : ∀ i, 0 ≤ v i := fun i => (ha.trans_le (hva i)).le
  have hB : ∀ i, HasLaw (b i) (gaussianReal 0 τ2.toNNReal) P := fun i =>
    (measurePreserving_fst (μ := gaussianReal 0 τ2.toNNReal)
      (ν := gaussianReal 0 (v i).toNNReal)).hasLaw.comp (hlaw i)
  have hE : ∀ i, HasLaw (ε i) (gaussianReal 0 (v i).toNNReal) P := fun i =>
    (measurePreserving_snd (μ := gaussianReal 0 τ2.toNNReal)
      (ν := gaussianReal 0 (v i).toNNReal)).hasLaw.comp (hlaw i)
  refine isUnequalVarianceStudies_of_components (fun i j hij => hind.indepFun hij)
    (fun i => (hB i).memLp (memLp_id_gaussianReal 4))
    (fun i => (hE i).memLp (memLp_id_gaussianReal 4))
    (fun i => by rw [(hB i).integral_eq, integral_id_gaussianReal])
    (fun i => by rw [(hE i).integral_eq, integral_id_gaussianReal])
    (fun i => by rw [(hB i).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ hτ])
    (fun i => by rw [(hE i).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (hv i)])
    (fun i => ?_) ha hva hvA (fun i => ?_)
  · have hBE : IndepFun (b i) (ε i) P := (indepFun_iff_hasLaw_prodMk_prod (hB i) (hE i)).2
      (hlaw i)
    exact hBE.covariance_eq_zero ((hB i).memLp (memLp_id_gaussianReal 2))
      ((hE i).memLp (memLp_id_gaussianReal 2))
  · exact integral_pow_four_le_of_hasLaw_gaussian (by linarith [hv i])
      (by linarith [hvA i]) (hasLaw_add_of_gaussian_prod hτ (hv i) (hlaw i))

/-- **Consistency in the Gaussian random effects model with unequal variances**: under the
hypotheses of `isUnequalVarianceStudies_gaussian`, from the first `k` studies the untruncated
and the truncated DerSimonian and Laird estimators are consistent for `τ²`, and the DerSimonian
and Laird pooled estimate and the common effect pooled estimate are consistent for `θ`. -/
theorem isConsistent_dl_gaussian_unequalVar {b ε : ℕ → Ω → ℝ} {v : ℕ → ℝ} {τ2 a A : ℝ}
    (hind : iIndepFun (fun i ω => (b i ω, ε i ω)) P)
    (hlaw : ∀ i, HasLaw (fun ω => (b i ω, ε i ω))
      ((gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 (v i).toNNReal)) P)
    (hτ : 0 ≤ τ2) (ha : 0 < a) (hva : ∀ i, a ≤ v i) (hvA : ∀ i, v i ≤ A) (θ : ℝ) :
    IsConsistent (fun k ω => dlTau2Untruncated (fun i : Fin k => v i)
        fun i => θ + b i ω + ε i ω) τ2 P ∧
      IsConsistent (fun k ω => dlTau2 (fun i : Fin k => v i) fun i => θ + b i ω + ε i ω) τ2 P ∧
      IsConsistent (fun k ω => dlEstimate (fun i : Fin k => v i)
        fun i => θ + b i ω + ε i ω) θ P ∧
      IsConsistent (fun k ω => ivwEstimate (fun i : Fin k => v i)
        fun i => θ + b i ω + ε i ω) θ P := by
  have h := isUnequalVarianceStudies_gaussian hind hlaw hτ ha hva hvA θ
  exact ⟨h.isConsistent_dlTau2Untruncated, h.isConsistent_dlTau2 hτ,
    h.isConsistent_dlEstimate hτ, h.isConsistent_ivwEstimate⟩

/-! ### A concrete model with alternating variances -/

/-- The alternating within study variances: `1` for even `i`, `2` for odd `i`. -/
noncomputable def alternatingVar (i : ℕ) : ℝ := if Even i then 1 else 2

theorem one_le_alternatingVar (i : ℕ) : 1 ≤ alternatingVar i := by
  unfold alternatingVar; split_ifs <;> norm_num

theorem alternatingVar_le_two (i : ℕ) : alternatingVar i ≤ 2 := by
  unfold alternatingVar; split_ifs <;> norm_num

/-- The product law `⊗ᵢ (N(0, τ²) ⊗ N(0, vᵢ))` of the alternating model on `ℕ → ℝ × ℝ`. -/
noncomputable def alternatingVarLaw (τ2 : ℝ) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun i =>
    (gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 (alternatingVar i).toNNReal)

/-- **Consistency in the concrete Gaussian model with alternating variances**: on `ℕ → ℝ × ℝ`
with the law `⊗ᵢ (N(0, τ²) ⊗ N(0, vᵢ))`, `vᵢ` alternating between `1` and `2`, `τ² ≥ 0`, the
study effects `bᵢ(ω) = (ω i).1` and errors `εᵢ(ω) = (ω i).2` give estimates
`Yᵢ = θ + bᵢ + εᵢ` for which the DerSimonian and Laird estimators from the first `k` studies are
consistent for `τ²`, and the DerSimonian and Laird and the common effect pooled estimates are
consistent for `θ`. Every hypothesis is verified. -/
theorem isConsistent_dl_alternatingVar {τ2 : ℝ} (hτ : 0 ≤ τ2) (θ : ℝ) :
    IsConsistent (fun k ω => dlTau2Untruncated (fun i : Fin k => alternatingVar i)
        fun i => θ + ((ω : ℕ → ℝ × ℝ) i).1 + (ω i).2) τ2 (alternatingVarLaw τ2) ∧
      IsConsistent (fun k ω => dlTau2 (fun i : Fin k => alternatingVar i)
        fun i => θ + ((ω : ℕ → ℝ × ℝ) i).1 + (ω i).2) τ2 (alternatingVarLaw τ2) ∧
      IsConsistent (fun k ω => dlEstimate (fun i : Fin k => alternatingVar i)
        fun i => θ + ((ω : ℕ → ℝ × ℝ) i).1 + (ω i).2) θ (alternatingVarLaw τ2) ∧
      IsConsistent (fun k ω => ivwEstimate (fun i : Fin k => alternatingVar i)
        fun i => θ + ((ω : ℕ → ℝ × ℝ) i).1 + (ω i).2) θ (alternatingVarLaw τ2) := by
  have hind : iIndepFun (fun i (ω : ℕ → ℝ × ℝ) => ((ω i).1, (ω i).2))
      (alternatingVarLaw τ2) := by
    simp only [Prod.mk.eta, alternatingVarLaw]
    exact iIndepFun_infinitePi (X := fun _ (p : ℝ × ℝ) => p) fun _ => measurable_id
  have hlaw : ∀ i, HasLaw (fun ω : ℕ → ℝ × ℝ => ((ω i).1, (ω i).2))
      ((gaussianReal 0 τ2.toNNReal).prod (gaussianReal 0 (alternatingVar i).toNNReal))
      (alternatingVarLaw τ2) := fun i =>
    ⟨by fun_prop, by
      simp only [Prod.mk.eta, alternatingVarLaw]
      exact Measure.infinitePi_map_eval _ i⟩
  exact isConsistent_dl_gaussian_unequalVar (P := alternatingVarLaw τ2)
    (b := fun i ω => (ω i).1) (ε := fun i ω => (ω i).2) (v := alternatingVar)
    hind hlaw hτ one_pos one_le_alternatingVar alternatingVar_le_two θ

end MetaAnalysis

end CausalInference
