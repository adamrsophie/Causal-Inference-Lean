/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ExchangeableBinaryMixing
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# de Finetti's theorem for binary sequences: uniqueness of the mixing law

* **Finite measures on `[0, 1]` are determined by their moments**
  (`eq_of_integral_pow_eq_of_isFiniteMeasure`): two finite measures on `ℝ` concentrated on
  `[0, 1]` with the same moments `∫ θᵏ`, `k = 0, 1, …`, coincide. A bounded continuous function is
  uniformly approximated on `[0, 1]` by polynomials (Weierstrass), the integrals of polynomials
  agree, and the integrals of bounded continuous functions determine a finite Borel measure.
* **The mixing law is unique** (`binaryMixture_unique`): if two probability measures on `[0, 1]`
  give the same probabilities `P(X₀ = … = X_{k-1} = 1) = ∫ θᵏ dΠ(θ)` of the all success
  patterns, they are equal. Only these patterns are needed.
* **de Finetti's theorem with uniqueness** (`InfExchangeable.existsUnique_binaryMixture`): an
  infinitely exchangeable binary sequence has exactly one mixing law on `[0, 1]`.

## Main results

* `eq_of_integral_pow_eq_of_isFiniteMeasure`, `binaryMixture_unique`,
  `InfExchangeable.existsUnique_binaryMixture`.

## References

* B. de Finetti, *La prévision : ses lois logiques, ses sources subjectives*, Annales de
  l'Institut Henri Poincaré 7 (1937).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Integrals of polynomials against a finite measure on `[0, 1]` are determined by its
moments. -/
theorem integral_polynomial_eval_eq_of_integral_pow_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) (hν : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1)
    (hmom : ∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) (p : Polynomial ℝ) :
    ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
  have hint : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ → (∀ᵐ x ∂ρ, x ∈ Icc (0 : ℝ) 1) →
      ∀ k : ℕ, Integrable (fun x : ℝ => p.coeff k * x ^ k) ρ := by
    intro ρ _ hρ k
    refine Integrable.const_mul (Integrable.of_bound (by fun_prop) 1 ?_) _
    filter_upwards [hρ] with x hx
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact pow_le_one₀ hx.1 hx.2
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ fun k _ => hint μ inferInstance hμ k,
    integral_finsetSum _ fun k _ => hint ν inferInstance hν k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_const_mul, hmom]

/-- **Finite measures on `[0, 1]` are determined by their moments**: two finite measures on `ℝ`
with no mass outside `[0, 1]` and the same moments `∫ θᵏ`, `k = 0, 1, …`, coincide. Proof: a
bounded continuous function is uniformly within `ε` of a polynomial on `[0, 1]` (Weierstrass),
the integrals of polynomials agree, and bounded continuous functions determine a finite Borel
measure. -/
theorem eq_of_integral_pow_eq_of_isFiniteMeasure {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ (Icc (0 : ℝ) 1)ᶜ = 0) (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) : μ = ν := by
  have hμ' : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1 := mem_ae_iff.2 hμ
  have hν' : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1 := mem_ae_iff.2 hν
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  refine eq_of_forall_dist_le fun ε hε => ?_
  set m : ℝ := (μ univ).toReal + (ν univ).toReal + 1 with hm
  have hm0 : 0 < m := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f f.continuous.continuousOn
    (ε / (2 * m)) (by positivity)
  have key : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ → (∀ᵐ x ∂ρ, x ∈ Icc (0 : ℝ) 1) →
      (ρ univ).toReal ≤ m → dist (∫ x, f x ∂ρ) (∫ x, p.eval x ∂ρ) ≤ ε / 2 := by
    intro ρ _ hρ hρm
    have hpi : Integrable (fun x => p.eval x) ρ := by
      refine Integrable.of_bound (p.continuous.aestronglyMeasurable) (‖f‖ + ε / (2 * m)) ?_
      filter_upwards [hρ] with x hx
      have h1 := hp x hx
      have h2 : |f x| ≤ ‖f‖ := by
        rw [← Real.norm_eq_abs]
        exact f.norm_coe_le_norm x
      rw [Real.norm_eq_abs]
      have h3 : |p.eval x| ≤ |p.eval x - f x| + |f x| := by
        have := abs_add_le (p.eval x - f x) (f x)
        rwa [sub_add_cancel] at this
      linarith
    rw [dist_eq_norm, ← integral_sub (f.integrable ρ) hpi]
    have h := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun x => f x - p.eval x) (C := ε / (2 * m)) (by
        filter_upwards [hρ] with x hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hp x hx).le)
    refine h.trans ?_
    rw [measureReal_def]
    calc ε / (2 * m) * (ρ univ).toReal ≤ ε / (2 * m) * m := by gcongr
      _ = ε / 2 := by field_simp
  have hμm : (μ univ).toReal ≤ m := by rw [hm]; linarith [ENNReal.toReal_nonneg (a := ν univ)]
  have hνm : (ν univ).toReal ≤ m := by rw [hm]; linarith [ENNReal.toReal_nonneg (a := μ univ)]
  calc dist (∫ x, f x ∂μ) (∫ x, f x ∂ν)
      ≤ dist (∫ x, f x ∂μ) (∫ x, p.eval x ∂μ) + dist (∫ x, p.eval x ∂ν) (∫ x, f x ∂ν) := by
        rw [← integral_polynomial_eval_eq_of_integral_pow_eq hμ' hν' hmom p]
        exact dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add (key μ inferInstance hμ' hμm) ?_
        rw [dist_comm]
        exact key ν inferInstance hν' hνm
    _ = ε := by ring

/-- On a finite measure concentrated on `[0, 1]` the lower integral of `θᵏ` is the real integral
read in `ℝ≥0∞`. -/
theorem lintegral_ofReal_pow_eq {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (k : ℕ) : ∫⁻ θ, ENNReal.ofReal (θ ^ k) ∂μ = ENNReal.ofReal (∫ θ, θ ^ k ∂μ) := by
  have hae : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1 := mem_ae_iff.2 hμ
  rw [ofReal_integral_eq_lintegral_ofReal]
  · refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hae] with θ hθ
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact pow_le_one₀ hθ.1 hθ.2
  · filter_upwards [hae] with θ hθ
    exact pow_nonneg hθ.1 k

/-- **Uniqueness of the mixing law** (de Finetti 1937): let `μ` and `ν` be probability measures
on `ℝ` concentrated on `[0, 1]`. If both give the probabilities of the all success patterns,
`P(X₀ = … = X_{k-1} = 1) = ∫ θᵏ dμ(θ) = ∫ θᵏ dν(θ)` for every `k`, then `μ = ν`. No assumption
on `P` or on the other patterns is needed. -/
theorem binaryMixture_unique {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Bool} {P : Measure Ω}
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (Icc (0 : ℝ) 1)ᶜ = 0) (hν : ν (Icc (0 : ℝ) 1)ᶜ = 0)
    (hrμ : ∀ k : ℕ, P {ω | ∀ i : Fin k, X i ω = true} = ∫⁻ θ, ENNReal.ofReal (θ ^ k) ∂μ)
    (hrν : ∀ k : ℕ, P {ω | ∀ i : Fin k, X i ω = true} = ∫⁻ θ, ENNReal.ofReal (θ ^ k) ∂ν) :
    μ = ν := by
  refine eq_of_integral_pow_eq_of_isFiniteMeasure hμ hν fun k => ?_
  have h := (hrμ k).symm.trans (hrν k)
  rw [lintegral_ofReal_pow_eq hμ, lintegral_ofReal_pow_eq hν] at h
  have h0 : ∀ ρ : Measure ℝ, IsFiniteMeasure ρ → ρ (Icc (0 : ℝ) 1)ᶜ = 0 →
      0 ≤ ∫ θ, θ ^ k ∂ρ := fun ρ _ hρ =>
    integral_nonneg_of_ae (Filter.Eventually.mono (mem_ae_iff.2 hρ) fun θ hθ =>
      pow_nonneg hθ.1 k)
  exact (ENNReal.ofReal_eq_ofReal_iff (h0 μ inferInstance hμ) (h0 ν inferInstance hν)).1 h

/-- **de Finetti's theorem for binary sequences with uniqueness** (de Finetti 1937): an infinitely
exchangeable sequence of measurable `Bool` valued variables on a probability space has exactly
one probability measure `Π` on `ℝ` with `Π([0, 1]ᶜ) = 0` and
`P(X₀ = x₀, …, X_{n-1} = x_{n-1}) = ∫ θ^s (1 - θ)^{n-s} dΠ(θ)` for every pattern `x` with `s`
successes. -/
theorem InfExchangeable.existsUnique_binaryMixture {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
        ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ := by
  obtain ⟨μ, hμp, hμs, hμr⟩ := hE.exists_binaryMixture hX
  refine ⟨μ, ⟨hμp, hμs, hμr⟩, fun ν ⟨hνp, hνs, hνr⟩ => ?_⟩
  have hones : ∀ k, boolCount (fun _ : Fin k => true) = k := fun k => by simp [boolCount]
  have hr : ∀ (ρ : Measure ℝ), (∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂ρ) →
      ∀ k : ℕ, P {ω | ∀ i : Fin k, X i ω = true} = ∫⁻ θ, ENNReal.ofReal (θ ^ k) ∂ρ := by
    intro ρ h k
    rw [h k fun _ => true, hones k, Nat.sub_self]
    simp
  exact binaryMixture_unique hνs hμs (hr ν hνr) (hr μ hμr)

end MetaAnalysis

end CausalInference
