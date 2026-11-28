/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountPoisson
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The law of the aggregate count of a Poisson outcome

An arm of `n` patients with covariates drawn independently from `F` and `Po(r(x))` outcomes
reports the count `S = ∑ Yᵢ`. Given the covariates `x = (x₁, …, xₙ)` the count is
`Po(Λ(x))`, `Λ(x) = ∑ r(xᵢ)`; with the covariates integrated out it is the mixed Poisson law of
the total rate `Λ` under `Fⁿ`.

* **The generating function of the Poisson law** (`generatingFunction_poissonMeasure`):
  `E z^N = exp(t (z - 1))` for `N ∼ Po(t)` and `|z| ≤ 1`.
* **The generating function of a mixed Poisson law** (`generatingFunction_snd_poissonKernel`):
  `∫ exp(g(x)(z - 1)) ρ(dx)`.
* **The aggregate count is mixed Poisson** (`map_count_pi_compProd_poissonKernel`): its law is
  the mixture of `Po(Λ(x))` over `x ∼ Fⁿ`.
* **Its mass function** (`measureReal_count_pi_compProd_poissonKernel`):
  `P(S = y) = ∫ e^{-Λ(x)} Λ(x)^y / y! Fⁿ(dx)`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Nat

namespace CausalInference

namespace NetworkMetaRegression

/-- **The generating function of the Poisson law**: `Po(t)` has `E z^N = exp(t (z - 1))` for
`|z| ≤ 1`. -/
theorem generatingFunction_poissonMeasure (t : ℝ≥0) {z : ℝ} (hz : |z| ≤ 1) :
    generatingFunction (poissonMeasure t) z = Real.exp (t * (z - 1)) := by
  have h1 := hasSum_generatingFunction (ν := poissonMeasure t) hz
  have h2 : HasSum (fun k : ℕ => (poissonMeasure t).real {k} * z ^ k)
      (Real.exp (-t) * Real.exp (t * z)) := by
    have := (NormedSpace.expSeries_div_hasSum_exp ((t : ℝ) * z)).mul_left (Real.exp (-t))
    rw [← Real.exp_eq_exp_ℝ] at this
    convert this using 1
    funext k
    rw [poissonMeasure_real_singleton, mul_pow]
    ring
  rw [h1.unique h2, ← Real.exp_add]
  ring_nf

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The generating function of a mixed Poisson law**: if the rate `g(x) ≥ 0` is drawn from `ρ`,
the count has `E z^N = ∫ exp(g(x)(z - 1)) ρ(dx)` for `|z| ≤ 1`. -/
theorem generatingFunction_snd_poissonKernel (ρ : Measure 𝒳) [IsProbabilityMeasure ρ]
    {g : 𝒳 → ℝ} (hg : Measurable g) (h0 : ∀ x, 0 ≤ g x) {z : ℝ} (hz : |z| ≤ 1) :
    generatingFunction (ρ ⊗ₘ poissonKernel g hg).snd z =
      ∫ x, Real.exp (g x * (z - 1)) ∂ρ := by
  have hb : ∀ k : ℕ, ‖z ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow, Real.norm_eq_abs]; exact pow_le_one₀ (abs_nonneg z) hz
  have hi : Integrable (fun p : 𝒳 × ℕ => z ^ p.2) (ρ ⊗ₘ poissonKernel g hg) :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun p => hb p.2)
  rw [generatingFunction, Measure.snd, integral_map measurable_snd.aemeasurable (by fun_prop),
    Measure.integral_compProd hi]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change generatingFunction (poissonKernel g hg x) z = _
  rw [poissonKernel_apply, generatingFunction_poissonMeasure _ hz, Real.coe_toNNReal _ (h0 x)]

variable {F : Measure 𝒳} [IsProbabilityMeasure F] {r : 𝒳 → ℝ} {hr : Measurable r}

/-- The total rate `Λ(x) = ∑ r(xᵢ)` of `n` patients. -/
theorem measurable_totalRate (hr : Measurable r) (n : ℕ) :
    Measurable fun x : Fin n → 𝒳 => ∑ i, r (x i) :=
  Finset.measurable_sum _ fun i _ => hr.comp (measurable_pi_apply i)

/-- **The aggregate Poisson count is mixed Poisson**: the count of `n` independent patients with
covariates from `F` and `Po(r(x))` outcomes has the law of a Poisson count with the rate
`Λ(x) = ∑ r(xᵢ)` drawn from `Fⁿ`. -/
theorem map_count_pi_compProd_poissonKernel (h0 : ∀ x, 0 ≤ r x) (n : ℕ) :
    (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr).map (fun z => ∑ i, (z i).2) =
      ((Measure.pi fun _ : Fin n => F) ⊗ₘ
        poissonKernel _ (measurable_totalRate hr n)).snd := by
  have hΛ0 : ∀ x : Fin n → 𝒳, 0 ≤ ∑ i, r (x i) := fun x =>
    Finset.sum_nonneg fun i _ => h0 (x i)
  refine eq_of_generatingFunction_eqOn fun z hz => ?_
  have hz' : |z| ≤ 1 := (abs_lt.mpr hz).le
  have hind : iIndepFun (fun (i : Fin n) (w : Fin n → 𝒳 × ℕ) => (w i).2)
      (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) :=
    iIndepFun_pi (X := fun _ (p : 𝒳 × ℕ) => p.2) fun _ => measurable_snd.aemeasurable
  rw [(generatingFunction_map_sum (Y := fun (i : Fin n) (w : Fin n → 𝒳 × ℕ) => (w i).2)
    (fun i => by fun_prop) hind hz').2, generatingFunction_snd_poissonKernel _ _ hΛ0 hz']
  have hmap : ∀ i : Fin n, (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr).map
      (fun w => (w i).2) = (F ⊗ₘ poissonKernel r hr).snd := fun i => by
    rw [show (fun w : Fin n → 𝒳 × ℕ => (w i).2) = Prod.snd ∘ fun w => w i from rfl,
      ← Measure.map_map measurable_snd (measurable_pi_apply i),
      (measurePreserving_eval (μ := fun _ : Fin n => F ⊗ₘ poissonKernel r hr) i).map_eq]
    rfl
  simp_rw [hmap, generatingFunction_snd_poissonKernel F hr h0 hz', Finset.sum_mul,
    Real.exp_sum]
  exact (integral_fintype_prod_eq_prod (fun _ x => Real.exp (r x * (z - 1)))).symm

/-- **The mass function of the aggregate Poisson count**: with covariates integrated out, the
count of an arm of `n` patients equals `y` with probability
`∫ e^{-Λ(x)} Λ(x)^y / y! Fⁿ(dx)`, with `Λ(x) = ∑ r(xᵢ)`. -/
theorem measureReal_count_pi_compProd_poissonKernel (h0 : ∀ x, 0 ≤ r x) (n y : ℕ) :
    (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr).real {z | ∑ i, (z i).2 = y} =
      ∫ x : Fin n → 𝒳, Real.exp (-∑ i, r (x i)) * (∑ i, r (x i)) ^ y / y.factorial
        ∂(Measure.pi fun _ => F) := by
  rw [show {z : Fin n → 𝒳 × ℕ | ∑ i, (z i).2 = y} = (fun z => ∑ i, (z i).2) ⁻¹' {y} from rfl,
    ← map_measureReal_apply (by fun_prop) (measurableSet_singleton y),
    map_count_pi_compProd_poissonKernel h0, measureReal_snd_compProd_poissonKernel
      (fun x => Finset.sum_nonneg fun i _ => h0 (x i))]

end NetworkMetaRegression

end CausalInference
