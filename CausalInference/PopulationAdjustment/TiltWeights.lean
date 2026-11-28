/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Basic
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Population adjustment: exponential tilting weights and moment balance

Matching adjusted indirect comparison reweights the individual data of one trial so that the
weighted means of chosen covariate features match the feature means reported by another trial
(Signorovitch and coauthors 2010). The weights are exponential tilts of the features,

`w(x) = exp(α + βᵀ(φ(x) - c))`,

with a feature map `φ : 𝒳 → ℝ^p` (covariates, their squares, products, indicators), a centering
point `c` (in the applications the target feature means) and parameters `α`, `β`.

**One definition for samples and populations.** `tiltWeight φ c α β` is a function of the
covariate. The weight of unit `i` of a sample `x : Fin n → 𝒳` is `tiltWeight φ c α β (x i)`; a
population weight is the same function applied to the covariate of a population. The sample
statements are the population statements of the empirical law `Trial.ipdEmpirical`
(`integral_ipdEmpirical`):

* moment balance of a weight vector (`MomentBalanced`) is population balance
  (`PopulationBalanced`) of the empirical law (`populationBalanced_ipdEmpirical_iff`);
* the normalized weights (`normalizedWeights`) form a probability vector, and the reweighted
  empirical law is Mathlib's exponentially tilted measure `Measure.tilted` of the empirical
  law (`integral_tilted_ipdEmpirical`); when the weights balance the features at `t`, every
  feature mean of the reweighted empirical law is `t`
  (`integral_feature_tilted_ipdEmpirical_iff`).

The intercept `α` only scales the weights, so it cancels in the normalized weights
(`normalizedWeights_tiltWeight`) and in the balance condition (`momentBalanced_smul_iff`).

## Main definitions

* `tiltWeight φ c α β x = exp(α + βᵀ(φ(x) - c))`.
* `MomentBalanced w z t`: `∑ᵢ wᵢ (zᵢ - t) = 0`.
* `normalizedWeights w`: `wᵢ / ∑ⱼ wⱼ`.
* `PopulationBalanced ν w ψ t`: `∫ w(x) (ψ(x)ⱼ - tⱼ) dν(x) = 0` for every coordinate `j`.

## Main results

* `tiltWeight_pos`, `log_tiltWeight`, `tiltWeight_recenter`.
* `momentBalanced_iff_sum_mul`, `momentBalanced_iff_weightedMean`: the forms of balance.
* `sum_normalizedWeights`, `normalizedWeights_nonneg`, `normalizedWeights_tiltWeight`.
* `integral_ipdEmpirical`: integrals under the empirical law are sample means.
* `populationBalanced_ipdEmpirical_iff`, `integral_tilted_ipdEmpirical`,
  `integral_feature_tilted_ipdEmpirical_iff`: the sample objects as population objects of the
  empirical law.
* `integral_feature_tilted_iff`: for a population covariate law, the feature means of the tilted
  law equal `t` exactly when the tilt weights balance the features at `t`.

## References

* J. E. Signorovitch, E. Q. Wu, A. P. Yu, C. M. Gerrits, E. Kantor, Y. Bao, S. R. Gupta and
  P. M. Mulani, *Comparative effectiveness without head-to-head trials: a method for
  matching-adjusted indirect comparisons applied to psoriasis treatment with adalimumab or
  etanercept*, PharmacoEconomics 28 (2010).
* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory Finset IndirectComparison

/-! ### The weight function -/

section Weight

variable {𝒳 : Type*} {p : ℕ}

/-- The **exponential tilting weight** `w(x) = exp(α + βᵀ(φ(x) - c))` of the covariate value `x`,
for the feature map `φ`, the centering point `c` and the parameters `α` and `β`. -/
noncomputable def tiltWeight (φ : 𝒳 → Fin p → ℝ) (c : Fin p → ℝ) (α : ℝ) (β : Fin p → ℝ)
    (x : 𝒳) : ℝ :=
  Real.exp (α + β ⬝ᵥ (φ x - c))

variable (φ : 𝒳 → Fin p → ℝ) (c : Fin p → ℝ) (α : ℝ) (β : Fin p → ℝ)

/-- The tilting weights are strictly positive. -/
theorem tiltWeight_pos (x : 𝒳) : 0 < tiltWeight φ c α β x :=
  Real.exp_pos _

/-- The logarithm of a tilting weight is affine in the features. -/
theorem log_tiltWeight (x : 𝒳) : Real.log (tiltWeight φ c α β x) = α + β ⬝ᵥ (φ x - c) :=
  Real.log_exp _

/-- The intercept factors out: `w(x) = e^α exp(βᵀ(φ(x) - c))`. -/
theorem tiltWeight_eq_exp_mul (x : 𝒳) :
    tiltWeight φ c α β x = Real.exp α * Real.exp (β ⬝ᵥ (φ x - c)) :=
  Real.exp_add _ _

/-- **Changing the centering point changes only the intercept**:
`exp(α + βᵀ(φ(x) - c)) = exp(α + βᵀ(c' - c) + βᵀ(φ(x) - c'))`. -/
theorem tiltWeight_recenter (c' : Fin p → ℝ) :
    tiltWeight φ c α β = tiltWeight φ c' (α + β ⬝ᵥ (c' - c)) β := by
  funext x
  simp only [tiltWeight, dotProduct_sub]
  ring_nf

theorem measurable_tiltWeight [MeasurableSpace 𝒳] (hφ : Measurable φ) :
    Measurable (tiltWeight φ c α β) := by
  unfold tiltWeight
  have : Measurable fun x => β ⬝ᵥ (φ x - c) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul
      ((measurable_pi_apply j).comp hφ |>.sub measurable_const)
  exact (measurable_const.add this).exp

end Weight

/-! ### Moment balance of a weight vector -/

section Balance

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-- **Moment balance**: the weights `w` balance the vectors `z` at `t` when
`∑ᵢ wᵢ (zᵢ - t) = 0`. With `zᵢ = φ(xᵢ)` this is balance of the features `φ`; for a positive
total weight it says that the weighted mean of every feature is its target
(`momentBalanced_iff_weightedMean`). -/
def MomentBalanced (w : ι → ℝ) (z : ι → Fin p → ℝ) (t : Fin p → ℝ) : Prop :=
  ∑ i, w i • (z i - t) = 0

variable {w : ι → ℝ} {z : ι → Fin p → ℝ} {t : Fin p → ℝ}

/-- Moment balance coordinatewise: `∑ᵢ wᵢ zᵢⱼ = (∑ᵢ wᵢ) tⱼ` for every `j`. -/
theorem momentBalanced_iff_sum_mul :
    MomentBalanced w z t ↔ ∀ j, ∑ i, w i * z i j = (∑ i, w i) * t j := by
  rw [MomentBalanced, funext_iff]
  refine forall_congr' fun j => ?_
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, sub_eq_zero]

/-- **Moment balance is matching of weighted means**: for a nonzero total weight, `w` balances
`z` at `t` exactly when the weighted mean `∑ᵢ wᵢ zᵢⱼ / ∑ᵢ wᵢ` of every coordinate is `tⱼ`. -/
theorem momentBalanced_iff_weightedMean (hw : ∑ i, w i ≠ 0) :
    MomentBalanced w z t ↔ ∀ j, (∑ i, w i * z i j) / ∑ i, w i = t j := by
  rw [momentBalanced_iff_sum_mul]
  refine forall_congr' fun j => ?_
  rw [div_eq_iff hw, mul_comm]

/-- Balance is invariant under rescaling the weights by a nonzero constant. -/
theorem momentBalanced_smul_iff {a : ℝ} (ha : a ≠ 0) :
    MomentBalanced (fun i => a * w i) z t ↔ MomentBalanced w z t := by
  simp only [MomentBalanced, ← smul_smul, ← Finset.smul_sum, smul_eq_zero, ha, false_or]

/-- The **normalized weights** `wᵢ / ∑ⱼ wⱼ`. -/
noncomputable def normalizedWeights (w : ι → ℝ) : ι → ℝ := fun i => w i / ∑ j, w j

/-- The normalized weights sum to one when the total weight is nonzero. -/
theorem sum_normalizedWeights (hw : ∑ i, w i ≠ 0) : ∑ i, normalizedWeights w i = 1 := by
  simp only [normalizedWeights, ← Finset.sum_div, div_self hw]

/-- Nonnegative weights have nonnegative normalized weights. -/
theorem normalizedWeights_nonneg (hw : ∀ i, 0 ≤ w i) (i : ι) : 0 ≤ normalizedWeights w i :=
  div_nonneg (hw i) (Finset.sum_nonneg fun j _ => hw j)

/-- Normalization removes a nonzero scale factor. -/
theorem normalizedWeights_smul {a : ℝ} (ha : a ≠ 0) :
    normalizedWeights (fun i => a * w i) = normalizedWeights w := by
  funext i
  simp only [normalizedWeights, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ ha

/-- Normalized weights balance exactly when the weights do (nonzero total weight). -/
theorem momentBalanced_normalizedWeights_iff (hw : ∑ i, w i ≠ 0) :
    MomentBalanced (normalizedWeights w) z t ↔ MomentBalanced w z t := by
  have h : normalizedWeights w = fun i => (∑ j, w j)⁻¹ * w i := by
    funext i; rw [normalizedWeights, div_eq_inv_mul]
  rw [h, momentBalanced_smul_iff (inv_ne_zero hw)]

/-- For weights summing to one, balance is `∑ᵢ wᵢ zᵢ = t`. -/
theorem momentBalanced_iff_sum_smul_eq (hw : ∑ i, w i = 1) :
    MomentBalanced w z t ↔ ∑ i, w i • z i = t := by
  simp only [MomentBalanced, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul,
    sub_eq_zero]

variable {𝒳 : Type*} (φ : 𝒳 → Fin p → ℝ) (c : Fin p → ℝ) (α : ℝ) (β : Fin p → ℝ)

/-- The total of the tilting weights of a nonempty sample is positive. -/
theorem sum_tiltWeight_pos [Nonempty ι] (x : ι → 𝒳) : 0 < ∑ i, tiltWeight φ c α β (x i) :=
  Finset.sum_pos (fun i _ => tiltWeight_pos φ c α β (x i)) Finset.univ_nonempty

/-- **The normalized tilting weights do not depend on the intercept**:
`wᵢ / ∑ⱼ wⱼ = exp(βᵀ(φ(xᵢ) - c)) / ∑ⱼ exp(βᵀ(φ(xⱼ) - c))`. -/
theorem normalizedWeights_tiltWeight (x : ι → 𝒳) :
    normalizedWeights (fun i => tiltWeight φ c α β (x i)) =
      normalizedWeights (fun i => Real.exp (β ⬝ᵥ (φ (x i) - c))) := by
  simp_rw [tiltWeight_eq_exp_mul]
  exact normalizedWeights_smul (Real.exp_pos α).ne'

/-- Balance of the tilting weights does not depend on the intercept. -/
theorem momentBalanced_tiltWeight_iff (x : ι → 𝒳) (α' : ℝ) :
    MomentBalanced (fun i => tiltWeight φ c α β (x i)) (fun i => φ (x i)) t ↔
      MomentBalanced (fun i => tiltWeight φ c α' β (x i)) (fun i => φ (x i)) t := by
  simp_rw [tiltWeight_eq_exp_mul]
  rw [momentBalanced_smul_iff (Real.exp_pos α).ne', momentBalanced_smul_iff (Real.exp_pos α').ne']

end Balance

/-! ### Population balance and the tilted law -/

section Population

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {p : ℕ}

/-- **Population balance**: the weight function `w` balances the features `ψ` at `t` under the
law `ν` when `∫ w(x) (ψ(x)ⱼ - tⱼ) dν(x) = 0` for every coordinate `j`. The theorems that use it
assume the integrability of `w ψⱼ` and `w`. -/
def PopulationBalanced (ν : Measure 𝒳) (w : 𝒳 → ℝ) (ψ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) :
    Prop :=
  ∀ j, ∫ x, w x * (ψ x j - t j) ∂ν = 0

variable (φ : 𝒳 → Fin p → ℝ) (c : Fin p → ℝ) (α : ℝ) (β : Fin p → ℝ)

/-- **The feature means of the tilted law.** Let `ν` be a nonzero finite law, and let
`exp(βᵀ(φ - c))` and `exp(βᵀ(φ - c)) φⱼ` be integrable under `ν`. The law `ν` exponentially
tilted by `βᵀ(φ - c)` (density proportional to the tilting weight) has feature means `t` exactly
when the tilting weights balance the features at `t` under `ν`, for any intercept `α`. -/
theorem integral_feature_tilted_iff (ν : Measure 𝒳) [IsFiniteMeasure ν] [NeZero ν]
    (t : Fin p → ℝ) (he : Integrable (fun x => Real.exp (β ⬝ᵥ (φ x - c))) ν)
    (heφ : ∀ j, Integrable (fun x => Real.exp (β ⬝ᵥ (φ x - c)) * φ x j) ν) :
    (∀ j, ∫ x, φ x j ∂(ν.tilted fun x => β ⬝ᵥ (φ x - c)) = t j) ↔
      PopulationBalanced ν (tiltWeight φ c α β) φ t := by
  set f : 𝒳 → ℝ := fun x => β ⬝ᵥ (φ x - c)
  have hZ : 0 < ∫ x, Real.exp (f x) ∂ν := integral_exp_pos he
  refine forall_congr' fun j => ?_
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div, div_eq_iff hZ.ne']
  have hw : ∫ x, tiltWeight φ c α β x * (φ x j - t j) ∂ν =
      Real.exp α * (∫ x, Real.exp (f x) * φ x j ∂ν - t j * ∫ x, Real.exp (f x) ∂ν) := by
    have h1 : (fun x => tiltWeight φ c α β x * (φ x j - t j)) = fun x =>
        Real.exp α * (Real.exp (f x) * φ x j) - Real.exp α * t j * Real.exp (f x) := by
      funext x; simp only [tiltWeight_eq_exp_mul, f]; ring
    rw [h1, integral_sub ((heφ j).const_mul _) (he.const_mul _), integral_const_mul,
      integral_const_mul]
    ring
  rw [hw, mul_eq_zero, sub_eq_zero]
  simp only [(Real.exp_pos α).ne', false_or, mul_comm (t j)]

end Population

/-! ### The empirical law -/

section Empirical

variable {𝒳 ι' : Type*} [MeasurableSpace 𝒳] [MeasurableSpace ι'] [MeasurableSingletonClass 𝒳]
  [MeasurableSingletonClass ι'] {n p : ℕ}

/-- **Integrals under the empirical law are sample means**: for every `f`,
`∫ f d(ipdEmpirical x a y) = n⁻¹ ∑ᵢ f(xᵢ, aᵢ, yᵢ)`. -/
theorem integral_ipdEmpirical (x : Fin n → 𝒳) (a : Fin n → ι') (y : Fin n → ℝ)
    (f : 𝒳 × ι' × ℝ → ℝ) :
    ∫ z, f z ∂(Trial.ipdEmpirical x a y) = (n : ℝ)⁻¹ * ∑ i, f (x i, a i, y i) := by
  rw [Trial.ipdEmpirical, integral_smul_measure,
    integral_finsetSum_measure fun i _ => integrable_dirac (by simp)]
  simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **Sample balance is population balance of the empirical law**: for a nonempty sample, the
weight function `w` balances the features `φ` at `t` under the empirical law exactly when the
sample weights `w(xᵢ)` balance the sample features `φ(xᵢ)` at `t`. -/
theorem populationBalanced_ipdEmpirical_iff (hn : 0 < n) (x : Fin n → 𝒳) (a : Fin n → ι')
    (y : Fin n → ℝ) (w : 𝒳 → ℝ) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) :
    PopulationBalanced (Trial.ipdEmpirical x a y) (fun z => w z.1) (fun z => φ z.1) t ↔
      MomentBalanced (fun i => w (x i)) (fun i => φ (x i)) t := by
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  rw [MomentBalanced, funext_iff]
  refine forall_congr' fun j => ?_
  rw [integral_ipdEmpirical, mul_eq_zero]
  simp only [hn', false_or, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Pi.zero_apply]

/-- **The tilted empirical law is the reweighted empirical law**: for a nonempty sample and any
exponent `f`, the empirical law tilted by `f` gives each observation the normalized weight
`exp(f(zᵢ)) / ∑ⱼ exp(f(zⱼ))`. -/
theorem integral_tilted_ipdEmpirical (hn : 0 < n) (x : Fin n → 𝒳) (a : Fin n → ι')
    (y : Fin n → ℝ) (f g : 𝒳 × ι' × ℝ → ℝ) :
    ∫ z, g z ∂((Trial.ipdEmpirical x a y).tilted f) =
      ∑ i, normalizedWeights (fun i => Real.exp (f (x i, a i, y i))) i * g (x i, a i, y i) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [integral_tilted, integral_ipdEmpirical, integral_ipdEmpirical, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [normalizedWeights, smul_eq_mul]
  field_simp

/-- The tilted empirical law of a nonempty sample is a probability measure. -/
theorem isProbabilityMeasure_tilted_ipdEmpirical (hn : 0 < n) (x : Fin n → 𝒳) (a : Fin n → ι')
    (y : Fin n → ℝ) (f : 𝒳 × ι' × ℝ → ℝ) :
    IsProbabilityMeasure ((Trial.ipdEmpirical x a y).tilted f) := by
  have := Trial.isProbabilityMeasure_ipdEmpirical hn x a y
  refine isProbabilityMeasure_tilted ?_
  rw [Trial.ipdEmpirical]
  exact (integrable_finsetSum_measure.2 fun i _ => integrable_dirac (by simp)).smul_measure
    (by simp [hn.ne'])

/-- **The reweighted empirical law has the target feature means.** For a nonempty sample, the
empirical law tilted by `βᵀ(φ(x) - c)` (weights proportional to the tilting weights
`exp(α + βᵀ(φ(xᵢ) - c))`) is a probability measure, and its feature means are `t` exactly when
the tilting weights of the sample balance the features at `t`. -/
theorem integral_feature_tilted_ipdEmpirical_iff (hn : 0 < n) (x : Fin n → 𝒳) (a : Fin n → ι')
    (y : Fin n → ℝ) (φ : 𝒳 → Fin p → ℝ) (c : Fin p → ℝ) (α : ℝ) (β : Fin p → ℝ)
    (t : Fin p → ℝ) :
    IsProbabilityMeasure ((Trial.ipdEmpirical x a y).tilted fun z => β ⬝ᵥ (φ z.1 - c)) ∧
      ((∀ j, ∫ z, φ z.1 j ∂((Trial.ipdEmpirical x a y).tilted fun z => β ⬝ᵥ (φ z.1 - c)) =
        t j) ↔ MomentBalanced (fun i => tiltWeight φ c α β (x i)) (fun i => φ (x i)) t) := by
  refine ⟨isProbabilityMeasure_tilted_ipdEmpirical hn x a y _, ?_⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hS := sum_tiltWeight_pos φ c α β x
  simp_rw [integral_tilted_ipdEmpirical hn x a y]
  rw [momentBalanced_iff_weightedMean hS.ne', ← normalizedWeights_tiltWeight φ c α β x]
  refine forall_congr' fun j => ?_
  simp only [normalizedWeights, div_mul_eq_mul_div, ← Finset.sum_div]

end Empirical

end PopulationAdjustment

end CausalInference
