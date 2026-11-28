/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountBinomial
public import CausalInference.NetworkMetaRegression.AggregationLog
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The aggregate count of a Poisson outcome

An arm of `n` patients reports the number of events `∑ Yᵢ`, where a patient with covariates
`x` has a Poisson number of events with rate `r(x)`; in the multilevel model of Phillippo et al.
(2020) the rate is the mean surface `g⁻¹(η(x))`, for instance `exp(η(x))`.

* **Fixed covariates** (`map_sum_pi_poisson`): given the covariates `x₁, …, xₙ` the count is
  exactly Poisson with the summed rate `∑ r(xᵢ)`.
* **Random covariates: a mixed Poisson law** (`measureReal_snd_compProd_poissonKernel`): a
  patient drawn from the covariate law `F` has the mass function `P(Y = y) = ∫ e^{-r} r^y / y! dF`.
* **Mean and variance** (`integral_count_poisson`, `variance_count_poisson`): the count of `n`
  independent patients has mean `n ∫ r dF` and variance `n ∫ r dF + n Var r`.
* **Overdispersion** (`integral_le_variance_count_poisson`,
  `variance_count_poisson_eq_integral_iff`): the variance is at least the mean, with equality
  (for `n ≥ 1`) exactly when the rate is almost surely constant.
* **When the count is Poisson** (`exists_poisson_count_iff`): for `n ≥ 1` the count has a Poisson
  law exactly when the rate is almost surely constant; then the law is `Po(n c)`.
* **The multilevel model** (`MultilevelModel.integral_count_poisson`,
  `MultilevelModel.variance_count_poisson`, `MultilevelModel.variance_count_poisson_eq_iff`,
  `MultilevelModel.variance_count_exp_gaussian`): the count of an arm has mean `n θ` with `θ` the
  aggregate arm mean, variance `n θ + n Var g⁻¹(η)`, and under the log link with Gaussian
  covariates variance `n θ + n θ² (exp(v) - 1)`, `v` the variance of `xᵀ(β₁ + β₂,k)`.

## Main definitions

* `poissonKernel`.

## Main results

* `hasLaw_sum_poissonMeasure`, `map_sum_pi_poisson`, `integral_variance_poissonMeasure`.
* `measureReal_snd_compProd_poissonKernel`, `integral_snd_compProd_poissonKernel`,
  `variance_snd_compProd_poissonKernel`.
* `integral_count_poisson`, `variance_count_poisson`, `integral_le_variance_count_poisson`,
  `variance_count_poisson_eq_integral_iff`, `exists_poisson_count_iff`.
* `MultilevelModel.integral_count_poisson`, `MultilevelModel.variance_count_poisson`,
  `MultilevelModel.variance_count_poisson_eq_iff`, `MultilevelModel.variance_count_exp_gaussian`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace CausalInference

namespace NetworkMetaRegression

/-! ### Poisson laws -/

section Poisson

theorem poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun k => ?_
  rw [poissonMeasure_singleton]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [hk, Set.indicator, Ne.symm hk]

/-- **A sum of independent Poisson counts is Poisson**: if `Yᵢ ∼ Po(lamᵢ)` are independent,
`∑ Yᵢ ∼ Po(∑ lamᵢ)`. -/
theorem hasLaw_sum_poissonMeasure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {Y : Fin n → Ω → ℕ} (hmeas : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) {r : Fin n → ℝ≥0} (hY : ∀ i, HasLaw (Y i) (poissonMeasure (r i)) μ) :
    HasLaw (∑ i, Y i) (poissonMeasure (∑ i, r i)) μ := by
  classical
  suffices h : ∀ s : Finset (Fin n),
      HasLaw (∑ i ∈ s, Y i) (poissonMeasure (∑ i ∈ s, r i)) μ from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, poissonMeasure_zero_eq_dirac]
    refine ⟨aemeasurable_const, ?_⟩
    change μ.map (fun _ => (0 : ℕ)) = _
    rw [Measure.map_const]; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm (Y a), add_comm (r a)]
    exact IndepFun.hasLaw_add_poissonMeasure (hind.indepFun_finsetSum_of_notMem hmeas ha) ih
      (hY a)

/-- **Given the covariates the count is Poisson with the summed rate**: independent `Po(lamᵢ)`
outcomes have the count law `Po(∑ lamᵢ)`. -/
theorem map_sum_pi_poisson {n : ℕ} (r : Fin n → ℝ≥0) :
    (Measure.pi fun i => poissonMeasure (r i)).map (fun y => ∑ i, y i) =
      poissonMeasure (∑ i, r i) := by
  classical
  have hind : iIndepFun (fun i (y : Fin n → ℕ) => y i) (Measure.pi fun i => poissonMeasure (r i)) :=
    iIndepFun_pi (X := fun _ (k : ℕ) => k) fun _ => aemeasurable_id
  have hY : ∀ i, HasLaw (fun y : Fin n → ℕ => y i) (poissonMeasure (r i))
      (Measure.pi fun i => poissonMeasure (r i)) := fun i => by
    refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
    rw [show (fun y : Fin n → ℕ => y i) = Function.eval i from rfl, Measure.pi_map_eval]
    simp
  rw [← (hasLaw_sum_poissonMeasure (fun i => measurable_pi_apply i) hind hY).map_eq]
  congr 1
  funext y; simp

open Real in
private lemma hasSum_poissonMeasure_moments (r : ℝ≥0) :
    HasSum (fun k : ℕ => (exp (-r) * r ^ k / k.factorial) * (k : ℝ)) r ∧
      HasSum (fun k : ℕ => (exp (-r) * r ^ k / k.factorial) * (k : ℝ) ^ 2) (r + r ^ 2) := by
  have he := (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left (exp (-r))
  have hc : exp (-r) * NormedSpace.exp (r : ℝ) = 1 := by
    rw [← exp_eq_exp_ℝ, ← exp_add]; simp
  have h1 : HasSum (fun k : ℕ => (exp (-r) * r ^ k / k.factorial) * (k : ℝ)) r := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, mul_zero, sub_zero]
    convert he.mul_left (r : ℝ) using 1
    · funext m
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      field_simp
    · rw [hc, mul_one]
  have h2 : HasSum (fun k : ℕ => (exp (-r) * r ^ k / k.factorial) * ((k : ℝ) * (k - 1)))
      (r ^ 2) := by
    rw [← hasSum_nat_add_iff' 2]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      Nat.cast_one, zero_mul, mul_zero, sub_self, zero_add, sub_zero]
    convert he.mul_left ((r : ℝ) ^ 2) using 1
    · funext m
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul, pow_add]
      push_cast
      field_simp
      ring
    · rw [hc, mul_one]
  refine ⟨h1, ?_⟩
  convert h2.add h1 using 1
  · funext k; ring
  · ring

/-- **The moments of a Poisson law**: `Po(lam)` has finite second moment, mean `lam`, second moment
`lam + lam²` and variance `lam`. -/
theorem integral_variance_poissonMeasure (r : ℝ≥0) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (poissonMeasure r) ∧ ∫ k, (k : ℝ) ∂poissonMeasure r = r ∧
      ∫ k, (k : ℝ) ^ 2 ∂poissonMeasure r = r + r ^ 2 ∧
      variance (fun k : ℕ => (k : ℝ)) (poissonMeasure r) = r := by
  obtain ⟨h1, h2⟩ := hasSum_poissonMeasure_moments r
  have i1 : Integrable (fun k : ℕ => (k : ℝ)) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]; simpa using h1.summable
  have i2 : Integrable (fun k : ℕ => (k : ℝ) ^ 2) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]; simpa using h2.summable
  have e1 : ∫ k, (k : ℝ) ∂poissonMeasure r = r :=
    (hasSum_integral_poissonMeasure i1).unique (by simpa using h1)
  have e2 : ∫ k, (k : ℝ) ^ 2 ∂poissonMeasure r = r + r ^ 2 :=
    (hasSum_integral_poissonMeasure i2).unique (by simpa using h2)
  have hm : MemLp (fun k : ℕ => (k : ℝ)) 2 (poissonMeasure r) :=
    (memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).mpr i2
  refine ⟨hm, e1, e2, ?_⟩
  rw [variance_eq_sub hm]
  simp only [Pi.pow_apply]
  rw [e2, e1]; ring

end Poisson

/-! ### The Poisson kernel and the mixed Poisson law -/

section Kernel

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **Poisson outcome kernel** of a nonnegative rate function `r`: a patient with covariates
`x` has the outcome law `Po(r(x))`. -/
noncomputable def poissonKernel (r : 𝒳 → ℝ) (hr : Measurable r) :
    Kernel 𝒳 ℕ where
  toFun x := poissonMeasure (r x).toNNReal
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [poissonMeasure, Measure.sum_apply _ hs, smul_apply, smul_eq_mul]
    exact Measurable.tsum fun k => Measurable.mul_const
      (ENNReal.measurable_ofReal.comp (by fun_prop)) _

theorem poissonKernel_apply (r : 𝒳 → ℝ) (hr : Measurable r) (x : 𝒳) :
    poissonKernel r hr x = poissonMeasure (r x).toNNReal :=
  rfl

instance (r : 𝒳 → ℝ) (hr : Measurable r) :
    IsMarkovKernel (poissonKernel r hr) :=
  ⟨fun x => by rw [poissonKernel_apply]; infer_instance⟩

variable {F : Measure 𝒳} [IsProbabilityMeasure F] {r : 𝒳 → ℝ} {hr : Measurable r}
  (h0 : ∀ x, 0 ≤ r x)
include h0

/-- **The outcome of a patient drawn from the covariate law has a mixed Poisson law**:
`P(Y = y) = ∫ e^{-r(x)} r(x)^y / y! F(dx)`. -/
theorem measureReal_snd_compProd_poissonKernel (y : ℕ) :
    (F ⊗ₘ poissonKernel r hr).snd.real {y} =
      ∫ x, Real.exp (-r x) * r x ^ y / y.factorial ∂F := by
  have hb : ∀ x, Real.exp (-r x) * r x ^ y / y.factorial =
      (poissonMeasure (r x).toNNReal).real {y} := fun x => by
    rw [poissonMeasure_real_singleton, Real.coe_toNNReal _ (h0 x)]
  have hi : Integrable (fun x => Real.exp (-r x) * r x ^ y / y.factorial) F :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [hb, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hnn : ∀ x, 0 ≤ Real.exp (-r x) * r x ^ y / y.factorial := fun x => by
    rw [hb]; exact measureReal_nonneg
  rw [Measure.snd_compProd, measureReal_def, Measure.bind_apply (measurableSet_singleton y)
    (Kernel.aemeasurable _)]
  have hl : ∫⁻ x, poissonKernel r hr x {y} ∂F =
      ENNReal.ofReal (∫ x, Real.exp (-r x) * r x ^ y / y.factorial ∂F) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnn)]
    refine lintegral_congr fun x => ?_
    rw [hb, ofReal_measureReal, poissonKernel_apply]
  rw [hl, ENNReal.toReal_ofReal (integral_nonneg hnn)]

omit h0 in
/-- Expectations of a nonnegative function of the outcome under the mixed Poisson law are
covariate averages of the Poisson expectations. -/
private lemma integral_snd_poissonKernel_of_nonneg {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k)
    {G : 𝒳 → ℝ} (hG : ∀ x, Integrable g (poissonMeasure (r x).toNNReal) ∧
      ∫ k, g k ∂poissonMeasure (r x).toNNReal = G x) (hGi : Integrable G F) :
    Integrable g (F ⊗ₘ poissonKernel r hr).snd ∧
      ∫ k, g k ∂(F ⊗ₘ poissonKernel r hr).snd = ∫ x, G x ∂F := by
  have hG0 : ∀ x, 0 ≤ G x := fun x => (hG x).2 ▸ integral_nonneg hg
  have hl : ∫⁻ k, ENNReal.ofReal (g k) ∂(F ⊗ₘ poissonKernel r hr).snd =
      ENNReal.ofReal (∫ x, G x ∂F) := by
    rw [Measure.snd_compProd, Measure.lintegral_bind (Kernel.aemeasurable _)
      Measurable.of_discrete.aemeasurable, ofReal_integral_eq_lintegral_ofReal hGi
      (ae_of_all _ hG0)]
    refine lintegral_congr fun x => ?_
    rw [poissonKernel_apply, ← (hG x).2,
      ofReal_integral_eq_lintegral_ofReal (hG x).1 (ae_of_all _ hg)]
  have hi := integrable_toReal_of_lintegral_ne_top
    (Measurable.of_discrete (f := fun k => ENNReal.ofReal (g k))).aemeasurable
    (by rw [hl]; exact ENNReal.ofReal_ne_top)
  simp only [ENNReal.toReal_ofReal (hg _)] at hi
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg) hi.aestronglyMeasurable, hl,
    ENNReal.toReal_ofReal (integral_nonneg hG0)]

/-- **The mean of the mixed Poisson law**: for an integrable rate, the outcome is integrable
with mean `∫ r dF`. -/
theorem integral_snd_compProd_poissonKernel (hri : Integrable r F) :
    Integrable (fun k : ℕ => (k : ℝ)) (F ⊗ₘ poissonKernel r hr).snd ∧
      ∫ k, (k : ℝ) ∂(F ⊗ₘ poissonKernel r hr).snd = ∫ x, r x ∂F :=
  integral_snd_poissonKernel_of_nonneg (fun k => Nat.cast_nonneg k)
    (fun x => ⟨(integral_variance_poissonMeasure _).1.integrable one_le_two,
      by rw [(integral_variance_poissonMeasure _).2.1, Real.coe_toNNReal _ (h0 x)]⟩) hri

/-- **The variance of the mixed Poisson law**: for a square integrable rate, the outcome has
finite second moment and variance `∫ r dF + Var r`. -/
theorem variance_snd_compProd_poissonKernel (hr2 : MemLp r 2 F) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (F ⊗ₘ poissonKernel r hr).snd ∧
      variance (fun k : ℕ => (k : ℝ)) (F ⊗ₘ poissonKernel r hr).snd =
        ∫ x, r x ∂F + variance r F := by
  have hri := hr2.integrable one_le_two
  obtain ⟨-, e1⟩ := integral_snd_compProd_poissonKernel h0 (hr := hr) hri
  obtain ⟨i2, e2⟩ := integral_snd_poissonKernel_of_nonneg (hr := hr)
    (g := fun k => (k : ℝ) ^ 2) (fun k => sq_nonneg _) (G := fun x => r x + r x ^ 2)
    (fun x => ⟨(integral_variance_poissonMeasure _).1.integrable_sq,
      by rw [(integral_variance_poissonMeasure _).2.2.1, Real.coe_toNNReal _ (h0 x)]⟩)
    (hri.add hr2.integrable_sq)
  have hm : MemLp (fun k : ℕ => (k : ℝ)) 2 (F ⊗ₘ poissonKernel r hr).snd :=
    (memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).mpr i2
  refine ⟨hm, ?_⟩
  rw [variance_eq_sub hm, variance_eq_sub hr2]
  simp only [Pi.pow_apply]
  rw [e2, e1, integral_add hri hr2.integrable_sq]
  ring

end Kernel

/-! ### The count of an arm -/

section Count

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {F : Measure 𝒳} [IsProbabilityMeasure F]
  {r : 𝒳 → ℝ} {hr : Measurable r}

theorem measurable_snd_pi (n : ℕ) : Measurable fun z : Fin n → 𝒳 × ℕ => fun i => (z i).2 :=
  measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i)

/-- The outcomes of `n` independent patients with joint law `F ⊗ Po(r(x))` are independent with
the mixed Poisson law. -/
theorem map_snd_pi_compProd (n : ℕ) {κ : Kernel 𝒳 ℕ} [IsMarkovKernel κ] :
    (Measure.pi fun _ : Fin n => F ⊗ₘ κ).map (fun z i => (z i).2) =
      Measure.pi fun _ : Fin n => (F ⊗ₘ κ).snd := by
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  rfl

private lemma integral_sum_pi {n : ℕ} (ρ : Measure ℕ) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun k : ℕ => (k : ℝ)) ρ) :
    ∫ y, ((∑ i, y i : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin n => ρ) = n * ∫ k, (k : ℝ) ∂ρ := by
  have hcast : (fun y : Fin n → ℕ => ((∑ i, y i : ℕ) : ℝ)) = fun y => ∑ i, (y i : ℝ) := by
    funext y; simp
  · rw [hcast, integral_finsetSum (s := Finset.univ) (f := fun i (y : Fin n → ℕ) => (y i : ℝ))
      fun i _ => (measurePreserving_eval (μ := fun _ : Fin n => ρ) i).integrable_comp_of_integrable
        hρ]
    have he : ∀ i : Fin n, ∫ y, (y i : ℝ) ∂(Measure.pi fun _ : Fin n => ρ) =
        ∫ k, (k : ℝ) ∂ρ := fun i => by
      conv_rhs => rw [← (measurePreserving_eval (μ := fun _ : Fin n => ρ) i).map_eq]
      rw [integral_map (measurable_pi_apply i).aemeasurable
        Measurable.of_discrete.aestronglyMeasurable]
    simp [he]

private lemma variance_sum_pi_nat {n : ℕ} (ρ : Measure ℕ) [IsProbabilityMeasure ρ]
    (hρ : MemLp (fun k : ℕ => (k : ℝ)) 2 ρ) :
    variance (fun y => ((∑ i, y i : ℕ) : ℝ)) (Measure.pi fun _ : Fin n => ρ) =
      n * variance (fun k : ℕ => (k : ℝ)) ρ := by
  have hcast : (fun y : Fin n → ℕ => ((∑ i, y i : ℕ) : ℝ)) = fun y => ∑ i, (y i : ℝ) := by
    funext y; simp
  · rw [hcast]
    have := variance_sum_pi (μ := fun _ : Fin n => ρ) (X := fun _ (k : ℕ) => (k : ℝ))
      fun _ => hρ
    have e : (∑ i : Fin n, fun ω : Fin n → ℕ => (ω i : ℝ)) = fun y => ∑ i, (y i : ℝ) := by
      funext y; simp
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [← e]; exact this

/-- **The mean of the aggregate Poisson count**: the count of `n` independent patients with
covariates from `F` and `Po(r(x))` outcomes has mean `n ∫ r dF`. -/
theorem integral_count_poisson (h0 : ∀ x, 0 ≤ r x) (hri : Integrable r F) (n : ℕ) :
    ∫ z, ((∑ i, (z i).2 : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) =
      n * ∫ x, r x ∂F := by
  rw [← (integral_snd_compProd_poissonKernel h0 (hr := hr) hri).2,
    ← integral_sum_pi _ (integral_snd_compProd_poissonKernel h0 (hr := hr) hri).1,
    ← map_snd_pi_compProd, integral_map (measurable_snd_pi n).aemeasurable (by fun_prop)]

/-- **The variance of the aggregate Poisson count**: `n ∫ r dF + n Var r`. -/
theorem variance_count_poisson (h0 : ∀ x, 0 ≤ r x) (hr2 : MemLp r 2 F) (n : ℕ) :
    variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ))
        (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) =
      n * ∫ x, r x ∂F + n * variance r F := by
  have h := variance_sum_pi_nat (n := n) _
    (variance_snd_compProd_poissonKernel h0 (hr := hr) hr2).1
  rw [(variance_snd_compProd_poissonKernel h0 hr2).2, ← map_snd_pi_compProd,
    variance_map (by fun_prop) (measurable_snd_pi n).aemeasurable] at h
  rw [show (fun z : Fin n → 𝒳 × ℕ => ((∑ i, (z i).2 : ℕ) : ℝ)) =
    (fun y : Fin n → ℕ => ((∑ i, y i : ℕ) : ℝ)) ∘ fun z i => (z i).2 from rfl, h]
  ring

/-- **Overdispersion**: the variance of the aggregate Poisson count is at least its mean. -/
theorem integral_le_variance_count_poisson (h0 : ∀ x, 0 ≤ r x) (hr2 : MemLp r 2 F) (n : ℕ) :
    ∫ z, ((∑ i, (z i).2 : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) ≤
      variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ))
        (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) := by
  rw [integral_count_poisson h0 (hr2.integrable one_le_two), variance_count_poisson h0 hr2]
  have := variance_nonneg r F
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- **Equidispersion only for a constant rate**: for `n ≥ 1` the variance of the aggregate
Poisson count equals its mean exactly when the rate is almost surely constant. -/
theorem variance_count_poisson_eq_integral_iff (h0 : ∀ x, 0 ≤ r x) (hr2 : MemLp r 2 F) {n : ℕ}
    (hn : 0 < n) :
    variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ))
        (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) =
      ∫ z, ((∑ i, (z i).2 : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) ↔
      ∃ c : ℝ, r =ᵐ[F] fun _ => c := by
  rw [integral_count_poisson h0 (hr2.integrable one_le_two), variance_count_poisson h0 hr2]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · intro h
    have h0' : variance r F = 0 := by
      have : (n : ℝ) * variance r F = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hn'
    exact ⟨_, ae_eq_integral_of_variance_eq_zero hr2 h0'⟩
  · rintro ⟨c, hc⟩
    rw [variance_congr hc, variance_eq_sub (memLp_const _)]
    simp

/-- **When the aggregate count is Poisson**: for `n ≥ 1` and a square integrable rate, the count
has a Poisson law exactly when the rate is almost surely constant, `r = c`; the law is then
`Po(n c)`. -/
theorem exists_poisson_count_iff (h0 : ∀ x, 0 ≤ r x) (hr2 : MemLp r 2 F) {n : ℕ} (hn : 0 < n) :
    (∃ lam : ℝ≥0, (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr).map
        (fun z => ∑ i, (z i).2) = poissonMeasure lam) ↔
      ∃ c : ℝ≥0, r =ᵐ[F] fun _ => (c : ℝ) := by
  constructor
  · rintro ⟨lam, hlam⟩
    have hm : Measurable fun z : Fin n → 𝒳 × ℕ => ∑ i, (z i).2 := by fun_prop
    have hE : ∫ z, ((∑ i, (z i).2 : ℕ) : ℝ)
        ∂(Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) = lam := by
      rw [← (integral_variance_poissonMeasure lam).2.1, ← hlam,
        integral_map hm.aemeasurable (by fun_prop)]
    have hV : variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ))
        (Measure.pi fun _ : Fin n => F ⊗ₘ poissonKernel r hr) = lam := by
      rw [← (integral_variance_poissonMeasure lam).2.2.2, ← hlam,
        variance_map Measurable.of_discrete.aemeasurable hm.aemeasurable]
      rfl
    obtain ⟨c, hc⟩ := (variance_count_poisson_eq_integral_iff h0 hr2 hn).mp (hV.trans hE.symm)
    have hc0 : 0 ≤ c := by
      obtain ⟨x, hx⟩ := hc.exists
      have := h0 x
      rwa [hx] at this
    exact ⟨⟨c, hc0⟩, hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨n * c, ?_⟩
    have hsnd : (F ⊗ₘ poissonKernel r hr).snd = poissonMeasure c := by
      rw [Measure.snd_compProd]
      refine Measure.ext fun s hs => ?_
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      rw [lintegral_congr_ae (g := fun _ => poissonMeasure c s) (hc.mono fun x hx => by
        rw [poissonKernel_apply, hx, Real.toNNReal_coe])]
      simp
    rw [show (fun z : Fin n → 𝒳 × ℕ => ∑ i, (z i).2) =
        (fun y : Fin n → ℕ => ∑ i, y i) ∘ (fun z i => (z i).2) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), map_snd_pi_compProd, hsnd,
      map_sum_pi_poisson]
    simp

end Count

/-! ### The multilevel model -/

namespace MultilevelModel

variable {J K : Type*} {p : ℕ} {ginv : ℝ → ℝ}

/-- A nonnegative inverse link gives a nonnegative rate surface. -/
theorem surface_nonneg (h0 : ∀ y, 0 ≤ ginv y) (M : MultilevelModel J K p) (α : ℝ) (k : K)
    (x : Fin p → ℝ) : 0 ≤ M.surface ginv α k x :=
  h0 _

variable (hginv : Measurable ginv) (h0 : ∀ y, 0 ≤ ginv y) (M : MultilevelModel J K p) (α : ℝ)
  (k : K) {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
include h0

/-- **The mean of the aggregate count of the multilevel model for a count outcome**: the count of
an arm of `n` patients has mean `n θ`, with `θ` the aggregate arm mean. -/
theorem integral_count_poisson (hF : Integrable (M.surface ginv α k) F) (n : ℕ) :
    ∫ z, ((∑ i, (z i).2 : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin n =>
        F ⊗ₘ poissonKernel _ (M.measurable_surface hginv α k)) =
      n * M.armMean ginv α F k :=
  NetworkMetaRegression.integral_count_poisson (surface_nonneg h0 M α k) hF n

/-- **The variance of the aggregate count of the multilevel model**: `n θ + n Var g⁻¹(η_k)`. -/
theorem variance_count_poisson (hF : MemLp (M.surface ginv α k) 2 F) (n : ℕ) :
    variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ)) (Measure.pi fun _ : Fin n =>
        F ⊗ₘ poissonKernel _ (M.measurable_surface hginv α k)) =
      n * M.armMean ginv α F k + n * variance (M.surface ginv α k) F :=
  NetworkMetaRegression.variance_count_poisson (surface_nonneg h0 M α k) hF n

/-- **Equidispersion of the multilevel count**: for `n ≥ 1` the variance of the count of an arm
equals its mean exactly when the rate surface is almost surely equal to the arm mean. -/
theorem variance_count_poisson_eq_iff (hF : MemLp (M.surface ginv α k) 2 F) {n : ℕ}
    (hn : 0 < n) :
    variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ)) (Measure.pi fun _ : Fin n =>
        F ⊗ₘ poissonKernel _ (M.measurable_surface hginv α k)) =
      n * M.armMean ginv α F k ↔ M.surface ginv α k =ᵐ[F] fun _ => M.armMean ginv α F k := by
  rw [← M.integral_count_poisson hginv h0 α k (hF.integrable one_le_two) n,
    variance_count_poisson_eq_integral_iff (surface_nonneg h0 M α k) hF hn]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun h => ⟨_, h⟩⟩
  have hθ : M.armMean ginv α F k = c := by
    rw [armMean, integral_congr_ae hc]; simp
  rwa [hθ]

omit h0 in
/-- **The aggregate count under the log link with Gaussian covariates**: with `g⁻¹ = exp` and a
Gaussian covariate law, the count of an arm of `n` patients has variance
`n θ + n θ² (exp(v) - 1)`, with `θ` the aggregate arm mean and `v` the variance of
`xᵀ(β₁ + β₂,k)`. -/
theorem variance_count_exp_gaussian (M : MultilevelModel J K p) (α : ℝ) (k : K)
    (F : Measure (Fin p → ℝ)) [IsGaussian F] (n : ℕ) :
    variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ)) (Measure.pi fun _ : Fin n =>
        F ⊗ₘ poissonKernel _ (M.measurable_surface Real.measurable_exp α k)
) =
      n * M.armMean Real.exp α F k +
        n * (M.armMean Real.exp α F k) ^ 2 * (Real.exp (slopeVar F (M.β₁ + M.β₂ k)) - 1) := by
  have hθ : 0 < M.armMean Real.exp α F k := by
    rw [(M.armMean_exp_gaussian α F k)]; exact Real.exp_pos _
  have hod := M.overdispersion_exp_gaussian α F k
  have hV : variance (M.surface Real.exp α k) F = (M.armMean Real.exp α F k) ^ 2 *
      (Real.exp (slopeVar F (M.β₁ + M.β₂ k)) - 1) := by
    have h := hod
    rw [div_eq_iff (pow_ne_zero 2 hθ.ne')] at h
    rw [mul_comm]; exact h
  have hL := M.hasLaw_eta_gaussian α F k
  have hint2 : Integrable (fun x => Real.exp (2 * M.eta α k x)) F := by
    have := integrable_exp_mul_gaussianReal (μ := M.eta α k (IndirectComparison.covMean F))
      (v := (slopeVar F (M.β₁ + M.β₂ k)).toNNReal) 2
    rw [← hL.map_eq] at this
    exact (integrable_map_measure (by fun_prop) hL.aemeasurable).mp this
  have hmem : MemLp (M.surface Real.exp α k) 2 F := by
    have hm : AEStronglyMeasurable (fun x => Real.exp (M.eta α k x)) F :=
      (Real.continuous_exp.measurable.comp_aemeasurable hL.aemeasurable).aestronglyMeasurable
    change MemLp (fun x => Real.exp (M.eta α k x)) 2 F
    rw [memLp_two_iff_integrable_sq hm]
    simpa [← Real.exp_nat_mul] using hint2
  rw [M.variance_count_poisson Real.measurable_exp (fun y => (Real.exp_pos y).le) α k hmem n, hV]
  ring

end MultilevelModel

end NetworkMetaRegression

end CausalInference
