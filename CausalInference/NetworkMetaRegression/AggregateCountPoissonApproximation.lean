/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountApproximation
public import CausalInference.NetworkMetaRegression.AggregateCountPoisson

/-!
# Poisson approximation of the aggregate binary count

Given the covariates, the count of events of an arm with risks `q₁, …, qₙ` has the Poisson
binomial law `PoBin(q)` (`poissonBinomial`). Le Cam's inequality says that it is close to the
Poisson law with the same mean `∑ qᵢ` when the risks are small. The total variation distance is
Mathlib's `MeasureTheory.tvDist`, the total variation norm of `μ - ν`; for probability laws the
largest difference of set probabilities is half of it.

* **The `ℓ¹` formula** (`hasSum_abs_measureReal_singleton_tvDist`,
  `tvDist_eq_tsum_abs_measureReal_singleton`): for finite measures on a countable space with
  measurable points, `|μ {k} - ν {k}|` is summable and `tvDist μ ν = ∑ₖ |μ {k} - ν {k}|`; for
  probability laws `∑ₖ min (μ {k}) (ν {k}) = 1 - tvDist μ ν / 2`
  (`hasSum_min_measureReal_singleton`).
* **One Bernoulli and one Poisson count** (`bernoulliPoissonCoupling`,
  `map_fst_bernoulliPoissonCoupling`, `map_snd_bernoulliPoissonCoupling`,
  `measureReal_ne_bernoulliPoissonCoupling`): a law on pairs with margins `Ber(p)` and `Po(p)`
  whose coordinates differ with probability `p - p e^{-p} ≤ p²`.
* **Sums of coupled pairs** (`measureReal_sum_ne_sum_le`, `sumPairLaw`, `map_fst_sumPairLaw`,
  `map_snd_sumPairLaw`, `measureReal_ne_sumPairLaw_le`): `P(∑ Xᵢ ≠ ∑ Yᵢ) ≤ ∑ P(Xᵢ ≠ Yᵢ)`; for
  independent pairs the first sum has the law `PoBin(q)` when `Xᵢ ∼ Ber(qᵢ)` and the second sum
  has the law `Po(∑ rᵢ)` when `Yᵢ ∼ Po(rᵢ)`.
* **Le Cam's inequality** (`abs_measureReal_poissonBinomial_sub_poissonMeasure_le`,
  `abs_measureReal_poissonBinomial_sub_poissonMeasure_le_sum_sub_mul_exp`,
  `tvDist_poissonBinomial_poissonMeasure_le`): on every set `A`,
  `|PoBin(q)(A) - Po(∑ qᵢ)(A)| ≤ ∑ (qᵢ - qᵢ e^{-qᵢ}) ≤ ∑ qᵢ²`, and
  `tvDist (PoBin(q)) (Po(∑ qᵢ)) ≤ 2 ∑ qᵢ²`.
* **The binomial law** (`abs_measureReal_binomial_sub_poissonMeasure_le`,
  `abs_measureReal_binomial_div_sub_poissonMeasure_le`, `tendsto_tvDist_binomial_poissonMeasure`):
  `|Bin(n, θ)(A) - Po(n θ)(A)| ≤ n θ²`; for `n > 0` and `0 ≤ t ≤ n`, `Bin(n, t/n)` is within
  `t² / n` of `Po(t)` on every set, so `Bin(n, t/n) → Po(t)` in total variation.

## Main definitions

* `bernoulliPoissonCoupling`, `sumPairLaw`, `poissonBinomialCoupling`.

## Main results

* `hasSum_abs_measureReal_singleton_tvDist`, `tvDist_eq_tsum_abs_measureReal_singleton`,
  `hasSum_min_measureReal_singleton`.
* `map_fst_bernoulliPoissonCoupling`, `map_snd_bernoulliPoissonCoupling`,
  `measureReal_ne_bernoulliPoissonCoupling`.
* `measureReal_sum_ne_sum_le`, `map_fst_sumPairLaw`, `map_snd_sumPairLaw`,
  `measureReal_ne_sumPairLaw_le`, `poissonBinomialCoupling_spec`.
* `abs_measureReal_poissonBinomial_sub_poissonMeasure_le`,
  `tvDist_poissonBinomial_poissonMeasure_le`, `abs_measureReal_binomial_sub_poissonMeasure_le`,
  `abs_measureReal_binomial_div_sub_poissonMeasure_le`, `tendsto_tvDist_binomial_poissonMeasure`.

## References

* L. Le Cam, *An approximation theorem for the Poisson binomial distribution*, Pacific Journal
  of Mathematics 10 (1960).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped unitInterval ENNReal NNReal

namespace CausalInference

namespace NetworkMetaRegression

/-! ### Total variation on a countable space -/

section Countable

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- On a countable space with measurable points, the probability of a set is the sum of the
point masses in it. -/
theorem hasSum_indicator_measureReal_singleton (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    HasSum (A.indicator fun k => μ.real {k}) (μ.real A) := by
  have h := μ.tsum_indicator_apply_singleton A A.to_countable.measurableSet
  have hne : ∑' k, A.indicator (fun k => μ {k}) k ≠ ∞ := by rw [h]; exact measure_ne_top _ _
  have e : (fun k => (A.indicator (fun k => μ {k}) k).toReal) =
      A.indicator fun k => μ.real {k} := by
    funext k
    by_cases hk : k ∈ A <;> simp [hk, measureReal_def]
  have hs := ENNReal.hasSum_toReal hne
  rw [measureReal_def, ← h, ENNReal.tsum_toReal_eq fun k => ?_, ← e]
  · exact hs
  · by_cases hk : k ∈ A <;> simp [hk, measure_ne_top]

/-- **Total variation as the `ℓ¹` distance of the mass functions**: for finite measures on a
countable space with measurable points, the point differences `|μ {k} - ν {k}|` are summable
with sum `tvDist μ ν`. Proof: on a Hahn set `s` of the pair every point has
`μ {k} ≤ ν {k}`, off it `ν {k} ≤ μ {k}`, and `tvDist μ ν = (ν s - μ s) + (μ sᶜ - ν sᶜ)`. -/
theorem hasSum_abs_measureReal_singleton_tvDist (μ ν : Measure S) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : HasSum (fun k => |μ.real {k} - ν.real {k}|) (tvDist μ ν) := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  have hle : ∀ k ∈ s, μ.real {k} ≤ ν.real {k} := fun k hk => by
    have := h.le_on {k}
    rw [Measure.restrict_apply (measurableSet_singleton k),
      Measure.restrict_apply (measurableSet_singleton k),
      Set.singleton_inter_of_mem hk] at this
    exact ENNReal.toReal_mono (measure_ne_top _ _) this
  have hge : ∀ k ∉ s, ν.real {k} ≤ μ.real {k} := fun k hk => by
    have := h.ge_on_compl {k}
    rw [Measure.restrict_apply (measurableSet_singleton k),
      Measure.restrict_apply (measurableSet_singleton k),
      Set.singleton_inter_of_mem (Set.mem_compl hk)] at this
    exact ENNReal.toReal_mono (measure_ne_top _ _) this
  have e : (fun k => |μ.real {k} - ν.real {k}|) =
      fun k => (s.indicator (fun k => ν.real {k}) k - s.indicator (fun k => μ.real {k}) k) +
        (sᶜ.indicator (fun k => μ.real {k}) k - sᶜ.indicator (fun k => ν.real {k}) k) := by
    funext k
    by_cases hk : k ∈ s
    · simp only [Set.indicator_of_mem hk, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hk)]
      rw [abs_of_nonpos (by linarith [hle k hk])]; ring
    · simp only [Set.indicator_of_notMem hk, Set.indicator_of_mem (Set.mem_compl hk)]
      rw [abs_of_nonneg (by linarith [hge k hk])]; ring
  rw [e, h.tvDist_eq]
  exact ((hasSum_indicator_measureReal_singleton ν s).sub
    (hasSum_indicator_measureReal_singleton μ s)).add
    ((hasSum_indicator_measureReal_singleton μ sᶜ).sub
      (hasSum_indicator_measureReal_singleton ν sᶜ))

/-- **The `ℓ¹` formula for total variation**: for finite measures on a countable space with
measurable points, `|μ {k} - ν {k}|` is summable and `tvDist μ ν = ∑ₖ |μ {k} - ν {k}|`. -/
theorem tvDist_eq_tsum_abs_measureReal_singleton (μ ν : Measure S) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : Summable (fun k => |μ.real {k} - ν.real {k}|) ∧
      tvDist μ ν = ∑' k, |μ.real {k} - ν.real {k}| :=
  ⟨(hasSum_abs_measureReal_singleton_tvDist μ ν).summable,
    (hasSum_abs_measureReal_singleton_tvDist μ ν).tsum_eq.symm⟩

/-- **Total variation through the overlap of the mass functions**: for probability laws on a
countable space with measurable points, `min (μ {k}) (ν {k})` is summable with sum
`1 - tvDist μ ν / 2`. Proof: `min a b = (a + b - |a - b|) / 2`. -/
theorem hasSum_min_measureReal_singleton (μ ν : Measure S) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    HasSum (fun k => min (μ.real {k}) (ν.real {k})) (1 - tvDist μ ν / 2) := by
  have hμ := hasSum_indicator_measureReal_singleton μ Set.univ
  have hν := hasSum_indicator_measureReal_singleton ν Set.univ
  simp only [Set.indicator_univ, probReal_univ] at hμ hν
  have h := ((hμ.add hν).sub (hasSum_abs_measureReal_singleton_tvDist μ ν)).div_const 2
  convert h using 1
  · funext k
    rcases le_total (μ.real {k}) (ν.real {k}) with hk | hk
    · rw [min_eq_left hk, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right hk, abs_of_nonneg (by linarith)]; ring
  · ring

end Countable

/-! ### The coupling of one Bernoulli and one Poisson count -/

section SingleCoupling

/-- The law on pairs coupling `Ber(p)` with `Po(p)`: mass `1 - p` at `(0, 0)`,
`e^{-p} - (1 - p)` at `(1, 0)` and `Po(p) {k}` at `(1, k)` for every `k ≥ 1`. -/
noncomputable def bernoulliPoissonCoupling (p : I) : Measure (ℕ × ℕ) :=
  ENNReal.ofReal (1 - p) • Measure.dirac (0, 0) +
    ENNReal.ofReal (Real.exp (-p) - (1 - p)) • Measure.dirac (1, 0) +
    ((poissonMeasure (p : ℝ).toNNReal).restrict {k | 1 ≤ k}).map fun k => (1, k)

private lemma poissonMeasure_real_zero (p : I) :
    (poissonMeasure (p : ℝ).toNNReal).real {0} = Real.exp (-p) := by
  rw [poissonMeasure_real_singleton, Real.coe_toNNReal _ p.2.1]; simp

private lemma poissonMeasure_real_one (p : I) :
    (poissonMeasure (p : ℝ).toNNReal).real {1} = p * Real.exp (-p) := by
  rw [poissonMeasure_real_singleton, Real.coe_toNNReal _ p.2.1]; simp; ring

/-- The second margin of the coupling is `Po(p)`. -/
theorem map_snd_bernoulliPoissonCoupling (p : I) :
    (bernoulliPoissonCoupling p).map Prod.snd = poissonMeasure (p : ℝ).toNNReal := by
  have hE : MeasurableSet {k : ℕ | 1 ≤ k} := MeasurableSet.of_discrete
  rw [bernoulliPoissonCoupling, Measure.map_add _ _ measurable_snd,
    Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd,
    Measure.map_map measurable_snd (by fun_prop)]
  rotate_left
  · fun_prop
  · fun_prop
  have hc : (Prod.snd ∘ fun k : ℕ => ((1 : ℕ), k)) = id := rfl
  rw [hc, Measure.map_id]
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := poissonMeasure _) hE.compl,
    compl_compl]
  rw [← add_smul]
  congr 1
  have h0 : ({k : ℕ | 1 ≤ k}ᶜ) = {0} := by ext k; simp
  rw [h0, Measure.restrict_singleton, ← ofReal_measureReal, poissonMeasure_real_zero,
    ← ENNReal.ofReal_add (by linarith [p.2.2]) (by linarith [Real.one_sub_le_exp_neg (p : ℝ)])]
  congr 2; ring

instance (p : I) : IsProbabilityMeasure (bernoulliPoissonCoupling p) :=
  (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mp
    (by rw [map_snd_bernoulliPoissonCoupling]; infer_instance)

/-- The first margin of the coupling is `Ber(p)` on `{0, 1}`. -/
theorem map_fst_bernoulliPoissonCoupling (p : I) :
    (bernoulliPoissonCoupling p).map Prod.fst = Ber(1, 0, p) := by
  have hE : MeasurableSet {k : ℕ | 1 ≤ k} := MeasurableSet.of_discrete
  rw [bernoulliPoissonCoupling, Measure.map_add _ _ measurable_fst,
    Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst,
    Measure.map_map measurable_fst (by fun_prop)]
  rotate_left
  · fun_prop
  · fun_prop
  have hc : (Prod.fst ∘ fun k : ℕ => ((1 : ℕ), k)) = fun _ => 1 := rfl
  have hge : poissonMeasure (p : ℝ).toNNReal {k | 1 ≤ k} =
      ENNReal.ofReal (1 - Real.exp (-p)) := by
    have h : {k : ℕ | 1 ≤ k} = ({0} : Set ℕ)ᶜ := by ext k; simp [Nat.one_le_iff_ne_zero]
    rw [h, ← ofReal_measureReal, probReal_compl_eq_one_sub (measurableSet_singleton 0),
      poissonMeasure_real_zero]
  rw [hc, Measure.map_const, Measure.restrict_apply_univ, hge]
  refine Measure.ext_of_singleton fun k => ?_
  rw [← ofReal_measureReal (s := {k}) (μ := Ber(1, 0, p)), bernoulli_real_singleton,
    coeff_bernoulliGenPoly]
  simp only [add_apply, smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
  rcases k with _ | _ | k
  · simp
  · simp only [zero_ne_one, ite_false, ite_true, mul_zero, mul_one, zero_add, one_ne_zero]
    rw [← ENNReal.ofReal_add (by linarith [Real.one_sub_le_exp_neg (p : ℝ)])
      (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr p.2.1)])]
    congr 1; ring
  · simp

/-- **The coupling rarely disagrees**: the pair differs with probability exactly
`p - p e^{-p}`, which is at most `p²`. The off diagonal mass is
`(e^{-p} - 1 + p) + (1 - e^{-p} - p e^{-p})`, and `1 - e^{-p} ≤ p`. -/
theorem measureReal_ne_bernoulliPoissonCoupling (p : I) :
    (bernoulliPoissonCoupling p).real {z | z.1 ≠ z.2} = p - p * Real.exp (-p) ∧
      (p : ℝ) - p * Real.exp (-p) ≤ (p : ℝ) ^ 2 := by
  have hD : MeasurableSet {z : ℕ × ℕ | z.1 ≠ z.2} := MeasurableSet.of_discrete
  have hpre : (fun k : ℕ => ((1 : ℕ), k)) ⁻¹' {z : ℕ × ℕ | z.1 ≠ z.2} ∩ {k | 1 ≤ k} =
      ({0} ∪ {1} : Set ℕ)ᶜ := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_compl_iff,
      Set.mem_union, Set.mem_singleton_iff]
    omega
  have h01 : MeasurableSet ({0} ∪ {1} : Set ℕ) := MeasurableSet.of_discrete
  have hval : (poissonMeasure (p : ℝ).toNNReal).real (({0} ∪ {1} : Set ℕ)ᶜ) =
      1 - Real.exp (-p) - p * Real.exp (-p) := by
    rw [probReal_compl_eq_one_sub h01, measureReal_union (by simp) (measurableSet_singleton 1),
      poissonMeasure_real_zero, poissonMeasure_real_one]; ring
  have hb : 0 ≤ 1 - Real.exp (-p) - p * Real.exp (-p) := hval ▸ measureReal_nonneg
  have ha : 0 ≤ Real.exp (-p) - (1 - p) := by linarith [Real.one_sub_le_exp_neg (p : ℝ)]
  have h2 : poissonMeasure (p : ℝ).toNNReal (({0} ∪ {1} : Set ℕ)ᶜ) =
      ENNReal.ofReal (1 - Real.exp (-p) - p * Real.exp (-p)) := by
    rw [← hval, ofReal_measureReal]
  have hc : bernoulliPoissonCoupling p {z | z.1 ≠ z.2} =
      ENNReal.ofReal (Real.exp (-p) - (1 - p) + (1 - Real.exp (-p) - p * Real.exp (-p))) := by
    rw [bernoulliPoissonCoupling, add_apply, add_apply, smul_apply,
      smul_apply, Measure.map_apply (by fun_prop) hD,
      Measure.restrict_apply MeasurableSet.of_discrete, hpre, h2,
      Measure.dirac_apply' _ hD, Measure.dirac_apply' _ hD, ENNReal.ofReal_add ha hb]
    simp
  refine ⟨?_, ?_⟩
  · rw [measureReal_def, hc, ENNReal.toReal_ofReal (add_nonneg ha hb)]; ring
  · have h1 : 1 - Real.exp (-p) ≤ p := by linarith [Real.one_sub_le_exp_neg (p : ℝ)]
    nlinarith [p.2.1]

end SingleCoupling

/-! ### Sums of coupled pairs -/

section SumCoupling

/-- **A sum of pairs disagrees only where some pair disagrees**: for finitely many pairs of
counts on one space, `P(∑ Xᵢ ≠ ∑ Yᵢ) ≤ ∑ P(Xᵢ ≠ Yᵢ)`. No independence is needed. -/
theorem measureReal_sum_ne_sum_le {Ω M : Type*} [MeasurableSpace Ω] [AddCommMonoid M]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ι : Type*} [Fintype ι] (X Y : ι → Ω → M) :
    μ.real {ω | ∑ i, X i ω ≠ ∑ i, Y i ω} ≤ ∑ i, μ.real {ω | X i ω ≠ Y i ω} := by
  refine (measureReal_mono fun ω hω => ?_).trans (measureReal_iUnion_fintype_le _)
  by_contra h
  simp only [Set.mem_iUnion, not_exists, Set.mem_ofPred_eq, not_not] at h
  exact hω (Finset.sum_congr rfl fun i _ => h i)

variable {n : ℕ}

/-- The law of the two sums `(∑ Xᵢ, ∑ Yᵢ)` when the pairs `(Xᵢ, Yᵢ)` are independent with laws
`πᵢ`. -/
noncomputable def sumPairLaw (π : Fin n → Measure (ℕ × ℕ)) : Measure (ℕ × ℕ) :=
  (Measure.pi π).map fun ω => (∑ i, (ω i).1, ∑ i, (ω i).2)

instance (π : Fin n → Measure (ℕ × ℕ)) [∀ i, IsProbabilityMeasure (π i)] :
    IsProbabilityMeasure (sumPairLaw π) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- **The first sum of independent pairs with Bernoulli first coordinates is Poisson
binomial**: if the first margin of `πᵢ` is `Ber(qᵢ)`, the first margin of the law of the sums
is the Poisson binomial law with risks `q`. -/
theorem map_fst_sumPairLaw (π : Fin n → Measure (ℕ × ℕ)) [∀ i, IsProbabilityMeasure (π i)]
    {q : Fin n → I} (h : ∀ i, (π i).map Prod.fst = Ber(1, 0, q i)) :
    (sumPairLaw π).map Prod.fst = poissonBinomial q := by
  have hm : ∀ i, Measurable fun ω : Fin n → ℕ × ℕ => (ω i).1 := fun i => by fun_prop
  have hind : iIndepFun (fun i (ω : Fin n → ℕ × ℕ) => (ω i).1) (Measure.pi π) :=
    iIndepFun_pi (X := fun _ (z : ℕ × ℕ) => z.1) fun _ => measurable_fst.aemeasurable
  have hY : ∀ i, HasLaw (fun ω : Fin n → ℕ × ℕ => (ω i).1) Ber(1, 0, q i) (Measure.pi π) :=
    fun i => ⟨(hm i).aemeasurable, by
      rw [show (fun ω : Fin n → ℕ × ℕ => (ω i).1) = Prod.fst ∘ fun ω => ω i from rfl,
        ← Measure.map_map measurable_fst (measurable_pi_apply i),
        (measurePreserving_eval (μ := π) i).map_eq, h]⟩
  rw [sumPairLaw, Measure.map_map measurable_fst (by fun_prop)]
  exact map_sum_eq_poissonBinomial hm hind hY

/-- **The second sum of independent pairs with Poisson second coordinates is Poisson**: if the
second margin of `πᵢ` is `Po(rᵢ)`, the second margin of the law of the sums is `Po(∑ rᵢ)`. -/
theorem map_snd_sumPairLaw (π : Fin n → Measure (ℕ × ℕ)) [∀ i, IsProbabilityMeasure (π i)]
    {r : Fin n → ℝ≥0} (h : ∀ i, (π i).map Prod.snd = poissonMeasure (r i)) :
    (sumPairLaw π).map Prod.snd = poissonMeasure (∑ i, r i) := by
  have hm : ∀ i, Measurable fun ω : Fin n → ℕ × ℕ => (ω i).2 := fun i => by fun_prop
  have hind : iIndepFun (fun i (ω : Fin n → ℕ × ℕ) => (ω i).2) (Measure.pi π) :=
    iIndepFun_pi (X := fun _ (z : ℕ × ℕ) => z.2) fun _ => measurable_snd.aemeasurable
  have hY : ∀ i, HasLaw (fun ω : Fin n → ℕ × ℕ => (ω i).2) (poissonMeasure (r i))
      (Measure.pi π) :=
    fun i => ⟨(hm i).aemeasurable, by
      rw [show (fun ω : Fin n → ℕ × ℕ => (ω i).2) = Prod.snd ∘ fun ω => ω i from rfl,
        ← Measure.map_map measurable_snd (measurable_pi_apply i),
        (measurePreserving_eval (μ := π) i).map_eq, h]⟩
  rw [sumPairLaw, Measure.map_map measurable_snd (by fun_prop),
    ← (hasLaw_sum_poissonMeasure hm hind hY).map_eq]
  congr 1
  funext ω; simp

/-- **The sums disagree at most as often as the pairs**: under the law of the sums of
independent pairs, `P(∑ Xᵢ ≠ ∑ Yᵢ) ≤ ∑ πᵢ(X ≠ Y)`. -/
theorem measureReal_ne_sumPairLaw_le (π : Fin n → Measure (ℕ × ℕ))
    [∀ i, IsProbabilityMeasure (π i)] :
    (sumPairLaw π).real {z | z.1 ≠ z.2} ≤ ∑ i, (π i).real {z | z.1 ≠ z.2} := by
  rw [sumPairLaw, map_measureReal_apply (by fun_prop) MeasurableSet.of_discrete]
  refine (measureReal_sum_ne_sum_le (μ := Measure.pi π) (fun i ω => (ω i).1)
    (fun i ω => (ω i).2)).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [← (measurePreserving_eval (μ := π) i).map_eq, map_measureReal_apply (measurable_pi_apply i)
    MeasurableSet.of_discrete]
  rfl

end SumCoupling

/-! ### The Poisson approximation of the Poisson binomial law -/

section PoissonApproximation

variable {n : ℕ}

/-- The law of the two sums of independent couplings of `Ber(qᵢ)` with `Po(qᵢ)`. -/
noncomputable def poissonBinomialCoupling (q : Fin n → I) : Measure (ℕ × ℕ) :=
  sumPairLaw fun i => bernoulliPoissonCoupling (q i)

instance (q : Fin n → I) : IsProbabilityMeasure (poissonBinomialCoupling q) := by
  unfold poissonBinomialCoupling; infer_instance

/-- **A coupling of the Poisson binomial law with the Poisson law of the same mean**: the law of
the two sums has the margins `PoBin(q)` and `Po(∑ qᵢ)`, and the sums differ with probability at
most `∑ (qᵢ - qᵢ e^{-qᵢ})`. -/
theorem poissonBinomialCoupling_spec (q : Fin n → I) :
    (poissonBinomialCoupling q).map Prod.fst = poissonBinomial q ∧
      (poissonBinomialCoupling q).map Prod.snd = poissonMeasure (∑ i, (q i : ℝ)).toNNReal ∧
      (poissonBinomialCoupling q).real {z | z.1 ≠ z.2} ≤
        ∑ i, ((q i : ℝ) - q i * Real.exp (-q i)) := by
  refine ⟨map_fst_sumPairLaw _ fun i => map_fst_bernoulliPoissonCoupling (q i), ?_, ?_⟩
  · rw [poissonBinomialCoupling,
      map_snd_sumPairLaw _ fun i => map_snd_bernoulliPoissonCoupling (q i),
      Real.toNNReal_sum_of_nonneg fun i _ => (q i).2.1]
  · refine (measureReal_ne_sumPairLaw_le _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    exact (measureReal_ne_bernoulliPoissonCoupling (q i)).1

/-- **Le Cam's inequality on every set, with the exact coupling bound**: for every set `A` of
counts, `|PoBin(q)(A) - Po(∑ qᵢ)(A)| ≤ ∑ (qᵢ - qᵢ e^{-qᵢ})`. -/
theorem abs_measureReal_poissonBinomial_sub_poissonMeasure_le_sum_sub_mul_exp (q : Fin n → I)
    (A : Set ℕ) :
    |(poissonBinomial q).real A - (poissonMeasure (∑ i, (q i : ℝ)).toNNReal).real A| ≤
      ∑ i, ((q i : ℝ) - q i * Real.exp (-q i)) := by
  obtain ⟨h1, h2, h3⟩ := poissonBinomialCoupling_spec q
  exact (abs_measureReal_sub_le_coupling h1 h2 MeasurableSet.of_discrete).trans h3

/-- **Le Cam's inequality**: for every set `A` of counts,
`|PoBin(q)(A) - Po(∑ qᵢ)(A)| ≤ ∑ qᵢ²`. -/
theorem abs_measureReal_poissonBinomial_sub_poissonMeasure_le (q : Fin n → I) (A : Set ℕ) :
    |(poissonBinomial q).real A - (poissonMeasure (∑ i, (q i : ℝ)).toNNReal).real A| ≤
      ∑ i, (q i : ℝ) ^ 2 :=
  (abs_measureReal_poissonBinomial_sub_poissonMeasure_le_sum_sub_mul_exp q A).trans
    (Finset.sum_le_sum fun i _ => (measureReal_ne_bernoulliPoissonCoupling (q i)).2)

/-- **Le Cam's inequality in total variation**: `tvDist (PoBin(q)) (Po(∑ qᵢ)) ≤ 2 ∑ qᵢ²`, with
`tvDist` the total variation norm (twice the largest difference of set probabilities). -/
theorem tvDist_poissonBinomial_poissonMeasure_le (q : Fin n → I) :
    tvDist (poissonBinomial q) (poissonMeasure (∑ i, (q i : ℝ)).toNNReal) ≤
      2 * ∑ i, (q i : ℝ) ^ 2 :=
  tvDist_le_of_forall_abs_measureReal_sub_le fun A _ =>
    abs_measureReal_poissonBinomial_sub_poissonMeasure_le q A

/-- **The Poisson approximation of the binomial law**: for every set `A`,
`|Bin(n, θ)(A) - Po(n θ)(A)| ≤ n θ²`. -/
theorem abs_measureReal_binomial_sub_poissonMeasure_le (n : ℕ) (θ : I) (A : Set ℕ) :
    |(Bin(n, θ)).real A - (poissonMeasure (n * (θ : ℝ)).toNNReal).real A| ≤ n * (θ : ℝ) ^ 2 := by
  have h := abs_measureReal_poissonBinomial_sub_poissonMeasure_le (fun _ : Fin n => θ) A
  simpa [poissonBinomial_const] using h

/-- **The binomial law with risk `t / n` is within `t² / n` of `Po(t)` on every set**: for
`n > 0`, `0 ≤ t ≤ n` and every set `A`, `|Bin(n, t/n)(A) - Po(t)(A)| ≤ t² / n`. -/
theorem abs_measureReal_binomial_div_sub_poissonMeasure_le (hn : 0 < n) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ n) (A : Set ℕ) :
    |(Bin(n, ⟨t / n, div_nonneg h0 n.cast_nonneg, div_le_one_of_le₀ h1 n.cast_nonneg⟩)).real A -
      (poissonMeasure t.toNNReal).real A| ≤ t ^ 2 / n := by
  have h := abs_measureReal_binomial_sub_poissonMeasure_le n
    ⟨t / n, div_nonneg h0 n.cast_nonneg, div_le_one_of_le₀ h1 n.cast_nonneg⟩ A
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e1 : (n : ℝ) * (t / n) = t := by field_simp
  have e2 : (n : ℝ) * (t / n) ^ 2 = t ^ 2 / n := by field_simp
  simp only at h
  rwa [e1, e2] at h

/-- **The binomial law with risk `t / n` converges to `Po(t)` in total variation**: with the
risk `t / n` clipped to `[0, 1]` (it lies in `[0, 1]` once `n ≥ t`),
`tvDist (Bin(n, t/n)) (Po(t)) → 0` as `n → ∞`. -/
theorem tendsto_tvDist_binomial_poissonMeasure (t : ℝ≥0) :
    Tendsto (fun n : ℕ => tvDist (Bin(n, Set.projIcc 0 1 zero_le_one ((t : ℝ) / n)))
      (poissonMeasure t)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => 2 * (t : ℝ) ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => tvDist_nonneg) ?_
  filter_upwards [eventually_ge_atTop ⌈(t : ℝ)⌉₊, eventually_gt_atTop 0] with n hn hn0
  have h1 : (t : ℝ) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hp : Set.projIcc 0 1 zero_le_one ((t : ℝ) / n) =
      ⟨(t : ℝ) / n, div_nonneg t.2 n.cast_nonneg, div_le_one_of_le₀ h1 n.cast_nonneg⟩ :=
    Set.projIcc_of_mem _ _
  rw [hp]
  have h := tvDist_le_of_forall_abs_measureReal_sub_le (μ := Bin(n, _))
    (ν := poissonMeasure (t : ℝ).toNNReal)
    fun A _ => abs_measureReal_binomial_div_sub_poissonMeasure_le hn0 t.2 h1 A
  rw [Real.toNNReal_coe] at h
  rwa [mul_div_assoc]

end PoissonApproximation

end NetworkMetaRegression

end CausalInference
