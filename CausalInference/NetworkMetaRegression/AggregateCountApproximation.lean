/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountBinomial
public import CausalInference.Estimation.PosteriorLimitTotalVariation

/-!
# Approximating the aggregate binary count

The total variation distance is Mathlib's `MeasureTheory.tvDist`, the total variation norm of
`μ - ν`. For probability laws the largest difference of set probabilities is half of it.

* **Total variation and set probabilities** (`exists_measureReal_sub_eq_half_tvDist`,
  `tvDist_le_of_forall_abs_measureReal_sub_le`): for probability laws some measurable set
  attains `μ A - ν A = tvDist μ ν / 2`, so `sup_A |μ A - ν A| = tvDist μ ν / 2`.
* **The coupling inequality** (`abs_measureReal_sub_le_coupling`, `tvDist_le_coupling`): if
  `π` is a law on pairs with margins `μ` and `ν`, then `|μ A - ν A| ≤ π(X ≠ Y)` and
  `tvDist μ ν ≤ 2 π(X ≠ Y)`.
* **The adjusted binomial law** (`adjustedBinomial_moments`, `adjustedBinomial_unique`,
  `le_adjustedProb`, `adjustedSize_le`): a Poisson binomial law with risks `q` of mean `p̄` and
  spread `s² = (1/n) ∑ (qᵢ - p̄)²` has the mean `n p̄` and the variance `n p̄ (1 - p̄) - n s²`.
  For `p̄ > 0` the unique real pair `(N*, π*)` with `N* π* = n p̄` and
  `N* π* (1 - π*) = n p̄ (1 - p̄) - n s²` is `π* = (p̄² + s²) / p̄`, `N* = n p̄² / (p̄² + s²)`;
  `π* ≥ p̄` and `N* ≤ n`, each with equality exactly when all risks are equal; `π* < 1` when
  `s² < p̄ (1 - p̄)`.
* **Integer and noninteger size** (`binomial_adjusted_moments`,
  `not_exists_binomial_of_adjustedSize`): when `N*` is a natural number the binomial law
  `Bin(N*, π*)` has the mean and variance of the Poisson binomial law; when it is not, no
  binomial law `Bin(m, θ)` has both.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal NNReal

namespace CausalInference

namespace NetworkMetaRegression

/-! ### Total variation and set probabilities -/

section TotalVariation

variable {E : Type*} [MeasurableSpace E] {μ ν : Measure E}

/-- **Half the total variation distance is attained by a set**: for probability laws there is a
measurable `A` with `μ A - ν A = tvDist μ ν / 2`. -/
theorem exists_measureReal_sub_eq_half_tvDist [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ A, MeasurableSet A ∧ μ.real A - ν.real A = tvDist μ ν / 2 := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  obtain ⟨he, -, -⟩ := PosteriorLimit.tvDist_eq_of_isHahnDecomposition h
  refine ⟨sᶜ, h.measurableSet.compl, ?_⟩
  have cμ := probReal_compl_eq_one_sub (μ := μ) h.measurableSet
  have cν := probReal_compl_eq_one_sub (μ := ν) h.measurableSet
  rw [he]
  linarith

/-- **A uniform bound on set probabilities bounds the total variation distance**: for
probability laws, if `|μ A - ν A| ≤ c` for every measurable `A` then `tvDist μ ν ≤ 2 c`. -/
theorem tvDist_le_of_forall_abs_measureReal_sub_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ} (h : ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ c) :
    tvDist μ ν ≤ 2 * c := by
  obtain ⟨A, hA, he⟩ := exists_measureReal_sub_eq_half_tvDist (μ := μ) (ν := ν)
  have := (le_abs_self _).trans (h A hA)
  linarith

/-- **The coupling inequality**: if `π` is a finite law on pairs with margins `μ` and `ν`, then
for every measurable `A`, `|μ A - ν A| ≤ π(X ≠ Y)`. -/
theorem abs_measureReal_sub_le_coupling {π : Measure (E × E)} [IsFiniteMeasure π]
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) {A : Set E} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ π.real {p | p.1 ≠ p.2} := by
  rw [← h1, ← h2, map_measureReal_apply measurable_fst hA,
    map_measureReal_apply measurable_snd hA]
  have hf : MeasurableSet (Prod.fst ⁻¹' A : Set (E × E)) := measurable_fst hA
  have hs : MeasurableSet (Prod.snd ⁻¹' A : Set (E × E)) := measurable_snd hA
  have k1 : π.real (Prod.fst ⁻¹' A) ≤ π.real (Prod.snd ⁻¹' A) + π.real {p | p.1 ≠ p.2} := by
    refine (measureReal_mono fun p hp => ?_).trans (measureReal_union_le _ _)
    by_cases e : p.1 = p.2
    · exact Or.inl (by simpa [e] using hp)
    · exact Or.inr e
  have k2 : π.real (Prod.snd ⁻¹' A) ≤ π.real (Prod.fst ⁻¹' A) + π.real {p | p.1 ≠ p.2} := by
    refine (measureReal_mono fun p hp => ?_).trans (measureReal_union_le _ _)
    by_cases e : p.1 = p.2
    · exact Or.inl (by simpa [← e] using hp)
    · exact Or.inr e
  rw [abs_le]
  constructor <;> linarith

/-- **The coupling inequality for the total variation distance**: for a probability law `π` on
pairs with margins `μ` and `ν`, `tvDist μ ν ≤ 2 π(X ≠ Y)`. -/
theorem tvDist_le_coupling {π : Measure (E × E)} [IsProbabilityMeasure π]
    (h1 : π.map Prod.fst = μ) (h2 : π.map Prod.snd = ν) :
    tvDist μ ν ≤ 2 * π.real {p | p.1 ≠ p.2} := by
  have : IsProbabilityMeasure μ := h1 ▸ inferInstance
  have : IsProbabilityMeasure ν := h2 ▸ inferInstance
  exact tvDist_le_of_forall_abs_measureReal_sub_le fun A hA =>
    abs_measureReal_sub_le_coupling h1 h2 hA

end TotalVariation

/-! ### The adjusted binomial law -/

section Adjusted

variable {n : ℕ}

/-- The mean risk `p̄ = (1/n) ∑ qᵢ`. -/
noncomputable def meanRisk (q : Fin n → ℝ) : ℝ := (∑ i, q i) / n

/-- The spread of the risks, `s² = (1/n) ∑ (qᵢ - p̄)²`. -/
noncomputable def riskSpread (q : Fin n → ℝ) : ℝ := (∑ i, (q i - meanRisk q) ^ 2) / n

/-- The adjusted probability `π* = (p̄² + s²) / p̄`. -/
noncomputable def adjustedProb (q : Fin n → ℝ) : ℝ :=
  (meanRisk q ^ 2 + riskSpread q) / meanRisk q

/-- The adjusted size `N* = n p̄² / (p̄² + s²)`. -/
noncomputable def adjustedSize (q : Fin n → ℝ) : ℝ :=
  n * meanRisk q ^ 2 / (meanRisk q ^ 2 + riskSpread q)

theorem riskSpread_nonneg (q : Fin n → ℝ) : 0 ≤ riskSpread q :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg n)

/-- The sum of squares of the risks is `n (p̄² + s²)`. -/
theorem sum_sq_eq_meanRisk_riskSpread (q : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, q i ^ 2 = n * (meanRisk q ^ 2 + riskSpread q) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ∑ i, q i = n * meanRisk q := by rw [meanRisk]; field_simp
  have e : ∑ i, (q i - meanRisk q) ^ 2 =
      ∑ i, q i ^ 2 - 2 * meanRisk q * ∑ i, q i + n * meanRisk q ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    ring_nf
    congr 2
    exact funext fun x => by ring
  rw [riskSpread, e, hs]
  field_simp
  ring

/-- **The moments of the Poisson binomial law in terms of `p̄` and `s²`**: mean `n p̄` and
variance `n p̄ (1 - p̄) - n s²`. -/
theorem adjustedBinomial_moments (q : Fin n → I) (hn : 0 < n) :
    ∫ k, (k : ℝ) ∂poissonBinomial q = n * meanRisk (fun i => (q i : ℝ)) ∧
      variance (fun k : ℕ => (k : ℝ)) (poissonBinomial q) =
        n * meanRisk (fun i => (q i : ℝ)) * (1 - meanRisk (fun i => (q i : ℝ))) -
          n * riskSpread (fun i => (q i : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨hE, hV⟩ := integral_variance_poissonBinomial q
  have hsq := sum_sq_eq_meanRisk_riskSpread (fun i => (q i : ℝ)) hn
  have hs : ∑ i, (q i : ℝ) = n * meanRisk (fun i => (q i : ℝ)) := by
    rw [meanRisk]; field_simp
  refine ⟨by rw [hE, hs], ?_⟩
  rw [hV]
  have : ∑ i, (q i : ℝ) * (1 - q i) = ∑ i, (q i : ℝ) - ∑ i, (q i : ℝ) ^ 2 := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, hsq, hs]
  ring

/-- **The adjusted pair solves the moment equations**: for `p̄ > 0`,
`N* π* = n p̄` and `N* π* (1 - π*) = n p̄ (1 - p̄) - n s²`. -/
theorem adjustedBinomial_solution (q : Fin n → ℝ) (hp : 0 < meanRisk q) :
    adjustedSize q * adjustedProb q = n * meanRisk q ∧
      adjustedSize q * adjustedProb q * (1 - adjustedProb q) =
        n * meanRisk q * (1 - meanRisk q) - n * riskSpread q := by
  have hd : 0 < meanRisk q ^ 2 + riskSpread q := by
    have := riskSpread_nonneg q; positivity
  have h1 : adjustedSize q * adjustedProb q = n * meanRisk q := by
    rw [adjustedSize, adjustedProb]; field_simp
  refine ⟨h1, ?_⟩
  rw [h1, adjustedProb]
  field_simp
  ring

/-- **Uniqueness of the adjusted pair**: for `p̄ > 0`, the real pair `(N, π)` with `N π = n p̄`
and `N π (1 - π) = n p̄ (1 - p̄) - n s²` is `(N*, π*)`. -/
theorem adjustedBinomial_unique (q : Fin n → ℝ) (hn : 0 < n) (hp : 0 < meanRisk q) {N π : ℝ}
    (h1 : N * π = n * meanRisk q)
    (h2 : N * π * (1 - π) = n * meanRisk q * (1 - meanRisk q) - n * riskSpread q) :
    π = adjustedProb q ∧ N = adjustedSize q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : n * meanRisk q ≠ 0 := (mul_pos hn' hp).ne'
  have hπ : π = adjustedProb q := by
    rw [h1] at h2
    rw [adjustedProb, eq_div_iff hp.ne']
    have h3 : (n : ℝ) * (meanRisk q * π - (meanRisk q ^ 2 + riskSpread q)) = 0 := by
      linear_combination -h2
    have := (mul_eq_zero.mp h3).resolve_left hn'.ne'
    linarith
  refine ⟨hπ, ?_⟩
  have hπ0 : adjustedProb q ≠ 0 := by
    have := riskSpread_nonneg q
    rw [adjustedProb]; positivity
  have := (adjustedBinomial_solution q hp).1
  rw [hπ] at h1
  exact mul_right_cancel₀ hπ0 (h1.trans this.symm)

/-- **The adjusted probability is at least the mean risk**: `π* ≥ p̄`, with equality exactly when
all risks are equal. -/
theorem le_adjustedProb (q : Fin n → ℝ) (hn : 0 < n) (hp : 0 < meanRisk q) :
    meanRisk q ≤ adjustedProb q ∧ (adjustedProb q = meanRisk q ↔ ∀ i j, q i = q j) := by
  have hs := riskSpread_nonneg q
  have e : adjustedProb q = meanRisk q + riskSpread q / meanRisk q := by
    rw [adjustedProb]; field_simp
  have hz : riskSpread q = 0 ↔ ∀ i j, q i = q j := spread_eq_zero_iff q hn
  refine ⟨by rw [e]; exact le_add_of_nonneg_right (div_nonneg hs hp.le), ?_⟩
  rw [e, add_eq_left, div_eq_zero_iff, or_iff_left hp.ne', hz]
where
  spread_eq_zero_iff (q : Fin n → ℝ) (hn : 0 < n) : riskSpread q = 0 ↔ ∀ i j, q i = q j := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [riskSpread, div_eq_zero_iff, or_iff_left hn',
      Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
    simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    refine ⟨fun h i j => (h i).trans (h j).symm, fun h i => ?_⟩
    rw [meanRisk, eq_div_iff hn', Finset.sum_congr rfl fun j _ => h j i]
    simp [mul_comm]

/-- **The adjusted size is at most the arm size**: `N* ≤ n`, with equality exactly when all
risks are equal. -/
theorem adjustedSize_le (q : Fin n → ℝ) (hn : 0 < n) (hp : 0 < meanRisk q) :
    adjustedSize q ≤ n ∧ (adjustedSize q = n ↔ ∀ i j, q i = q j) := by
  have hs := riskSpread_nonneg q
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < meanRisk q ^ 2 + riskSpread q := by positivity
  refine ⟨?_, ?_⟩
  · rw [adjustedSize, div_le_iff₀ hd]; nlinarith
  · rw [adjustedSize, div_eq_iff hd.ne', ← le_adjustedProb.spread_eq_zero_iff q hn]
    constructor
    · intro h
      have : (n : ℝ) * riskSpread q = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hn'.ne'
    · intro h; rw [h]; ring

/-- The adjusted probability is below `1` when `s² < p̄ (1 - p̄)`. -/
theorem adjustedProb_lt_one (q : Fin n → ℝ) (hp : 0 < meanRisk q)
    (hs : riskSpread q < meanRisk q * (1 - meanRisk q)) : adjustedProb q < 1 := by
  rw [adjustedProb, div_lt_one hp]
  nlinarith

/-- **An integer adjusted size**: when `N* = m` is a natural number and `0 ≤ π* ≤ 1`, the binomial
law `Bin(m, π*)` has the mean and the variance of the Poisson binomial law. -/
theorem binomial_adjusted_moments (q : Fin n → I) (hn : 0 < n)
    (hp : 0 < meanRisk (fun i => (q i : ℝ))) {m : ℕ} (hm : adjustedSize (fun i => (q i : ℝ)) = m)
    (θ : I) (hθ : (θ : ℝ) = adjustedProb fun i => (q i : ℝ)) :
    ∫ k, (k : ℝ) ∂Bin(m, θ) = ∫ k, (k : ℝ) ∂poissonBinomial q ∧
      variance (fun k : ℕ => (k : ℝ)) (Bin(m, θ)) =
        variance (fun k : ℕ => (k : ℝ)) (poissonBinomial q) := by
  obtain ⟨hE, hV⟩ := adjustedBinomial_moments q hn
  obtain ⟨s1, s2⟩ := adjustedBinomial_solution (fun i => (q i : ℝ)) hp
  rw [hm] at s1 s2
  rw [integral_binomial_id, variance_binomial, hE, hV, hθ, ← s2]
  exact ⟨s1, rfl⟩

/-- **A noninteger adjusted size**: when `N*` is not a natural number, no binomial law
`Bin(m, θ)` has both the mean and the variance of the Poisson binomial law. -/
theorem not_exists_binomial_of_adjustedSize (q : Fin n → I) (hn : 0 < n)
    (hp : 0 < meanRisk (fun i => (q i : ℝ)))
    (hN : ∀ m : ℕ, adjustedSize (fun i => (q i : ℝ)) ≠ m) :
    ¬ ∃ (m : ℕ) (θ : I), ∫ k, (k : ℝ) ∂Bin(m, θ) = ∫ k, (k : ℝ) ∂poissonBinomial q ∧
      variance (fun k : ℕ => (k : ℝ)) (Bin(m, θ)) =
        variance (fun k : ℕ => (k : ℝ)) (poissonBinomial q) := by
  rintro ⟨m, θ, h1, h2⟩
  obtain ⟨hE, hV⟩ := adjustedBinomial_moments q hn
  rw [integral_binomial_id, hE] at h1
  rw [variance_binomial, hV] at h2
  refine hN m (adjustedBinomial_unique _ hn hp (N := m) (π := θ) h1 ?_).2.symm
  rw [← h2]

end Adjusted

end NetworkMetaRegression

end CausalInference
