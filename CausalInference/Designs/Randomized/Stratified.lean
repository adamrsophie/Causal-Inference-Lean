/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.Neyman
public import CausalInference.Designs.Randomized.Fisher

/-!
# Stratified (block) randomization

The units are partitioned into strata by a map `s : ι → σ`. Within every stratum `k` exactly
`n1 k` of its `N_k` units are treated by complete randomization, independently across strata.
We construct this design as the uniform design on the assignments with the prescribed number
of treated units in every stratum, compute its inclusion probabilities by symmetry, and show
that the stratified estimator `Σ_k (N_k / N) τ̂_k` is unbiased with variance
`Σ_k (N_k / N)² V_k`, where `V_k` is Neyman's variance within the stratum `k`. Sources:
Neyman (1923, translated 1990); Imbens and Rubin (2015), *Causal Inference for Statistics,
Social, and Biomedical Sciences*, chapter 9.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `stratum`, `stratumSize`, `numTreatedIn`: the units of a stratum, their number `N_k`, and the
  number of them treated by an assignment.
* `stratifiedSupport`, `stratifiedDesign`: stratified randomization as a `Design`.
* `PotentialOutcomes.stratumDiffInMeans`, `PotentialOutcomes.stratifiedEstimator`: the
  difference in means within a stratum and the stratified estimator.
* `PotentialOutcomes.restrict`: the potential outcomes of one stratum as a population.

## Main results

* `stratifiedSupport_nonempty`: the design is well defined when `n1 k ≤ N_k` for every `k`.
* `stratifiedDesign_inclusionProb`: unit `i` is treated with probability `n1 k / N_k`, where
  `k` is its stratum.
* `stratifiedDesign_pairInclusionProb_of_eq`, `stratifiedDesign_pairInclusionProb_of_ne`:
  second order inclusion probabilities within a stratum and, by independence, across strata.
* `stratified_estimator_unbiased`: the stratified estimator is unbiased for the average
  treatment effect.
* `stratified_estimator_variance`: its variance is `Σ_k (N_k / N)² V_k`.
* `stratifiedDesign_unit`, `stratifiedEstimator_unit`: with one stratum, the design is complete
  randomization and the estimator is the difference in means.
* `stratified_fisher_pValue_valid`: Fisher's randomization test is valid under this design.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- The stratum `{i | s i = k}` of the units mapped to `k` by the stratum map `s`. -/
def stratum (s : ι → σ) (k : σ) : Finset ι := {i | s i = k}

omit [DecidableEq ι] [Fintype σ] in
theorem mem_stratum {s : ι → σ} {k : σ} {i : ι} : i ∈ stratum s k ↔ s i = k := by
  simp [stratum]

/-- The number of units `N_k` in the stratum `k`. -/
def stratumSize (s : ι → σ) (k : σ) : ℕ := #(stratum s k)

/-- The number of units of the stratum `k` treated by the assignment `a`. -/
def numTreatedIn (s : ι → σ) (k : σ) (a : ι → Bool) : ℕ := #{i ∈ stratum s k | a i = true}

omit [DecidableEq ι] [Fintype σ] in
/-- The number of treated units in a stratum, as a real number, is the sum of the treatment
indicators over the stratum. -/
theorem numTreatedIn_eq_sum (s : ι → σ) (k : σ) (a : ι → Bool) :
    (numTreatedIn s k a : ℝ) = ∑ i ∈ stratum s k, treatInd a i := by
  rw [numTreatedIn, natCast_card_filter]
  rfl

omit [DecidableEq ι] [Fintype σ] in
/-- A permutation of the units that preserves every unit's stratum does not change the number
of treated units in any stratum. -/
theorem numTreatedIn_comp_perm (s : ι → σ) (k : σ) (a : ι → Bool) (e : Equiv.Perm ι)
    (he : ∀ i, s (e i) = s i) : numTreatedIn s k (a ∘ e) = numTreatedIn s k a := by
  have h : (numTreatedIn s k (a ∘ e) : ℝ) = numTreatedIn s k a := by
    simp only [numTreatedIn_eq_sum, stratum, sum_filter]
    have := Equiv.sum_comp e (fun i => if s i = k then treatInd a i else 0)
    simp only [he] at this
    exact this
  exact_mod_cast h

/-- The support of stratified randomization: the assignments treating exactly `n1 k` units of
every stratum `k`. -/
def stratifiedSupport (s : ι → σ) (n1 : σ → ℕ) : Finset (ι → Bool) :=
  {a | ∀ k, numTreatedIn s k a = n1 k}

theorem mem_stratifiedSupport {s : ι → σ} {n1 : σ → ℕ} {a : ι → Bool} :
    a ∈ stratifiedSupport s n1 ↔ ∀ k, numTreatedIn s k a = n1 k := by
  simp [stratifiedSupport]

/-- If no stratum is asked to treat more units than it has, some assignment treats exactly
`n1 k` units of every stratum `k`. -/
theorem stratifiedSupport_nonempty {s : ι → σ} {n1 : σ → ℕ}
    (h : ∀ k, n1 k ≤ stratumSize s k) : (stratifiedSupport s n1).Nonempty := by
  choose T hTsub hTcard using fun k => exists_subset_card_eq (h k)
  refine ⟨fun i => decide (i ∈ T (s i)), mem_stratifiedSupport.mpr fun k => ?_⟩
  rw [numTreatedIn, ← hTcard k]
  congr 1
  ext i
  simp only [mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hi, hT⟩
    rwa [mem_stratum.mp hi] at hT
  · intro hi
    have := mem_stratum.mp (hTsub k hi)
    exact ⟨mem_stratum.mpr this, this ▸ hi⟩

/-- Stratified randomization: within every stratum `k`, exactly `n1 k` of its `N_k` units are
treated, independently across strata. It is the uniform design on the assignments with the
prescribed number of treated units in every stratum; independence across strata is proved at
the level of inclusion probabilities in `stratifiedDesign_pairInclusionProb_of_ne`. -/
noncomputable def stratifiedDesign (s : ι → σ) (n1 : σ → ℕ) (h : ∀ k, n1 k ≤ stratumSize s k) :
    Design ι :=
  Design.uniform (stratifiedSupport s n1) (stratifiedSupport_nonempty h)

/-- Stratified randomization is invariant under every permutation of the units that preserves
the strata. -/
theorem stratifiedDesign_expect_comp_perm (s : ι → σ) (n1 : σ → ℕ)
    (h : ∀ k, n1 k ≤ stratumSize s k) (e : Equiv.Perm ι) (he : ∀ i, s (e i) = s i)
    (f : (ι → Bool) → ℝ) :
    (stratifiedDesign s n1 h).expect (fun a => f (a ∘ e)) = (stratifiedDesign s n1 h).expect f := by
  have he' : ∀ i, s (e.symm i) = s i := fun i => by
    simpa using (he (e.symm i)).symm
  simp only [stratifiedDesign, Design.uniform_expect]
  congr 1
  refine sum_nbij' (fun a => a ∘ e) (fun a => a ∘ e.symm) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    simpa [mem_stratifiedSupport, numTreatedIn_comp_perm s _ a e he] using ha
  · intro a ha
    simpa [mem_stratifiedSupport, numTreatedIn_comp_perm s _ a e.symm he'] using ha
  · intro a _
    funext i
    simp
  · intro a _
    funext i
    simp

omit [Fintype ι] [Fintype σ] [DecidableEq σ] in
/-- Swapping two units of the same stratum preserves every unit's stratum. -/
theorem stratum_swap {s : ι → σ} {i j : ι} (hij : s i = s j) (x : ι) :
    s (Equiv.swap i j x) = s x := by
  rcases eq_or_ne x i with rfl | hxi
  · simp [hij]
  rcases eq_or_ne x j with rfl | hxj
  · simp [hij]
  rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]

/-- Under stratified randomization a unit `i` is treated with probability `n1 k / N_k`, where `k`
is its stratum. -/
theorem stratifiedDesign_inclusionProb (s : ι → σ) (n1 : σ → ℕ)
    (h : ∀ k, n1 k ≤ stratumSize s k) (i : ι) :
    (stratifiedDesign s n1 h).inclusionProb i = n1 (s i) / stratumSize s (s i) := by
  set d := stratifiedDesign s n1 h
  have hsym : ∀ j ∈ stratum s (s i), d.inclusionProb j = d.inclusionProb i := by
    intro j hj
    have := stratifiedDesign_expect_comp_perm s n1 h (Equiv.swap i j)
      (stratum_swap (mem_stratum.mp hj).symm) (fun a => treatInd a i)
    simp only [Function.comp_def] at this
    unfold Design.inclusionProb
    rw [← this]
    refine d.expect_congr fun a _ => ?_
    simp [treatInd]
  have htot : ∑ j ∈ stratum s (s i), d.inclusionProb j = n1 (s i) := by
    unfold Design.inclusionProb
    rw [← d.expect_sum]
    rw [d.expect_congr (g := fun _ => (n1 (s i) : ℝ)) fun a ha => by
      rw [← numTreatedIn_eq_sum, mem_stratifiedSupport.mp ha]]
    exact d.expect_const _
  rw [sum_congr rfl hsym, sum_const, nsmul_eq_mul] at htot
  have hpos : (stratumSize s (s i) : ℝ) ≠ 0 := by
    have : 0 < stratumSize s (s i) := card_pos.mpr ⟨i, mem_stratum.mpr rfl⟩
    exact_mod_cast this.ne'
  rw [stratumSize] at hpos ⊢
  field_simp
  linarith

/-- Under stratified randomization two distinct units of the same stratum `k` are both treated
with probability `n1 k (n1 k - 1) / (N_k (N_k - 1))`. -/
theorem stratifiedDesign_pairInclusionProb_of_eq (s : ι → σ) (n1 : σ → ℕ)
    (h : ∀ k, n1 k ≤ stratumSize s k) {i j : ι} (hij : i ≠ j) (hs : s i = s j) :
    (stratifiedDesign s n1 h).pairInclusionProb i j =
      n1 (s i) * (n1 (s i) - 1) / (stratumSize s (s i) * (stratumSize s (s i) - 1)) := by
  set d := stratifiedDesign s n1 h
  set S := stratum s (s i) with hS
  have hiS : i ∈ S := mem_stratum.mpr rfl
  have hjS : j ∈ S := mem_stratum.mpr hs.symm
  have hsym : ∀ l ∈ S.erase i, d.pairInclusionProb i l = d.pairInclusionProb i j := by
    intro l hl
    have hli : l ≠ i := ne_of_mem_erase hl
    have hl' : s j = s l := hs.symm.trans (mem_stratum.mp (mem_of_mem_erase hl)).symm
    have := stratifiedDesign_expect_comp_perm s n1 h (Equiv.swap j l) (stratum_swap hl')
      (fun a => treatInd a i * treatInd a j)
    unfold Design.pairInclusionProb
    rw [← this]
    refine d.expect_congr fun a _ => ?_
    simp [treatInd, Equiv.swap_apply_of_ne_of_ne hij hli.symm]
  have htot : ∑ l ∈ S.erase i, d.pairInclusionProb i l = (n1 (s i) - 1) * d.inclusionProb i := by
    unfold Design.pairInclusionProb Design.inclusionProb
    rw [← d.expect_sum, ← d.expect_mul_left]
    refine d.expect_congr fun a ha => ?_
    rw [← mul_sum, sum_erase_eq_sub hiS, ← numTreatedIn_eq_sum, mem_stratifiedSupport.mp ha]
    unfold treatInd
    split_ifs <;> ring
  have hcard : 1 < #S := one_lt_card.mpr ⟨i, hiS, j, hjS, hij⟩
  rw [sum_congr rfl hsym, sum_const, card_erase_of_mem hiS, nsmul_eq_mul,
    stratifiedDesign_inclusionProb, Nat.cast_sub hcard.le, Nat.cast_one] at htot
  have h1 : (#S : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < #S := by exact_mod_cast hcard
    linarith
  have h2 : (#S : ℝ) ≠ 0 := by
    have : (0 : ℝ) < #S := by exact_mod_cast (by omega : 0 < #S)
    exact this.ne'
  rw [stratumSize, ← hS] at htot ⊢
  field_simp at htot ⊢
  linarith

/-- Under stratified randomization two units of different strata are treated independently:
the probability that both are treated is the product of their inclusion probabilities. -/
theorem stratifiedDesign_pairInclusionProb_of_ne (s : ι → σ) (n1 : σ → ℕ)
    (h : ∀ k, n1 k ≤ stratumSize s k) {i j : ι} (hs : s i ≠ s j) :
    (stratifiedDesign s n1 h).pairInclusionProb i j =
      (stratifiedDesign s n1 h).inclusionProb i * (stratifiedDesign s n1 h).inclusionProb j := by
  set d := stratifiedDesign s n1 h
  set S := stratum s (s j) with hS
  have hjS : j ∈ S := mem_stratum.mpr rfl
  have hij : i ≠ j := fun e => hs (e ▸ rfl)
  have hsym : ∀ l ∈ S, d.pairInclusionProb i l = d.pairInclusionProb i j := by
    intro l hl
    have hl' : s j = s l := (mem_stratum.mp hl).symm
    have hli : l ≠ i := fun e => hs (e ▸ hl'.symm)
    have := stratifiedDesign_expect_comp_perm s n1 h (Equiv.swap j l) (stratum_swap hl')
      (fun a => treatInd a i * treatInd a j)
    unfold Design.pairInclusionProb
    rw [← this]
    refine d.expect_congr fun a _ => ?_
    simp [treatInd, Equiv.swap_apply_of_ne_of_ne hij hli.symm]
  have htot : ∑ l ∈ S, d.pairInclusionProb i l = n1 (s j) * d.inclusionProb i := by
    unfold Design.pairInclusionProb Design.inclusionProb
    rw [← d.expect_sum, ← d.expect_mul_left]
    refine d.expect_congr fun a ha => ?_
    rw [← mul_sum, ← numTreatedIn_eq_sum, mem_stratifiedSupport.mp ha, mul_comm]
  rw [sum_congr rfl hsym, sum_const, nsmul_eq_mul] at htot
  have h2 : (#S : ℝ) ≠ 0 := by
    have : 0 < #S := card_pos.mpr ⟨j, hjS⟩
    exact_mod_cast this.ne'
  rw [stratifiedDesign_inclusionProb s n1 h j, stratumSize, ← hS]
  field_simp
  linarith

/-! ### The stratified estimator -/

namespace PotentialOutcomes

/-- The difference in means within the stratum `k`, with `n1` treated and `n0` control units
there: `(1/n1) Σ_{i ∈ k} A_i Y_i - (1/n0) Σ_{i ∈ k} (1 - A_i) Y_i`. -/
noncomputable def stratumDiffInMeans (po : PotentialOutcomes ι) (s : ι → σ) (k : σ) (n1 n0 : ℕ)
    (a : ι → Bool) : ℝ :=
  (n1 : ℝ)⁻¹ * ∑ i ∈ stratum s k, treatInd a i * po.observed a i -
    (n0 : ℝ)⁻¹ * ∑ i ∈ stratum s k, (1 - treatInd a i) * po.observed a i

/-- The stratified estimator `Σ_k (N_k / N) τ̂_k`, where `τ̂_k` is the difference in means within
the stratum `k`, with `n1 k` treated and `n0 k` control units there. -/
noncomputable def stratifiedEstimator (po : PotentialOutcomes ι) (s : ι → σ) (n1 n0 : σ → ℕ)
    (a : ι → Bool) : ℝ :=
  ∑ k, (stratumSize s k : ℝ) / Fintype.card ι * po.stratumDiffInMeans s k (n1 k) (n0 k) a

/-- The coefficient of the treatment indicator of unit `i` in the stratified estimator:
`(N_k / N) (y1 i / n1 k + y0 i / n0 k)`, where `k` is the stratum of `i`. -/
noncomputable def stratifiedWeight (po : PotentialOutcomes ι) (s : ι → σ) (n1 n0 : σ → ℕ)
    (i : ι) : ℝ :=
  (stratumSize s (s i) : ℝ) / Fintype.card ι * (po.y1 i / n1 (s i) + po.y0 i / n0 (s i))

omit [DecidableEq ι] in
/-- The stratified estimator is affine in the treatment indicators:
`τ̂ = -Σ_i (N_k / N) y0 i / n0 k + Σ_i A_i w_i`, with `w` the stratified weights. -/
theorem stratifiedEstimator_eq_linear (po : PotentialOutcomes ι) (s : ι → σ) (n1 n0 : σ → ℕ)
    (a : ι → Bool) :
    po.stratifiedEstimator s n1 n0 a =
      -∑ i, (stratumSize s (s i) : ℝ) / Fintype.card ι * (po.y0 i / n0 (s i)) +
        ∑ i, treatInd a i * po.stratifiedWeight s n1 n0 i := by
  set G : ι → ℝ := fun i => (stratumSize s (s i) : ℝ) / Fintype.card ι *
    (treatInd a i * (po.y1 i / n1 (s i) + po.y0 i / n0 (s i)) - po.y0 i / n0 (s i)) with hG
  have hk : ∀ k, (stratumSize s k : ℝ) / Fintype.card ι *
      po.stratumDiffInMeans s k (n1 k) (n0 k) a = ∑ i ∈ stratum s k, G i := by
    intro k
    simp only [stratumDiffInMeans, mul_sub, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    obtain rfl := mem_stratum.mp hi
    simp only [hG, treatInd, observed]
    split_ifs <;> ring
  rw [stratifiedEstimator, sum_congr rfl fun k _ => hk k]
  rw [show (∑ k, ∑ i ∈ stratum s k, G i) = ∑ i, G i from sum_fiberwise univ s G,
    ← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [hG, stratifiedWeight]
  ring

end PotentialOutcomes

/-- **Unbiasedness of the stratified estimator.** Under stratified randomization with `n1 k`
treated and `n0 k` control units in every stratum `k`, `n1 k + n0 k = N_k`, `n1 k, n0 k > 0`,
the stratified estimator `Σ_k (N_k / N) τ̂_k` is unbiased for the population average treatment
effect. The positivity hypotheses force every stratum to contain at least two units; strata
without units must not be listed in `σ`. -/
theorem stratified_estimator_unbiased (po : PotentialOutcomes ι) (s : ι → σ) {n1 n0 : σ → ℕ}
    (hn : ∀ k, n1 k + n0 k = stratumSize s k) (hn1 : ∀ k, 0 < n1 k) (hn0 : ∀ k, 0 < n0 k) :
    (stratifiedDesign s n1 (fun k => by have := hn k; omega)).expect
      (po.stratifiedEstimator s n1 n0) = po.ate := by
  set d := stratifiedDesign s n1 (fun k => by have := hn k; omega)
  rw [d.expect_congr fun a _ => po.stratifiedEstimator_eq_linear s n1 n0 a, d.expect_add,
    d.expect_const, d.expect_sum, PotentialOutcomes.ate, popMean, mul_sum, ← sum_neg_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [d.expect_congr (g := fun a => po.stratifiedWeight s n1 n0 i * treatInd a i)
      (fun _ _ => mul_comm _ _), d.expect_mul_left]
  change _ + _ * d.inclusionProb i = _
  rw [stratifiedDesign_inclusionProb]
  have hN : (stratumSize s (s i) : ℝ) = n1 (s i) + n0 (s i) := by
    rw [← hn (s i)]; push_cast; ring
  have h1 : (n1 (s i) : ℝ) ≠ 0 := by exact_mod_cast (hn1 (s i)).ne'
  have h0 : (n0 (s i) : ℝ) ≠ 0 := by exact_mod_cast (hn0 (s i)).ne'
  have hNi : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
  have hNk : (n1 (s i) : ℝ) + n0 (s i) ≠ 0 := by positivity
  simp only [PotentialOutcomes.stratifiedWeight, PotentialOutcomes.unitEffect, hN]
  field_simp
  ring

/-- The potential outcomes of the units of the stratum `k`, as a population of its own. -/
def PotentialOutcomes.restrict (po : PotentialOutcomes ι) (s : ι → σ) (k : σ) :
    PotentialOutcomes {i // s i = k} where
  y1 := fun i => po.y1 i
  y0 := fun i => po.y0 i

omit [DecidableEq ι] [Fintype σ] in
/-- The stratum `k`, viewed as a type, has `N_k` elements. -/
theorem card_stratum_subtype (s : ι → σ) (k : σ) :
    Fintype.card {i // s i = k} = stratumSize s k :=
  Fintype.card_subtype _

/-- **Variance of the stratified estimator.** Under stratified randomization with `n1 k` treated
and `n0 k` control units in every stratum `k`, `n1 k + n0 k = N_k`, `n1 k, n0 k > 0`, the
variance of the stratified estimator is `Σ_k (N_k / N)² V_k`, where
`V_k = S1k²/n1 k + S0k²/n0 k - Sτk²/N_k` is Neyman's variance of the difference in means within
the stratum `k`, computed from the potential outcomes of that stratum alone. -/
theorem stratified_estimator_variance (po : PotentialOutcomes ι) (s : ι → σ) {n1 n0 : σ → ℕ}
    (hn : ∀ k, n1 k + n0 k = stratumSize s k) (hn1 : ∀ k, 0 < n1 k) (hn0 : ∀ k, 0 < n0 k) :
    (stratifiedDesign s n1 (fun k => by have := hn k; omega)).variance
      (po.stratifiedEstimator s n1 n0) =
      ∑ k, ((stratumSize s k : ℝ) / Fintype.card ι) ^ 2 *
        ((po.restrict s k).varTreated / n1 k + (po.restrict s k).varControl / n0 k -
          (po.restrict s k).varEffect / stratumSize s k) := by
  set d := stratifiedDesign s n1 (fun k => by have := hn k; omega)
  set w := po.stratifiedWeight s n1 n0 with hw
  rw [d.variance_of_linear _ _ w fun a _ => po.stratifiedEstimator_eq_linear s n1 n0 a]
  set C : ι → ι → ℝ := fun i j =>
    (d.pairInclusionProb i j - d.inclusionProb i * d.inclusionProb j) * w i * w j with hC
  have hoff : ∀ i j, s i ≠ s j → C i j = 0 := by
    intro i j hij
    simp only [hC, d, stratifiedDesign_pairInclusionProb_of_ne s n1 _ hij, sub_self, zero_mul]
  have hrow : ∀ i, ∑ j, C i j = ∑ j ∈ stratum s (s i), C i j := fun i =>
    (sum_subset (subset_univ _) fun j _ hj => hoff i j fun e => hj (mem_stratum.mpr e.symm)).symm
  rw [sum_congr rfl fun i _ => hrow i,
    ← sum_fiberwise univ s (fun i => ∑ j ∈ stratum s (s i), C i j)]
  refine sum_congr rfl fun k _ => ?_
  rw [show (∑ i ∈ univ with s i = k, ∑ j ∈ stratum s (s i), C i j) =
      ∑ i ∈ stratum s k, ∑ j ∈ stratum s k, C i j from
    sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]]
  have hcard := card_stratum_subtype s k
  have hnk : n1 k + n0 k = Fintype.card {i // s i = k} := by rw [hcard]; exact hn k
  have hN1 : 1 < Fintype.card {i // s i = k} := by have := hn1 k; have := hn0 k; omega
  set w' : {i // s i = k} → ℝ := fun i => (po.restrict s k).y1 i / n1 k +
    (po.restrict s k).y0 i / n0 k with hw'
  have hV := neyman_variance (po.restrict s k) hnk (hn1 k) (hn0 k)
  rw [Design.variance_of_linear _ _ _ w' fun a _ => (po.restrict s k).diffInMeans_eq_linear _ _ a,
    hcard] at hV
  rw [← hV, sum_subtype (stratum s k) (fun _ => mem_stratum), mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_subtype (stratum s k) (fun _ => mem_stratum), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hπC : ∀ x, (completeDesign (ι := {i // s i = k}) (n1 k) (by omega)).inclusionProb x =
      n1 k / stratumSize s k := fun x => by
    rw [completeDesign_inclusionProb _ _ (by omega), hcard]
  have hπS : ∀ x : {i // s i = k}, d.inclusionProb x = n1 k / stratumSize s k := fun x => by
    rw [stratifiedDesign_inclusionProb, x.2]
  have hwx : ∀ x : {i // s i = k}, w x = stratumSize s k / Fintype.card ι * w' x := fun x => by
    simp only [hw, hw', PotentialOutcomes.stratifiedWeight, x.2]
    rfl
  simp only [hC, hwx]
  by_cases hij : i = j
  · subst hij
    rw [d.pairInclusionProb_self, Design.pairInclusionProb_self, hπC, hπS]
    ring
  · have hij' : (i : ι) ≠ j := fun e => hij (Subtype.ext e)
    rw [stratifiedDesign_pairInclusionProb_of_eq s n1 _ hij' (i.2.trans j.2.symm),
      completeDesign_pairInclusionProb _ _ hN1 hij, hπC, hπC, hπS, hπS, hcard, i.2]
    ring

/-! ### One stratum and the Fisher test -/

omit [DecidableEq ι] in
/-- With a single stratum, the stratum is the whole population. -/
theorem stratum_unit (s : ι → Unit) : stratum s () = univ := by
  ext i
  simp [mem_stratum]

/-- **One stratum is complete randomization.** With a single stratum, stratified randomization
treating `n1` units is the complete randomization treating `n1` units. -/
theorem stratifiedDesign_unit (s : ι → Unit) (n1 : Unit → ℕ) (h : ∀ k, n1 k ≤ stratumSize s k) :
    stratifiedDesign s n1 h =
      completeDesign (n1 ()) (by simpa [stratumSize, stratum_unit] using h ()) := by
  have hS : stratifiedSupport s n1 = completeSupport (n1 ()) := by
    ext a
    have hk : ∀ k : Unit, numTreatedIn s k a = numTreated a := fun k => by
      cases k
      simp [numTreatedIn, numTreated, stratum_unit]
    rw [mem_stratifiedSupport, mem_completeSupport]
    simp only [hk]
    exact ⟨fun H => H (), fun H _ => H⟩
  unfold stratifiedDesign completeDesign
  congr 1

omit [DecidableEq ι] in
/-- With a single stratum, the stratified estimator is the difference in means. -/
theorem stratifiedEstimator_unit (po : PotentialOutcomes ι) (s : ι → Unit) (n1 n0 : Unit → ℕ)
    (hN : 0 < Fintype.card ι) (a : ι → Bool) :
    po.stratifiedEstimator s n1 n0 a = po.diffInMeans (n1 ()) (n0 ()) a := by
  have hN' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [PotentialOutcomes.stratifiedEstimator, PotentialOutcomes.stratumDiffInMeans,
    PotentialOutcomes.diffInMeans, stratumSize, stratum_unit, hN']

/-- **Fisher's test under stratified randomization.** Under the sharp null the Fisher
randomization p-value computed with the stratified design is valid. -/
theorem stratified_fisher_pValue_valid (po : PotentialOutcomes ι) (hnull : po.SharpNull)
    (s : ι → σ) (n1 : σ → ℕ) (h : ∀ k, n1 k ≤ stratumSize s k) (T : (ι → Bool) → (ι → ℝ) → ℝ)
    {α : ℝ} (hα : 0 ≤ α) :
    (stratifiedDesign s n1 h).prob
      (fun a => (stratifiedDesign s n1 h).fisherPValue T (po.observed a) a ≤ α) ≤ α :=
  fisher_pValue_valid po hnull _ T hα

end CausalInference.Randomized
