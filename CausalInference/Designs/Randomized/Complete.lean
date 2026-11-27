/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.FinitePopulation
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Fintype

/-!
# Complete randomization

Exactly `n1` of the `N` units are treated, and the treated set is drawn uniformly among the
`N choose n1` possibilities. We compute the first and second order inclusion probabilities by a
symmetry argument and show that the difference in means is unbiased for the finite-population
average treatment effect. Source: Neyman (1923, translated 1990); Imbens and Rubin (2015),
*Causal Inference for Statistics, Social, and Biomedical Sciences*.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `numTreated`: the number of treated units of an assignment.
* `completeSupport`: the assignments treating exactly `n1` units.
* `completeDesign`: the uniform design on `completeSupport n1`.
* `PotentialOutcomes.diffInMeans`: the fixed-denominator difference in means, with the arm
  sizes supplied from outside.
* `PotentialOutcomes.diffInMeansObs`: the observed difference in means, with the realized arm
  counts as denominators.

## Main results

* `card_completeSupport`: there are `N choose n1` such assignments.
* `completeDesign_inclusionProb`: each unit is treated with probability
  `n1 / N`.
* `completeDesign_pairInclusionProb`: two distinct units are both treated with
  probability `n1 (n1 - 1) / (N (N - 1))`.
* `complete_diffInMeans_unbiased`: the fixed-denominator difference in means is unbiased.
* `PotentialOutcomes.diffInMeansObs_eq_diffInMeans`: on the support of complete
  randomization the two statistics agree.
* `complete_diffInMeansObs_unbiased`: the observed difference in means is unbiased.
* `Design.inclusionProb_perm`, `Design.pairInclusionProb_perm`,
  `Design.inclusionProb_of_perm_invariant`: inclusion probabilities of designs invariant
  under relabeling the units.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of units treated by the assignment `a`. -/
def numTreated (a : ι → Bool) : ℕ := #{i | a i = true}

omit [DecidableEq ι] in
/-- The number of treated units, as a real number, is the sum of the treatment indicators. -/
theorem numTreated_eq_sum (a : ι → Bool) : (numTreated a : ℝ) = ∑ i, treatInd a i := by
  rw [numTreated, natCast_card_filter]
  rfl

omit [DecidableEq ι] in
/-- Permuting the units does not change the number of treated units. -/
theorem numTreated_comp_perm (a : ι → Bool) (σ : Equiv.Perm ι) :
    numTreated (a ∘ σ) = numTreated a := by
  have h : (numTreated (a ∘ σ) : ℝ) = numTreated a := by
    simp only [numTreated_eq_sum]
    exact Equiv.sum_comp σ (fun i => treatInd a i)
  exact_mod_cast h

/-- The support of complete randomization: the assignments treating exactly `n1` units. -/
def completeSupport (n1 : ℕ) : Finset (ι → Bool) := {a | numTreated a = n1}

theorem mem_completeSupport {n1 : ℕ} {a : ι → Bool} :
    a ∈ completeSupport n1 ↔ numTreated a = n1 := by
  simp [completeSupport]

/-- The assignments treating exactly `n1` units correspond to the `n1`-element subsets of the
population, so there are `N choose n1` of them. -/
theorem card_completeSupport (n1 : ℕ) :
    #(completeSupport (ι := ι) n1) = (Fintype.card ι).choose n1 := by
  rw [← card_univ, ← card_powersetCard]
  refine card_nbij' (fun a => ({i | a i = true} : Finset ι)) (fun s i => decide (i ∈ s)) ?_ ?_ ?_ ?_
  · intro a ha
    simpa [mem_completeSupport, numTreated] using ha
  · intro s hs
    simp only [mem_coe, mem_powersetCard] at hs
    simp [mem_completeSupport, numTreated, hs.2]
  · intro a _
    funext i
    simp
  · intro s _
    ext i
    simp

theorem completeSupport_nonempty {n1 : ℕ} (h : n1 ≤ Fintype.card ι) :
    (completeSupport (ι := ι) n1).Nonempty := by
  rw [← card_pos, card_completeSupport]
  exact Nat.choose_pos h

/-- Complete randomization: the uniform design on the assignments treating exactly `n1` of the
`N` units, for `n1 ≤ N`. -/
noncomputable def completeDesign (n1 : ℕ) (h : n1 ≤ Fintype.card ι) : Design ι :=
  Design.uniform (completeSupport n1) (completeSupport_nonempty h)

/-- Complete randomization is invariant under relabeling the units: the expectation of
`a ↦ f (a ∘ σ)` equals that of `f` for every permutation `σ`. -/
theorem completeDesign_expect_comp_perm (n1 : ℕ) (h : n1 ≤ Fintype.card ι)
    (σ : Equiv.Perm ι) (f : (ι → Bool) → ℝ) :
    (completeDesign n1 h).expect (fun a => f (a ∘ σ)) = (completeDesign n1 h).expect f := by
  simp only [completeDesign, Design.uniform_expect]
  congr 1
  refine sum_nbij' (fun a => a ∘ σ) (fun a => a ∘ σ.symm) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    simpa [mem_completeSupport, numTreated_comp_perm] using ha
  · intro a ha
    simpa [mem_completeSupport, numTreated_comp_perm] using ha
  · intro a _
    funext i
    simp
  · intro a _
    funext i
    simp

/-- Under complete randomization every unit is treated with probability `n1 / N`. -/
theorem completeDesign_inclusionProb (n1 : ℕ) (h : n1 ≤ Fintype.card ι)
    (hN : 0 < Fintype.card ι) (i : ι) :
    (completeDesign n1 h).inclusionProb i = n1 / Fintype.card ι := by
  set d := completeDesign n1 h
  have hsym : ∀ j, d.inclusionProb j = d.inclusionProb i := by
    intro j
    have := completeDesign_expect_comp_perm n1 h (Equiv.swap i j) (fun a => treatInd a i)
    simp only [Function.comp_def] at this
    unfold Design.inclusionProb
    rw [← this]
    refine d.expect_congr fun a _ => ?_
    simp [treatInd]
  have htot : ∑ j, d.inclusionProb j = n1 := by
    unfold Design.inclusionProb
    rw [← d.expect_sum]
    rw [d.expect_congr (g := fun _ => (n1 : ℝ)) fun a ha => by
      rw [← numTreated_eq_sum, mem_completeSupport.mp ha]]
    exact d.expect_const _
  rw [sum_congr rfl fun j _ => hsym j, sum_const, card_univ, nsmul_eq_mul] at htot
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  linarith

/-- Under complete randomization two distinct units are both treated with probability
`n1 (n1 - 1) / (N (N - 1))`. -/
theorem completeDesign_pairInclusionProb (n1 : ℕ) (h : n1 ≤ Fintype.card ι)
    (hN : 1 < Fintype.card ι) {i j : ι} (hij : i ≠ j) :
    (completeDesign n1 h).pairInclusionProb i j =
      n1 * (n1 - 1) / (Fintype.card ι * (Fintype.card ι - 1)) := by
  set d := completeDesign n1 h
  have hsym : ∀ l ∈ univ.erase i, d.pairInclusionProb i l = d.pairInclusionProb i j := by
    intro l hl
    have hli : l ≠ i := ne_of_mem_erase hl
    have := completeDesign_expect_comp_perm n1 h (Equiv.swap j l)
      (fun a => treatInd a i * treatInd a j)
    unfold Design.pairInclusionProb
    rw [← this]
    refine d.expect_congr fun a _ => ?_
    simp [treatInd, Equiv.swap_apply_of_ne_of_ne hij hli.symm]
  have htot : ∑ l ∈ univ.erase i, d.pairInclusionProb i l = (n1 - 1) * d.inclusionProb i := by
    unfold Design.pairInclusionProb Design.inclusionProb
    rw [← d.expect_sum, ← d.expect_mul_left]
    refine d.expect_congr fun a ha => ?_
    rw [← mul_sum, sum_erase_eq_sub (mem_univ i), ← numTreated_eq_sum,
      mem_completeSupport.mp ha]
    unfold treatInd
    split_ifs <;> ring
  have hN0 : 0 < Fintype.card ι := by omega
  rw [sum_congr rfl hsym, sum_const, card_erase_of_mem (mem_univ i), card_univ, nsmul_eq_mul,
    completeDesign_inclusionProb n1 h hN0, Nat.cast_sub hN.le, Nat.cast_one] at htot
  have h1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hN
    linarith
  have h2 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  field_simp at htot ⊢
  exact htot

/-- The fixed-denominator difference in means `(1/n1) Σ_i A_i Y_i - (1/n0) Σ_i (1 - A_i) Y_i`,
with the counts `n1` and `n0` supplied from outside. It is the difference between the average
observed outcomes of the treated and the control units only for assignments that treat exactly
`n1` units, with `n1 + n0 = N` (see `diffInMeansObs_eq_diffInMeans`); for other assignments it
is a different statistic. The observed statistic computed from the realized arm counts is
`PotentialOutcomes.diffInMeansObs`. -/
noncomputable def PotentialOutcomes.diffInMeans (po : PotentialOutcomes ι) (n1 n0 : ℕ)
    (a : ι → Bool) : ℝ :=
  (n1 : ℝ)⁻¹ * ∑ i, treatInd a i * po.observed a i -
    (n0 : ℝ)⁻¹ * ∑ i, (1 - treatInd a i) * po.observed a i

omit [DecidableEq ι] in
/-- A fixed-denominator identity: with `n1 + n0 = N` and both positive, the fixed-denominator
expression `diffInMeans n1 n0` coincides, for every assignment, with the Horvitz-Thompson
estimator using the treatment probability `n1 / N`. For an assignment that does not treat
exactly `n1` units neither side is the observed difference in means. -/
theorem PotentialOutcomes.diffInMeans_eq_htEstimator (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) (a : ι → Bool) :
    po.diffInMeans n1 n0 a = po.htEstimator (n1 / Fintype.card ι) a := by
  have hN : (Fintype.card ι : ℝ) = n1 + n0 := by rw [← hn]; push_cast; ring
  have h1 : (n1 : ℝ) ≠ 0 := by exact_mod_cast hn1.ne'
  have h0 : (n0 : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hN0 : (n1 : ℝ) + n0 ≠ 0 := by positivity
  unfold diffInMeans htEstimator
  rw [hN, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  have : 1 - (n1 : ℝ) / (n1 + n0) = n0 / (n1 + n0) := by field_simp; ring
  rw [this]
  field_simp

/-- **Unbiasedness of the difference in means under complete randomization.** If exactly `n1`
of the `N = n1 + n0` units are treated, uniformly at random, with `n1, n0 > 0`, then the
difference in means is unbiased for the finite-population average treatment effect. -/
theorem complete_diffInMeans_unbiased (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).expect (po.diffInMeans n1 n0) = po.ate := by
  have hN : 0 < Fintype.card ι := by omega
  have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have : Nonempty ι := Fintype.card_pos_iff.mp hN
  rw [show po.diffInMeans n1 n0 = _ from funext (po.diffInMeans_eq_htEstimator hn hn1 hn0)]
  refine po.htEstimator_unbiased _ _ (by positivity) ?_
    (completeDesign_inclusionProb n1 (by omega) hN)
  rw [div_lt_one hNr]
  exact_mod_cast (by omega : n1 < Fintype.card ι)

/-- The observed difference in means: the average observed outcome among the units actually
treated by `a` minus that among the units actually left as controls, with the realized arm
counts `numTreated a` and `N - numTreated a` as denominators. It is a difference of arm means
when both arms are nonempty, which holds on the support of complete randomization with
`0 < n1 < N`. -/
noncomputable def PotentialOutcomes.diffInMeansObs (po : PotentialOutcomes ι) (a : ι → Bool) :
    ℝ :=
  (numTreated a : ℝ)⁻¹ * ∑ i, treatInd a i * po.observed a i -
    ((Fintype.card ι - numTreated a : ℕ) : ℝ)⁻¹ * ∑ i, (1 - treatInd a i) * po.observed a i

/-- On the support of complete randomization with `n1` treated, `n1 + n0 = N`, the observed
difference in means equals the fixed-denominator expression `diffInMeans n1 n0`. -/
theorem PotentialOutcomes.diffInMeansObs_eq_diffInMeans (po : PotentialOutcomes ι)
    {n1 n0 : ℕ} (hn : n1 + n0 = Fintype.card ι) {a : ι → Bool}
    (ha : a ∈ completeSupport n1) : po.diffInMeansObs a = po.diffInMeans n1 n0 a := by
  rw [mem_completeSupport] at ha
  have h0 : Fintype.card ι - n1 = n0 := by omega
  simp only [diffInMeansObs, diffInMeans, ha, h0]

/-- **Unbiasedness of the observed difference in means under complete randomization.** If
exactly `n1` of the `N = n1 + n0` units are treated, uniformly at random, with `n1, n0 > 0`,
then the observed difference in means is unbiased for the finite-population average treatment
effect. -/
theorem complete_diffInMeansObs_unbiased (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).expect po.diffInMeansObs = po.ate := by
  rw [Design.expect_congr _ fun a ha => po.diffInMeansObs_eq_diffInMeans hn ha]
  exact complete_diffInMeans_unbiased po hn hn1 hn0

/-! ### Permutation-invariant designs -/

omit [Fintype ι] [DecidableEq ι] in
/-- For a design invariant under the relabeling `σ` of the units, the unit `σ i` is treated
with the same probability as `i`. -/
theorem Design.inclusionProb_perm (d : Design ι) (σ : Equiv.Perm ι)
    (hσ : ∀ f : (ι → Bool) → ℝ, d.expect (fun a => f (a ∘ σ)) = d.expect f) (i : ι) :
    d.inclusionProb (σ i) = d.inclusionProb i :=
  hσ fun a => treatInd a i

omit [Fintype ι] [DecidableEq ι] in
/-- For a design invariant under the relabeling `σ` of the units, the pair `(σ i, σ j)` is
treated jointly with the same probability as `(i, j)`. -/
theorem Design.pairInclusionProb_perm (d : Design ι) (σ : Equiv.Perm ι)
    (hσ : ∀ f : (ι → Bool) → ℝ, d.expect (fun a => f (a ∘ σ)) = d.expect f) (i j : ι) :
    d.pairInclusionProb (σ i) (σ j) = d.pairInclusionProb i j :=
  hσ fun a => treatInd a i * treatInd a j

omit [DecidableEq ι] in
/-- **Inclusion probabilities of an exchangeable design.** If a design is invariant under every
relabeling of the units and every assignment in its support treats exactly `m` units, then
every unit is treated with probability `m / N`. -/
theorem Design.inclusionProb_of_perm_invariant (d : Design ι) (m : ℕ)
    (hσ : ∀ (σ : Equiv.Perm ι) (f : (ι → Bool) → ℝ),
      d.expect (fun a => f (a ∘ σ)) = d.expect f)
    (hsupp : ∀ a ∈ d.support, numTreated a = m) (i : ι) :
    d.inclusionProb i = m / Fintype.card ι := by
  classical
  have hsym : ∀ j, d.inclusionProb j = d.inclusionProb i := fun j => by
    simpa using d.inclusionProb_perm (Equiv.swap i j) (hσ _) i
  have htot : ∑ j, d.inclusionProb j = m := by
    unfold Design.inclusionProb
    rw [← d.expect_sum, d.expect_congr (g := fun _ => (m : ℝ)) fun a ha => by
      rw [← numTreated_eq_sum, hsupp a ha]]
    exact d.expect_const _
  rw [sum_congr rfl fun j _ => hsym j, sum_const, card_univ, nsmul_eq_mul] at htot
  have : Nonempty ι := ⟨i⟩
  have : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp
  linarith

end CausalInference.Randomized
