/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.Complete
public import CausalInference.Designs.Randomized.Fisher
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

/-!
# Cluster randomization

The units are partitioned into clusters by a map `g : ι → κ`, and `m1` of the `M` clusters are
drawn by complete randomization; every unit of a drawn cluster is treated. Treating clusters as
units whose outcomes are the cluster totals reduces the analysis to complete randomization: the
Horvitz-Thompson estimator built from the cluster totals is unbiased for the unit-level average
treatment effect. A concrete example with clusters of unequal sizes shows that the plain
difference in means of individual outcomes is biased. Sources: Middleton and Aronow (2015),
*Unbiased estimation of the average treatment effect in cluster-randomized experiments*;
Imbens and Rubin (2015), *Causal Inference for Statistics, Social, and Biomedical Sciences*.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `clusterSupport`, `clusterDesign`: cluster randomization as a `Design` on the units.
* `PotentialOutcomes.clusterTotals`: the cluster-level potential outcome totals.
* `PotentialOutcomes.naiveDiffInMeans`: the difference in means with realized group sizes.

## Main results

* `clusterDesign_expect`: when every cluster is nonempty, expectations under cluster
  randomization are expectations under complete randomization of the clusters.
* `PotentialOutcomes.htEstimator_comp_eq`: the unit-level Horvitz-Thompson estimator with
  probability `m1 / M` is `(M / N)` times the difference in means of the cluster totals.
* `cluster_htEstimator_unbiased`: this estimator is unbiased for the average treatment effect.
* `clusterExample_naiveDiffInMeans_biased`: the plain difference in means is biased in a
  concrete example with clusters of sizes one and two.
* `cluster_fisher_pValue_valid`: Fisher's randomization test is valid under this design.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The support of cluster randomization: the unit-level assignments `b ∘ g` obtained from an
assignment `b` treating exactly `m1` clusters, where `g` maps each unit to its cluster. -/
def clusterSupport (g : ι → κ) (m1 : ℕ) : Finset (ι → Bool) :=
  (completeSupport m1).image fun b => b ∘ g

/-- Cluster randomization: `m1` of the `M` clusters are drawn by complete randomization and all
units of the drawn clusters are treated. It is the uniform design on `clusterSupport g m1`; this
matches complete randomization of the clusters when every cluster is nonempty (`g` surjective),
which the results below assume. -/
noncomputable def clusterDesign (g : ι → κ) (m1 : ℕ) (h : m1 ≤ Fintype.card κ) : Design ι :=
  Design.uniform (clusterSupport g m1) ((completeSupport_nonempty h).image _)

/-- If every cluster is nonempty, an expectation under cluster randomization is the
expectation under complete randomization of the clusters of the induced unit-level statistic.
-/
theorem clusterDesign_expect {g : ι → κ} (hg : Function.Surjective g) (m1 : ℕ)
    (h : m1 ≤ Fintype.card κ) (f : (ι → Bool) → ℝ) :
    (clusterDesign g m1 h).expect f = (completeDesign m1 h).expect fun b => f (b ∘ g) := by
  have hinj : Set.InjOn (fun b : κ → Bool => b ∘ g)
      (completeSupport (ι := κ) m1 : Set (κ → Bool)) :=
    hg.injective_comp_right.injOn
  simp only [clusterDesign, completeDesign, Design.uniform_expect, clusterSupport,
    card_image_of_injOn hinj, sum_image hinj]

/-! ### The Horvitz-Thompson estimator from cluster totals -/

/-- The cluster-level potential outcomes: the totals `T1 c = Σ_{i ∈ c} y1 i` and
`T0 c = Σ_{i ∈ c} y0 i` of the potential outcomes over each cluster `c`. -/
def PotentialOutcomes.clusterTotals (po : PotentialOutcomes ι) (g : ι → κ) :
    PotentialOutcomes κ where
  y1 := fun c => ∑ i ∈ univ with g i = c, po.y1 i
  y0 := fun c => ∑ i ∈ univ with g i = c, po.y0 i

/-- **The cluster Horvitz-Thompson estimator as a cluster-level difference in means.** For a
cluster assignment `b` treating `m1` of the `M = m1 + m0` clusters, the unit-level
Horvitz-Thompson estimator with treatment probability `m1 / M` evaluated at the induced unit
assignment `b ∘ g` equals `(M / N)` times the difference in means of the cluster totals:
`(1/N) ((M/m1) Σ_c B_c T_c - (M/m0) Σ_c (1 - B_c) T_c)`, with `T_c` the observed cluster total. -/
theorem PotentialOutcomes.htEstimator_comp_eq (po : PotentialOutcomes ι) (g : ι → κ)
    {m1 m0 : ℕ} (hm : m1 + m0 = Fintype.card κ) (hm1 : 0 < m1) (hm0 : 0 < m0) (b : κ → Bool) :
    po.htEstimator (m1 / Fintype.card κ) (b ∘ g) =
      (Fintype.card κ : ℝ) / Fintype.card ι * (po.clusterTotals g).diffInMeans m1 m0 b := by
  set p : ℝ := m1 / Fintype.card κ
  have hM : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card κ ≠ 0)
  rw [(po.clusterTotals g).diffInMeans_eq_htEstimator hm hm1 hm0, htEstimator_eq,
    htEstimator_eq]
  have hc : ∀ c, treatInd b c * (po.clusterTotals g).y1 c / p -
      (1 - treatInd b c) * (po.clusterTotals g).y0 c / (1 - p) =
      ∑ i ∈ univ with g i = c,
        (treatInd b (g i) * po.y1 i / p - (1 - treatInd b (g i)) * po.y0 i / (1 - p)) := by
    intro c
    simp only [clusterTotals, mul_sum, sum_div, ← sum_sub_distrib]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  rw [sum_congr rfl fun c _ => hc c, sum_fiberwise univ g]
  field_simp
  rfl

/-- **Unbiasedness under cluster randomization.** If every cluster is nonempty and `m1` of the
`M = m1 + m0` clusters are treated by complete randomization, `m1, m0 > 0`, then the
Horvitz-Thompson estimator built from the cluster totals is unbiased for the unit-level average
treatment effect. The proof treats clusters as units with outcome totals and applies the
unbiasedness of the difference in means under complete randomization. -/
theorem cluster_htEstimator_unbiased (po : PotentialOutcomes ι) {g : ι → κ}
    (hg : Function.Surjective g) {m1 m0 : ℕ} (hm : m1 + m0 = Fintype.card κ) (hm1 : 0 < m1)
    (hm0 : 0 < m0) :
    (clusterDesign g m1 (by omega)).expect (po.htEstimator (m1 / Fintype.card κ)) = po.ate := by
  have hM : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card κ ≠ 0)
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    obtain ⟨c⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card κ)
    obtain ⟨i, -⟩ := hg c
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
  rw [clusterDesign_expect hg, Design.expect_congr _ fun b _ => po.htEstimator_comp_eq g hm hm1
    hm0 b, Design.expect_mul_left, complete_diffInMeans_unbiased _ hm hm1 hm0]
  simp only [PotentialOutcomes.ate, popMean, PotentialOutcomes.unitEffect,
    PotentialOutcomes.clusterTotals, ← sum_sub_distrib]
  rw [sum_fiberwise univ g (fun i => po.y1 i - po.y0 i)]
  field_simp

/-- **Fisher's test under cluster randomization.** Under the sharp null the Fisher
randomization p-value computed with the cluster design is valid. -/
theorem cluster_fisher_pValue_valid (po : PotentialOutcomes ι) (hnull : po.SharpNull)
    (g : ι → κ) (m1 : ℕ) (h : m1 ≤ Fintype.card κ) (T : (ι → Bool) → (ι → ℝ) → ℝ)
    {α : ℝ} (hα : 0 ≤ α) :
    (clusterDesign g m1 h).prob
      (fun a => (clusterDesign g m1 h).fisherPValue T (po.observed a) a ≤ α) ≤ α :=
  fisher_pValue_valid po hnull _ T hα

/-! ### The naive difference in means is biased under cluster randomization -/

/-- The plain difference in means of individual outcomes, with the realized (random) group
sizes: `(1/n1(a)) Σ_i A_i Y_i - (1/(N - n1(a))) Σ_i (1 - A_i) Y_i`, where `n1(a)` is the number
of treated units under `a`. -/
noncomputable def PotentialOutcomes.naiveDiffInMeans (po : PotentialOutcomes ι)
    (a : ι → Bool) : ℝ :=
  (numTreated a : ℝ)⁻¹ * ∑ i, treatInd a i * po.observed a i -
    ((Fintype.card ι : ℝ) - numTreated a)⁻¹ * ∑ i, (1 - treatInd a i) * po.observed a i

section Example

/-- Three units in two clusters of unequal sizes: unit `0` forms cluster `0`, and units `1`
and `2` form cluster `1`. -/
def clusterExampleMap : Fin 3 → Fin 2 := ![0, 1, 1]

/-- Potential outcomes of the example: `y1 = (1, 0, 0)` and `y0 = (0, 0, 0)`, so only the unit
of the small cluster responds to treatment. -/
def clusterExamplePO : PotentialOutcomes (Fin 3) where
  y1 := ![1, 0, 0]
  y0 := ![0, 0, 0]

/-- Every cluster of the example is nonempty. -/
theorem clusterExampleMap_surjective : Function.Surjective clusterExampleMap := by decide

/-- Treating one of the two clusters yields exactly two unit-level assignments: treat unit `0`
alone, or treat units `1` and `2`. -/
theorem clusterExample_clusterSupport :
    clusterSupport clusterExampleMap 1 = {![true, false, false], ![false, true, true]} := by
  decide

/-- In every assignment of the example both the treated and the control group are nonempty, so
the bias below is not an artifact of dividing by zero. -/
theorem clusterExample_groups_nonempty :
    ∀ a ∈ clusterSupport clusterExampleMap 1, 0 < numTreated a ∧ numTreated a < 3 := by
  decide

/-- The average treatment effect of the example is `1/3`. -/
theorem clusterExample_ate : clusterExamplePO.ate = 1 / 3 := by
  simp [PotentialOutcomes.ate, popMean, PotentialOutcomes.unitEffect, clusterExamplePO,
    Fin.sum_univ_three]

/-- Under cluster randomization of the example (one of two clusters treated), the plain
difference in means has expectation `1/2`. -/
theorem clusterExample_expect_naiveDiffInMeans :
    (clusterDesign clusterExampleMap 1 (by decide)).expect clusterExamplePO.naiveDiffInMeans =
      1 / 2 := by
  have hne : (![true, false, false] : Fin 3 → Bool) ≠ ![false, true, true] := by decide
  have h1 : numTreated (![true, false, false] : Fin 3 → Bool) = 1 := by decide
  have h2 : numTreated (![false, true, true] : Fin 3 → Bool) = 2 := by decide
  simp only [clusterDesign, Design.uniform_expect, clusterExample_clusterSupport,
    card_pair hne, sum_pair hne, PotentialOutcomes.naiveDiffInMeans, h1, h2]
  simp [Fin.sum_univ_three, treatInd, PotentialOutcomes.observed, clusterExamplePO]

/-- **Counterexample.** With clusters of unequal sizes, the plain difference in means of
individual outcomes is biased under cluster randomization: in the example its expectation is
`1/2`, while the average treatment effect is `1/3`. -/
theorem clusterExample_naiveDiffInMeans_biased :
    (clusterDesign clusterExampleMap 1 (by decide)).expect clusterExamplePO.naiveDiffInMeans ≠
      clusterExamplePO.ate := by
  rw [clusterExample_expect_naiveDiffInMeans, clusterExample_ate]
  norm_num

end Example

end CausalInference.Randomized
