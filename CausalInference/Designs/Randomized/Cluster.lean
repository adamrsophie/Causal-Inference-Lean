/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.Neyman
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

* `clusterSupport`, `clusterDesign`: cluster randomization as a `Design` on the units, the push
  forward of complete randomization of the cluster labels.
* `PotentialOutcomes.clusterTotals`: the cluster-level potential outcome totals.
* `PotentialOutcomes.naiveDiffInMeans`: the difference in means with realized group sizes.

## Main results

* `clusterDesign_expect`, `clusterDesign_variance`: expectations and variances under cluster
  randomization are those under complete randomization of the clusters, with no assumption on
  the cluster map.
* `clusterDesign_expect_eq_uniform`: when every cluster is nonempty, cluster randomization is
  the uniform design on the induced unit-level assignments; `emptyCluster_laws_differ` shows that
  this fails when a cluster label has no units.
* `clusterDesign_inclusionProb`: every unit is treated with probability `m1 / M`.
* `PotentialOutcomes.htEstimator_comp_eq`: the unit-level Horvitz-Thompson estimator with
  probability `m1 / M` is `(M / N)` times the difference in means of the cluster totals.
* `cluster_htEstimator_unbiased`: this estimator is unbiased for the average treatment effect.
* `cluster_htEstimator_variance`: its variance is
  `(M / N)² (S_{T1}²/m1 + S_{T0}²/m0 - S_{T1 - T0}²/M)`, Neyman's formula on the cluster totals.
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
units of the drawn clusters are treated. It is the push forward of complete randomization of the
cluster labels under `b ↦ b ∘ g`: a unit-level assignment `a` has probability
`#{b | numTreated b = m1, b ∘ g = a} / (M choose m1)`, the number of cluster assignments that
induce it over the number of cluster assignments. When some cluster label has no units, several
cluster assignments induce the same unit-level assignment, and these multiplicities are kept. -/
noncomputable def clusterDesign (g : ι → κ) (m1 : ℕ) (h : m1 ≤ Fintype.card κ) : Design ι where
  support := clusterSupport g m1
  weight a := (#{b ∈ completeSupport m1 | b ∘ g = a} : ℝ) / #(completeSupport (ι := κ) m1)
  weight_nonneg _ _ := by positivity
  sum_weight := by
    have hC : (#(completeSupport (ι := κ) m1) : ℝ) ≠ 0 := by
      exact_mod_cast (completeSupport_nonempty h).card_pos.ne'
    rw [← sum_div, div_eq_one_iff_eq hC]
    exact_mod_cast (card_eq_sum_card_image (fun b => b ∘ g) (completeSupport m1)).symm

/-- An expectation under cluster randomization is the expectation under complete randomization
of the clusters of the induced unit-level statistic. No assumption on the cluster map is needed:
cluster labels without units are allowed. -/
theorem clusterDesign_expect (g : ι → κ) (m1 : ℕ) (h : m1 ≤ Fintype.card κ)
    (f : (ι → Bool) → ℝ) :
    (clusterDesign g m1 h).expect f = (completeDesign m1 h).expect fun b => f (b ∘ g) := by
  rw [completeDesign, Design.uniform_expect, sum_comp f (fun b => b ∘ g), mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [clusterDesign, nsmul_eq_mul]
  ring

/-- The variance under cluster randomization is the variance under complete randomization of
the clusters of the induced unit-level statistic. -/
theorem clusterDesign_variance (g : ι → κ) (m1 : ℕ) (h : m1 ≤ Fintype.card κ)
    (f : (ι → Bool) → ℝ) :
    (clusterDesign g m1 h).variance f = (completeDesign m1 h).variance fun b => f (b ∘ g) := by
  simp only [Design.variance, clusterDesign_expect]

/-- **The uniform form under nonempty clusters.** If every cluster is nonempty (`g`
surjective), distinct cluster assignments induce distinct unit-level assignments, and cluster
randomization is the uniform design on `clusterSupport g m1`. Without surjectivity the two laws
differ (see `emptyCluster_laws_differ`). -/
theorem clusterDesign_expect_eq_uniform {g : ι → κ} (hg : Function.Surjective g) (m1 : ℕ)
    (h : m1 ≤ Fintype.card κ) (f : (ι → Bool) → ℝ) :
    (clusterDesign g m1 h).expect f =
      (Design.uniform (clusterSupport g m1) ((completeSupport_nonempty h).image _)).expect f := by
  have hinj : Set.InjOn (fun b : κ → Bool => b ∘ g)
      (completeSupport (ι := κ) m1 : Set (κ → Bool)) :=
    hg.injective_comp_right.injOn
  rw [clusterDesign_expect]
  simp only [completeDesign, Design.uniform_expect, clusterSupport,
    card_image_of_injOn hinj, sum_image hinj]

/-- Under cluster randomization every unit is treated with probability `m1 / M`. -/
theorem clusterDesign_inclusionProb (g : ι → κ) (m1 : ℕ) (h : m1 ≤ Fintype.card κ) (i : ι) :
    (clusterDesign g m1 h).inclusionProb i = m1 / Fintype.card κ := by
  rw [Design.inclusionProb, clusterDesign_expect]
  exact completeDesign_inclusionProb m1 h (Fintype.card_pos_iff.mpr ⟨g i⟩) (g i)

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
`(1/N) ((M/m1) Σ_c B_c T_c - (M/m0) Σ_c (1 - B_c) T_c)`, with `T_c` the observed cluster total.
The population of units is assumed nonempty, so that `N > 0`. -/
theorem PotentialOutcomes.htEstimator_comp_eq [Nonempty ι] (po : PotentialOutcomes ι) (g : ι → κ)
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

/-- **Unbiasedness under cluster randomization.** In a nonempty population of units, if `m1`
of the `M = m1 + m0` clusters are treated by complete randomization, `m1, m0 > 0`, then the
Horvitz-Thompson estimator built from the cluster totals is unbiased for the unit-level average
treatment effect. Cluster labels without units are allowed: such a cluster has totals zero. The
proof treats clusters as units with outcome totals and applies the unbiasedness of the
difference in means under complete randomization. -/
theorem cluster_htEstimator_unbiased [Nonempty ι] (po : PotentialOutcomes ι) (g : ι → κ)
    {m1 m0 : ℕ} (hm : m1 + m0 = Fintype.card κ) (hm1 : 0 < m1) (hm0 : 0 < m0) :
    (clusterDesign g m1 (by omega)).expect (po.htEstimator (m1 / Fintype.card κ)) = po.ate := by
  have hM : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card κ ≠ 0)
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [clusterDesign_expect, Design.expect_congr _ fun b _ => po.htEstimator_comp_eq g hm hm1
    hm0 b, Design.expect_mul_left, complete_diffInMeans_unbiased _ hm hm1 hm0]
  simp only [PotentialOutcomes.ate, popMean, PotentialOutcomes.unitEffect,
    PotentialOutcomes.clusterTotals, ← sum_sub_distrib]
  rw [sum_fiberwise univ g (fun i => po.y1 i - po.y0 i)]
  field_simp

omit [Fintype ι] in
/-- Scaling a statistic by a constant `c` scales its variance by `c²`. -/
theorem Design.variance_const_mul (d : Design ι) (c : ℝ) (f : (ι → Bool) → ℝ) :
    d.variance (fun a => c * f a) = c ^ 2 * d.variance f := by
  rw [Design.variance, Design.variance, d.expect_mul_left, ← d.expect_mul_left (c ^ 2)]
  exact d.expect_congr fun a _ => by ring

/-- **Exact variance under cluster randomization.** In a nonempty population of units, if `m1`
of the `M = m1 + m0` clusters are treated by complete randomization, `m1, m0 > 0`, then the
variance of the Horvitz-Thompson estimator built from the cluster totals is
`(M / N)² (S_{T1}²/m1 + S_{T0}²/m0 - S_{T1 - T0}²/M)`, Neyman's formula applied to the cluster
totals, with all three finite-population variances taken across the `M` clusters. -/
theorem cluster_htEstimator_variance [Nonempty ι] (po : PotentialOutcomes ι) (g : ι → κ)
    {m1 m0 : ℕ} (hm : m1 + m0 = Fintype.card κ) (hm1 : 0 < m1) (hm0 : 0 < m0) :
    (clusterDesign g m1 (by omega)).variance (po.htEstimator (m1 / Fintype.card κ)) =
      ((Fintype.card κ : ℝ) / Fintype.card ι) ^ 2 *
        ((po.clusterTotals g).varTreated / m1 + (po.clusterTotals g).varControl / m0 -
          (po.clusterTotals g).varEffect / Fintype.card κ) := by
  rw [clusterDesign_variance, Design.variance_congr _ fun b _ => po.htEstimator_comp_eq g hm hm1
    hm0 b, Design.variance_const_mul, neyman_variance _ hm hm1 hm0]

/-- **Fisher's test under cluster randomization.** Under the sharp null the Fisher
randomization p-value computed with the cluster design is valid. No assumption on the cluster
map is needed: the design carries the multiplicities of cluster assignments. -/
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
  rw [clusterDesign_expect_eq_uniform clusterExampleMap_surjective]
  simp only [Design.uniform_expect, clusterExample_clusterSupport,
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

/-! ### Empty cluster labels -/

section EmptyCluster

/-- One unit and three cluster labels, of which only the label `0` has a unit. -/
def emptyClusterMap : Fin 1 → Fin 3 := fun _ => 0

/-- Drawing one of the three labels induces two unit-level assignments: treat the unit, or not.
-/
theorem emptyCluster_clusterSupport :
    clusterSupport emptyClusterMap 1 = {![true], ![false]} := by
  decide

/-- Under cluster randomization (one of three labels drawn) the unit is treated with
probability `1/3`. -/
theorem emptyCluster_inclusionProb :
    (clusterDesign emptyClusterMap 1 (by decide)).inclusionProb 0 = 1 / 3 := by
  rw [clusterDesign_inclusionProb]
  norm_num

/-- Under the uniform design on the induced unit-level assignments the unit is treated with
probability `1/2`. -/
theorem emptyCluster_uniform_inclusionProb :
    (Design.uniform (clusterSupport emptyClusterMap 1)
      ((completeSupport_nonempty (by decide)).image _)).inclusionProb 0 = 1 / 2 := by
  have hne : (![true] : Fin 1 → Bool) ≠ ![false] := by decide
  simp only [Design.inclusionProb, Design.uniform_expect, emptyCluster_clusterSupport,
    card_pair hne, sum_pair hne]
  norm_num [treatInd]

/-- **The two laws differ when a cluster label has no units.** With one unit and three labels,
one of which is drawn, cluster randomization and the uniform design on the induced unit-level
assignments give the unit different treatment probabilities (`1/3` and `1/2`). -/
theorem emptyCluster_laws_differ :
    (clusterDesign emptyClusterMap 1 (by decide)).inclusionProb 0 ≠
      (Design.uniform (clusterSupport emptyClusterMap 1)
        ((completeSupport_nonempty (by decide)).image _)).inclusionProb 0 := by
  rw [emptyCluster_inclusionProb, emptyCluster_uniform_inclusionProb]
  norm_num

end EmptyCluster

end CausalInference.Randomized
