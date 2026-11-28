/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.Consistency
public import CausalInference.NetworkMetaAnalysis.NetworkModel
public import CausalInference.NetworkMetaAnalysis.Pooling

/-!
# Network meta-analysis: worked examples

**A connected triangle.** Treatments `a, b, c`, comparisons `a → b`, `a → c`, `b → c` with
variances `v = (1, 1, 2)` and estimates `y = (1, 3, 1)`. Recomputed by hand:

* the comparison graph is connected and the reduced design has rank `2 = 3 - 1`;
* the reduced design in `(d_ab, d_ac)` is `[[1, 0], [0, 1], [-1, 1]]`, the reduced design of the
  network with reference `a` (`triangleExample_reducedDesign`);
* the Gram matrix with weights `1 / v = (1, 1, 1/2)` is `[[3/2, -1/2], [-1/2, 3/2]]`, its
  inverse `[[3/4, 1/4], [1/4, 3/4]]`;
* the network estimate is `(d̂_ab, d̂_ac) = (5/4, 11/4)`, and `d̂_bc = 3/2`;
* `d̂_ab = 5/4` pools the direct `y_ab = 1` (variance `1`) with the indirect `y_ac - y_bc = 2`
  (variance `3`): `(1 · 3 + 2 · 1) / 4 = 5/4`, with variance `1 / (1 + 1/3) = 3/4`, the first
  diagonal entry of the inverse Gram matrix;
* under independent Gaussian estimates the network estimate is unbiased with covariance the
  inverse Gram matrix, and `3/4 < 1` and `3/4 < 3` (`triangleExample_pooling`);
* the unweighted Laplacian of the triangle is the Laplacian of the complete graph on three
  vertices (`triangleExample_lapMatrix`);
* the contrasts `(1, 0, 0)` violate the cycle condition of the circulation `(1, -1, 1)`
  (`triangleExample_inconsistent`);
* the weighted Laplacian has rank `2`, the least squares minimizer is unique, and the direct
  estimator is unbiased with a larger covariance (`triangleExample_facts`);
* two independent Gaussian estimates of variances `1` and `3` pool to variance `3/4`
  (`poolingExample`).

**A disconnected network.** Treatments `0, 1, 2, 3`, comparisons `0 → 1` and `2 → 3`. The level
vector `(0, 0, 1, 1)` is in the kernel of the incidence matrix, so `0` and `2` are in different
components; the reduced design with reference `0` kills the basic parameters `(0, 1, 1)`, its
Gram matrix is singular, the rank of the incidence matrix is not `3`, a nonzero `d_02` is
invisible in the means, and in the Gaussian contrast model no linear estimator is unbiased for
`d_02` (`disconnectedExample`). Read as two two-arm studies, the contrasts of independent arm
estimates are uncorrelated (`twoStudiesExample`).

**A multi-arm study.** One study with arms `0, 1, 2` and baseline `0` reports the contrasts
`0 → 1`, `0 → 2` from independent arm estimates with variances `σ = (1, 2, 3)`: their
covariance is `[[3, 1], [1, 4]]`, its off diagonal entry the baseline variance `1`, and it is
positive definite (`multiArmExample`).

**An arm based network.** Study `0` has arms `{0, 1, 2}` with baseline `0`, study `1` has arms
`{1, 2}` with baseline `1`: the network of within-study contrasts is connected, so the arm
design is injective of rank `4` and the arm based Gaussian model satisfies the Gauss-Markov
theorem (`armExample`, `armExample_rank`). Studies `{0, 1}` and `{2, 3}` give a disconnected
network in which the relative effect of `2` against `0` is not identified
(`armSplitExample`).

**Constant relative effects.** Two point populations with arm means `j + t` have constant
relative effects on the identity scale, so their network contrast is consistent
(`constancyExample`).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError MetaAnalysis
  IndirectComparison

/-! ### The connected triangle -/

section Triangle

/-- The variances `(1, 1, 2)` of the triangle example. -/
noncomputable def triangleExampleVar : Fin 3 → ℝ := ![1, 1, 2]

/-- The estimates `(1, 3, 1)` of the triangle example. -/
noncomputable def triangleExampleY : Fin 3 → ℝ := ![1, 3, 1]

theorem triangleExampleVar_pos : ∀ i, 0 < triangleExampleVar i := by
  intro i; fin_cases i <;> norm_num [triangleExampleVar]

/-- The triangle design is the reduced design of the triangle network with reference `a`. -/
theorem triangleExample_reducedDesign (d : {k : Fin 3 // k ≠ 0} → ℝ) :
    reducedDesign triangleTail triangleHead 0 *ᵥ d =
      triangleDesign *ᵥ ![d ⟨1, by decide⟩, d ⟨2, by decide⟩] := by
  rw [reducedDesign_mulVec, triangleDesign_mulVec]
  congr 1
  funext k
  fin_cases k
  · simp
  · simp [padReference_of_ne (show (1 : Fin 3) ≠ 0 by decide)]
  · simp [padReference_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

/-- The triangle network is connected: its reduced design has rank `3 - 1`. -/
theorem triangleExample_rank :
    (reducedDesign triangleTail triangleHead 0).rank + 1 = 3 := by
  have := (rank_reducedDesign_iff triangleTail triangleHead 0).2
    comparisonGraph_triangle_connected
  simpa using this

/-- The reduced Gram matrix of the triangle with positive weights is positive definite. -/
theorem triangleExample_posDef_reducedGram :
    (reducedGram triangleTail triangleHead 0 fun i => 1 / triangleExampleVar i).PosDef :=
  (posDef_reducedGram_iff _ _ 0 fun i => one_div_pos.2 (triangleExampleVar_pos i)).2
    comparisonGraph_triangle_connected

/-- The Gram matrix of the triangle example. -/
theorem triangleExample_gram :
    triangleDesignᵀ * (diagonal triangleExampleVar)⁻¹ * triangleDesign =
      !![3 / 2, -1 / 2; -1 / 2, 3 / 2] := by
  rw [inv_diagonal_eq fun i => (triangleExampleVar_pos i).ne']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleDesign, triangleExampleVar, Matrix.mul_apply, Fin.sum_univ_three,
      diagonal_apply]

/-- The inverse Gram matrix (the covariance of the network estimate) of the triangle example. -/
theorem triangleExample_gram_inv :
    (triangleDesignᵀ * (diagonal triangleExampleVar)⁻¹ * triangleDesign)⁻¹ =
      !![3 / 4, 1 / 4; 1 / 4, 3 / 4] := by
  rw [triangleExample_gram]
  refine inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The network estimate of the triangle example is `(5/4, 11/4)`, the first coordinate the
pooling of the direct `1` and the indirect `2`, and `d̂_bc = 3/2`. -/
theorem triangleExample_estimate :
    glsEstimate triangleDesign (diagonal triangleExampleVar) triangleExampleY = ![5 / 4, 11 / 4] ∧
      ivwEstimate ![1, 3] ![1, 2] = 5 / 4 ∧
      glsEstimate triangleDesign (diagonal triangleExampleVar) triangleExampleY 1 -
        glsEstimate triangleDesign (diagonal triangleExampleVar) triangleExampleY 0 = 3 / 2 := by
  obtain ⟨h0, h1⟩ := triangle_glsEstimate triangleExampleVar_pos triangleExampleY
  have e0 : glsEstimate triangleDesign (diagonal triangleExampleVar) triangleExampleY 0 =
      5 / 4 := by
    rw [h0, ivwEstimate_two (by norm_num [triangleExampleVar]) (by norm_num [triangleExampleVar])]
    norm_num [triangleExampleVar, triangleExampleY]
  have e1 : glsEstimate triangleDesign (diagonal triangleExampleVar) triangleExampleY 1 =
      11 / 4 := by
    rw [h1, ivwEstimate_two (by norm_num [triangleExampleVar]) (by norm_num [triangleExampleVar])]
    norm_num [triangleExampleVar, triangleExampleY]
  refine ⟨?_, ?_, by rw [e0, e1]; norm_num⟩
  · funext k; fin_cases k
    · exact e0
    · exact e1
  · rw [ivwEstimate_two (by norm_num) (by norm_num)]; norm_num

/-- The Gaussian law of the triangle example at the parameter `β`. -/
noncomputable def triangleExampleLaw (β : Fin 2 → ℝ) : Measure (Fin 3 → ℝ) :=
  Measure.pi fun i => gaussianReal ((triangleDesign *ᵥ β) i) (triangleExampleVar i).toNNReal

theorem triangleExample_isLinearModel :
    IsLinearModel (Fin 3) triangleExampleLaw (fun i x => x i) triangleDesign
      (diagonal triangleExampleVar) :=
  isLinearModel_pi_gaussian triangleDesign triangleExampleVar_pos

/-- **The triangle example under independent Gaussian estimates**: the network estimate is
unbiased, its covariance is `[[3/4, 1/4], [1/4, 3/4]]`, the estimate of `d_ab` pools direct and
indirect evidence with variance `3/4`, below the direct variance `1` and the indirect variance
`3`, and no linear unbiased estimator of `d_ab` does better. -/
theorem triangleExample_pooling (β : Fin 2 → ℝ) :
    (∀ k, ∫ x, glsEstimate triangleDesign (diagonal triangleExampleVar) x k
      ∂triangleExampleLaw β = β k) ∧
      covMatrix (triangleExampleLaw β)
          (fun k x => glsEstimate triangleDesign (diagonal triangleExampleVar) x k) =
        !![3 / 4, 1 / 4; 1 / 4, 3 / 4] ∧
      Var[fun x => glsEstimate triangleDesign (diagonal triangleExampleVar) x 0;
        triangleExampleLaw β] = 3 / 4 ∧
      ∀ w : Fin 3 → ℝ, (∀ β', ∫ x, w ⬝ᵥ x ∂triangleExampleLaw β' = β' 0) →
        3 / 4 ≤ Var[fun x => w ⬝ᵥ x; triangleExampleLaw β] := by
  have hV : (diagonal triangleExampleVar).PosDef := posDef_diagonal_iff.2 triangleExampleVar_pos
  have h := triangle_pooling triangleExampleVar_pos triangleExample_isLinearModel β
  have hv : 1 / (1 / triangleExampleVar 0 + 1 / (triangleExampleVar 1 + triangleExampleVar 2)) =
      (3 / 4 : ℝ) := by norm_num [triangleExampleVar]
  rw [hv] at h
  refine ⟨triangleExample_isLinearModel.integral_glsEstimate hV triangleDesign_injective β, ?_,
    h.2.2.1, h.2.2.2.2.2⟩
  rw [← triangleExample_gram_inv]
  exact triangleExample_isLinearModel.covMatrix_glsEstimate hV triangleDesign_injective β

/-- The contrast based model of the triangle network in its basic parameters
`{k // k ≠ a}` satisfies the hypotheses of `contrastModel_gauss_markov`. -/
theorem triangleExample_contrastModel (d : {k : Fin 3 // k ≠ 0} → ℝ) :
    ∀ k, ∫ x, glsEstimate (reducedDesign triangleTail triangleHead 0)
      (diagonal triangleExampleVar) x k ∂(Measure.pi fun i => gaussianReal
        ((reducedDesign triangleTail triangleHead 0 *ᵥ d) i) (triangleExampleVar i).toNNReal) =
        d k :=
  (contrastModel_gauss_markov (isLinearModel_pi_gaussian _ triangleExampleVar_pos)
    (posDef_diagonal_iff.2 triangleExampleVar_pos) comparisonGraph_triangle_connected d).1

/-- The unweighted Laplacian of the triangle network is the Laplacian of its comparison graph,
here the complete graph on three vertices. -/
theorem triangleExample_lapMatrix
    [DecidableRel (comparisonGraph triangleTail triangleHead).Adj] :
    weightedLaplacian triangleTail triangleHead 1 =
      (comparisonGraph triangleTail triangleHead).lapMatrix ℝ := by
  refine weightedLaplacian_one_eq_lapMatrix _ _ (fun e => by fin_cases e <;> decide) ?_
  intro e e' h
  fin_cases e <;> fin_cases e' <;> simp_all [triangleTail, triangleHead]

/-- **The cycle condition in the triangle.** Level contrasts satisfy
`δ_ab - δ_ac + δ_bc = 0` (the circulation `(1, -1, 1)`), and the contrasts `(1, 0, 0)` violate
it, so they are the contrasts of no level vector. -/
theorem triangleExample_inconsistent :
    (incidenceMatrix triangleTail triangleHead)ᵀ *ᵥ ![1, -1, 1] = 0 ∧
      ¬∃ θ : Fin 3 → ℝ, incidenceMatrix triangleTail triangleHead *ᵥ θ = ![1, 0, 0] := by
  have hc : (incidenceMatrix triangleTail triangleHead)ᵀ *ᵥ ![1, -1, 1] = 0 := by
    funext k
    fin_cases k <;> simp [incidenceMatrix, triangleTail, triangleHead, mulVec, dotProduct,
      Fin.sum_univ_three]
  refine ⟨hc, fun hδ => ?_⟩
  have := (exists_level_iff_circulation triangleTail triangleHead _).1 hδ _ hc
  norm_num [dotProduct, Fin.sum_univ_three] at this

/-- **Further facts of the triangle example**: the basic parameters of a level contrast vector
are unique, the weighted Laplacian with weights `1 / v` has rank `2`, the least squares
objective has a unique minimizer for every data vector and the network estimate attains it,
and the direct estimator `(y_ab, y_ac)` is unbiased with a covariance that exceeds that of the
network estimate in the positive semidefinite order. -/
theorem triangleExample_facts (y : Fin 3 → ℝ) (β : Fin 2 → ℝ) :
    (∃! d, reducedDesign triangleTail triangleHead 0 *ᵥ d =
      incidenceMatrix triangleTail triangleHead *ᵥ ![0, 1, 3]) ∧
      (weightedLaplacian triangleTail triangleHead fun i => 1 / triangleExampleVar i).rank = 2 ∧
      (∀ y, ∃! β, ∀ β', glsObjective triangleDesign (diagonal triangleExampleVar) y β ≤
        glsObjective triangleDesign (diagonal triangleExampleVar) y β') ∧
      glsObjective triangleDesign (diagonal triangleExampleVar) y
          (glsEstimate triangleDesign (diagonal triangleExampleVar) y) ≤
        glsObjective triangleDesign (diagonal triangleExampleVar) y β ∧
      (covMatrix (triangleExampleLaw β) (fun k x => (!![1, 0, 0; 0, 1, 0] *ᵥ x) k) -
        covMatrix (triangleExampleLaw β)
          (fun k x => glsEstimate triangleDesign (diagonal triangleExampleVar) x k)).PosSemidef :=
    by
  have hV : (diagonal triangleExampleVar).PosDef := posDef_diagonal_iff.2 triangleExampleVar_pos
  have hrank := rank_weightedLaplacian_add_card triangleTail triangleHead
    (fun i => one_div_pos.2 (triangleExampleVar_pos i))
  rw [SimpleGraph.card_connectedComponent_eq_one_iff.2 comparisonGraph_triangle_connected,
    Fintype.card_fin] at hrank
  have hA : (!![1, 0, 0; 0, 1, 0] : Matrix (Fin 2) (Fin 3) ℝ) * triangleDesign = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triangleDesign, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨existsUnique_basic_of_connected _ _ 0 comparisonGraph_triangle_connected ⟨_, rfl⟩,
    by omega, (existsUnique_minimizer_iff hV).2 triangleDesign_injective,
    (glsObjective_glsEstimate_le hV triangleDesign_injective y β).1,
    (triangleExample_isLinearModel.gauss_markov hV triangleDesign_injective
      ((triangleExample_isLinearModel.integral_mulVec_eq_iff _).2 hA) β).1⟩

/-- The law of two independent Gaussian estimates of a common effect `d`, with variances `1`
(direct) and `3` (indirect), as in the triangle example. -/
noncomputable def poolingExampleLaw (d : ℝ) : Measure (Fin 2 → ℝ) :=
  Measure.pi fun i => gaussianReal (((fun _ _ => 1 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ
    fun _ => d) i) ((![1, 3] : Fin 2 → ℝ) i).toNNReal

/-- **Pooling two Gaussian estimates** of variances `1` and `3`: the pooled estimate is unbiased
with variance `3/4`, and no unbiased linear combination does better. -/
theorem poolingExample (d : ℝ) :
    ∫ x, ivwEstimate ![1, 3] ![x 0, x 1] ∂poolingExampleLaw d = d ∧
      Var[fun x => ivwEstimate ![1, 3] ![x 0, x 1]; poolingExampleLaw d] = 3 / 4 ∧
      ∀ a₁ a₂ : ℝ, (∀ d', ∫ x, a₁ * x 0 + a₂ * x 1 ∂poolingExampleLaw d' = d') →
        3 / 4 ≤ Var[fun x => a₁ * x 0 + a₂ * x 1; poolingExampleLaw d] := by
  have hv : ∀ i, 0 < (![1, 3] : Fin 2 → ℝ) i := by intro i; fin_cases i <;> norm_num
  have h := isLinearModel_pi_gaussian (fun _ _ => 1 : Matrix (Fin 2) (Fin 1) ℝ) hv
  have hP : ∀ d', IsProbabilityMeasure (poolingExampleLaw d') :=
    fun d' => h.isProbabilityMeasure fun _ => d'
  have hmean : ∀ d' i, ∫ x, x i ∂poolingExampleLaw d' = d' := fun d' i => by
    rw [poolingExampleLaw, h.integral_eq (fun _ => d') i]
    simp [mulVec, dotProduct]
  have hcov : ∀ d' i j, cov[fun x : Fin 2 → ℝ => x i, fun x => x j; poolingExampleLaw d'] =
      diagonal ![1, 3] i j := fun d' i j => by
    rw [← h.covMatrix_eq fun _ => d']; rfl
  have hvar : ∀ d' i, Var[fun x : Fin 2 → ℝ => x i; poolingExampleLaw d'] =
      (![1, 3] : Fin 2 → ℝ) i := fun d' i => by
    have hm : MemLp (fun x : Fin 2 → ℝ => x i) 2 (poolingExampleLaw d') := h.memLp _ i
    rw [← covariance_self hm.aestronglyMeasurable.aemeasurable, hcov, diagonal_apply_eq]
  have := ivwEstimate_two_pooling (P := poolingExampleLaw) (Xd := fun x => x 0)
    (Xi := fun x => x 1) (vd := 1) (vi := 3) one_pos (by norm_num)
    (fun d' => h.memLp (fun _ => d') 0) (fun d' => h.memLp (fun _ => d') 1)
    (fun d' => by rw [hcov, diagonal_apply_ne _ (by decide)]) (fun d' => hmean d' 0)
    (fun d' => hmean d' 1) (fun d' => hvar d' 0) (fun d' => hvar d' 1) d
  have e : (1 : ℝ) / (1 / 1 + 1 / 3) = 3 / 4 := by norm_num
  rw [e] at this
  exact this

end Triangle

/-! ### A disconnected network -/

section Disconnected

/-- Tails of the disconnected example: comparisons `0 → 1` and `2 → 3`. -/
def disconnectedTail : Fin 2 → Fin 4 := ![0, 2]

/-- Heads of the disconnected example. -/
def disconnectedHead : Fin 2 → Fin 4 := ![1, 3]

/-- **A disconnected network.** The level vector `(0, 0, 1, 1)` is a nonzero kernel vector of
the incidence matrix, `0` and `2` are not joined, the rank is not `4 - 1`, the reduced design
with reference `0` kills the nonzero basic parameters `(0, 1, 1)`, the reduced Gram matrix with
unit weights is singular, some basic parameters with zero means have a nonzero relative effect
of `2` against `0`, and in the Gaussian contrast model with unit variances no linear estimator
is unbiased for that relative effect. -/
theorem disconnectedExample :
    incidenceMatrix disconnectedTail disconnectedHead *ᵥ ![0, 0, 1, 1] = 0 ∧
      ¬(comparisonGraph disconnectedTail disconnectedHead).Reachable 0 2 ∧
      (incidenceMatrix disconnectedTail disconnectedHead).rank + 1 ≠ 4 ∧
      reducedDesign disconnectedTail disconnectedHead 0 *ᵥ (fun k => if k.1 = 1 then 0 else 1) =
        0 ∧
      ¬IsUnit (reducedGram disconnectedTail disconnectedHead 0 1) ∧
      (∃ d', reducedDesign disconnectedTail disconnectedHead 0 *ᵥ d' = 0 ∧
        padReference 0 d' 2 - padReference 0 d' 0 ≠ 0) ∧
      ¬∃ w : Fin 2 → ℝ, ∀ d, ∫ x, w ⬝ᵥ x ∂(Measure.pi fun i => gaussianReal
          ((reducedDesign disconnectedTail disconnectedHead 0 *ᵥ d) i) (1 : ℝ).toNNReal) =
        padReference 0 d 2 - padReference 0 d 0 := by
  have hk : incidenceMatrix disconnectedTail disconnectedHead *ᵥ ![0, 0, 1, 1] = 0 := by
    funext e
    rw [incidenceMatrix_mulVec]
    fin_cases e <;> simp [disconnectedTail, disconnectedHead]
  have hnr : ¬(comparisonGraph disconnectedTail disconnectedHead).Reachable 0 2 := fun h => by
    have := (incidenceMatrix_mulVec_eq_zero_iff_reachable _ _ _).1 hk 0 2 h
    norm_num at this
  have hnc : ¬(comparisonGraph disconnectedTail disconnectedHead).Connected :=
    fun h => hnr (h.preconnected 0 2)
  refine ⟨hk, hnr, fun h => hnc ?_, ?_, fun h => hnc ?_, ?_, ?_⟩
  · exact (rank_incidenceMatrix_add_one_iff _ _).1 (by simpa using h)
  · rw [reducedDesign_mulVec]
    have : padReference (0 : Fin 4) (fun k : {k : Fin 4 // k ≠ 0} => if k.1 = 1 then 0 else 1) =
        ![0, 0, 1, 1] := by
      funext k
      fin_cases k <;> simp [padReference]
    rw [this, hk]
  · exact (isUnit_reducedGram_iff _ _ 0 fun _ => one_pos).1 h
  · obtain ⟨d', hd', hne⟩ := exists_ne_relativeEffect_of_not_reachable 0 hnr 0
    refine ⟨d', by rw [hd', mulVec_zero], ?_⟩
    simpa [padReference] using hne
  · exact not_exists_unbiased_of_not_reachable
      (isLinearModel_pi_gaussian (v := fun _ => 1) _ fun _ => one_pos) hnr

/-- **Two two-arm studies** `0 → 1` and `2 → 3` with independent Gaussian arm estimates of
unit variance: the two contrasts share no arm, so they are uncorrelated. -/
theorem twoStudiesExample (m : Fin 4 → ℝ) :
    covMatrix (Measure.pi fun i => gaussianReal (m i) (1 : ℝ).toNNReal)
      (armContrasts disconnectedTail disconnectedHead fun t x => x t) 0 1 = 0 := by
  have h := isLinearModel_pi_gaussian (1 : Matrix (Fin 4) (Fin 4) ℝ) (v := fun _ => 1)
    fun _ => one_pos
  simp only [one_mulVec] at h
  have := h.isProbabilityMeasure m
  have hcov : ∀ i j, cov[fun x : Fin 4 → ℝ => x i, fun x => x j;
      Measure.pi fun i => gaussianReal (m i) (1 : ℝ).toNNReal] = diagonal (fun _ => 1) i j :=
    fun i j => by rw [← h.covMatrix_eq m]; rfl
  refine covMatrix_armContrasts_eq_zero _ _ (h.memLp m) (σ := fun _ => 1) (fun i => by
      rw [← covariance_self ((h.memLp m i).aestronglyMeasurable.aemeasurable), hcov,
        diagonal_apply_eq])
    (fun i j hij => by rw [hcov, diagonal_apply_ne _ hij]) ?_
  decide

end Disconnected

/-! ### A multi-arm study -/

section MultiArmExample

/-- The variances `(1, 2, 3)` of the arm estimates of the multi-arm example. -/
noncomputable def multiArmVar : Fin 3 → ℝ := ![1, 2, 3]

/-- Tails of the multi-arm example: the contrasts `0 → 1` and `0 → 2` against baseline `0`. -/
def multiArmTail : Fin 2 → Fin 3 := ![0, 0]

/-- Heads of the multi-arm example. -/
def multiArmHead : Fin 2 → Fin 3 := ![1, 2]

theorem multiArmVar_pos : ∀ i, 0 < multiArmVar i := by
  intro i; fin_cases i <;> norm_num [multiArmVar]

/-- **A three-arm study.** For independent Gaussian arm estimates with variances `(1, 2, 3)`, the
contrasts `0 → 1` and `0 → 2` against the shared baseline have covariance `[[3, 1], [1, 4]]`
(the off diagonal entry is the baseline variance), which is positive definite. -/
theorem multiArmExample (m : Fin 3 → ℝ) :
    covMatrix (Measure.pi fun i => gaussianReal (m i) (multiArmVar i).toNNReal)
        (armContrasts multiArmTail multiArmHead fun t x => x t) = !![3, 1; 1, 4] ∧
      covMatrix (Measure.pi fun i => gaussianReal (m i) (multiArmVar i).toNNReal)
        (armContrasts multiArmTail multiArmHead fun t x => x t) 0 1 = multiArmVar 0 ∧
      (covMatrix (Measure.pi fun i => gaussianReal (m i) (multiArmVar i).toNNReal)
        (armContrasts multiArmTail multiArmHead fun t x => x t)).PosDef := by
  have h := isLinearModel_pi_gaussian (1 : Matrix (Fin 3) (Fin 3) ℝ) multiArmVar_pos
  simp only [one_mulVec] at h
  have := h.isProbabilityMeasure m
  have hmem := h.memLp m
  have hcov : ∀ i j, cov[fun x : Fin 3 → ℝ => x i, fun x => x j;
      Measure.pi fun i => gaussianReal (m i) (multiArmVar i).toNNReal] =
        diagonal multiArmVar i j := fun i j => by
    rw [← h.covMatrix_eq m]; rfl
  have hvar : ∀ i, Var[fun x : Fin 3 → ℝ => x i;
      Measure.pi fun i => gaussianReal (m i) (multiArmVar i).toNNReal] = multiArmVar i :=
    fun i => by
      rw [← covariance_self (hmem i).aestronglyMeasurable.aemeasurable, hcov, diagonal_apply_eq]
  have hunc : ∀ i j, i ≠ j → cov[fun x : Fin 3 → ℝ => x i, fun x => x j;
      Measure.pi fun i => gaussianReal (m i) (multiArmVar i).toNNReal] = 0 :=
    fun i j hij => by rw [hcov, diagonal_apply_ne _ hij]
  refine ⟨?_, covMatrix_armContrasts_common_baseline _ _ hmem hvar hunc (by decide) (by decide)
    (by decide) (by decide), posDef_covMatrix_armContrasts _ _ hmem multiArmVar_pos hvar hunc ?_⟩
  · rw [covMatrix_armContrasts _ _ hmem hvar hunc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [incidenceMatrix, multiArmTail, multiArmHead, multiArmVar, Matrix.mul_apply,
        Fin.sum_univ_three, diagonal_apply, transpose_apply, Function.swap]
  · intro u u' huu
    have h1 : u 0 = u' 0 := by
      simpa [vecMul, dotProduct, incidenceMatrix, multiArmTail, multiArmHead,
        Fin.sum_univ_two] using congrFun huu 1
    have h2 : u 1 = u' 1 := by
      simpa [vecMul, dotProduct, incidenceMatrix, multiArmTail, multiArmHead,
        Fin.sum_univ_two] using congrFun huu 2
    funext e
    fin_cases e
    · exact h1
    · exact h2

end MultiArmExample

/-! ### An arm based network -/

section ArmExample

/-- The arms of the arm based example: study `0` has arms `{0, 1, 2}`, study `1` has `{1, 2}`. -/
def armExampleArms : Fin 2 → Finset (Fin 3) := ![{0, 1, 2}, {1, 2}]

/-- The baselines of the arm based example: `0` in study `0` and `1` in study `1`. -/
def armExampleBase : Fin 2 → Fin 3 := ![0, 1]

theorem armExampleBase_mem : ∀ j, armExampleBase j ∈ armExampleArms j := by decide

/-- The network of within-study contrasts of the arm based example is connected. -/
theorem armExample_connected : (armContrastGraph armExampleArms armExampleBase).Connected := by
  have h01 : (armContrastGraph armExampleArms armExampleBase).Adj 0 1 :=
    comparisonGraph_adj_of_ne (tail := fun e : ArmContrast armExampleArms armExampleBase =>
      armExampleBase e.1.1.1) (head := fun e => e.1.1.2) ⟨⟨(0, 1), by decide⟩, by decide⟩
      (by decide)
  have h02 : (armContrastGraph armExampleArms armExampleBase).Adj 0 2 :=
    comparisonGraph_adj_of_ne (tail := fun e : ArmContrast armExampleArms armExampleBase =>
      armExampleBase e.1.1.1) (head := fun e => e.1.1.2) ⟨⟨(0, 2), by decide⟩, by decide⟩
      (by decide)
  have hr : ∀ k, (armContrastGraph armExampleArms armExampleBase).Reachable 0 k := by
    intro k
    fin_cases k
    · exact SimpleGraph.Reachable.refl _
    · exact h01.reachable
    · exact h02.reachable
  exact ⟨fun a b => (hr a).symm.trans (hr b)⟩

/-- **The arm based example under independent Gaussian arm estimates with unit variances**: the
arm design is injective, there are `3 + 2 = 5` arms, and the generalized least squares estimate
of the study intercepts and basic parameters is unbiased. -/
theorem armExample (β : Fin 2 ⊕ {k : Fin 3 // k ≠ 0} → ℝ) :
    Function.Injective (armDesign armExampleArms armExampleBase 0).mulVec ∧
      Fintype.card (ArmContrast armExampleArms armExampleBase) + 2 = 5 ∧
      ∀ c, ∫ x, glsEstimate (armDesign armExampleArms armExampleBase 0) (diagonal fun _ => 1)
          (fun a => x a) c ∂(Measure.pi fun a => gaussianReal
            ((armDesign armExampleArms armExampleBase 0 *ᵥ β) a) (1 : ℝ).toNNReal) = β c := by
  refine ⟨(armDesign_injective_iff armExampleBase_mem 0).2 armExample_connected, ?_,
    (armModel_gauss_markov armExampleBase_mem
      (isLinearModel_pi_gaussian (v := fun _ => 1) _ fun _ => one_pos)
      (posDef_diagonal_iff.2 fun _ => one_pos) armExample_connected β).1⟩
  have h := card_armContrast_add armExampleBase_mem
  have h5 : Fintype.card (ArmIndex armExampleArms) = 5 := by decide
  simp only [Fintype.card_fin, h5] at h
  omega

/-- **Rank of the arm based example**: `rank X + 1 = 2 + 3`, so `rank X = 4` is full, and the
Gram matrix with unit variances is invertible; the kernel of `X` is described by
`armDesign_mulVec_eq_zero_iff`. -/
theorem armExample_rank (β : Fin 2 ⊕ {k : Fin 3 // k ≠ 0} → ℝ) :
    (armDesign armExampleArms armExampleBase 0).rank = 4 ∧
      IsUnit ((armDesign armExampleArms armExampleBase 0)ᵀ *
        (diagonal fun _ => (1 : ℝ))⁻¹ * armDesign armExampleArms armExampleBase 0) ∧
      (armDesign armExampleArms armExampleBase 0 *ᵥ β = 0 ↔ β ∘ Sum.inl = 0 ∧
        reducedDesign (fun e : ArmContrast armExampleArms armExampleBase =>
          armExampleBase e.1.1.1) (fun e => e.1.1.2) 0 *ᵥ (β ∘ Sum.inr) = 0) := by
  have h := rank_armDesign_add_card armExampleBase_mem 0
  rw [SimpleGraph.card_connectedComponent_eq_one_iff.2 armExample_connected] at h
  simp only [Fintype.card_fin] at h
  refine ⟨by omega, ((rank_armDesign_iff armExampleBase_mem 0
    (posDef_diagonal_iff.2 fun _ => one_pos)).2).2 armExample_connected,
    armDesign_mulVec_eq_zero_iff armExampleBase_mem 0 β⟩

/-- The arms of a disconnected arm based network: study `0` compares `{0, 1}`, study `1`
compares `{2, 3}`. -/
def armSplitArms : Fin 2 → Finset (Fin 4) := ![{0, 1}, {2, 3}]

/-- The baselines `0` and `2` of the disconnected arm based network. -/
def armSplitBase : Fin 2 → Fin 4 := ![0, 2]

/-- **A disconnected arm based network**: treatments `0` and `2` are not joined, so for every
study intercepts and basic parameters some other basic parameters give the same arm means and a
different relative effect of `2` against `0`. -/
theorem armSplitExample (μ : Fin 2 → ℝ) (d : {k : Fin 4 // k ≠ 0} → ℝ) :
    ¬(armContrastGraph armSplitArms armSplitBase).Reachable 0 2 ∧
      ∃ d', armDesign armSplitArms armSplitBase 0 *ᵥ Sum.elim μ d' =
          armDesign armSplitArms armSplitBase 0 *ᵥ Sum.elim μ d ∧
        padReference 0 d' 2 - padReference 0 d' 0 ≠ padReference 0 d 2 - padReference 0 d 0 := by
  have hk : incidenceMatrix (fun e : ArmContrast armSplitArms armSplitBase => armSplitBase e.1.1.1)
      (fun e => e.1.1.2) *ᵥ ![0, 0, 1, 1] = 0 := by
    funext e
    rw [incidenceMatrix_mulVec]
    obtain ⟨⟨⟨j, k⟩, hk⟩, hne⟩ := e
    fin_cases j <;> fin_cases k <;>
      first
      | (exfalso; revert hk; decide)
      | simp [armSplitBase]
  have hnr : ¬(armContrastGraph armSplitArms armSplitBase).Reachable 0 2 := fun h => by
    have := (incidenceMatrix_mulVec_eq_zero_iff_reachable _ _ _).1 hk 0 2 h
    norm_num at this
  exact ⟨hnr, armDesign_exists_ne_relativeEffect 0 hnr μ d⟩

end ArmExample

/-! ### Constant relative effects -/

section ConstancyExample

/-- **Constant relative effects give consistent network contrasts.** Two point populations with
arm means `j + t` for treatments `t = 0, 1, 2` have the relative effects `b - a` in both, so
there are consistent contrasts equal to every marginal effect. -/
theorem constancyExample :
    ∃ d : Fin 3 → Fin 3 → ℝ, IsConsistent d ∧ ∀ a b (j : Fin 2),
      (pointPopulation fun t : Fin 3 => (j : ℝ) + t).marginalEffect id a b = d a b := by
  refine ConstantRelativeEffects.exists_isConsistent_networkContrast
    (P := fun j : Fin 2 => pointPopulation fun t : Fin 3 => (j : ℝ) + t) ?_
  intro p _ j j'
  simp [Population.marginalEffect, pointPopulation_armMean]

end ConstancyExample

end NetworkMetaAnalysis

end CausalInference
