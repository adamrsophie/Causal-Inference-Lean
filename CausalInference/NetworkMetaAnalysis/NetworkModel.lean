/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.GaussMarkov

/-!
# Network meta-analysis: the contrast based and the arm based fixed effect models

**The contrast based model.** Each comparison `e` of a network reports an estimate `y_e` of the
contrast `d̃_{head e} - d̃_{tail e}`, where `d` are the basic parameters against a reference `r`
and `d̃` their padding (`d̃_r = 0`): `E[y] = X d` for the reduced design `X`, with a covariance
matrix `V`. For a connected network and `V` positive definite the generalized least squares
estimate of `d` is unbiased with covariance `(Xᵀ V⁻¹ X)⁻¹` and best linear unbiased, and so is
the estimate `d̂̃_b - d̂̃_a` of every relative effect (`contrastModel_gauss_markov`). If `a` and `b`
lie in different components, two parameters with the same mean vector have different `d_ab`
(`exists_ne_relativeEffect_of_not_reachable`), and no linear estimator is unbiased for `d_ab`
(`not_exists_unbiased_of_not_reachable`).

**Multi-arm studies.** A study with arms `t₁, …, t_m` contributes the `m - 1` contrasts of its
arms against its baseline arm; these share the baseline arm estimate, so they are correlated.
For uncorrelated arm estimates `Z_t` with variances `σ_t`, the contrasts `Z_{head} - Z_{tail}`
have covariance `B diag(σ) Bᵀ` (`covMatrix_armContrasts`); two contrasts against a common
baseline arm `b` with distinct other arms have covariance `σ_b`
(`covMatrix_armContrasts_common_baseline`), contrasts of different studies are uncorrelated
(`covMatrix_armContrasts_eq_zero`), so the covariance of the network is block diagonal by study,
and it is positive definite when the contrasts are linearly independent
(`posDef_covMatrix_armContrasts`).

**The arm based model.** Study `j` has the arm set `arms j` and the baseline arm
`base j ∈ arms j`; arm `(j, k)` has mean `μ_j + d̃_k - d̃_{base j}` with a free study intercept
`μ_j` (`armDesign`). The within-study contrasts `base j → k` form the network of the study
(`armContrastGraph`). The arm design has full column rank exactly when that network is
connected (`armDesign_injective_iff`, `rank_armDesign_iff`); in general
`rank X + q = J + T` for `q` components (`rank_armDesign_add_card`), and a relative effect
across components is not identified (`armDesign_exists_ne_relativeEffect`). The arm mean
vectors it produces are exactly those whose baseline shifted contrasts
`θ_{jk} - θ_{j, base j}` are consistent, that is, reduced design contrasts
(`mem_range_armDesign_iff`). The baseline shift coordinates
`(θ_{j, base j}, θ_{jk} - θ_{j, base j})` relabel the arm means bijectively
(`baselineShift_inverse`), and there are `N - J` contrasts for `N` arms (`card_armContrast_add`).

## Main definitions

* `armContrasts`, `ArmIndex`, `ArmContrast`, `armContrastGraph`, `armDesign`,
  `baselineShiftMean`, `baselineShiftCoords`.

## Main results

* `contrastModel_gauss_markov`, `exists_ne_relativeEffect_of_not_reachable`,
  `not_exists_unbiased_of_not_reachable`.
* `covMatrix_armContrasts`, `covMatrix_armContrasts_common_baseline`,
  `covMatrix_armContrasts_eq_zero`, `posDef_covMatrix_armContrasts`.
* `armDesign_mulVec_base`, `armDesign_mulVec_contrast`, `armDesign_injective_iff`,
  `armDesign_mulVec_eq_zero_iff`, `rank_armDesign_add_card`, `rank_armDesign_iff`,
  `armDesign_exists_ne_relativeEffect`, `mem_range_armDesign_iff`, `baselineShift_inverse`,
  `card_armContrast_add`, `armModel_gauss_markov`.

## References

* G. Lu and A. E. Ades, *Combination of direct and indirect evidence in mixed treatment
  comparisons*, Statistics in Medicine 23 (2004).
* G. Rücker, *Network meta-analysis, electrical networks and graph theory*, Research Synthesis
  Methods 3 (2012).
* S. Dias, A. J. Sutton, A. E. Ades and N. J. Welton, *Evidence synthesis for decision making 2:
  a generalized linear modeling framework for pairwise and network meta-analysis of randomized
  controlled trials*, Medical Decision Making 33 (2013).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError

/-! ### The contrast based model -/

section Contrast

variable {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]
  {Ω : Type*} [MeasurableSpace Ω]

/-- **The contrast based fixed effect model** (Lu and Ades 2004). Let the comparison estimates
follow a linear model with the reduced design `X` of a connected network, reference `r`, and a
positive definite covariance `V`. Then the generalized least squares estimate `d̂` of the basic
parameters is unbiased with covariance `(Xᵀ V⁻¹ X)⁻¹`, every linear unbiased estimator has a
covariance at least as large in the positive semidefinite order, and the network estimate
`d̂̃_b - d̂̃_a` of every relative effect is unbiased. -/
theorem contrastModel_gauss_markov {tail head : E → K} {r : K}
    {P : ({k // k ≠ r} → ℝ) → Measure Ω} {Y : E → Ω → ℝ} {V : Matrix E E ℝ}
    (h : IsLinearModel E P Y (reducedDesign tail head r) V) (hV : V.PosDef)
    (hcon : (comparisonGraph tail head).Connected) (d : {k // k ≠ r} → ℝ) :
    (∀ k, ∫ ω, glsEstimate (reducedDesign tail head r) V (fun e => Y e ω) k ∂P d = d k) ∧
      covMatrix (P d) (fun k ω => glsEstimate (reducedDesign tail head r) V (fun e => Y e ω) k) =
        ((reducedDesign tail head r)ᵀ * V⁻¹ * reducedDesign tail head r)⁻¹ ∧
      (∀ A : Matrix {k // k ≠ r} E ℝ,
        (∀ d' k, ∫ ω, (A *ᵥ fun e => Y e ω) k ∂P d' = d' k) →
        (covMatrix (P d) (fun k ω => (A *ᵥ fun e => Y e ω) k) -
          covMatrix (P d) (fun k ω =>
            glsEstimate (reducedDesign tail head r) V (fun e => Y e ω) k)).PosSemidef) ∧
      ∀ a b : K, ∫ ω, (padReference r (glsEstimate (reducedDesign tail head r) V
          (fun e => Y e ω)) b - padReference r (glsEstimate (reducedDesign tail head r) V
          (fun e => Y e ω)) a) ∂P d = padReference r d b - padReference r d a := by
  have hX := (reducedDesign_injective_iff tail head r).2 hcon
  have := h.isProbabilityMeasure d
  have hpad : ∀ (z : E → ℝ) (t : K), padReference r (glsEstimate (reducedDesign tail head r) V z)
      t = if ht : t = r then 0 else glsEstimate (reducedDesign tail head r) V z ⟨t, ht⟩ :=
    fun _ _ => rfl
  have hint : ∀ t : K, Integrable (fun ω => padReference r
      (glsEstimate (reducedDesign tail head r) V (fun e => Y e ω)) t) (P d) := by
    intro t
    simp only [hpad]
    split_ifs with ht
    · exact integrable_const 0
    · exact (memLp_matrix_mulVec (h.memLp d) _ _).integrable one_le_two
  have hmean : ∀ t : K, ∫ ω, padReference r
      (glsEstimate (reducedDesign tail head r) V (fun e => Y e ω)) t ∂P d =
        padReference r d t := by
    intro t
    simp only [hpad]
    split_ifs with ht
    · simp [ht]
    · rw [h.integral_glsEstimate hV hX, padReference_of_ne ht]
  refine ⟨h.integral_glsEstimate hV hX d, h.covMatrix_glsEstimate hV hX d,
    fun A hA => (h.gauss_markov hV hX hA d).1, fun a b => ?_⟩
  rw [integral_sub (hint b) (hint a), hmean, hmean]

omit [Fintype E] [DecidableEq E] in
/-- **A relative effect across components is not identified**: if `a` and `b` lie in different
components of the comparison graph, then for every basic parameter `d` there is `d'` with the
same contrast means `X d' = X d` and a different relative effect `d̃'_b - d̃'_a`. -/
theorem exists_ne_relativeEffect_of_not_reachable {tail head : E → K} (r : K) {a b : K}
    (hab : ¬(comparisonGraph tail head).Reachable a b) (d : {k // k ≠ r} → ℝ) :
    ∃ d', reducedDesign tail head r *ᵥ d' = reducedDesign tail head r *ᵥ d ∧
      padReference r d' b - padReference r d' a ≠ padReference r d b - padReference r d a := by
  classical
  set G := comparisonGraph tail head
  let c := if G.Reachable b r then a else b
  have hcr : ¬G.Reachable c r := by
    by_cases hb : G.Reachable b r
    · simp only [c, hb, ite_true]; exact fun har => hab (har.trans hb.symm)
    · simp [c, hb]
  let v : K → ℝ := fun k => if G.Reachable c k then 1 else 0
  have hvr : v r = 0 := by simp [v, hcr]
  have hv : incidenceMatrix tail head *ᵥ v = 0 := by
    rw [incidenceMatrix_mulVec_eq_zero_iff_reachable]
    intro x y hxy
    by_cases hx : G.Reachable c x
    · simp [v, hx, hx.trans hxy]
    · have hy : ¬G.Reachable c y := fun h => hx (h.trans hxy.symm)
      simp [v, hx, hy]
  refine ⟨d + fun k => v k.1, ?_, ?_⟩
  · rw [mulVec_add, reducedDesign_mulVec tail head r (fun k => v k.1),
      padReference_restrict hvr, hv, add_zero]
  · rw [padReference_add, padReference_restrict hvr]
    simp only [Pi.add_apply]
    by_cases hb : G.Reachable b r
    · have hc : c = a := by simp [c, hb]
      have hvb : v b = 0 := by simp [v, hc, hab]
      have hva : v a = 1 := by simp [v, hc]
      rw [hva, hvb]; intro h; linarith
    · have hc : c = b := by simp [c, hb]
      have hvb : v b = 1 := by simp [v, hc]
      have hba : ¬G.Reachable b a := fun h => hab h.symm
      have hva : v a = 0 := by simp [v, hc, hba]
      rw [hva, hvb]; intro h; linarith

omit [DecidableEq E] in
/-- **No unbiased estimator across components**: if `a` and `b` lie in different components of
the comparison graph, then in a contrast based linear model no linear estimator `wᵀ y` is
unbiased for the relative effect `d̃_b - d̃_a` at every parameter. -/
theorem not_exists_unbiased_of_not_reachable {tail head : E → K} {r : K}
    {P : ({k // k ≠ r} → ℝ) → Measure Ω} {Y : E → Ω → ℝ} {V : Matrix E E ℝ}
    (h : IsLinearModel E P Y (reducedDesign tail head r) V) {a b : K}
    (hab : ¬(comparisonGraph tail head).Reachable a b) :
    ¬∃ w : E → ℝ, ∀ d, ∫ ω, w ⬝ᵥ (fun e => Y e ω) ∂P d =
      padReference r d b - padReference r d a := by
  rintro ⟨w, hw⟩
  have hmean : ∀ d, ∫ ω, w ⬝ᵥ (fun e => Y e ω) ∂P d = w ⬝ᵥ (reducedDesign tail head r *ᵥ d) := by
    intro d
    have := h.isProbabilityMeasure d
    simp only [dotProduct]
    rw [integral_finsetSum _ fun e _ => ((h.memLp d e).integrable one_le_two).const_mul _]
    simp only [integral_const_mul, h.integral_eq]
  obtain ⟨d', hd', hne⟩ := exists_ne_relativeEffect_of_not_reachable r hab 0
  apply hne
  rw [← hw, ← hw, hmean, hmean, hd']

end Contrast

/-! ### Multi-arm studies: the covariance of contrasts of arm estimates -/

section MultiArm

variable {E T : Type*} [Fintype E] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **contrasts of arm estimates**: contrast `e` is `Z_{head e} - Z_{tail e}` for estimates
`Z_t` of the arms `t`. -/
def armContrasts (tail head : E → T) (Z : T → Ω → ℝ) (e : E) (ω : Ω) : ℝ :=
  Z (head e) ω - Z (tail e) ω

omit [Fintype E] [MeasurableSpace Ω] in
theorem armContrasts_eq [Fintype T] [DecidableEq T] (tail head : E → T) (Z : T → Ω → ℝ) :
    armContrasts tail head Z = fun e ω => (incidenceMatrix tail head *ᵥ fun t => Z t ω) e := by
  funext e ω
  rw [incidenceMatrix_mulVec]; rfl

omit [Fintype E] in
/-- **The covariance of contrasts of uncorrelated arm estimates** is `B diag(σ) Bᵀ`, for square
integrable, pairwise uncorrelated arm estimates with variances `σ_t`. -/
theorem covMatrix_armContrasts [Fintype T] [DecidableEq T] [IsFiniteMeasure μ]
    (tail head : E → T) {Z : T → Ω → ℝ}
    (hZ : ∀ t, MemLp (Z t) 2 μ) {σ : T → ℝ} (hvar : ∀ t, Var[Z t; μ] = σ t)
    (hunc : ∀ s t, s ≠ t → cov[Z s, Z t; μ] = 0) :
    covMatrix μ (armContrasts tail head Z) =
      incidenceMatrix tail head * diagonal σ * (incidenceMatrix tail head)ᵀ := by
  have hcov : covMatrix μ Z = diagonal σ := by
    ext s t
    simp only [covMatrix, Matrix.of_apply, diagonal_apply]
    by_cases hst : s = t
    · subst hst; simp only [↓reduceIte]
      rw [covariance_self (hZ s).aestronglyMeasurable.aemeasurable, hvar]
    · simp only [hst, ↓reduceIte]; exact hunc s t hst
  rw [armContrasts_eq, covMatrix_matrix_mulVec hZ, hcov]

omit [Fintype E] in
/-- An entry of the covariance of contrasts: `Cov(y_e, y_{e'}) = f(head e) - f(tail e)` with
`f t = σ_t B_{e' t}`. -/
theorem covMatrix_armContrasts_apply [Finite T] [DecidableEq T] [IsFiniteMeasure μ]
    (tail head : E → T) {Z : T → Ω → ℝ}
    (hZ : ∀ t, MemLp (Z t) 2 μ) {σ : T → ℝ} (hvar : ∀ t, Var[Z t; μ] = σ t)
    (hunc : ∀ s t, s ≠ t → cov[Z s, Z t; μ] = 0) (e e' : E) :
    covMatrix μ (armContrasts tail head Z) e e' =
      σ (head e) * incidenceMatrix tail head e' (head e) -
        σ (tail e) * incidenceMatrix tail head e' (tail e) := by
  have := Fintype.ofFinite T
  rw [covMatrix_armContrasts tail head hZ hvar hunc]
  have h := incidenceMatrix_mulVec tail head (fun t => σ t * incidenceMatrix tail head e' t) e
  rw [← h]
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply, mulVec, dotProduct]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [Fintype E] in
/-- **Contrasts against a common baseline arm are correlated**: two contrasts `b → k` and
`b → k'` with `k`, `k'`, `b` distinct have covariance `σ_b`, the variance of the shared baseline
arm estimate. -/
theorem covMatrix_armContrasts_common_baseline [Finite T] [IsFiniteMeasure μ] (tail head : E → T)
    {Z : T → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) {σ : T → ℝ} (hvar : ∀ t, Var[Z t; μ] = σ t)
    (hunc : ∀ s t, s ≠ t → cov[Z s, Z t; μ] = 0) {e e' : E} (hb : tail e = tail e')
    (hk : head e ≠ head e') (hke : head e ≠ tail e) (hke' : head e' ≠ tail e') :
    covMatrix μ (armContrasts tail head Z) e e' = σ (tail e) := by
  classical
  have := Fintype.ofFinite T
  rw [covMatrix_armContrasts_apply tail head hZ hvar hunc]
  have h1 : tail e ≠ head e' := hb ▸ hke'.symm
  have h2 : head e ≠ tail e' := hb ▸ hke
  simp [incidenceMatrix, hk, h2, hb, Ne.symm hke']

omit [Fintype E] in
/-- **Contrasts of different studies are uncorrelated**: if the arms of contrast `e` and the
arms of contrast `e'` are disjoint (for instance, they belong to different studies), their
covariance is `0`. -/
theorem covMatrix_armContrasts_eq_zero [Finite T] [IsFiniteMeasure μ] (tail head : E → T)
    {Z : T → Ω → ℝ}
    (hZ : ∀ t, MemLp (Z t) 2 μ) {σ : T → ℝ} (hvar : ∀ t, Var[Z t; μ] = σ t)
    (hunc : ∀ s t, s ≠ t → cov[Z s, Z t; μ] = 0) {e e' : E}
    (hd : ∀ t, (t = head e ∨ t = tail e) → t ≠ head e' ∧ t ≠ tail e') :
    covMatrix μ (armContrasts tail head Z) e e' = 0 := by
  classical
  have := Fintype.ofFinite T
  rw [covMatrix_armContrasts_apply tail head hZ hvar hunc]
  obtain ⟨h1, h2⟩ := hd (head e) (Or.inl rfl)
  obtain ⟨h3, h4⟩ := hd (tail e) (Or.inr rfl)
  simp [incidenceMatrix, h1, h2, h3, h4]

/-- **The covariance of linearly independent contrasts is positive definite**: for positive arm
variances and contrasts whose rows of `B` are linearly independent (`v ↦ vᵀ B` injective), the
covariance `B diag(σ) Bᵀ` is positive definite. -/
theorem posDef_covMatrix_armContrasts [Finite T] [DecidableEq T] [IsFiniteMeasure μ]
    (tail head : E → T)
    {Z : T → Ω → ℝ} (hZ : ∀ t, MemLp (Z t) 2 μ) {σ : T → ℝ} (hσ : ∀ t, 0 < σ t)
    (hvar : ∀ t, Var[Z t; μ] = σ t) (hunc : ∀ s t, s ≠ t → cov[Z s, Z t; μ] = 0)
    (hB : Function.Injective (incidenceMatrix tail head).vecMul) :
    (covMatrix μ (armContrasts tail head Z)).PosDef := by
  classical
  have := Fintype.ofFinite T
  rw [covMatrix_armContrasts tail head hZ hvar hunc]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (posDef_diagonal_iff.2 hσ).mul_mul_conjTranspose_same hB

end MultiArm

/-! ### The arm based model -/

section Arm

variable {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

/-- The **arms** of a network of studies: the pairs `(j, k)` with `k ∈ arms j`. -/
abbrev ArmIndex (arms : J → Finset K) : Type _ := {p : J × K // p.2 ∈ arms p.1}

/-- The **within-study contrasts**: the arms `(j, k)` with `k ≠ base j`, each the comparison
`base j → k`. Parallel comparisons of different studies are distinct. -/
abbrev ArmContrast (arms : J → Finset K) (base : J → K) : Type _ :=
  {a : ArmIndex arms // a.1.2 ≠ base a.1.1}

/-- The **comparison graph of the studies**: the comparison graph of the within-study contrasts
`base j → k`. -/
def armContrastGraph (arms : J → Finset K) (base : J → K) : SimpleGraph K :=
  comparisonGraph (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2)

/-- The **arm based design** with free study intercepts and the basic parameters of a reference
`r`: the row of arm `(j, k)` has `1` in the column of study `j`, `+1` in the column `k` and `-1`
in the column `base j` (entries of the reference column omitted), so the arm mean is
`μ_j + d̃_k - d̃_{base j}`. -/
def armDesign (arms : J → Finset K) (base : J → K) (r : K) :
    Matrix (ArmIndex arms) (J ⊕ {k // k ≠ r}) ℝ :=
  Matrix.of fun a => Sum.elim (fun j => if j = a.1.1 then 1 else 0)
    (fun k => (if k.1 = a.1.2 then 1 else 0) - (if k.1 = base a.1.1 then 1 else 0))

/-- The arm design computes the arm means `μ_j + d̃_k - d̃_{base j}`. -/
theorem armDesign_mulVec (arms : J → Finset K) (base : J → K) (r : K)
    (β : J ⊕ {k // k ≠ r} → ℝ) (a : ArmIndex arms) :
    (armDesign arms base r *ᵥ β) a = β (Sum.inl a.1.1) +
      (padReference r (β ∘ Sum.inr) a.1.2 - padReference r (β ∘ Sum.inr) (base a.1.1)) := by
  have hsum : ∀ t : K, ∑ k : {k // k ≠ r}, (if k.1 = t then β (Sum.inr k) else 0) =
      padReference r (β ∘ Sum.inr) t := by
    intro t
    by_cases ht : t = r
    · subst ht
      rw [padReference_self]
      exact Finset.sum_eq_zero fun k _ => ite_eq_right_iff.2 fun h => absurd h k.2
    · rw [padReference_of_ne ht, Fintype.sum_eq_single ⟨t, ht⟩]
      · simp
      · intro k hk
        exact ite_eq_right_iff.2 fun h => absurd (Subtype.ext h) hk
  simp only [armDesign, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, ite_mul, one_mul, zero_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum, hsum]

/-- The baseline arm of a study has mean `μ_j`. -/
theorem armDesign_mulVec_base (arms : J → Finset K) (base : J → K) (r : K)
    (β : J ⊕ {k // k ≠ r} → ℝ) (j : J) (hj : base j ∈ arms j) :
    (armDesign arms base r *ᵥ β) ⟨(j, base j), hj⟩ = β (Sum.inl j) := by
  rw [armDesign_mulVec]; ring

/-- A non-baseline arm has mean `μ_j` plus the contrast of the reduced design of the
within-study contrasts. -/
theorem armDesign_mulVec_contrast (arms : J → Finset K) (base : J → K) (r : K)
    (β : J ⊕ {k // k ≠ r} → ℝ) (e : ArmContrast arms base) :
    (armDesign arms base r *ᵥ β) e.1 = β (Sum.inl e.1.1.1) +
      (reducedDesign (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2) r *ᵥ
        (β ∘ Sum.inr)) e := by
  rw [armDesign_mulVec, reducedDesign_mulVec_apply]

/-- **The arm based design has full column rank exactly for a connected network**: with study
intercepts and a reference treatment, when every study contains its baseline arm, `X` is
injective if and only if the comparison graph of the within-study contrasts is connected. -/
theorem armDesign_injective_iff {arms : J → Finset K} {base : J → K}
    (hbase : ∀ j, base j ∈ arms j) (r : K) :
    Function.Injective (armDesign arms base r).mulVec ↔
      (armContrastGraph arms base).Connected := by
  set Xc := reducedDesign (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2) r
  rw [armContrastGraph, ← reducedDesign_injective_iff _ _ r]
  constructor
  · intro hinj u u' hu
    have h := @hinj (Sum.elim 0 u) (Sum.elim 0 u') (funext fun a => by
      by_cases ha : a.1.2 = base a.1.1
      · have : a = ⟨(a.1.1, base a.1.1), hbase _⟩ := Subtype.ext (Prod.ext rfl ha)
        rw [this, armDesign_mulVec_base, armDesign_mulVec_base]; rfl
      · have h1 := armDesign_mulVec_contrast arms base r (Sum.elim 0 u) ⟨a, ha⟩
        have h2 := armDesign_mulVec_contrast arms base r (Sum.elim 0 u') ⟨a, ha⟩
        simp only [Sum.elim_comp_inr] at h1 h2
        rw [h1, h2, hu]; rfl)
    funext k
    exact congrFun h (Sum.inr k)
  · intro hinj β β' h
    have hμ : ∀ j, β (Sum.inl j) = β' (Sum.inl j) := fun j => by
      have := congrFun h ⟨(j, base j), hbase j⟩
      rwa [armDesign_mulVec_base, armDesign_mulVec_base] at this
    have hd : β ∘ Sum.inr = β' ∘ Sum.inr := hinj (funext fun e => by
      have := congrFun h e.1
      rw [armDesign_mulVec_contrast, armDesign_mulVec_contrast, hμ] at this
      linarith)
    funext c
    cases c with
    | inl j => exact hμ j
    | inr k => exact congrFun hd k

/-- **The arm means of the model are the consistent ones**: an arm mean vector `θ` is
`X (μ, d)` for some study intercepts and basic parameters exactly when its baseline shifted
contrasts `θ_{jk} - θ_{j, base j}` are the contrasts of the within-study network for some basic
parameters, that is, consistent. -/
theorem mem_range_armDesign_iff {arms : J → Finset K} {base : J → K}
    (hbase : ∀ j, base j ∈ arms j) (r : K) (θ : ArmIndex arms → ℝ) :
    (∃ β, armDesign arms base r *ᵥ β = θ) ↔
      ∃ d, ∀ e : ArmContrast arms base, θ e.1 - θ ⟨(e.1.1.1, base e.1.1.1), hbase _⟩ =
        (reducedDesign (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2) r *ᵥ
          d) e := by
  constructor
  · rintro ⟨β, rfl⟩
    refine ⟨β ∘ Sum.inr, fun e => ?_⟩
    rw [armDesign_mulVec_contrast, armDesign_mulVec_base]; ring
  · rintro ⟨d, hd⟩
    refine ⟨Sum.elim (fun j => θ ⟨(j, base j), hbase j⟩) d, funext fun a => ?_⟩
    by_cases ha : a.1.2 = base a.1.1
    · have : a = ⟨(a.1.1, base a.1.1), hbase _⟩ := Subtype.ext (Prod.ext rfl ha)
      rw [this, armDesign_mulVec_base]; rfl
    · have h1 := armDesign_mulVec_contrast arms base r
        (Sum.elim (fun j => θ ⟨(j, base j), hbase j⟩) d) ⟨a, ha⟩
      rw [Sum.elim_comp_inr, ← hd ⟨a, ha⟩] at h1
      rw [h1]; simp

/-- **The kernel of the arm design**: `X (μ, d) = 0` if and only if the study intercepts vanish
and the within-study contrasts of `d` vanish, when every study contains its baseline arm. -/
theorem armDesign_mulVec_eq_zero_iff {arms : J → Finset K} {base : J → K}
    (hbase : ∀ j, base j ∈ arms j) (r : K) (β : J ⊕ {k // k ≠ r} → ℝ) :
    armDesign arms base r *ᵥ β = 0 ↔ β ∘ Sum.inl = 0 ∧
      reducedDesign (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2) r *ᵥ
        (β ∘ Sum.inr) = 0 := by
  constructor
  · intro h
    have hμ : β ∘ Sum.inl = 0 := funext fun j => by
      have := congrFun h ⟨(j, base j), hbase j⟩
      rwa [armDesign_mulVec_base] at this
    refine ⟨hμ, funext fun e => ?_⟩
    have := congrFun h e.1
    rw [armDesign_mulVec_contrast, show β (Sum.inl e.1.1.1) = 0 from congrFun hμ e.1.1.1,
      zero_add] at this
    exact this
  · rintro ⟨hμ, hd⟩
    funext a
    rw [Pi.zero_apply]
    by_cases ha : a.1.2 = base a.1.1
    · have : a = ⟨(a.1.1, base a.1.1), hbase _⟩ := Subtype.ext (Prod.ext rfl ha)
      rw [this, armDesign_mulVec_base]
      exact congrFun hμ _
    · rw [show a = (⟨a, ha⟩ : ArmContrast arms base).1 from rfl, armDesign_mulVec_contrast,
        show β (Sum.inl a.1.1) = 0 from congrFun hμ a.1.1, congrFun hd ⟨a, ha⟩]
      simp

/-- **The rank of the arm design**: `rank X + q = J + T`, for `J` studies, `T` treatments and
`q` connected components of the network of within-study contrasts, when every study contains
its baseline arm. -/
theorem rank_armDesign_add_card {arms : J → Finset K} {base : J → K}
    (hbase : ∀ j, base j ∈ arms j) (r : K) :
    (armDesign arms base r).rank + Nat.card (armContrastGraph arms base).ConnectedComponent =
      Fintype.card J + Fintype.card K := by
  let Xc := reducedDesign (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2) r
  have h1 : ∀ β ∈ LinearMap.ker (armDesign arms base r).mulVecLin,
      β ∘ Sum.inr ∈ LinearMap.ker Xc.mulVecLin := fun β hβ => by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hβ ⊢
    exact ((armDesign_mulVec_eq_zero_iff hbase r β).1 hβ).2
  have h2 : ∀ d ∈ LinearMap.ker Xc.mulVecLin,
      (Sum.elim 0 d : J ⊕ {k // k ≠ r} → ℝ) ∈ LinearMap.ker (armDesign arms base r).mulVecLin :=
    fun d hd => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hd ⊢
      exact (armDesign_mulVec_eq_zero_iff hbase r _).2
        ⟨Sum.elim_comp_inl _ _, by rwa [Sum.elim_comp_inr]⟩
  have h3 : ∀ β ∈ LinearMap.ker (armDesign arms base r).mulVecLin, β ∘ Sum.inl = 0 :=
    fun β hβ => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hβ
      exact ((armDesign_mulVec_eq_zero_iff hbase r β).1 hβ).1
  have hker : Module.finrank ℝ (LinearMap.ker (armDesign arms base r).mulVecLin) =
      Module.finrank ℝ (LinearMap.ker Xc.mulVecLin) :=
    LinearEquiv.finrank_eq
      { toFun := fun β => ⟨β.1 ∘ Sum.inr, h1 β.1 β.2⟩
        invFun := fun d => ⟨Sum.elim 0 d.1, h2 d.1 d.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun β => Subtype.ext (funext fun c => by
          cases c with
          | inl j => exact (congrFun (h3 β.1 β.2) j).symm
          | inr k => rfl)
        right_inv := fun _ => rfl }
  have hX : (armDesign arms base r).rank +
      Module.finrank ℝ (LinearMap.ker (armDesign arms base r).mulVecLin) =
        Fintype.card J + Fintype.card {k // k ≠ r} := by
    have := (armDesign arms base r).mulVecLin.finrank_range_add_finrank_ker
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at this
  have hXc : Xc.rank + Module.finrank ℝ (LinearMap.ker Xc.mulVecLin) =
      Fintype.card {k // k ≠ r} := by
    have := Xc.mulVecLin.finrank_range_add_finrank_ker
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have hB := rank_incidenceMatrix_add_card
    (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2)
  have hrank : Xc.rank = (incidenceMatrix (fun e : ArmContrast arms base => base e.1.1.1)
      (fun e => e.1.1.2)).rank := rank_reducedDesign _ _ r
  have hcard := card_ne_reference_add_one r
  have hG : Nat.card (armContrastGraph arms base).ConnectedComponent =
      Nat.card (comparisonGraph (fun e : ArmContrast arms base => base e.1.1.1)
        (fun e => e.1.1.2)).ConnectedComponent := rfl
  omega

/-- **Rank and invertibility of the arm design exactly for a connected network**: `X` has full
column rank `J + (T - 1)`, and `Xᵀ V⁻¹ X` is invertible for a positive definite `V`, if and only
if the network of within-study contrasts is connected. -/
theorem rank_armDesign_iff {arms : J → Finset K} {base : J → K}
    (hbase : ∀ j, base j ∈ arms j) (r : K) {V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ}
    (hV : V.PosDef) :
    ((armDesign arms base r).rank = Fintype.card (J ⊕ {k // k ≠ r}) ↔
        (armContrastGraph arms base).Connected) ∧
      (IsUnit ((armDesign arms base r)ᵀ * V⁻¹ * armDesign arms base r) ↔
        (armContrastGraph arms base).Connected) := by
  rw [rank_eq_card_iff_injective_mulVec, isUnit_transpose_mul_mul_iff hV.inv,
    armDesign_injective_iff hbase r]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **A relative effect across components is not identified in the arm based model**: if `a`
and `b` lie in different components of the network of within-study contrasts, then for all
study intercepts `μ` and basic parameters `d` there is `d'` with the same arm means and a
different relative effect `d̃'_b - d̃'_a`. -/
theorem armDesign_exists_ne_relativeEffect {arms : J → Finset K} {base : J → K} (r : K)
    {a b : K} (hab : ¬(armContrastGraph arms base).Reachable a b) (μ : J → ℝ)
    (d : {k // k ≠ r} → ℝ) :
    ∃ d', armDesign arms base r *ᵥ Sum.elim μ d' = armDesign arms base r *ᵥ Sum.elim μ d ∧
      padReference r d' b - padReference r d' a ≠ padReference r d b - padReference r d a := by
  obtain ⟨d', hd', hne⟩ := exists_ne_relativeEffect_of_not_reachable
    (tail := fun e : ArmContrast arms base => base e.1.1.1) (head := fun e => e.1.1.2) r hab d
  refine ⟨d', funext fun x => ?_, hne⟩
  rw [armDesign_mulVec, armDesign_mulVec]
  simp only [Sum.elim_inl, Sum.elim_comp_inr]
  by_cases hx : x.1.2 = base x.1.1
  · rw [hx, sub_self, sub_self]
  · have h := congrFun hd' ⟨x, hx⟩
    rw [reducedDesign_mulVec_apply, reducedDesign_mulVec_apply] at h
    rw [h]

/-- The **baseline shift parameterization**: `θ_{jk} = μ_j + δ_{jk}`, with `δ = 0` on the
baseline arm, from study baselines `μ` and within-study contrasts `δ`. -/
def baselineShiftMean {arms : J → Finset K} (base : J → K) (μ : J → ℝ)
    (δ : ArmContrast arms base → ℝ) (a : ArmIndex arms) : ℝ :=
  μ a.1.1 + if h : a.1.2 = base a.1.1 then 0 else δ ⟨a, h⟩

/-- The **baseline shift coordinates** `(θ_{j, base j}, θ_{jk} - θ_{j, base j})` of an arm mean
vector. -/
def baselineShiftCoords {arms : J → Finset K} {base : J → K} (hbase : ∀ j, base j ∈ arms j)
    (θ : ArmIndex arms → ℝ) : (J → ℝ) × (ArmContrast arms base → ℝ) :=
  (fun j => θ ⟨(j, base j), hbase j⟩, fun e => θ e.1 - θ ⟨(e.1.1.1, base e.1.1.1), hbase _⟩)

omit [Fintype J] [Fintype K] [DecidableEq J] in
/-- **The baseline shift parameterization is a relabeling of the arm means**: the coordinates
and the baseline shift means are mutually inverse. -/
theorem baselineShift_inverse {arms : J → Finset K} {base : J → K}
    (hbase : ∀ j, base j ∈ arms j) :
    (∀ θ, baselineShiftMean base (baselineShiftCoords hbase θ).1 (baselineShiftCoords hbase θ).2
        = θ) ∧
      ∀ μ δ, baselineShiftCoords hbase (baselineShiftMean (arms := arms) base μ δ) = (μ, δ) := by
  refine ⟨fun θ => funext fun a => ?_, fun μ δ => ?_⟩
  · simp only [baselineShiftMean, baselineShiftCoords]
    split_ifs with h
    · rw [add_zero]
      exact congrArg θ (Subtype.ext (Prod.ext rfl h.symm))
    · ring
  · refine Prod.ext (funext fun j => ?_) (funext fun e => ?_)
    · simp [baselineShiftCoords, baselineShiftMean]
    · simp [baselineShiftCoords, baselineShiftMean, e.2]

omit [DecidableEq J] in
/-- **The contrast count**: `C + J = N`, for `N` arms, `J` studies and `C` within-study
contrasts, when every study contains its baseline arm. -/
theorem card_armContrast_add {arms : J → Finset K} {base : J → K}
    (hbase : ∀ j, base j ∈ arms j) :
    Fintype.card (ArmContrast arms base) + Fintype.card J = Fintype.card (ArmIndex arms) := by
  let e : {a : ArmIndex arms // a.1.2 = base a.1.1} ≃ J :=
    { toFun := fun a => a.1.1.1
      invFun := fun j => ⟨⟨(j, base j), hbase j⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨⟨j, k⟩, hk⟩, h⟩
        simp only at h
        subst h
        rfl
      right_inv := fun j => rfl }
  rw [← Fintype.card_congr e, add_comm, ← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.sumCompl _)

/-- **The arm based fixed effect model**: for arm estimates following a linear model with the
arm design of a connected network and a positive definite covariance, the generalized least
squares estimate of the study intercepts and basic parameters is unbiased with covariance
`(Xᵀ V⁻¹ X)⁻¹`, and every linear unbiased estimator has a covariance at least as large in the
positive semidefinite order. -/
theorem armModel_gauss_markov {Ω : Type*} [MeasurableSpace Ω] {arms : J → Finset K}
    {base : J → K} (hbase : ∀ j, base j ∈ arms j) {r : K}
    {P : (J ⊕ {k // k ≠ r} → ℝ) → Measure Ω} {Y : ArmIndex arms → Ω → ℝ}
    {V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ}
    (h : IsLinearModel (ArmIndex arms) P Y (armDesign arms base r) V) (hV : V.PosDef)
    (hcon : (armContrastGraph arms base).Connected) (β : J ⊕ {k // k ≠ r} → ℝ) :
    (∀ c, ∫ ω, glsEstimate (armDesign arms base r) V (fun a => Y a ω) c ∂P β = β c) ∧
      covMatrix (P β) (fun c ω => glsEstimate (armDesign arms base r) V (fun a => Y a ω) c) =
        ((armDesign arms base r)ᵀ * V⁻¹ * armDesign arms base r)⁻¹ ∧
      ∀ A : Matrix (J ⊕ {k // k ≠ r}) (ArmIndex arms) ℝ,
        (∀ β' c, ∫ ω, (A *ᵥ fun a => Y a ω) c ∂P β' = β' c) →
        (covMatrix (P β) (fun c ω => (A *ᵥ fun a => Y a ω) c) -
          covMatrix (P β) (fun c ω =>
            glsEstimate (armDesign arms base r) V (fun a => Y a ω) c)).PosSemidef := by
  have hX := (armDesign_injective_iff hbase r).2 hcon
  exact ⟨h.integral_glsEstimate hV hX β, h.covMatrix_glsEstimate hV hX β,
    fun A hA => (h.gauss_markov hV hX hA β).1⟩

end Arm

end NetworkMetaAnalysis

end CausalInference
