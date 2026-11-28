/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.Pooling
public import CausalInference.Estimation.LimitLaws

/-!
# Node splitting: direct against indirect evidence

In the triangle with comparisons `a → b`, `a → c`, `b → c` and estimates `y_ab, y_ac, y_bc`,
the comparison `a → b` is **split**: its direct estimate `y_ab` estimates a direct parameter
`d_ab^dir`, and the indirect estimate `y_ac - y_bc` (`indirectEstimate`) estimates the indirect
parameter `d_ac - d_bc`. The **inconsistency** is `ω = d_ab^dir - (d_ac - d_bc)`, estimated by
`ω̂ = y_ab - (y_ac - y_bc)` (`inconsistencyEstimate`).

* **The split model** (`nodeSplitDesign`): parameters `(d_ab, d_ac, ω)`, means
  `(d_ab + ω, d_ac, d_ac - d_ab)`; with `ω = 0` it is the consistency model of the triangle
  (`nodeSplitDesign_mulVec_zero`). It is saturated, and for every positive definite covariance
  its generalized least squares estimate is `(y_ac - y_bc, y_ac, ω̂)`
  (`glsEstimate_nodeSplitDesign`).
* **Moments** (`inconsistencyEstimate_moments`): for square integrable, pairwise uncorrelated
  estimates, the indirect estimate has mean `d_ac - d_bc` and variance `v_ac + v_bc`, and `ω̂`
  has mean `ω` and variance `v_ab + v_ac + v_bc`.
* **Exact law** (`hasLaw_inconsistencyEstimate`): for independent Gaussian estimates with known
  variances, `ω̂ ~ N(ω, v)` with `v = v_ab + v_ac + v_bc`, and the standardized statistic
  `ω̂ / √v` has the law `N(ω / √v, 1)`: standard normal under consistency, shifted by `ω / √v`
  under inconsistency.
* **Relation to the network estimate** (`triangle_direct_eq_pooled_add`,
  `covariance_glsEstimate_inconsistencyEstimate`): the network estimate of the consistency model
  is the inverse variance pooling of the direct and the indirect estimate (the
  `triangle_pooling`); the direct estimate is the pooled estimate plus
  `v_ab / (v_ab + v_ac + v_bc) ω̂` and the indirect estimate the pooled estimate minus
  `(v_ac + v_bc) / (v_ab + v_ac + v_bc) ω̂`; and the split difference `ω̂` is uncorrelated with
  the pooled estimate.
* **Asymptotic version** (`tendstoInDistribution_inconsistencyStat`): without Gaussian errors,
  if a limit theorem gives `r_n (ω̂_n - ω) → N(0, v)` in distribution and the standard error is
  ratio consistent, `r_n SE_n → √v` in probability, with `r_n ≠ 0`, then
  `(ω̂_n - ω) / SE_n → N(0, 1)`; under consistency this is the statistic `ω̂_n / SE_n`.

## Main definitions

* `inconsistencyEstimate`, `nodeSplitDesign`.

## Main results

* `nodeSplitDesign_mulVec`, `nodeSplitDesign_mulVec_zero`, `glsEstimate_eq_of_mulVec_eq`,
  `glsEstimate_nodeSplitDesign`, `nodeSplit_isLinearModel_estimate`.
* `inconsistencyEstimate_moments`, `hasLaw_inconsistencyEstimate`.
* `triangle_direct_eq_pooled_add`, `covariance_glsEstimate_inconsistencyEstimate`.
* `tendstoInDistribution_inconsistencyStat`.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
* S. Dias, N. J. Welton, D. M. Caldwell and A. E. Ades, *Checking consistency in mixed treatment
  comparison meta-analysis*, Statistics in Medicine 29 (2010).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError MetaAnalysis
  IndirectComparison Filter
open scoped NNReal

/-! ### The split model -/

section Design

/-- The **inconsistency estimate** of a node split: the direct estimate minus the indirect
estimate, `ω̂ = y_ab - (y_ac - y_bc)`. -/
def inconsistencyEstimate {Ω : Type*} (yab yac ybc : Ω → ℝ) : Ω → ℝ :=
  fun ω => yab ω - indirectEstimate yac ybc ω

/-- The **design of the node split model** of the triangle in the parameters `(d_ab, d_ac, ω)`:
the comparison `a → b` has mean `d_ab + ω`, `a → c` has mean `d_ac`, `b → c` has mean
`d_ac - d_ab`. -/
def nodeSplitDesign : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 1; 0, 1, 0; -1, 1, 0]

theorem nodeSplitDesign_mulVec (β : Fin 3 → ℝ) :
    nodeSplitDesign *ᵥ β = ![β 0 + β 2, β 1, β 1 - β 0] := by
  funext e
  fin_cases e <;> simp [nodeSplitDesign, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- **Without inconsistency the split model is the consistency model** of the triangle. -/
theorem nodeSplitDesign_mulVec_zero (β : Fin 2 → ℝ) :
    nodeSplitDesign *ᵥ ![β 0, β 1, 0] = triangleDesign *ᵥ β := by
  rw [nodeSplitDesign_mulVec]
  funext e
  fin_cases e <;> simp [triangleDesign, mulVec, dotProduct, Fin.sum_univ_two]
  ring

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- **An exact fit is the generalized least squares estimate**: if `X β = y` and `Xᵀ V⁻¹ X` is
invertible, then `β̂(y) = β`. -/
theorem glsEstimate_eq_of_mulVec_eq {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hM : IsUnit (Xᵀ * V⁻¹ * X)) {y : n → ℝ} {β : p → ℝ} (hβ : X *ᵥ β = y) :
    glsEstimate X V y = β :=
  glsEstimate_eq_of_normal hM (by rw [← hβ, ← mulVec_mulVec, ← mulVec_mulVec])

theorem nodeSplitDesign_injective : Function.Injective nodeSplitDesign.mulVec := by
  intro β β' h
  rw [nodeSplitDesign_mulVec, nodeSplitDesign_mulVec] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp at h0 h1 h2
  funext i
  fin_cases i <;> simp <;> linarith

/-- **The split model is saturated**: for every positive definite covariance, its generalized
least squares estimate is `(y_ac - y_bc, y_ac, y_ab - (y_ac - y_bc))`: the indirect estimate of
`d_ab`, the direct estimate of `d_ac`, and the inconsistency estimate. -/
theorem glsEstimate_nodeSplitDesign {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : V.PosDef)
    (y : Fin 3 → ℝ) :
    glsEstimate nodeSplitDesign V y = ![y 1 - y 2, y 1, y 0 - (y 1 - y 2)] := by
  refine glsEstimate_eq_of_mulVec_eq (isUnit_gram_inv hV nodeSplitDesign_injective) ?_
  rw [nodeSplitDesign_mulVec]
  funext e
  fin_cases e <;> simp

/-- **The split model as a linear model.** In a linear model with the node split design and a
positive definite covariance `V`, the inconsistency estimate is the generalized least squares
estimate of `ω`: it is unbiased for `ω` at every parameter, and it is best linear unbiased. -/
theorem nodeSplit_isLinearModel_estimate {Ω : Type*} [MeasurableSpace Ω]
    {P : (Fin 3 → ℝ) → Measure Ω} {Y : Fin 3 → Ω → ℝ} {V : Matrix (Fin 3) (Fin 3) ℝ}
    (h : IsLinearModel (Fin 3) P Y nodeSplitDesign V) (hV : V.PosDef) (β : Fin 3 → ℝ) :
    (∀ ω, glsEstimate nodeSplitDesign V (fun e => Y e ω) 2 =
      inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω) ∧
      ∫ ω, inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω ∂P β = β 2 ∧
      ∀ a : Fin 3 → ℝ, (∀ β', ∫ ω, a ⬝ᵥ (fun e => Y e ω) ∂P β' = β' 2) →
        Var[fun ω => inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω; P β] ≤
          Var[fun ω => a ⬝ᵥ (fun e => Y e ω); P β] := by
  have hpt : ∀ ω, glsEstimate nodeSplitDesign V (fun e => Y e ω) 2 =
      inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω := fun ω => by
    rw [glsEstimate_nodeSplitDesign hV]; rfl
  have hfun : (fun ω => inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω) =
      fun ω => (Pi.single 2 1 : Fin 3 → ℝ) ⬝ᵥ glsEstimate nodeSplitDesign V (fun e => Y e ω) := by
    funext ω; rw [single_dotProduct, one_mul, hpt]
  refine ⟨hpt, ?_, fun a ha => ?_⟩
  · rw [← funext hpt]
    exact h.integral_glsEstimate hV nodeSplitDesign_injective β 2
  · have hge := h.variance_dotProduct_ge hV nodeSplitDesign_injective (Pi.single 2 1) (a := a)
      (fun β' => by rw [ha, single_dotProduct, one_mul]) β
    rw [hfun, hge.2.1]
    exact hge.2.2.1

end Design

/-! ### Moments and the exact law -/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The moments of a node split** (Bucher et al. 1997; Dias et al. 2010). For square
integrable, pairwise uncorrelated estimates `y_ab, y_ac, y_bc` with means `d_ab^dir, d_ac, d_bc`
and variances `v_ab, v_ac, v_bc`, the indirect estimate has mean `d_ac - d_bc` and variance
`v_ac + v_bc`, the inconsistency estimate has mean `ω = d_ab^dir - (d_ac - d_bc)` and variance
`v_ab + v_ac + v_bc`. -/
theorem inconsistencyEstimate_moments [IsProbabilityMeasure P] {yab yac ybc : Ω → ℝ}
    (hab : MemLp yab 2 P) (hac : MemLp yac 2 P) (hbc : MemLp ybc 2 P)
    (h1 : cov[yab, yac; P] = 0) (h2 : cov[yab, ybc; P] = 0) (h3 : cov[yac, ybc; P] = 0) :
    ∫ ω, indirectEstimate yac ybc ω ∂P = (∫ ω, yac ω ∂P) - ∫ ω, ybc ω ∂P ∧
      Var[indirectEstimate yac ybc; P] = Var[yac; P] + Var[ybc; P] ∧
      ∫ ω, inconsistencyEstimate yab yac ybc ω ∂P =
        (∫ ω, yab ω ∂P) - ((∫ ω, yac ω ∂P) - ∫ ω, ybc ω ∂P) ∧
      Var[inconsistencyEstimate yab yac ybc; P] = Var[yab; P] + Var[yac; P] + Var[ybc; P] := by
  have hsub : MemLp (fun ω => yac ω - ybc ω) 2 P := hac.sub hbc
  have hE : ∫ ω, indirectEstimate yac ybc ω ∂P = (∫ ω, yac ω ∂P) - ∫ ω, ybc ω ∂P :=
    integral_sub (hac.integrable one_le_two) (hbc.integrable one_le_two)
  refine ⟨hE, variance_indirectEstimate hac hbc h3, ?_, ?_⟩
  · change ∫ ω, yab ω - indirectEstimate yac ybc ω ∂P = _
    rw [integral_sub (f := yab) (g := indirectEstimate yac ybc) (hab.integrable one_le_two)
      (hsub.integrable one_le_two), hE]
  · change Var[fun ω => yab ω - (yac ω - ybc ω); P] = _
    rw [variance_fun_sub hab hsub, variance_fun_sub hac hbc, covariance_fun_sub_right hab hac hbc,
      h1, h2, h3]
    ring

/-- **The exact law of the node split statistic** under independent Gaussian estimates with
known variances (Dias et al. 2010). If `y_ab, y_ac, y_bc` are independent with laws
`N(m_ab, v_ab)`, `N(m_ac, v_ac)`, `N(m_bc, v_bc)` and `v = v_ab + v_ac + v_bc > 0`, then
`ω̂ ~ N(ω, v)` with `ω = m_ab - (m_ac - m_bc)`, and `ω̂ / √v ~ N(ω / √v, 1)`; under consistency
(`ω = 0`) the statistic is standard normal. -/
theorem hasLaw_inconsistencyEstimate [IsProbabilityMeasure P] {Y : Fin 3 → Ω → ℝ}
    (hind : iIndepFun Y P) {m : Fin 3 → ℝ} {v : Fin 3 → ℝ≥0}
    (hlaw : ∀ i, HasLaw (Y i) (gaussianReal (m i) (v i)) P) (hv : 0 < v 0 + v 1 + v 2) :
    HasLaw (inconsistencyEstimate (Y 0) (Y 1) (Y 2))
        (gaussianReal (m 0 - (m 1 - m 2)) (v 0 + v 1 + v 2)) P ∧
      HasLaw (fun ω => inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω /
          Real.sqrt ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ))
        (gaussianReal ((m 0 - (m 1 - m 2)) / Real.sqrt ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)) 1) P ∧
      (m 0 = m 1 - m 2 → HasLaw (fun ω => inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω /
          Real.sqrt ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ)) (gaussianReal 0 1) P) := by
  have hmeas : ∀ i, AEMeasurable (Y i) P := fun i => (hlaw i).aemeasurable
  -- the law of `-y_ac + y_bc`
  have hneg : HasLaw (fun ω => -Y 1 ω) (gaussianReal (-m 1) (v 1)) P :=
    HasLaw.comp (X := Y 1) (Y := fun x => -x) ⟨by fun_prop, gaussianReal_map_neg⟩ (hlaw 1)
  have hI : HasLaw ((fun ω => -Y 1 ω) + Y 2) (gaussianReal (-m 1 + m 2) (v 1 + v 2)) P :=
    ⟨hneg.aemeasurable.add (hmeas 2), gaussianReal_add_gaussianReal_of_indepFun
      ((hind.indepFun (show (1 : Fin 3) ≠ 2 by decide)).comp measurable_neg measurable_id)
      hneg (hlaw 2)⟩
  -- independence of `y_ab` and `-y_ac + y_bc`
  have hpair := hind.indepFun_prodMk₀ hmeas 1 2 0 (by decide) (by decide)
  have hind0 : IndepFun (Y 0) ((fun ω => -Y 1 ω) + Y 2) P := by
    have := (hpair.comp₀ ((hmeas 1).prodMk (hmeas 2)) (hmeas 0)
      (φ := fun q : ℝ × ℝ => -q.1 + q.2) (ψ := id) (by fun_prop) (by fun_prop)).symm
    exact this
  have hW : HasLaw (Y 0 + ((fun ω => -Y 1 ω) + Y 2))
      (gaussianReal (m 0 + (-m 1 + m 2)) (v 0 + (v 1 + v 2))) P :=
    ⟨(hmeas 0).add hI.aemeasurable, gaussianReal_add_gaussianReal_of_indepFun hind0 (hlaw 0) hI⟩
  have hO : HasLaw (inconsistencyEstimate (Y 0) (Y 1) (Y 2))
      (gaussianReal (m 0 - (m 1 - m 2)) (v 0 + v 1 + v 2)) P := by
    have e1 : m 0 + (-m 1 + m 2) = m 0 - (m 1 - m 2) := by ring
    have e2 : v 0 + (v 1 + v 2) = v 0 + v 1 + v 2 := by rw [add_assoc]
    rw [e1, e2] at hW
    refine hW.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [inconsistencyEstimate, indirectEstimate, Pi.add_apply]
    ring
  set s := Real.sqrt ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) with hs
  have hvR : (0 : ℝ) < ((v 0 + v 1 + v 2 : ℝ≥0) : ℝ) := by exact_mod_cast hv
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 hvR).ne'
  have hZ : HasLaw (fun ω => inconsistencyEstimate (Y 0) (Y 1) (Y 2) ω / s)
      (gaussianReal ((m 0 - (m 1 - m 2)) / s) 1) P := by
    have h := HasLaw.comp (X := inconsistencyEstimate (Y 0) (Y 1) (Y 2)) (Y := fun x => x / s)
      ⟨by fun_prop, gaussianReal_map_div_const s⟩ hO
    convert h using 2
    all_goals first
      | rfl
      | (ext; rw [NNReal.coe_div, NNReal.coe_mk, hs, Real.sq_sqrt hvR.le, div_self hvR.ne',
          NNReal.coe_one])
  refine ⟨hO, hZ, fun h0 => ?_⟩
  rw [h0, sub_self, zero_div] at hZ
  exact hZ

end Law

/-! ### Relation to the network estimate of the triangle -/

section Triangle

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The direct and the indirect estimate around the network estimate.** For positive variances
`v`, the direct estimate is the network estimate of `d_ab` of the consistency model plus
`v_ab / (v_ab + v_ac + v_bc) ω̂`, and the indirect estimate is the network estimate minus
`(v_ac + v_bc) / (v_ab + v_ac + v_bc) ω̂`. -/
theorem triangle_direct_eq_pooled_add {v : Fin 3 → ℝ} (hv : ∀ i, 0 < v i) (y : Fin 3 → ℝ) :
    y 0 = glsEstimate triangleDesign (diagonal v) y 0 +
        v 0 / (v 0 + v 1 + v 2) * (y 0 - (y 1 - y 2)) ∧
      y 1 - y 2 = glsEstimate triangleDesign (diagonal v) y 0 -
        (v 1 + v 2) / (v 0 + v 1 + v 2) * (y 0 - (y 1 - y 2)) := by
  have hv0 := hv 0
  have hv1 := hv 1
  have hv2 := hv 2
  rw [(triangle_glsEstimate hv y).1, ivwEstimate_two hv0 (by positivity)]
  have hS : v 0 + v 1 + v 2 ≠ 0 := by positivity
  have hS' : v 0 + (v 1 + v 2) ≠ 0 := by positivity
  constructor <;> field_simp <;> ring

/-- **The split difference is uncorrelated with the network estimate.** For square integrable,
pairwise uncorrelated comparison estimates with variances `v > 0`, the inconsistency estimate
`ω̂` and the network estimate of `d_ab` of the consistency model (the inverse variance pooling
of the direct and the indirect estimate) have covariance zero. -/
theorem covariance_glsEstimate_inconsistencyEstimate [IsFiniteMeasure P] {Y : Fin 3 → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 2 P) {v : Fin 3 → ℝ} (hv : ∀ i, 0 < v i)
    (hvar : ∀ i, Var[Y i; P] = v i) (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    cov[fun ω => glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0,
      inconsistencyEstimate (Y 0) (Y 1) (Y 2); P] = 0 := by
  have hv0 := hv 0
  have hv1 := hv 1
  have hv2 := hv 2
  have hS : v 0 + (v 1 + v 2) ≠ 0 := by positivity
  set a : Fin 3 → ℝ := ![(v 1 + v 2) / (v 0 + (v 1 + v 2)), v 0 / (v 0 + (v 1 + v 2)),
    -(v 0 / (v 0 + (v 1 + v 2)))] with ha
  set b : Fin 3 → ℝ := ![1, -1, 1] with hb
  have hfun : (fun ω => glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0) =
      fun ω => ∑ i, a i * Y i ω := by
    funext ω
    rw [(triangle_glsEstimate hv _).1, ivwEstimate_two hv0 (by positivity)]
    simp only [Fin.sum_univ_three, ha, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
    ring
  have hfun2 : inconsistencyEstimate (Y 0) (Y 1) (Y 2) = fun ω => ∑ i, b i * Y i ω := by
    funext ω
    simp only [inconsistencyEstimate, indirectEstimate, Fin.sum_univ_three, hb,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    ring
  have hcv : ∀ i j, cov[Y i, Y j; P] = if i = j then v i else 0 := fun i j => by
    by_cases h : i = j
    · subst h; rw [covariance_self (hY i).aestronglyMeasurable.aemeasurable, hvar]; simp
    · rw [hunc i j h]; simp [h]
  rw [hfun, hfun2, covariance_fun_sum_fun_sum (X := fun i ω => a i * Y i ω)
    (Y := fun i ω => b i * Y i ω) (fun i => (hY i).const_mul _) (fun i => (hY i).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hcv, Fin.sum_univ_three]
  simp [ha, hb]
  field_simp
  ring

end Triangle

/-! ### The asymptotic version -/

section Asymptotic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **The node split statistic is asymptotically standard normal under a stated limit theorem.**
Let `ω̂_n` be inconsistency estimates and `SE_n` standard errors, `r_n ≠ 0` rates, and suppose
that `r_n (ω̂_n - ω) → Z` in distribution with `Z ~ N(0, v)`, `v > 0` (the limit theorem), and
that `r_n SE_n → √v` in probability (ratio consistency of the standard error). Then
`(ω̂_n - ω) / SE_n → N(0, 1)` in distribution; under consistency, `ω = 0`, this is the node
split statistic `ω̂_n / SE_n`. -/
theorem tendstoInDistribution_inconsistencyStat {est SE : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (hr : ∀ n, r n ≠ 0) {ω₀ : ℝ} {v : ℝ≥0} (hv : 0 < v) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 v) P')
    (hclt : TendstoInDistribution (fun n ω => r n * (est n ω - ω₀)) atTop Z (fun _ => μ) P')
    (hSE : TendstoInMeasure μ (fun n ω => r n * SE n ω) atTop
      (fun _ => Real.sqrt (v : ℝ)))
    (hSEm : ∀ n, AEMeasurable (SE n) μ) :
    TendstoInDistribution (fun n ω => (est n ω - ω₀) / SE n ω) atTop (fun ω => Z ω /
      Real.sqrt (v : ℝ)) (fun _ => μ) P' ∧
      HasLaw (fun ω => Z ω / Real.sqrt (v : ℝ)) (gaussianReal 0 1) P' := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hs0 : Real.sqrt (v : ℝ) ≠ 0 := (Real.sqrt_pos.2 hvR).ne'
  have key := hclt.div_tendstoInMeasure_const hs0 hSE fun n => (hSEm n).const_mul _
  have e : (fun n ω => r n * (est n ω - ω₀) / (r n * SE n ω)) =
      fun n ω => (est n ω - ω₀) / SE n ω := by
    funext n ω
    exact mul_div_mul_left _ _ (hr n)
  rw [e] at key
  refine ⟨key, ?_⟩
  have h := HasLaw.comp (X := Z) (Y := fun x => x / Real.sqrt (v : ℝ))
    ⟨by fun_prop, gaussianReal_map_div_const _⟩ hZ
  rw [zero_div] at h
  convert h using 2
  all_goals first
    | rfl
    | (ext; rw [NNReal.coe_div, NNReal.coe_mk, Real.sq_sqrt hvR.le, div_self hvR.ne',
        NNReal.coe_one])

end Asymptotic

end NetworkMetaAnalysis

end CausalInference
