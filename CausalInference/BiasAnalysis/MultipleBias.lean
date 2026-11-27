/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.SelectionAdjustment
public import CausalInference.BiasAnalysis.ExternalAdjustment
public import CausalInference.BiasAnalysis.MisclassificationTables
public import CausalInference.BiasAnalysis.MisclassificationMatrix

/-!
# Multiple bias modeling

Serial bias adjustment for misclassification, selection bias and an unmeasured confounder on
two by two tables, following Fox, MacLehose and Lash (2021), Chapter 12 ("Order of Bias
Adjustments", "Serial Multiple Bias Analysis, Simple Methods") and Chapter 2 ("Order of Bias
Analysis Adjustments"). The three corrections are those of `MisclassificationTables`
(Table 6.8), `SelectionAdjustment` (inverse probability of participation weighting, Equations
4.2 and 12.1) and `ExternalAdjustment` (the case-control projection and the Mantel and Haenszel
summary of Table 12.5); this file composes them and does not redefine them.

## Conventions

Tables are disease first, `t d e`, as in `SelectionAdjustment.Table`. `MisclassificationTables`
indexes tables exposure first and `MisclassificationMatrix` uses vectors indexed by `(e, d)`;
`toExposureFirst`, `toDiseaseFirst` and `toVec` pass between them, and `misclassify`,
`misCorrect` are the exposure misclassification model and its correction transported to the
disease first convention. `confoundingStrata` is the case-control projection of a table onto a
binary confounder and `mhOR` the Mantel and Haenszel odds ratio of the resulting strata.

## Main results

* `toVec_misCorrect`, `toVec_misclassify`, `oddsRatio_misCorrect`: the transported correction is
  the matrix method (Equations 6.11 and 6.12) and has the closed form odds ratio of Chapter 6.
* Order of selection and misclassification adjustments: `misCorrect_ipw_of_disease_only`
  (selection depending on disease only commutes with the misclassification correction) and
  `selected_misclassify_of_disease_only` (the mechanisms commute as well);
  `misCorrect_ipw_comm_iff`: with imperfect specificity, the two corrections commute on every
  table if and only if selection does not depend on exposure.
* Order of selection and confounder adjustments: `splitCases_smul`, `confoundingStrata_ipw`: the
  projection commutes with any reweighting of the cells, so these adjustments always commute.
* `mhOR_confoundingStrata`, `confoundingStrata_collapse`: the projection multiplies the odds
  ratio by `(ψ p₀ + 1 - p₀) / (ψ p₁ + 1 - p₁)` and recovers a stratified table with the stated
  prevalences and confounder to disease odds ratio.
* Composition in the reverse order of the data generation: `generate` (confounding, then
  selection, then misclassification) and `serialAdjust` (the corrections in reverse order);
  `serialAdjust_generate`: the serial adjustment recovers the stratified source table;
  `mhOR_serialAdjust_generate`: its Mantel and Haenszel odds ratio is the confounder-adjusted
  odds ratio of the source; `mhOR_serialAdjust`: in general it is the misclassification corrected
  odds ratio divided by the selection odds ratio times the confounding factor;
  `misCorrect_ipw_selected_misclassify`: if the misclassification arose first, the other order
  of corrections is the right one.
* Worked example (namespace `Examples`): the Chien et al. data of Tables 12.1 to 12.5, chained
  through the three corrections with every parameter computed from the book's inputs
  (Table 12.2 and Equation 12.1). `table123_eq`, `table124_eq`, `chien_serial`,
  `table125_values` reproduce Tables 12.3 to 12.5; `chien_order_matters` (odds ratio `1.447`
  against `1.353`), `chien_serial_reversed` and `chien_confounding_misclassification_order`
  show orders of adjustment that give different answers.

## Printed values

All values were recomputed in exact rational arithmetic. Tables 12.3 to 12.5 and the reversed
order value `1.35` are confirmed to printed rounding; Table 12.3 reproduces only with the exact
validation fractions, not with the rounded percentages of the text
(`table123_rounded_parameters`), and one cell of Table 12.5 is `354.66`, printed `354.6`. The
text after Table 12.5 calls `1.40` the odds ratio adjusted "for selection bias and
misclassification"; it is adjusted for all three biases. Column β of Table 12.6 does not follow
from scenario β as defined (`table126_beta`: `1.18`, `1.58` and `1.40` against the printed
`1.20`, `1.61` and `1.43` for rows A and B).

## References

* M. P. Fox, R. F. MacLehose and T. L. Lash, *Applying Quantitative Bias Analysis to
  Epidemiologic Data*, second edition, Springer (2021), Chapters 2 and 12.
* Chien et al. (2006) and Boudreau et al. (2004), as cited there for the observed and
  validation data of the example.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace MultipleBias

open SelectionAdjustment MisclassificationTables ExternalAdjustment

open scoped Matrix

/-! ### Passing between the table conventions -/

/-- The exposure first form `q e d = t d e` of a disease first table `t d e`: the convention of
`MisclassificationTables` from that of `SelectionAdjustment`. -/
def toExposureFirst (t : Table) : Bool → Bool → ℝ := fun e d ↦ t d e

/-- The disease first form `t d e = q e d` of an exposure first table `q e d`. -/
def toDiseaseFirst (q : Bool → Bool → ℝ) : Table := fun d e ↦ q e d

@[simp] theorem toDiseaseFirst_toExposureFirst (t : Table) :
    toDiseaseFirst (toExposureFirst t) = t := rfl

@[simp] theorem toExposureFirst_toDiseaseFirst (q : Bool → Bool → ℝ) :
    toExposureFirst (toDiseaseFirst q) = q := rfl

/-- The two odds ratios agree: `oddsRatio t` of `SelectionAdjustment` is the cross product
ratio `crossOddsRatio` of `MisclassificationTables` of the exposure first form. -/
theorem oddsRatio_eq_crossOddsRatio (t : Table) :
    oddsRatio t = crossOddsRatio (toExposureFirst t) := rfl

/-! ### Misclassification on disease first tables -/

/-- The expected observed table, in the disease first convention, when the exposure of the
table `t d e` is classified with sensitivity `se d` and specificity `sp d` in disease row `d`
(`MisclassificationTables.exposureMisclassifiedDiff`, Table 6.5). -/
def misclassify (se sp : Bool → ℝ) (t : Table) : Table :=
  toDiseaseFirst (exposureMisclassifiedDiff (toExposureFirst t) se sp)

/-- The exposure misclassification correction of Table 6.8 in the disease first convention
(`MisclassificationTables.exposureCorrected`). -/
noncomputable def misCorrect (se sp : Bool → ℝ) (t : Table) : Table :=
  toDiseaseFirst (exposureCorrected (toExposureFirst t) se sp)

theorem misclassify_true (se sp : Bool → ℝ) (t : Table) (d : Bool) :
    misclassify se sp t d true = t d true * se d + t d false * (1 - sp d) :=
  exposureMisclassifiedDiff_exposed _ se sp d

theorem misclassify_false (se sp : Bool → ℝ) (t : Table) (d : Bool) :
    misclassify se sp t d false = t d true * (1 - se d) + t d false * sp d :=
  exposureMisclassifiedDiff_unexposed _ se sp d

theorem misCorrect_true (se sp : Bool → ℝ) (t : Table) (d : Bool) :
    misCorrect se sp t d true =
      (t d true - (t d true + t d false) * (1 - sp d)) / (se d + sp d - 1) := rfl

theorem misCorrect_false (se sp : Bool → ℝ) (t : Table) (d : Bool) :
    misCorrect se sp t d false = t d true + t d false -
      (t d true - (t d true + t d false) * (1 - sp d)) / (se d + sp d - 1) := rfl

/-- The correction recovers the true table from the expected observed table when
`SE_d + SP_d ≠ 1` (`exposureCorrected_misclassified`). -/
theorem misCorrect_misclassify (se sp : Bool → ℝ) (h : ∀ d, se d + sp d ≠ 1) (t : Table) :
    misCorrect se sp (misclassify se sp t) = t := by
  unfold misCorrect misclassify
  rw [toExposureFirst_toDiseaseFirst, exposureCorrected_misclassified _ se sp h,
    toDiseaseFirst_toExposureFirst]

/-- The odds ratio of the corrected table, in closed form (`crossOddsRatio_exposureCorrected`):
`(P₁ + SP₁ - 1)(SE₀ - P₀) / ((P₀ + SP₀ - 1)(SE₁ - P₁))` with `P_d` the observed exposed
proportion of disease row `d`. -/
theorem oddsRatio_misCorrect (se sp : Bool → ℝ) (t : Table) (h1 : t true true + t true false ≠ 0)
    (h0 : t false true + t false false ≠ 0) (hk : ∀ d, se d + sp d ≠ 1) :
    oddsRatio (misCorrect se sp t) =
      (exposedProportion (toExposureFirst t) true + sp true - 1) *
          (se false - exposedProportion (toExposureFirst t) false) /
        ((exposedProportion (toExposureFirst t) false + sp false - 1) *
          (se true - exposedProportion (toExposureFirst t) true)) :=
  crossOddsRatio_exposureCorrected _ se sp h1 h0 hk

/-- The cells of a disease first table as a vector indexed by `(e, d)`, the convention of
`MisclassificationMatrix`. -/
def toVec (t : Table) : Bool × Bool → ℝ := fun i ↦ t i.2 i.1

/-- The correction of Table 6.8 is the matrix method (Equation 6.12) with the block diagonal
exposure classification matrix of `MisclassificationMatrix` (`exposure_inv_mulVec`). -/
theorem toVec_misCorrect (se sp : Bool → ℝ) (h : ∀ d, se d + sp d ≠ 1) (t : Table) :
    toVec (misCorrect se sp t) =
      (MisclassificationMatrix.jointMatrix
        (fun d ↦ MisclassificationMatrix.binaryMatrix (se d) (sp d)) 1)⁻¹ *ᵥ toVec t := by
  rw [MisclassificationMatrix.exposure_inv_mulVec se sp h]
  funext ⟨e, d⟩
  cases e <;> rfl

/-- The expected observed table is the classification matrix applied to the true cells
(Equation 6.11). -/
theorem toVec_misclassify (se sp : Bool → ℝ) (t : Table) :
    toVec (misclassify se sp t) =
      MisclassificationMatrix.jointMatrix
        (fun d ↦ MisclassificationMatrix.binaryMatrix (se d) (sp d)) 1 *ᵥ toVec t := by
  funext ⟨e, d⟩
  simp only [toVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool,
    MisclassificationMatrix.jointMatrix_apply, MisclassificationMatrix.binaryMatrix,
    Matrix.one_apply, Bias.binaryKernel]
  cases e <;> cases d <;> simp [misclassify_true, misclassify_false] <;> ring

/-! ### Order of the selection and misclassification adjustments -/

/-- **Disease-only selection commutes with misclassification correction** (the precise content
of the order rule of Fox, MacLehose and Lash 2021, Chapter 12, "Order of Bias Adjustments", for
these two biases). If the selection proportions depend on disease status only,
`S d e = s d`, inverse probability of participation weighting is a scaling of each disease row,
and the rowwise correction of Table 6.8 is linear in the row, so the two adjustments give the
same table in either order. The identity holds for all real `s` and needs no positivity: no
division by `s d` is cancelled. -/
theorem misCorrect_ipw_of_disease_only (se sp s : Bool → ℝ) (t : Table) :
    misCorrect se sp (ipw (fun d _ ↦ s d) t) = ipw (fun d _ ↦ s d) (misCorrect se sp t) := by
  funext d e
  cases e
  · simp only [misCorrect_false, ipw]
    ring
  · simp only [misCorrect_true, ipw]
    ring

/-- The bias mechanisms commute in the same case: selection on disease only and exposure
misclassification give the same observed table in either order. -/
theorem selected_misclassify_of_disease_only (se sp s : Bool → ℝ) (t : Table) :
    selected (fun d _ ↦ s d) (misclassify se sp t) =
      misclassify se sp (selected (fun d _ ↦ s d) t) := by
  funext d e
  cases e
  · simp only [misclassify_false, selected]
    ring
  · simp only [misclassify_true, selected]
    ring

/-- The data-generating form of `misCorrect_ipw_of_disease_only`: if the observed table arises
from a source table by disease-only selection with nonzero proportions followed by exposure
misclassification with `SE_d + SP_d ≠ 1`, both orders of correction recover the source table. -/
theorem misCorrect_ipw_disease_only_recovers (se sp s : Bool → ℝ) (hs : ∀ d, s d ≠ 0)
    (hk : ∀ d, se d + sp d ≠ 1) (src : Table) :
    ipw (fun d _ ↦ s d) (misCorrect se sp (misclassify se sp (selected (fun d _ ↦ s d) src))) =
        src ∧
      misCorrect se sp (ipw (fun d _ ↦ s d) (misclassify se sp (selected (fun d _ ↦ s d) src))) =
        src := by
  have h1 : ipw (fun d _ ↦ s d)
      (misCorrect se sp (misclassify se sp (selected (fun d _ ↦ s d) src))) = src := by
    rw [misCorrect_misclassify se sp hk, ipw_selected _ _ fun d _ ↦ hs d]
  exact ⟨h1, by rw [misCorrect_ipw_of_disease_only, h1]⟩

/-- **The commutation criterion.** With nonzero selection proportions and, in every disease row,
`SE_d + SP_d ≠ 1` and imperfect specificity `SP_d ≠ 1`, correcting for misclassification and
weighting for selection commute on every table if and only if the selection proportions do not
depend on exposure. With exposure-dependent selection the order of the adjustments matters
(`Examples.chien_order_matters` gives the book's instance). -/
theorem misCorrect_ipw_comm_iff (se sp : Bool → ℝ) (S : Table) (hS : ∀ d e, S d e ≠ 0)
    (hk : ∀ d, se d + sp d ≠ 1) (hsp : ∀ d, sp d ≠ 1) :
    (∀ t, misCorrect se sp (ipw S t) = ipw S (misCorrect se sp t)) ↔
      ∀ d, S d true = S d false := by
  constructor
  · intro h d
    have hd := congrFun (congrFun (h fun _ e ↦ if e then 0 else 1) d) true
    simp only [misCorrect_true, ipw, ↓reduceIte, Bool.false_eq_true] at hd
    have hk' : se d + sp d - 1 ≠ 0 := sub_ne_zero.mpr (hk d)
    have hsp' : 1 - sp d ≠ 0 := sub_ne_zero.mpr (hsp d).symm
    have h1 := hS d true
    have h0 := hS d false
    field_simp at hd
    have : (1 - sp d) * (S d true - S d false) = 0 := by linear_combination (-1 : ℝ) * hd
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hsp'
    · exact sub_eq_zero.mp h'
  · intro h t
    have hS' : S = fun d _ ↦ S d false := by
      funext d e
      cases e
      · rfl
      · exact h d
    rw [hS']
    exact misCorrect_ipw_of_disease_only se sp (fun d ↦ S d false) t

/-! ### The unmeasured confounder adjustment on disease first tables -/

/-- The case-control projection of Chapter 5 ("Ratio Measures", case-control text) and Table
12.5 as a map from a disease first table `t d e` to a table stratified by the binary confounder
`c` (first argument): the controls of exposure group `e` are split by the confounder prevalence
`p₁` (exposed) or `p₀` (unexposed), and the cases by Equation 5.5 (`splitCases`) with the
confounder to disease odds ratio `ψ`. -/
noncomputable def confoundingStrata (ψ p₁ p₀ : ℝ) (t : Table) : Bool → Table := fun c d e ↦
  if d then
    (if c then splitCases ψ (t false e * (if e then p₁ else p₀)) (t false e) (t true e)
    else t true e - splitCases ψ (t false e * (if e then p₁ else p₀)) (t false e) (t true e))
  else
    (if c then t false e * (if e then p₁ else p₀)
    else t false e - t false e * (if e then p₁ else p₀))

/-- The table obtained from a stratified table by collapsing over the confounder. -/
def collapse (T : Bool → Table) : Table := fun d e ↦ T true d e + T false d e

/-- The Mantel and Haenszel odds ratio (`ExternalAdjustment.mhOddsRatio`) of a table stratified
by a binary confounder `c`, `T c d e`. -/
noncomputable def mhOR (T : Bool → Table) : ℝ :=
  mhOddsRatio (fun c ↦ T c true true) (fun c ↦ T c true false) (fun c ↦ T c false true)
    (fun c ↦ T c false false)

/-- **The confounder adjustment of a table** (Table 12.5): the Mantel and Haenszel odds ratio of
the projected strata is the crude odds ratio times `(ψ p₀ + 1 - p₀) / (ψ p₁ + 1 - p₁)`
(`mhOddsRatio_projected`). -/
theorem mhOR_confoundingStrata {ψ p₁ p₀ : ℝ} {t : Table} (ht : ∀ d e, 0 < t d e) (hψ : 0 < ψ)
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₀ : 0 < p₀) (hp₀' : p₀ < 1) :
    mhOR (confoundingStrata ψ p₁ p₀ t) = oddsRatio t * (mixFactor ψ p₀ / mixFactor ψ p₁) := by
  have key := mhOddsRatio_projected (ht false true) (ht false false) (ht true true)
    (ht true false) hψ hp₁ hp₁' hp₀ hp₀'
  have e : (t true true / t false true) / (t true false / t false false) = oddsRatio t := by
    have := ht true false; have := ht false true; have := ht false false
    unfold oddsRatio
    field_simp
  rw [e] at key
  rw [← key]
  rfl

/-- **The projection recovers the true strata** (`splitCases_recovers`). Let `T c d e` be a
stratified table with positive cells in which the confounder prevalence among the controls of
exposure group `e` is `p₁` (exposed) or `p₀` (unexposed) and the confounder to disease odds
ratio within each exposure group is `ψ` (written without division,
`T 1 1 e * T 0 0 e = ψ * T 1 0 e * T 0 1 e`). Then projecting the collapsed table returns `T`. -/
theorem confoundingStrata_collapse {ψ p₁ p₀ : ℝ} {T : Bool → Table} (hT : ∀ c d e, 0 < T c d e)
    (hψ : 0 < ψ) (hprev : ∀ e, T true false e = collapse T false e * (if e then p₁ else p₀))
    (hor : ∀ e, T true true e * T false false e = ψ * T true false e * T false true e) :
    confoundingStrata ψ p₁ p₀ (collapse T) = T := by
  have hsplit : ∀ e, splitCases ψ (T true false e) (T true false e + T false false e)
      (T true true e + T false true e) = T true true e := fun e ↦
    splitCases_recovers hψ.le (hT true false e) (hT false false e) (hor e)
  funext c d e
  cases d <;> cases c <;> simp only [confoundingStrata, ↓reduceIte, Bool.false_eq_true,
    ← hprev] <;> simp only [collapse, hsplit] <;> ring

/-- Equation 5.5 commutes with scaling: multiplying the controls by `k ≠ 0` and the cases by
`l` multiplies the projected cases by `l`. -/
theorem splitCases_smul (rr t₁ t x k l : ℝ) (hk : k ≠ 0) :
    splitCases rr (k * t₁) (k * t) (l * x) = l * splitCases rr t₁ t x := by
  unfold splitCases
  rw [show rr * (k * t₁) + k * t - k * t₁ = k * (rr * t₁ + t - t₁) by ring,
    show rr * (k * t₁) * (l * x) = k * (l * (rr * t₁ * x)) by ring, mul_div_mul_left _ _ hk]
  ring

/-- **The selection and confounder adjustments commute.** Weighting the cells by `1 / S d e`
before the projection gives the projection of the unweighted table with each stratum weighted by
the same proportions (the selection proportions do not depend on the confounder), for nonzero
selection proportions of the controls. -/
theorem confoundingStrata_ipw (ψ p₁ p₀ : ℝ) (S t : Table) (hS : ∀ e, S false e ≠ 0) :
    confoundingStrata ψ p₁ p₀ (ipw S t) = fun c ↦ ipw S (confoundingStrata ψ p₁ p₀ t c) := by
  have hsplit : ∀ e, splitCases ψ (ipw S t false e * (if e then p₁ else p₀)) (ipw S t false e)
      (ipw S t true e) =
      splitCases ψ (t false e * (if e then p₁ else p₀)) (t false e) (t true e) / S true e :=
    fun e ↦ by
      have := splitCases_smul ψ (t false e * (if e then p₁ else p₀)) (t false e) (t true e)
        (S false e)⁻¹ (S true e)⁻¹ (inv_ne_zero (hS e))
      simp only [ipw]
      rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul, ← this]
      ring_nf
  funext c d e
  cases d <;> cases c <;> simp only [confoundingStrata, ↓reduceIte, Bool.false_eq_true, hsplit] <;>
    simp only [ipw, confoundingStrata, ↓reduceIte, Bool.false_eq_true] <;> ring

/-! ### Serial adjustment in the reverse order of the data generation -/

/-- The data-generating description of the Chapter 12 example, in the order in which the book
believes the biases arose: a source population stratified by the unmeasured confounder,
`T c d e` (confounding), is collapsed over the confounder, sampled with selection proportions
`S d e` (selection bias), and its exposure is classified with sensitivity `se d` and specificity
`sp d` (misclassification). The result is the expected observed table. -/
def generate (se sp : Bool → ℝ) (S : Table) (T : Bool → Table) : Table :=
  misclassify se sp (selected S (collapse T))

/-- The serial simple bias analysis of Chapter 12 ("Serial Multiple Bias Analysis, Simple
Methods"): correct the observed table for misclassification (Table 6.8), weight it by the
inverse selection proportions (Chapter 4), then project it onto the unmeasured confounder
(Chapter 5), the reverse of the order in which the biases arose. -/
noncomputable def serialAdjust (se sp : Bool → ℝ) (S : Table) (ψ p₁ p₀ : ℝ) (obs : Table) :
    Bool → Table :=
  confoundingStrata ψ p₁ p₀ (ipw S (misCorrect se sp obs))

/-- **Serial adjustment in the reverse order recovers the truth.** If the observed table arises
by `generate` from a stratified source table with positive cells whose control prevalences of
the confounder are `p₁`, `p₀` and whose confounder to disease odds ratio within each exposure
group is `ψ > 0`, with nonzero selection proportions and `SE_d + SP_d ≠ 1`, then the serial
adjustment returns the stratified source table. -/
theorem serialAdjust_generate {se sp : Bool → ℝ} {S : Table} {ψ p₁ p₀ : ℝ} {T : Bool → Table}
    (hk : ∀ d, se d + sp d ≠ 1) (hS : ∀ d e, S d e ≠ 0) (hT : ∀ c d e, 0 < T c d e)
    (hψ : 0 < ψ) (hprev : ∀ e, T true false e = collapse T false e * (if e then p₁ else p₀))
    (hor : ∀ e, T true true e * T false false e = ψ * T true false e * T false true e) :
    serialAdjust se sp S ψ p₁ p₀ (generate se sp S T) = T := by
  unfold serialAdjust generate
  rw [misCorrect_misclassify se sp hk, ipw_selected S _ hS, confoundingStrata_collapse hT hψ hprev
    hor]

/-- The strata of a source table with a common confounder to disease odds ratio within each
exposure group are homogeneous: both stratum odds ratios are equal. -/
theorem oddsRatio_strata_eq {ψ : ℝ} {T : Bool → Table} (hT : ∀ c d e, 0 < T c d e)
    (hor : ∀ e, T true true e * T false false e = ψ * T true false e * T false true e) :
    oddsRatio (T true) = oddsRatio (T false) := by
  have := hT true true false; have := hT true false true
  have := hT false true false; have := hT false false true
  unfold oddsRatio
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination T true false false * T false true false * hor true -
    T false true true * T true false true * hor false

/-- **The serial adjustment estimates the confounder-adjusted odds ratio.** Under the hypotheses
of `serialAdjust_generate`, the Mantel and Haenszel odds ratio of the serially adjusted table
equals the common stratum odds ratio of the source population. -/
theorem mhOR_serialAdjust_generate {se sp : Bool → ℝ} {S : Table} {ψ p₁ p₀ : ℝ}
    {T : Bool → Table} (hk : ∀ d, se d + sp d ≠ 1) (hS : ∀ d e, S d e ≠ 0)
    (hT : ∀ c d e, 0 < T c d e) (hψ : 0 < ψ)
    (hprev : ∀ e, T true false e = collapse T false e * (if e then p₁ else p₀))
    (hor : ∀ e, T true true e * T false false e = ψ * T true false e * T false true e) :
    mhOR (serialAdjust se sp S ψ p₁ p₀ (generate se sp S T)) = oddsRatio (T true) := by
  rw [serialAdjust_generate hk hS hT hψ hprev hor]
  have hhom := oddsRatio_strata_eq hT hor
  apply mhOddsRatio_of_homogeneous
  · intro c
    have := hT c true false; have := hT c false true
    rw [show oddsRatio (T true) = oddsRatio (T c) by cases c <;> simp [hhom]]
    unfold oddsRatio
    field_simp
  · have := hT true true false; have := hT true false true
    have := hT false true false; have := hT false false true
    have := hT true true true; have := hT true false false
    have := hT false true true; have := hT false false false
    simp only [Fintype.sum_bool]
    positivity

/-- **The three corrections compose as Chapter 12 describes.** For an observed table whose
misclassification corrected cells are positive and for positive selection proportions, the
Mantel and Haenszel odds ratio of the serial adjustment is the misclassification corrected odds
ratio (in closed form `oddsRatio_misCorrect`), divided by the selection odds ratio (Equation
4.2), times the confounding factor `(ψ p₀ + 1 - p₀) / (ψ p₁ + 1 - p₁)` (Table 12.5). The last
two steps are multiplicative factors; the misclassification step is not. -/
theorem mhOR_serialAdjust {se sp : Bool → ℝ} {S : Table} {ψ p₁ p₀ : ℝ} {obs : Table}
    (hc : ∀ d e, 0 < misCorrect se sp obs d e) (hS : ∀ d e, 0 < S d e) (hψ : 0 < ψ)
    (hp₁ : 0 < p₁) (hp₁' : p₁ < 1) (hp₀ : 0 < p₀) (hp₀' : p₀ < 1) :
    mhOR (serialAdjust se sp S ψ p₁ p₀ obs) =
      oddsRatio (misCorrect se sp obs) / selectionOddsRatio S *
        (mixFactor ψ p₀ / mixFactor ψ p₁) := by
  unfold serialAdjust
  rw [mhOR_confoundingStrata (t := ipw S (misCorrect se sp obs))
    (fun d e ↦ div_pos (hc d e) (hS d e)) hψ hp₁ hp₁' hp₀ hp₀', oddsRatio_ipw S _ hS hc]

/-- If instead the misclassification arose before the selection (for example selective loss
after the exposure was recorded), the observed table is `selected S (misclassify se sp src)` and
the corrections must be applied in the other order: weighting first, then the misclassification
correction recovers the source table. -/
theorem misCorrect_ipw_selected_misclassify (se sp : Bool → ℝ) (S : Table)
    (hk : ∀ d, se d + sp d ≠ 1) (hS : ∀ d e, S d e ≠ 0) (src : Table) :
    misCorrect se sp (ipw S (selected S (misclassify se sp src))) = src := by
  rw [ipw_selected S _ hS, misCorrect_misclassify se sp hk]

/-! ### Worked example: Chien et al. (Fox, MacLehose and Lash 2021, Chapter 12) -/

namespace Examples

/-- The validation table of the cases, Table 12.2: `V e e'` counts true antidepressant use `e`
(2-year pharmacy record) and self-reported use `e'` (interview). -/
def validationCases (e e' : Bool) : ℝ :=
  if e then (if e' then 24 else 19) else (if e' then 2 else 144)

/-- The validation table of the controls, Table 12.2. -/
def validationControls (e e' : Bool) : ℝ :=
  if e then (if e' then 18 else 13) else (if e' then 4 else 130)

/-- The sensitivities of the self-report in cases (`d = true`) and controls, computed from
Table 12.2 by `MisclassificationTables.sensitivity`. -/
noncomputable def chienSe (d : Bool) : ℝ :=
  if d then sensitivity validationCases else sensitivity validationControls

/-- The specificities in cases and controls, from Table 12.2. -/
noncomputable def chienSp (d : Bool) : ℝ :=
  if d then specificity validationCases else specificity validationControls

/-- The bias parameters of the text: sensitivity `24/43` (about 56%) and specificity `72/73`
(about 99%) in cases, sensitivity `18/31` (about 58%) and specificity `65/67` (about 97%) in
controls. -/
theorem chienSe_chienSp :
    chienSe = (fun d ↦ if d then 24 / 43 else 18 / 31) ∧
      chienSp = (fun d ↦ if d then 72 / 73 else 65 / 67) := by
  constructor <;> funext d <;> cases d <;>
    norm_num [chienSe, chienSp, sensitivity, specificity, validationCases, validationControls]

/-- The observed table of Chien et al. (Table 12.1), disease first: 118 exposed and 832
unexposed cases, 103 exposed and 884 unexposed controls. -/
def chienObs : Table := fun d e ↦ if d then (if e then 118 else 832) else (if e then 103 else 884)

/-- The selection proportions of Table 12.4, computed by Equation 12.1
(`participationUnexposed`) from the participation proportions `0.806` (cases) and `0.738`
(controls), the exposure prevalence `0.12` and the participation ratios `0.9` (cases) and
`0.8` (controls). -/
noncomputable def chienS : Table := fun d e ↦
  if d then (if e then 0.9 * participationUnexposed 0.806 0.12 0.9
    else participationUnexposed 0.806 0.12 0.9)
  else (if e then 0.8 * participationUnexposed 0.738 0.12 0.8
    else participationUnexposed 0.738 0.12 0.8)

theorem chienS_eq : chienS = fun d e ↦
    if d then (if e then 279 / 380 else 31 / 38) else (if e then 369 / 610 else 369 / 488) := by
  funext d e
  cases d <;> cases e <;> norm_num [chienS, participationUnexposed]

theorem chienS_pos : ∀ d e, 0 < chienS d e := by
  rw [chienS_eq]; intro d e; cases d <;> cases e <;> norm_num

/-- The misclassification corrected table, exactly. -/
noncomputable def table123 : Table := fun d e ↦
  if d then (if e then 329552 / 1709 else 1293998 / 1709)
  else (if e then 11749 / 88 else 75107 / 88)

/-- **Table 12.3.** The misclassification correction of the observed table with the validation
parameters is `table123`: cells about `192.8`, `757.2` (cases) and `133.5`, `853.5` (controls),
odds ratio about `1.628` (printed `1.63`). The printed cells reproduce only with the exact
validation fractions; see `table123_rounded_parameters`. -/
theorem table123_eq : misCorrect chienSe chienSp chienObs = table123 := by
  obtain ⟨hse, hsp⟩ := chienSe_chienSp
  funext d e
  cases d <;> cases e <;>
    norm_num [misCorrect_true, misCorrect_false, hse, hsp, chienObs, table123]

/-- The cells of Table 12.3 and its odds ratio, to printed rounding. -/
theorem table123_values :
    (192.8 < table123 true true ∧ table123 true true < 192.9) ∧
      (757.1 < table123 true false ∧ table123 true false < 757.2) ∧
      (133.5 < table123 false true ∧ table123 false true < 133.6) ∧
      (853.4 < table123 false false ∧ table123 false false < 853.5) ∧
      (1.628 < oddsRatio table123 ∧ oddsRatio table123 < 1.629) := by
  norm_num [table123, oddsRatio]

/-- With the rounded parameters of the text (sensitivities `0.56`, `0.58`, specificities `0.99`,
`0.97`) the corrected exposed cases would be about `197.3`, not the printed `192.8`. -/
theorem table123_rounded_parameters :
    197.2 < misCorrect (fun d ↦ if d then 0.56 else 0.58) (fun d ↦ if d then 0.99 else 0.97)
      chienObs true true ∧
    misCorrect (fun d ↦ if d then 0.56 else 0.58) (fun d ↦ if d then 0.99 else 0.97)
      chienObs true true < 197.3 := by
  norm_num [misCorrect_true, chienObs]

/-- The misclassification and selection corrected table, exactly. -/
noncomputable def table124 : Table := fun d e ↦
  if d then (if e then 125229760 / 476811 else 49171924 / 52979)
  else (if e then 3583445 / 16236 else 4581527 / 4059)

/-- **Table 12.4.** Weighting the misclassification corrected table by the inverse selection
proportions gives `table124`: cells about `262.6`, `928.1` (cases) and `220.7`, `1128.7`
(controls), odds ratio about `1.447` (printed `1.45`). -/
theorem table124_eq : ipw chienS (misCorrect chienSe chienSp chienObs) = table124 := by
  rw [table123_eq, chienS_eq]
  funext d e
  cases d <;> cases e <;> norm_num [ipw, table123, table124]

/-- The cells of Table 12.4 and its odds ratio, to printed rounding. -/
theorem table124_values :
    (262.6 < table124 true true ∧ table124 true true < 262.7) ∧
      (928.1 < table124 true false ∧ table124 true false < 928.2) ∧
      (220.7 < table124 false true ∧ table124 false true < 220.8) ∧
      (1128.7 < table124 false false ∧ table124 false false < 1128.8) ∧
      (1.447 < oddsRatio table124 ∧ oddsRatio table124 < 1.448) := by
  norm_num [table124, oddsRatio]

/-- The selection then misclassification corrected table, exactly. -/
noncomputable def tableReversed : Table := fun d e ↦
  if d then (if e then 14065472 / 52979 else 436328008 / 476811)
  else (if e then 1280207 / 5412 else 17905147 / 16236)

/-- The adjustments in the other order (selection first, then misclassification) give
`tableReversed`, with odds ratio about `1.353` (the text after Table 12.4 says `1.35`). -/
theorem tableReversed_eq : misCorrect chienSe chienSp (ipw chienS chienObs) = tableReversed := by
  obtain ⟨hse, hsp⟩ := chienSe_chienSp
  rw [chienS_eq]
  funext d e
  cases d <;> cases e <;>
    norm_num [misCorrect_true, misCorrect_false, hse, hsp, ipw, chienObs, tableReversed]

/-- The odds ratio of the reversed order, about `1.353` (printed `1.35`). -/
theorem tableReversed_oddsRatio :
    1.352 < oddsRatio tableReversed ∧ oddsRatio tableReversed < 1.353 := by
  norm_num [tableReversed, oddsRatio]

/-- **The order of the adjustments matters** (Fox, MacLehose and Lash 2021, text after Table
12.4): on the data of Chien et al., misclassification then selection gives an odds ratio about
`1.447`, selection then misclassification about `1.353`. The selection proportions depend on
exposure, so `misCorrect_ipw_comm_iff` does not apply. -/
theorem chien_order_matters :
    oddsRatio (ipw chienS (misCorrect chienSe chienSp chienObs)) ≠
      oddsRatio (misCorrect chienSe chienSp (ipw chienS chienObs)) := by
  rw [table124_eq, tableReversed_eq]
  norm_num [table124, tableReversed, oddsRatio]

/-- The confounding factor of the simple unmeasured confounder analysis: `OR_CD = 0.8`,
prevalences `0.299` (antidepressant users) and `0.436` (nonusers), so
`(0.8 · 0.436 + 0.564) / (0.8 · 0.299 + 0.701)`, about `0.971`. -/
theorem chien_confounding_factor :
    0.9708 < mixFactor 0.8 0.436 / mixFactor 0.8 0.299 ∧
      mixFactor 0.8 0.436 / mixFactor 0.8 0.299 < (0.9709 : ℝ) := by
  norm_num [mixFactor]

theorem table124_pos : ∀ d e, 0 < table124 d e := by
  intro d e; cases d <;> cases e <;> norm_num [table124]

/-- **Table 12.5 from the exact chain.** The serial adjustment of the observed table for
misclassification, selection and the unmeasured confounder has Mantel and Haenszel odds ratio
about `1.405` (printed `1.40`). The text after Table 12.5 calls this the odds ratio adjusted
"for selection bias and misclassification"; it is adjusted for all three biases. Table 12.6
prints `1.43` for the same scenario (row B, column 2, major column β). -/
theorem chien_serial :
    1.404 < mhOR (serialAdjust chienSe chienSp chienS 0.8 0.299 0.436 chienObs) ∧
      mhOR (serialAdjust chienSe chienSp chienS 0.8 0.299 0.436 chienObs) < 1.405 := by
  unfold serialAdjust
  rw [table124_eq, mhOR_confoundingStrata table124_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [table124, oddsRatio, mixFactor]

/-- The projected strata of Table 12.5 from the exact chain: exposed and unexposed cases about
`66.8` and `354.7` among the exercisers (printed `66.8` and `354.6`) and `195.8` and `573.5`
among the others; exposed and unexposed controls about `66.0` and `492.1` among the exercisers
and `154.7` and `636.6` among the others. -/
theorem table125_values :
    let T := serialAdjust chienSe chienSp chienS 0.8 0.299 0.436 chienObs
    (66.8 < T true true true ∧ T true true true < 66.9) ∧
      (354.6 < T true true false ∧ T true true false < 354.7) ∧
      (195.8 < T false true true ∧ T false true true < 195.9) ∧
      (573.4 < T false true false ∧ T false true false < 573.5) ∧
      (65.9 < T true false true ∧ T true false true < 66.0) ∧
      (492.1 < T true false false ∧ T true false false < 492.2) ∧
      (154.7 < T false false true ∧ T false false true < 154.8) ∧
      (636.6 < T false false false ∧ T false false false < 636.7) := by
  intro T
  simp only [T, serialAdjust, table124_eq]
  norm_num [confoundingStrata, splitCases, table124]

theorem tableReversed_pos : ∀ d e, 0 < tableReversed d e := by
  intro d e; cases d <;> cases e <;> norm_num [tableReversed]

/-- The full chain in the order selection, misclassification, confounding gives about `1.313`
instead of `1.405`. -/
theorem chien_serial_reversed :
    1.313 < mhOR (confoundingStrata 0.8 0.299 0.436
        (misCorrect chienSe chienSp (ipw chienS chienObs))) ∧
      mhOR (confoundingStrata 0.8 0.299 0.436
        (misCorrect chienSe chienSp (ipw chienS chienObs))) < 1.314 := by
  rw [tableReversed_eq, mhOR_confoundingStrata tableReversed_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num [tableReversed, oddsRatio, mixFactor]

theorem chienObs_pos : ∀ d e, 0 < chienObs d e := by
  intro d e; cases d <;> cases e <;> norm_num [chienObs]

theorem table123_pos : ∀ d e, 0 < table123 d e := by
  intro d e; cases d <;> cases e <;> norm_num [table123]

/-- **Table 12.6, major column β, recomputed.** Scenario β is the confounder analysis of
Table 12.5 (`OR_CD = 0.8`, prevalences `0.299` and `0.436`). Applied to the observed table
(row A, column 1) it gives about `1.182`, printed `1.20`; after the misclassification correction
(row B, column 1) about `1.581`, printed `1.61`; the full chain (row B, column 2) is
`chien_serial`, about `1.405`, printed `1.43`. -/
theorem table126_beta :
    (1.181 < mhOR (confoundingStrata 0.8 0.299 0.436 chienObs) ∧
      mhOR (confoundingStrata 0.8 0.299 0.436 chienObs) < 1.182) ∧
    (1.580 < mhOR (confoundingStrata 0.8 0.299 0.436 (misCorrect chienSe chienSp chienObs)) ∧
      mhOR (confoundingStrata 0.8 0.299 0.436 (misCorrect chienSe chienSp chienObs)) < 1.581) := by
  rw [table123_eq, mhOR_confoundingStrata table123_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num), mhOR_confoundingStrata chienObs_pos (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [table123, chienObs, oddsRatio, mixFactor]

/-- **Misclassification and confounder adjustments do not commute either.** Projecting the
observed table onto the confounder first and then correcting each stratum for misclassification
gives a Mantel and Haenszel odds ratio of about `1.575`; correcting first and projecting after
(row B, column 1, major column β of Table 12.6) gives about `1.581`. -/
theorem chien_confounding_misclassification_order :
    (1.574 <
        mhOR (fun c ↦ misCorrect chienSe chienSp (confoundingStrata 0.8 0.299 0.436 chienObs c)) ∧
      mhOR (fun c ↦ misCorrect chienSe chienSp (confoundingStrata 0.8 0.299 0.436 chienObs c)) <
        1.575) ∧
    mhOR (fun c ↦ misCorrect chienSe chienSp (confoundingStrata 0.8 0.299 0.436 chienObs c)) ≠
      mhOR (confoundingStrata 0.8 0.299 0.436 (misCorrect chienSe chienSp chienObs)) := by
  obtain ⟨hse, hsp⟩ := chienSe_chienSp
  rw [table123_eq, mhOR_confoundingStrata table123_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)]
  simp only [mhOR, mhOddsRatio, Fintype.sum_bool, misCorrect_true, misCorrect_false, hse, hsp]
  norm_num [confoundingStrata, splitCases, chienObs, table123, oddsRatio, mixFactor]

end Examples

end MultipleBias

end BiasAnalysis

end CausalInference
