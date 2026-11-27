/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.MultipleBias
public import CausalInference.BiasAnalysis.VarianceFormulas

/-!
# One representation for two by two tables

The bias analysis files index a two by two table of exposure `E` and disease `D` in several ways.
This file fixes one canonical representation, the disease first table
`SelectionAdjustment.Table := Bool → Bool → ℝ`, `t d e` with `d = true` the cases and
`e = true` the exposed (the convention of `SelectionAdjustment` and `MultipleBias`), and gives
its accessors, margins and effect measures together with a conversion and a bridge lemma for every
other representation of the folder.

## Canonical table

* `ofCells a b c d`: the table with exposed cases `a`, unexposed cases `b`, exposed controls `c`
  and unexposed controls `d` (the order of the four counts in `VarianceFormulas.woolfVariance`
  and in Chapter 2 of Fox, MacLehose and Lash).
* Margins: `rowTotal t d` (disease row), `colTotal t e` (exposure column), `total t`.
* Measures: `risk t e = P(D = 1 | E = e)`, `exposureProportion t d = P(E = 1 | D = d)`,
  `riskRatio`, `riskDiff` (built from `EffectMeasure.riskRatio`, `EffectMeasure.riskDiff`), and the
  odds ratio `SelectionAdjustment.oddsRatio`, which is reused, not redefined.
  `oddsRatio_eq_effectMeasure` and `oddsRatio_eq_exposureOddsRatio`: with positive cells it is the
  odds ratio of the risks and the odds ratio of the exposure proportions.

## Bridges (index convention in each statement)

* Exposure first `q e d` (`MisclassificationTables`, `Bias.Misclassification`):
  `MultipleBias.toExposureFirst`, `MultipleBias.toDiseaseFirst`; `risk_eq_bias_risk`,
  `riskRatio_eq_tableRiskRatio`, `riskDiff_eq_bias_riskDiff`, `oddsRatio_eq_tableOddsRatio`,
  `exposureProportion_eq_exposedProportion`; `toExposureFirst_eq_transposeTable` and
  `toDiseaseFirst_eq_transposeTable`: the two conversions are `transposeTable`;
  `misclassify_const`: the disease first misclassification model with constant parameters is the
  nondifferential `Bias.exposureMisclassified`.
* Vectors indexed by `(e, d)` (`MisclassificationMatrix`): `MultipleBias.toVec` and `ofVec`;
  `cellRiskRatio_toVec`.
* Four cell counts and exposure proportions (`VarianceFormulas`): `woolf`,
  `woolfVariance_eq_woolf`, `log_oddsRatio_eq_logOddsRatio`.
* Record-level weighted cells (`VarianceFormulas.pvwCell`, disease first): `pvwTable`,
  `pvwOddsRatio_eq_oddsRatio`.
* Strata of four counts (`ExternalAdjustment.mhOddsRatio`): `mhOddsRatio_unique`.
* Stratified tables `c d e` (`ExternalAdjustment.projTable`, `MultipleBias.confoundingStrata`):
  each stratum is a canonical table; `collapse_projTable`, `mhOR_projTable`.

## The same printed table in opposite conventions

Table 6.9 of Fox, MacLehose and Lash (smoking and breast cancer: `215, 1449` cases and
`668, 4296` controls) is `MisclassificationTables.Examples.table69` (exposure first),
`MisclassificationMatrix.Examples.cells69` (vector indexed by `(e, d)`) and the argument list
`215 1449 668 4296` of `woolfVariance` in `VarianceFormulas`. `table69_eq` and `cells69_eq`
identify the first two with the canonical `table69Canonical` by transposition.

## Cross-file corollaries

* `pvwTable_eq_pvCorrected`: predictive value weighting of `VarianceFormulas` (record level) is
  the correction with predictive values of `MisclassificationTables` (Table 6.10) applied to the
  observed counts; `pvwTable_recovers`: with the predictive values of the true misclassification
  the weighted table of the records is the true table.
* `log_oddsRatio_misCorrect`: the logarithm of the odds ratio of the corrected table of
  `MultipleBias` is the adjusted log odds ratio `logORSeSp` whose delta method variance is
  Greenland's (`VarianceFormulas.greenland_differential`); `log_oddsRatio_ipw_misCorrect`: after
  a further selection adjustment the log odds ratio is shifted by `-log sOR`, with the same
  gradient in the misclassification inputs.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace Tables

open SelectionAdjustment MisclassificationTables MultipleBias VarianceFormulas Finset

/-! ### The canonical table, its cells and margins -/

/-- The disease first table with exposed cases `a`, unexposed cases `b`, exposed controls `c`
and unexposed controls `d`: `t true true = a`, `t true false = b`, `t false true = c`,
`t false false = d`. -/
def ofCells (a b c d : ℝ) : Table := fun dis e ↦
  if dis then (if e then a else b) else (if e then c else d)

@[simp] theorem ofCells_apply (a b c d : ℝ) :
    ofCells a b c d true true = a ∧ ofCells a b c d true false = b ∧
      ofCells a b c d false true = c ∧ ofCells a b c d false false = d :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every table is the table of its four cells. -/
theorem ofCells_cells (t : Table) :
    ofCells (t true true) (t true false) (t false true) (t false false) = t := by
  funext d e
  cases d <;> cases e <;> rfl

/-- The total of disease row `d` (cases for `d = true`). -/
def rowTotal (t : Table) (d : Bool) : ℝ := t d true + t d false

/-- The total of exposure column `e` (exposed for `e = true`). -/
def colTotal (t : Table) (e : Bool) : ℝ := t true e + t false e

/-- The total of the four cells. -/
def total (t : Table) : ℝ := rowTotal t true + rowTotal t false

theorem total_eq_colTotal (t : Table) : total t = colTotal t true + colTotal t false := by
  simp only [total, rowTotal, colTotal]
  ring

/-! ### Effect measures -/

/-- The risk `P(D = 1 | E = e) = t 1 e / (t 1 e + t 0 e)` of exposure column `e`. -/
noncomputable def risk (t : Table) (e : Bool) : ℝ := t true e / colTotal t e

/-- The exposure proportion `P(E = 1 | D = d) = t d 1 / (t d 1 + t d 0)` of disease row `d`. -/
noncomputable def exposureProportion (t : Table) (d : Bool) : ℝ := t d true / rowTotal t d

/-- The risk ratio `P(D = 1 | E = 1) / P(D = 1 | E = 0)` (`EffectMeasure.riskRatio`). -/
noncomputable def riskRatio (t : Table) : ℝ := EffectMeasure.riskRatio (risk t true) (risk t false)

/-- The risk difference `P(D = 1 | E = 1) - P(D = 1 | E = 0)` (`EffectMeasure.riskDiff`). -/
noncomputable def riskDiff (t : Table) : ℝ := EffectMeasure.riskDiff (risk t true) (risk t false)

/-- **The cross product ratio is the odds ratio of the risks.** With four positive cells,
`SelectionAdjustment.oddsRatio t = t 1 1 t 0 0 / (t 1 0 t 0 1)` is
`EffectMeasure.oddsRatio (risk t true) (risk t false)`. -/
theorem oddsRatio_eq_effectMeasure (t : Table) (ht : ∀ d e, 0 < t d e) :
    oddsRatio t = EffectMeasure.oddsRatio (risk t true) (risk t false) := by
  have := ht true true
  have := ht true false
  have := ht false true
  have := ht false false
  simp only [oddsRatio, EffectMeasure.oddsRatio, EffectMeasure.odds, risk, colTotal]
  field_simp
  have h1 : t true true + t false true - t true true = t false true := by ring
  have h0 : t true false + t false false - t true false = t false false := by ring
  rw [h1, h0]
  field_simp

/-- **The odds ratio is also the odds ratio of the exposure proportions.** With four positive
cells, `oddsRatio t` is the ratio of the exposure odds of cases and controls, the form used in
case-control studies and in `VarianceFormulas`. -/
theorem oddsRatio_eq_exposureOddsRatio (t : Table) (ht : ∀ d e, 0 < t d e) :
    oddsRatio t =
      EffectMeasure.oddsRatio (exposureProportion t true) (exposureProportion t false) := by
  have := ht true true
  have := ht true false
  have := ht false true
  have := ht false false
  simp only [oddsRatio, EffectMeasure.oddsRatio, EffectMeasure.odds, exposureProportion,
    rowTotal]
  field_simp
  have h1 : t true true + t true false - t true true = t true false := by ring
  have h0 : t false true + t false false - t false true = t false false := by ring
  rw [h1, h0]
  field_simp

/-! ### Exposure first tables (`MisclassificationTables`, `Bias.Misclassification`) -/

/-- The risk of the canonical table is `Bias.risk` of its exposure first form `q e d = t d e`. -/
theorem risk_eq_bias_risk (t : Table) (e : Bool) :
    risk t e = Bias.risk (toExposureFirst t) e := rfl

/-- The risk ratio is `MisclassificationTables.tableRiskRatio` of the exposure first form. -/
theorem riskRatio_eq_tableRiskRatio (t : Table) :
    riskRatio t = tableRiskRatio (toExposureFirst t) := rfl

/-- The risk difference is `Bias.riskDiff` of the exposure first form. -/
theorem riskDiff_eq_bias_riskDiff (t : Table) :
    riskDiff t = Bias.riskDiff (toExposureFirst t) := rfl

/-- With four positive cells, the odds ratio is `MisclassificationTables.tableOddsRatio` (odds
ratio of the risks) of the exposure first form; without a guard it is `crossOddsRatio`
(`MultipleBias.oddsRatio_eq_crossOddsRatio`). -/
theorem oddsRatio_eq_tableOddsRatio (t : Table) (ht : ∀ d e, 0 < t d e) :
    oddsRatio t = tableOddsRatio (toExposureFirst t) :=
  (tableOddsRatio_eq_cross _ fun e d ↦ ht d e).symm

/-- The exposure proportion of disease row `d` is `MisclassificationTables.exposedProportion` of
the exposure first form. -/
theorem exposureProportion_eq_exposedProportion (t : Table) (d : Bool) :
    exposureProportion t d = exposedProportion (toExposureFirst t) d := rfl

/-- The exposure first form of a disease first table `t d e` is its transpose `q e d = t d e`
(`MisclassificationTables.transposeTable`). -/
theorem toExposureFirst_eq_transposeTable (t : Table) :
    toExposureFirst t = transposeTable t := rfl

/-- The disease first form of an exposure first table `q e d` is its transpose. -/
theorem toDiseaseFirst_eq_transposeTable (q : Bool → Bool → ℝ) :
    toDiseaseFirst q = transposeTable q := rfl

/-- With sensitivity and specificity constant across disease rows, the disease first
misclassification model `MultipleBias.misclassify` is the nondifferential
`Bias.exposureMisclassified` of `Bias.Misclassification` applied to the exposure first form. -/
theorem misclassify_const (se sp : ℝ) (t : Table) :
    misclassify (fun _ ↦ se) (fun _ ↦ sp) t =
      toDiseaseFirst (Bias.exposureMisclassified (toExposureFirst t) se sp) := by
  rw [misclassify, exposureMisclassifiedDiff_const]

/-! ### Vectors indexed by `(e, d)` (`MisclassificationMatrix`) -/

/-- The disease first table of a vector of cells indexed by `(e, d)`. -/
def ofVec (F : Bool × Bool → ℝ) : Table := fun d e ↦ F (e, d)

@[simp] theorem ofVec_toVec (t : Table) : ofVec (toVec t) = t := rfl

@[simp] theorem toVec_ofVec (F : Bool × Bool → ℝ) : toVec (ofVec F) = F := rfl

/-- The risk ratio `MisclassificationMatrix.Examples.cellRiskRatio` of the vector `F (e, d)` is
the risk ratio of the canonical table. -/
theorem cellRiskRatio_toVec (t : Table) :
    MisclassificationMatrix.Examples.cellRiskRatio (toVec t) = riskRatio t := rfl

/-! ### Four counts and proportions (`VarianceFormulas`) -/

/-- The Woolf variance `1/a + 1/b + 1/c + 1/d` of the canonical table. -/
noncomputable def woolf (t : Table) : ℝ :=
  woolfVariance (t true true) (t true false) (t false true) (t false false)

/-- The four arguments of `VarianceFormulas.woolfVariance` are, in order, the exposed cases,
unexposed cases, exposed controls and unexposed controls of `ofCells`. -/
theorem woolfVariance_eq_woolf (a b c d : ℝ) : woolfVariance a b c d = woolf (ofCells a b c d) :=
  rfl

/-- **The log odds ratio of `VarianceFormulas` is the log odds ratio of the table.** For four
positive cells, `logOddsRatio` of the exposure proportions of cases and controls is
`log (oddsRatio t)`. -/
theorem log_oddsRatio_eq_logOddsRatio (t : Table) (ht : ∀ d e, 0 < t d e) :
    Real.log (oddsRatio t) =
      logOddsRatio (exposureProportion t true) (exposureProportion t false) := by
  have := ht true true
  have := ht true false
  have := ht false true
  have := ht false false
  have h1 : 0 < rowTotal t true := by simp only [rowTotal]; positivity
  have h0 : 0 < rowTotal t false := by simp only [rowTotal]; positivity
  have e1 : exposureProportion t true < 1 := by
    rw [exposureProportion, div_lt_one h1, rowTotal]; linarith
  have e0 : exposureProportion t false < 1 := by
    rw [exposureProportion, div_lt_one h0, rowTotal]; linarith
  rw [logOddsRatio_eq_log_crossProduct (p₁ := exposureProportion t true)
    (p₀ := exposureProportion t false) h1 h0 (div_pos (ht true true) h1) e1
    (div_pos (ht false true) h0) e0]
  congr 1
  have hb := (ht true false).ne'
  have hc := (ht false true).ne'
  have hr1 := h1.ne'
  have hr0 := h0.ne'
  simp only [oddsRatio, exposureProportion, rowTotal] at hr1 hr0 ⊢
  field_simp
  rw [add_sub_cancel_left, add_sub_cancel_left, mul_div_cancel_left₀ _ hb]

/-! ### Weighted record-level tables (`VarianceFormulas.pvwCell`) -/

/-- The weighted table of predictive value weighting of the records in `s`, as a canonical
table: `pvwCell` is already disease first (`d`, then reclassified exposure `e`). -/
noncomputable def pvwTable {ι : Type*} (s : Finset ι) (case obs : ι → Bool)
    (ppv npv : Bool → ℝ) : Table :=
  fun d e ↦ pvwCell s case obs ppv npv d e

/-- The odds ratio `pvwOddsRatio` of the weighted records is the odds ratio of `pvwTable`. -/
theorem pvwOddsRatio_eq_oddsRatio {ι : Type*} (s : Finset ι) (case obs : ι → Bool)
    (ppv npv : Bool → ℝ) :
    pvwOddsRatio s case obs ppv npv = oddsRatio (pvwTable s case obs ppv npv) := rfl

/-- The observed table of the records in `s`, disease first: the number of records with case
status `d` and observed exposure `e`. -/
def countTable {ι : Type*} (s : Finset ι) (case obs : ι → Bool) : Table :=
  fun d e ↦ (#{i ∈ s | case i = d ∧ obs i = e} : ℝ)

/-! ### Stratified counts (`ExternalAdjustment.mhOddsRatio`) -/

/-- With a single stratum of nonzero total, the Mantel and Haenszel odds ratio of
`ExternalAdjustment` (stratum cells: exposed cases, unexposed cases, exposed controls,
unexposed controls) is the odds ratio of the table. -/
theorem mhOddsRatio_unique (t : Table) (hT : total t ≠ 0) :
    ExternalAdjustment.mhOddsRatio (fun _ : Unit ↦ t true true) (fun _ ↦ t true false)
      (fun _ ↦ t false true) (fun _ ↦ t false false) = oddsRatio t := by
  have hT' : t true true + t true false + t false true + t false false ≠ 0 := by
    simpa [total, rowTotal, add_assoc] using hT
  simp only [ExternalAdjustment.mhOddsRatio, Finset.univ_unique, Finset.sum_singleton, oddsRatio]
  rw [div_div_div_cancel_right₀ hT']

/-- The projected stratified table `ExternalAdjustment.projTable` is indexed `c d e` (confounder,
disease, exposure), so each stratum is a canonical table and the whole is the stratified form
`Bool → Table` of `MultipleBias`. Collapsing over the confounder returns the crude table with
`a` exposed and `b` unexposed cases and `nE - a`, `nU - b` noncases (Tables 5.5 and 5.6 of Fox,
MacLehose and Lash collapse to the observed table). -/
theorem collapse_projTable (a b nE nU rr₁ rr₀ : ℝ) (p : Bool → ℝ) :
    collapse (ExternalAdjustment.projTable a b nE nU rr₁ rr₀ p) =
      ofCells a b (nE - a) (nU - b) := by
  funext d e
  cases d <;> cases e <;>
    simp [collapse, ExternalAdjustment.projTable, ExternalAdjustment.projColumn, ofCells] <;> ring

/-- The Mantel and Haenszel odds ratio of the projected strata, read as a stratified canonical
table, is `MultipleBias.mhOR`. -/
theorem mhOR_projTable (a b nE nU rr₁ rr₀ : ℝ) (p : Bool → ℝ) :
    mhOR (ExternalAdjustment.projTable a b nE nU rr₁ rr₀ p) =
      ExternalAdjustment.mhOddsRatio
        (fun c ↦ ExternalAdjustment.projTable a b nE nU rr₁ rr₀ p c true true)
        (fun c ↦ ExternalAdjustment.projTable a b nE nU rr₁ rr₀ p c true false)
        (fun c ↦ ExternalAdjustment.projTable a b nE nU rr₁ rr₀ p c false true)
        (fun c ↦ ExternalAdjustment.projTable a b nE nU rr₁ rr₀ p c false false) := rfl

/-! ### The same printed table in two conventions: Table 6.9 -/

/-- Table 6.9 of Fox, MacLehose and Lash (smoking during pregnancy and breast cancer), canonical
form: `215` exposed and `1449` unexposed cases, `668` exposed and `4296` unexposed controls. -/
noncomputable def table69Canonical : Table := ofCells 215 1449 668 4296

/-- **Transposition, Table 6.9.** `MisclassificationTables.Examples.table69`, indexed exposure
first (`e`, then `d`), is the transpose of the canonical table. -/
theorem table69_eq :
    MisclassificationTables.Examples.table69 = toExposureFirst table69Canonical := by
  funext e d
  cases e <;> cases d <;> rfl

/-- `MisclassificationMatrix.Examples.cells69`, a vector indexed by `(e, d)`, is `toVec` of the
canonical table. -/
theorem cells69_eq : MisclassificationMatrix.Examples.cells69 = toVec table69Canonical := by
  funext i
  obtain ⟨e, d⟩ := i
  cases e <;> cases d <;> rfl

/-- The Woolf variance `1/215 + 1/1449 + 1/668 + 1/4296` of `VarianceFormulas` is that of the
canonical Table 6.9, and its odds ratio is `215 · 4296 / (1449 · 668)`. -/
theorem table69_woolf_oddsRatio :
    woolfVariance 215 1449 668 4296 = woolf table69Canonical ∧
      oddsRatio table69Canonical = 215 * 4296 / (1449 * 668) :=
  ⟨rfl, rfl⟩

/-! ### Cross-file corollaries -/

/-- **Predictive value weighting is the correction with predictive values.** The weighted table
of the records in `s` (`VarianceFormulas.pvwCell`, disease first) is the bias-adjusted table of
Table 6.10 (`MisclassificationTables.pvCorrected`, exposure first) of the observed counts,
transported to the disease first convention. -/
theorem pvwTable_eq_pvCorrected {ι : Type*} (s : Finset ι) (case obs : ι → Bool)
    (ppv npv : Bool → ℝ) :
    pvwTable s case obs ppv npv =
      toDiseaseFirst (pvCorrected (toExposureFirst (countTable s case obs)) ppv npv) := by
  funext d e
  obtain ⟨h1, h0⟩ := pvwCell_eq s case obs ppv npv d
  cases e
  · simp only [pvwTable, h0, toDiseaseFirst, pvCorrected, toExposureFirst, countTable,
      Bool.false_eq_true, ↓reduceIte, pvwUnexposed]
    ring
  · simp only [pvwTable, h1, toDiseaseFirst, pvCorrected, toExposureFirst, countTable,
      ↓reduceIte, pvwExposed]

/-- **Predictive value weighting of the records recovers the true table.** Suppose the observed
counts of the records are the expected observed table of a true exposure first table `p` under
exposure misclassification with sensitivity `se d` and specificity `sp d` in disease row `d`
(`MisclassificationTables.exposureMisclassifiedDiff`), with nonzero observed cells, and the
weights use the predictive values of that classification (`MisclassificationTables.ppv`, `npv` of
`exposureJoint`). Then the weighted table of `VarianceFormulas` is the true table, in the disease
first convention. This combines `pvwTable_eq_pvCorrected` with
`MisclassificationTables.pvCorrected_misclassified`. -/
theorem pvwTable_recovers {ι : Type*} (s : Finset ι) (case obs : ι → Bool)
    (p : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (hobs : toExposureFirst (countTable s case obs) = exposureMisclassifiedDiff p se sp)
    (h1 : ∀ d, exposureMisclassifiedDiff p se sp true d ≠ 0)
    (h0 : ∀ d, exposureMisclassifiedDiff p se sp false d ≠ 0) :
    pvwTable s case obs (fun d ↦ ppv (exposureJoint p se sp d))
        (fun d ↦ npv (exposureJoint p se sp d)) = toDiseaseFirst p := by
  rw [pvwTable_eq_pvCorrected, hobs, pvCorrected_misclassified p se sp h1 h0]

/-- **The Greenland log odds ratio is the log odds ratio of the corrected table.** If in each
disease row `d` the observed exposure proportion `P_d` satisfies `P_d + SP_d - 1 > 0` and
`SE_d - P_d > 0` and the row total is positive, the logarithm of the odds ratio of the corrected
table `MultipleBias.misCorrect se sp t` is `VarianceFormulas.logORSeSp` at
`(SE₁, SP₁, P₁, SE₀, SP₀, P₀)`. So the delta method variance of
`VarianceFormulas.greenland_differential` is the variance of the log odds ratio of the table
corrected in `MultipleBias`. -/
theorem log_oddsRatio_misCorrect (se sp : Bool → ℝ) (t : Table)
    (hA : ∀ d, 0 < exposureProportion t d + sp d - 1)
    (hB : ∀ d, 0 < se d - exposureProportion t d) (hrow : ∀ d, 0 < rowTotal t d) :
    Real.log (oddsRatio (misCorrect se sp t)) =
      logORSeSp (se true) (sp true) (exposureProportion t true) (se false) (sp false)
        (exposureProportion t false) := by
  have hk : ∀ d, se d + sp d ≠ 1 := fun d ↦ by linarith [hA d, hB d]
  rw [oddsRatio_misCorrect_algebraic se sp t (hrow true).ne' (hrow false).ne' hk,
    logORSeSp_eq_log_direct (hA true) (hB true) (hA false) (hB false)]
  rfl

/-- **Selection after misclassification, on the log scale.** If moreover the selection
proportions `S d e` and the cells of the corrected table are positive, the log odds ratio after
the misclassification correction of `MultipleBias` and the inverse probability of participation
weighting of `SelectionAdjustment` is `logORSeSp … - log sOR`. With the selection proportions
fixed, its gradient in the misclassification inputs is that of `logORSeSp`, so its first-order
variance is again Greenland's. -/
theorem log_oddsRatio_ipw_misCorrect (se sp : Bool → ℝ) (S t : Table)
    (hA : ∀ d, 0 < exposureProportion t d + sp d - 1)
    (hB : ∀ d, 0 < se d - exposureProportion t d) (hrow : ∀ d, 0 < rowTotal t d)
    (hS : ∀ d e, 0 < S d e) (hc : ∀ d e, 0 < misCorrect se sp t d e) :
    Real.log (oddsRatio (ipw S (misCorrect se sp t))) =
      logORSeSp (se true) (sp true) (exposureProportion t true) (se false) (sp false)
          (exposureProportion t false) - Real.log (selectionOddsRatio S) := by
  have hpos : ∀ u : Table, (∀ d e, 0 < u d e) → 0 < oddsRatio u := fun u hu ↦ by
    have := hu true true
    have := hu true false
    have := hu false true
    have := hu false false
    simp only [oddsRatio]
    positivity
  rw [oddsRatio_ipw S _ hS hc, Real.log_div (hpos _ hc).ne' (y := selectionOddsRatio S)
    (hpos S hS).ne', log_oddsRatio_misCorrect se sp t hA hB hrow]

end Tables

end BiasAnalysis

end CausalInference
