/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.VarianceFormulas
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Witnesses for the variance formulas of bias analysis

Two kinds of statements complement `VarianceFormulas.lean`.

**Record-level data of Table 10.1.** `table101Case` and `table101Obs` label the `1144` records of
Table 10.1 of M. P. Fox, R. F. MacLehose and T. L. Lash (2021), *Applying Quantitative Bias
Analysis to Epidemiologic Data*, second edition (`122` cases reporting antibiotic use, `442` cases
not reporting it, `101` and `479` controls), and `table101_counts` proves the four class sizes.
On these records:

* `pvw_table103_cells`, `pvw_table103_rows`: the weighted cells of Table 10.3 and its eight
  weighted rows (`69.4, 52.6, 64.3, 36.7, 47.0, 395.0, 41.7, 437.3`) with the printed weights
  (`0.569, 0.431, 0.636, 0.364, 0.106, 0.894, 0.087, 0.913`), each to its printed rounding;
* `pvw_jackknife_table101`: the record-level jackknife of Chapter 10, pp. 337 to 338, without
  hypotheses: the standard error lies in `(0.0758, 0.0763)` (printed `0.076`) and the interval in
  `(0.995, 1.005)` and `(1.345, 1.355)` (printed `(1.00, 1.35)`).

Two further printed or quoted values are backed here: `greenland_example_rounded_se_sp`
(sensitivity `0.78` and specificity `0.99` in Equation 10.1 give `0.0088`) and
`marshall_example_rounded_inputs` (the rounded inputs printed for Equations 10.5 and 10.6 give
`0.05038…`).

**Satisfiable hypotheses.** For every theorem of `VarianceFormulas.lean` whose hypotheses are a
conjunction of positivity, admissibility or nonsingularity conditions, a theorem with suffix
`_satisfiable` exhibits explicit inputs (the book's inputs where the chapter has them) that satisfy
all hypotheses at once, so that none of these theorems is vacuous. The probabilistic ones
(`variance_linearization_satisfiable`, `logit_sampleMean_satisfiable`) build an i.i.d. sample
with `exists_isIIDSample`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace CausalInference

namespace BiasAnalysis.VarianceFormulas

namespace Witnesses

open Examples

/-! ### Record-level data of Table 10.1 -/

/-- The number of elements of `Fin n` satisfying a predicate that describes the index interval
`[a, b)` with `b ≤ n` is `b - a`. -/
theorem card_fin_filter_Ico {n a b : ℕ} (hb : b ≤ n) (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i : Fin n, p i ↔ a ≤ i.val ∧ i.val < b) : #{i | p i} = b - a := by
  have h : ({i | p i} : Finset (Fin n)).map Fin.valEmbedding = Ico a b := by
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (hp i).1 hi
    · intro hk
      exact ⟨⟨k, by omega⟩, (hp _).2 hk, rfl⟩
  rw [← card_map, h, Nat.card_Ico]

/-- Case status of the `1144` records of Table 10.1: records `0` to `563` are the cases. -/
def table101Case (i : Fin 1144) : Bool := decide (i.val < 564)

/-- Reported antibiotic use of the records of Table 10.1: cases `0` to `121` and controls `564`
to `664` report use. -/
def table101Obs (i : Fin 1144) : Bool :=
  decide (i.val < 122) || decide (564 ≤ i.val ∧ i.val < 665)

/-- **The records reproduce Table 10.1**: `122` cases and `101` controls report antibiotic use,
`442` cases and `479` controls do not. -/
theorem table101_counts :
    #{i | table101Case i = true ∧ table101Obs i = true} = 122 ∧
      #{i | table101Case i = true ∧ table101Obs i = false} = 442 ∧
      #{i | table101Case i = false ∧ table101Obs i = true} = 101 ∧
      #{i | table101Case i = false ∧ table101Obs i = false} = 479 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card_fin_filter_Ico (a := 0) (b := 122) (by omega)]
    intro i; simp [table101Case, table101Obs]; omega
  · rw [card_fin_filter_Ico (a := 122) (b := 564) (by omega)]
    intro i; simp [table101Case, table101Obs]; omega
  · rw [card_fin_filter_Ico (a := 564) (b := 665) (by omega)]
    intro i; simp [table101Case, table101Obs]; omega
  · rw [card_fin_filter_Ico (a := 665) (b := 1144) (by omega)]
    intro i; simp [table101Case, table101Obs]; omega

/-- **The weighted cells of Table 10.3 from the records.** Duplicating the records of Table 10.1
and weighting the copies with the predictive values of Table 10.2 gives the weighted cells
`116.335…`, `447.665…` (cases reclassified exposed and unexposed) and `105.925…`, `474.075…`
(controls), printed `116.34, 447.67, 105.92, 474.08`; the weighted odds ratio lies in
`(1.1630, 1.1632)`, printed `1.16`. -/
theorem pvw_table103_cells :
    (116.335 < pvwCell univ table101Case table101Obs examplePPV exampleNPV true true ∧
        pvwCell univ table101Case table101Obs examplePPV exampleNPV true true < 116.345) ∧
      (447.655 < pvwCell univ table101Case table101Obs examplePPV exampleNPV true false ∧
        pvwCell univ table101Case table101Obs examplePPV exampleNPV true false < 447.665) ∧
      (105.915 < pvwCell univ table101Case table101Obs examplePPV exampleNPV false true ∧
        pvwCell univ table101Case table101Obs examplePPV exampleNPV false true < 105.925) ∧
      (474.075 < pvwCell univ table101Case table101Obs examplePPV exampleNPV false false ∧
        pvwCell univ table101Case table101Obs examplePPV exampleNPV false false < 474.085) ∧
      (1.1630 < pvwOddsRatio univ table101Case table101Obs examplePPV exampleNPV ∧
        pvwOddsRatio univ table101Case table101Obs examplePPV exampleNPV < 1.1632) := by
  obtain ⟨h₁₁, h₁₀, h₀₁, h₀₀⟩ := table101_counts
  obtain ⟨c₁₁, c₁₀⟩ := pvwCell_eq univ table101Case table101Obs examplePPV exampleNPV true
  obtain ⟨c₀₁, c₀₀⟩ := pvwCell_eq univ table101Case table101Obs examplePPV exampleNPV false
  rw [h₁₁, h₁₀] at c₁₁ c₁₀
  rw [h₀₁, h₀₀] at c₀₁ c₀₀
  have hOR := (pvwOddsRatio_example table101Case table101Obs h₁₁ h₁₀ h₀₁ h₀₀).1
  rw [c₁₁, c₁₀, c₀₁, c₀₀, hOR]
  norm_num [examplePPV, exampleNPV, pvwExposed, pvwUnexposed, exampleWeightedOR]

/-- **The eight rows of Table 10.3.** For each class of records (case status `d`, reported
exposure `o`) and each reclassified exposure `e`, the weighted count is the number of records of
the class times the weight of the copy. The printed weights `0.569, 0.431, 0.636, 0.364, 0.106,
0.894, 0.087, 0.913` and weighted counts `69.4, 52.6, 64.3, 36.7, 47.0, 395.0, 41.7, 437.3` are
the roundings of the exact values, as the half-unit intervals below show. -/
theorem pvw_table103_rows :
    let w (d o e : Bool) : ℝ := pvwWeight (examplePPV d) (exampleNPV d) o e
    let N (d o e : Bool) : ℝ := #{i | table101Case i = d ∧ table101Obs i = o} * w d o e
    (0.5685 < w true true true ∧ w true true true < 0.5695 ∧
        69.35 < N true true true ∧ N true true true < 69.45) ∧
      (0.4305 < w true true false ∧ w true true false < 0.4315 ∧
        52.55 < N true true false ∧ N true true false < 52.65) ∧
      (0.6355 < w false true true ∧ w false true true < 0.6365 ∧
        64.25 < N false true true ∧ N false true true < 64.35) ∧
      (0.3635 < w false true false ∧ w false true false < 0.3645 ∧
        36.65 < N false true false ∧ N false true false < 36.75) ∧
      (0.1055 < w true false true ∧ w true false true < 0.1065 ∧
        46.95 < N true false true ∧ N true false true < 47.05) ∧
      (0.8935 < w true false false ∧ w true false false < 0.8945 ∧
        394.95 < N true false false ∧ N true false false < 395.05) ∧
      (0.0865 < w false false true ∧ w false false true < 0.0875 ∧
        41.65 < N false false true ∧ N false false true < 41.75) ∧
      (0.9125 < w false false false ∧ w false false false < 0.9135 ∧
        437.25 < N false false false ∧ N false false false < 437.35) := by
  intro w N
  obtain ⟨h₁₁, h₁₀, h₀₁, h₀₀⟩ := table101_counts
  simp only [w, N, h₁₁, h₁₀, h₀₁, h₀₀]
  norm_num [pvwWeight, examplePPV, exampleNPV]

/-- **The record-level jackknife of Table 10.3, without hypotheses** (Chapter 10, pp. 337 to
338). On the records of Table 10.1 (`table101Case`, `table101Obs`), deleting each record in turn
with both of its weighted copies, the jackknife standard error of the log odds ratio of the
weighted table lies in `(0.0758, 0.0763)` (printed `SE_jack = 0.076`), and the interval
`exp (ln OR ∓ 1.96 SE_jack)`, with `ln OR` from the full weighted table, has endpoints in
`(0.995, 1.005)` and `(1.345, 1.355)` (printed `(1.00, 1.35)`). The predictive values are held at
those of Table 10.2. -/
theorem pvw_jackknife_table101 :
    let θ : Fin 1144 → ℝ := fun i ↦
      Real.log (pvwOddsRatio (univ.erase i) table101Case table101Obs examplePPV exampleNPV)
    let OR := pvwOddsRatio univ table101Case table101Obs examplePPV exampleNPV
    (0.0758 < √(jackknifeVariance θ) ∧ √(jackknifeVariance θ) < 0.0763) ∧
      (0.995 < Real.exp (Real.log OR - 1.96 * √(jackknifeVariance θ)) ∧
        Real.exp (Real.log OR - 1.96 * √(jackknifeVariance θ)) < 1.005) ∧
      (1.345 < Real.exp (Real.log OR + 1.96 * √(jackknifeVariance θ)) ∧
        Real.exp (Real.log OR + 1.96 * √(jackknifeVariance θ)) < 1.355) := by
  obtain ⟨h₁₁, h₁₀, h₀₁, h₀₀⟩ := table101_counts
  exact pvw_jackknife_example table101Case table101Obs h₁₁ h₁₀ h₀₁ h₀₀

/-! ### Further quoted values -/

/-- **Equation 10.1 with rounded sensitivity and specificity.** With `SE = 0.78`, `SP = 0.99`, the
binomial variances of the validation fractions `128/164` and `465/470` and the unrounded observed
proportions `215/1664`, `668/4964`, the nondifferential Greenland variance lies in
`(0.00881, 0.00882)`, which rounds to `0.0088` rather than the printed `0.0089`
(`greenland_example`). -/
theorem greenland_example_rounded_se_sp :
    0.00881 < greenlandNondiff ((128 / 164) * (1 - 128 / 164) / 164)
        ((465 / 470) * (1 - 465 / 470) / 470) 0.78 0.99 (215 / 1664) 1664 (668 / 4964) 4964 ∧
      greenlandNondiff ((128 / 164) * (1 - 128 / 164) / 164)
        ((465 / 470) * (1 - 465 / 470) / 470) 0.78 0.99 (215 / 1664) 1664 (668 / 4964) 4964 <
        0.00882 := by
  constructor <;> norm_num [greenlandNondiff, trueProportion]

/-- **Equations 10.5 and 10.6 with the printed rounded inputs.** With `PPV₁ = 0.569`,
`NPV₁ = 0.894`, `P(e₁) = 0.216`, `Var PPV₁ = 0.0048`, `Var NPV₁ = 0.00059`, `PPV₀ = 0.636`,
`NPV₀ = 0.913`, `P(e₀) = 0.174`, `Var PPV₀ = 0.007`, `Var NPV₀ = 0.00043` (Table 10.2 and the
text after it) and binomial variances of `P(eᵢ)` in the row totals `564` and `580`, the variance
of Equation 10.5 lies in `(0.05038, 0.05039)`; the unrounded inputs give `0.0505`
(`marshall_example`), printed `0.051`. -/
theorem marshall_example_rounded_inputs :
    let a₁ := marshallA 0.0048 0.00059 (0.216 * (1 - 0.216) / 564) 0.569 0.894 0.216
    let a₀ := marshallA 0.007 0.00043 (0.174 * (1 - 0.174) / 580) 0.636 0.913 0.174
    let P₁ := trueProportionPV 0.569 0.894 0.216
    let P₀ := trueProportionPV 0.636 0.913 0.174
    0.05038 < a₀ / (P₀ * (1 - P₀)) ^ 2 + a₁ / (P₁ * (1 - P₁)) ^ 2 ∧
      a₀ / (P₀ * (1 - P₀)) ^ 2 + a₁ / (P₁ * (1 - P₁)) ^ 2 < 0.05039 := by
  norm_num [marshallA, trueProportionPV]

/-! ### Satisfiable hypotheses: delta method and Woolf variance -/

/-- `variance_linearization` is not vacuous: two independent standard Gaussian variables on a
probability space are square integrable, pairwise independent and have variance one. -/
theorem variance_linearization_satisfiable :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : Fin 2 → Ω → ℝ), (∀ i, MemLp (X i) 2 μ) ∧ (Pairwise fun i j ↦ IndepFun (X i) (X j) μ) ∧
        ∀ i, Var[X i; μ] = 1 := by
  obtain ⟨Ω, _, P, O, hP, -, hO, hlaw⟩ := exists_isIIDSample (gaussianReal 0 1)
  refine ⟨Ω, _, P, hP, fun i ↦ O i.val, fun i ↦ (hlaw i.val).memLp (memLp_id_gaussianReal 2),
    fun i j hij ↦ hO.indep.indepFun (Fin.val_injective.ne hij), fun i ↦ ?_⟩
  rw [(hlaw i.val).variance_eq]
  simp

/-- `logit_sampleMean_isAsymptoticallyLinear` and `integral_sq_logit_influence` are not vacuous:
an i.i.d. sample of fair coins with the indicator of heads has mean `1/2 ∈ (0, 1)`. -/
theorem logit_sampleMean_satisfiable :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (O : ℕ → Ω → Bool) (f : Bool → ℝ) (p : ℝ), IsIIDSample O μ ∧ Measurable f ∧
        (∀ x, f x = 0 ∨ f x = 1) ∧ μ[fun ω ↦ f (O 0 ω)] = p ∧ 0 < p ∧ p < 1 := by
  obtain ⟨Ω, _, P, O, hP, -, hO, hlaw⟩ :=
    exists_isIIDSample (PMF.ofFintype (fun _ : Bool ↦ (2 : ENNReal)⁻¹)
      (by simp [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top])).toMeasure
  refine ⟨Ω, _, P, hP, O, fun b ↦ if b then 1 else 0, 1 / 2, hO, measurable_of_finite _,
    fun x ↦ by cases x <;> simp, ?_, by norm_num, by norm_num⟩
  have h := (hlaw 0).integral_comp (f := fun b : Bool ↦ if b then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, PMF.integral_eq_sum]
  simp [PMF.ofFintype_apply]

/-- The hypotheses `0 < p < 1` of `logit_eq_log_div` and `hasDerivAt_logit` hold at the observed
exposure proportion `215/1664` of the cases of Chapter 6. -/
theorem logit_satisfiable : (0 : ℝ) < 215 / 1664 ∧ (215 / 1664 : ℝ) < 1 := by norm_num

/-- The hypotheses of `logOddsRatio_eq_log_crossProduct`, `hasDerivAt_logOddsRatio` and
`firstOrderVariance_logOddsRatio_eq_woolf` hold for the smoking and breast cancer data
(`n₁ = 1664` cases with `p₁ = 215/1664` exposed, `n₀ = 4964` controls with `p₀ = 668/4964`). -/
theorem logOddsRatio_satisfiable :
    ∃ n₁ n₀ p₁ p₀ : ℝ, 0 < n₁ ∧ 0 < n₀ ∧ 0 < p₁ ∧ p₁ < 1 ∧ 0 < p₀ ∧ p₀ < 1 :=
  ⟨1664, 4964, 215 / 1664, 668 / 4964, by norm_num⟩

/-! ### Satisfiable hypotheses: Greenland variance -/

/-- The positivity hypotheses `pe + sp - 1 > 0`, `se - pe > 0`, `D > 0` of
`logOddsSeSp_eq_logit`, `hasDerivAt_logOddsSeSp` and `firstOrderVariance_logOddsSeSp` hold for
the cases of the smoking and breast cancer example (`SE = 128/164`, `SP = 465/470`,
`pe = 215/1664`, `D = 1664`). -/
theorem logOddsSeSp_satisfiable :
    ∃ se sp pe D : ℝ, 0 < pe + sp - 1 ∧ 0 < se - pe ∧ 0 < D :=
  ⟨128 / 164, 465 / 470, 215 / 1664, 1664, by norm_num⟩

/-- The nonsingularity hypotheses of `firstOrderVariance_greenland_eq` hold at the same inputs,
and also in the mirrored region (`se = 0.2`, `sp = 0.3`, `pe = 0.45`). -/
theorem firstOrderVariance_greenland_eq_satisfiable :
    (∃ se sp pe D : ℝ, se + sp - 1 ≠ 0 ∧ pe + sp - 1 ≠ 0 ∧ se - pe ≠ 0 ∧ D ≠ 0 ∧
        0 < se + sp - 1) ∧
      ∃ se sp pe D : ℝ, se + sp - 1 ≠ 0 ∧ pe + sp - 1 ≠ 0 ∧ se - pe ≠ 0 ∧ D ≠ 0 ∧
        se + sp - 1 < 0 :=
  ⟨⟨128 / 164, 465 / 470, 215 / 1664, 1664, by norm_num⟩, ⟨0.2, 0.3, 0.45, 100, by norm_num⟩⟩

/-- The six positivity hypotheses of `logORSeSp_eq_log_direct` (four of them),
`greenland_differential`, `greenland_nondifferential` and `logORSeSp_eq_logORSeSpLogit` hold
together for the smoking and breast cancer example, with shared sensitivity `128/164` and
specificity `465/470` (so they also hold for the differential theorem with equal parameters in
both groups). -/
theorem greenland_satisfiable :
    ∃ se sp pe₁ D₁ pe₀ D₀ : ℝ, 0 < pe₁ + sp - 1 ∧ 0 < se - pe₁ ∧ 0 < D₁ ∧
      0 < pe₀ + sp - 1 ∧ 0 < se - pe₀ ∧ 0 < D₀ :=
  ⟨128 / 164, 465 / 470, 215 / 1664, 1664, 668 / 4964, 4964, by norm_num⟩

/-- The differential hypotheses can also be met with different parameters in the two groups:
cases with `SE₁ = 0.9`, `SP₁ = 0.95`, `pe₁ = 0.3` and controls with `SE₀ = 0.8`, `SP₀ = 0.9`,
`pe₀ = 0.2`. -/
theorem greenland_differential_satisfiable :
    ∃ se₁ sp₁ pe₁ D₁ se₀ sp₀ pe₀ D₀ : ℝ, se₁ ≠ se₀ ∧ sp₁ ≠ sp₀ ∧
      0 < pe₁ + sp₁ - 1 ∧ 0 < se₁ - pe₁ ∧ 0 < D₁ ∧
      0 < pe₀ + sp₀ - 1 ∧ 0 < se₀ - pe₀ ∧ 0 < D₀ :=
  ⟨0.9, 0.95, 0.3, 100, 0.8, 0.9, 0.2, 200, by norm_num⟩

/-- The nonsingularity hypotheses of `firstOrderVariance_greenlandNondiff_eq` hold for the
smoking and breast cancer example. -/
theorem firstOrderVariance_greenlandNondiff_eq_satisfiable :
    ∃ se sp pe₁ D₁ pe₀ D₀ : ℝ, se + sp - 1 ≠ 0 ∧ pe₁ + sp - 1 ≠ 0 ∧ se - pe₁ ≠ 0 ∧ D₁ ≠ 0 ∧
      pe₀ + sp - 1 ≠ 0 ∧ se - pe₀ ≠ 0 ∧ D₀ ≠ 0 :=
  ⟨128 / 164, 465 / 470, 215 / 1664, 1664, 668 / 4964, 4964, by norm_num⟩

/-- The hypotheses of `hasDerivAt_logit_trueProportion` (`se + sp ≠ 1` and a corrected proportion
in `(0, 1)`) hold in both regions: at the cases of the smoking and breast cancer example and at
the mirrored point `se = 0.2`, `sp = 0.3`, `pe = 0.45`. -/
theorem hasDerivAt_logit_trueProportion_satisfiable :
    (∃ se sp pe : ℝ, se + sp - 1 ≠ 0 ∧ 0 < trueProportion se sp pe ∧
        trueProportion se sp pe < 1 ∧ 0 < se + sp - 1) ∧
      ∃ se sp pe : ℝ, se + sp - 1 ≠ 0 ∧ 0 < trueProportion se sp pe ∧
        trueProportion se sp pe < 1 ∧ se + sp - 1 < 0 :=
  ⟨⟨128 / 164, 465 / 470, 215 / 1664, by norm_num [trueProportion]⟩,
    ⟨0.2, 0.3, 0.45, by norm_num [trueProportion]⟩⟩

/-- The hypotheses of `greenland_differential_admissible` hold with the cases in the mirrored
region (`se₁ = 0.2`, `sp₁ = 0.3`, `pe₁ = 0.45`) and the controls of the smoking and breast cancer
example in the usual region. -/
theorem greenland_differential_admissible_satisfiable :
    ∃ se₁ sp₁ pe₁ D₁ se₀ sp₀ pe₀ D₀ : ℝ, se₁ + sp₁ - 1 ≠ 0 ∧
      (0 < trueProportion se₁ sp₁ pe₁ ∧ trueProportion se₁ sp₁ pe₁ < 1) ∧ 0 < D₁ ∧
      se₀ + sp₀ - 1 ≠ 0 ∧
      (0 < trueProportion se₀ sp₀ pe₀ ∧ trueProportion se₀ sp₀ pe₀ < 1) ∧ 0 < D₀ ∧
      se₁ + sp₁ - 1 < 0 ∧ 0 < se₀ + sp₀ - 1 :=
  ⟨0.2, 0.3, 0.45, 100, 128 / 164, 465 / 470, 668 / 4964, 4964, by norm_num [trueProportion]⟩

/-- The hypotheses of `greenland_nondifferential_admissible` hold in the mirrored region: shared
`se = 0.2`, `sp = 0.3` with observed proportions `0.45` and `0.4`. -/
theorem greenland_nondifferential_admissible_satisfiable :
    ∃ se sp pe₁ D₁ pe₀ D₀ : ℝ, se + sp - 1 ≠ 0 ∧
      (0 < trueProportion se sp pe₁ ∧ trueProportion se sp pe₁ < 1) ∧ 0 < D₁ ∧
      (0 < trueProportion se sp pe₀ ∧ trueProportion se sp pe₀ < 1) ∧ 0 < D₀ ∧
      se + sp - 1 < 0 :=
  ⟨0.2, 0.3, 0.45, 100, 0.4, 200, by norm_num [trueProportion]⟩

/-- The hypotheses of `observed_mem_Ioo_of_admissible`, `greenlandTerm_nonneg` and
`greenlandNondiff_nonneg` hold together for the smoking and breast cancer example, with the
binomial variances of the validation fractions. -/
theorem greenland_nonneg_satisfiable :
    ∃ vse vsp se sp pe₁ D₁ pe₀ D₀ : ℝ, (0 ≤ se ∧ se ≤ 1) ∧ (0 ≤ sp ∧ sp ≤ 1) ∧ se + sp - 1 ≠ 0 ∧
      (0 < trueProportion se sp pe₁ ∧ trueProportion se sp pe₁ < 1) ∧
      (0 < trueProportion se sp pe₀ ∧ trueProportion se sp pe₀ < 1) ∧
      0 ≤ vse ∧ 0 ≤ vsp ∧ 0 < D₁ ∧ 0 < D₀ :=
  ⟨(128 / 164) * (1 - 128 / 164) / 164, (465 / 470) * (1 - 465 / 470) / 470, 128 / 164,
    465 / 470, 215 / 1664, 1664, 668 / 4964, 4964, by norm_num [trueProportion]⟩

/-! ### Satisfiable hypotheses: Marshall variance and predictive value weighting -/

/-- The hypotheses of `trueProportionPV_eq_true` hold for the joint law of true and observed
exposure with cells `q₁₁ = 0.15`, `q₀₁ = 0.05`, `q₁₀ = 0.05`, `q₀₀ = 0.75`. -/
theorem trueProportionPV_eq_true_satisfiable :
    ∃ q₁₁ q₀₁ q₁₀ q₀₀ : ℝ, 0 ≤ q₁₁ ∧ 0 ≤ q₀₁ ∧ 0 ≤ q₁₀ ∧ 0 ≤ q₀₀ ∧
      q₁₁ + q₀₁ + q₁₀ + q₀₀ = 1 ∧ 0 < q₁₁ + q₀₁ ∧ q₁₁ + q₀₁ < 1 :=
  ⟨0.15, 0.05, 0.05, 0.75, by norm_num⟩

/-- The hypotheses of `hasDerivAt_logOddsPV`, `firstOrderVariance_logOddsPV`,
`hasDerivAt_logORPV` and `marshall_variance` (the corrected proportions of both groups in
`(0, 1)`) hold for the antibiotics and sudden infant death example (Tables 10.1 and 10.2). -/
theorem marshall_satisfiable :
    0 < trueProportionPV (29 / 51) (143 / 160) (122 / 564) ∧
      trueProportionPV (29 / 51) (143 / 160) (122 / 564) < 1 ∧
      0 < trueProportionPV (21 / 33) (168 / 184) (101 / 580) ∧
      trueProportionPV (21 / 33) (168 / 184) (101 / 580) < 1 := by
  norm_num [trueProportionPV]

/-- The hypotheses of `pvw_recovers_true` and `pvwExposed_div` hold for the validation data of
the cases in Table 10.2: of the `51` cases reporting antibiotic use `29` were truly exposed, and
of the `160` reporting none `17` were truly exposed. -/
theorem pvw_recovers_true_satisfiable :
    ∃ n₁₁ n₀₁ n₁₀ n₀₀ : ℝ, 0 < n₁₁ + n₀₁ ∧ 0 < n₁₀ + n₀₀ ∧ n₁₁ / (n₁₁ + n₀₁) = 29 / 51 ∧
      n₀₀ / (n₁₀ + n₀₀) = 143 / 160 :=
  ⟨29, 22, 17, 143, by norm_num⟩

/-- The membership hypothesis of `pvwCell_erase` and the cardinality hypotheses of
`Examples.pvwOddsRatio_example` and `Examples.pvw_jackknife_example` hold for the records of
Table 10.1. -/
theorem pvw_jackknife_satisfiable :
    (⟨0, by norm_num⟩ : Fin 1144) ∈ (univ : Finset (Fin 1144)) ∧
      #{i | table101Case i = true ∧ table101Obs i = true} = 122 ∧
      #{i | table101Case i = true ∧ table101Obs i = false} = 442 ∧
      #{i | table101Case i = false ∧ table101Obs i = true} = 101 ∧
      #{i | table101Case i = false ∧ table101Obs i = false} = 479 :=
  ⟨mem_univ _, table101_counts⟩

/-! ### Satisfiable hypotheses: jackknife, Rubin's rules, pooling, intervals -/

/-- The sample size hypotheses of `jackknifeVariance_leaveOneOutMean` (`2 ≤ n`),
`jackknifeVariance_eq_centered` (`0 < n`), `rubinVariance_eq` and
`withinVariance_le_rubinVariance` (`2 ≤ M`) hold at the `1144` records of Table 10.1 and at
`M = 2` imputations. -/
theorem sampleSize_satisfiable : 2 ≤ 1144 ∧ 0 < 1144 ∧ 2 ≤ 2 := by norm_num

/-- The hypotheses of `ivTotalWeight_pos`, `ivPooled_eq_sum_weights`,
`firstOrderVariance_weights_eq`, `ivPooledVariance_le` and `firstOrderVariance_ivWeights` hold
for the two variances `0.225²`, `0.25²` of the "Misclassification Example" of Chapter 10 with the
equal weights `1/2, 1/2`. -/
theorem ivPooled_satisfiable :
    (∀ i, 0 < (![0.225 ^ 2, 0.25 ^ 2] : Fin 2 → ℝ) i) ∧ 0 < 2 ∧
      ∑ i, (![1 / 2, 1 / 2] : Fin 2 → ℝ) i = 1 := by
  refine ⟨fun i ↦ ?_, by norm_num, by norm_num [Fin.sum_univ_two]⟩
  fin_cases i <;> norm_num

/-- The hypotheses of `se_eq_of_waldIntervalSE_eq` hold for the balanced design of Chapter 2:
critical value `1.96`, standard error `0.4`, estimate `0` and interval `[-0.784, 0.784]`
(`Examples.woolf_balanced_interval`). -/
theorem se_eq_of_waldIntervalSE_eq_satisfiable :
    (0 : ℝ) < 1.96 ∧ (0 : ℝ) ≤ 2 / 5 ∧ waldIntervalSE 0 (2 / 5) 1.96 = Set.Icc (-0.784) 0.784 :=
  ⟨by norm_num, by norm_num, woolf_balanced_interval.1⟩

/-- The hypothesis `se + sp = 1` of `forward_eq_se_of_sum_eq_one` holds for `se = 0.4`,
`sp = 0.6`, a classification that carries no information. -/
theorem forward_eq_se_of_sum_eq_one_satisfiable : (0.4 : ℝ) + 0.6 = 1 := by norm_num

end Witnesses

end BiasAnalysis.VarianceFormulas

end CausalInference
