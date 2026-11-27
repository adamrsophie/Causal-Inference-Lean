/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Bias.Selection
public import CausalInference.PartialIdentification.IdentifiedSet
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Selection adjustment

Simple bias analysis for selection bias on two-by-two tables, following Fox, MacLehose and
Lash (2021), Chapter 4 ("Selection Bias") and Equation 12.1 of Chapter 12. Tables are real
valued, indexed by disease status `d` (first argument) and exposure status `e`, with explicit
positivity hypotheses wherever a ratio is formed.

## Main definitions

* `selected S src`: the selection model of Table 4.4, `obs d e = S d e * src d e`.
* `selectionOddsRatio S`: the selection odds ratio `sOR`.
* `ipw S obs`: inverse probability of participation weighting, `obs d e / S d e`.
* `proj a b m p`, `projSel`, `orProj`: projection of the exposed proportion among
  nonparticipants (Equation 4.1) and the selection proportions it implies (Table 4.5).
* `partRisk`, `nonpartRisk`, `mixRisk`: risks among participants, nonparticipants and the
  source when participation depends on a modifier `U` only (Figure 4.3).
* `adjRate`: the rate adjusted for loss to follow-up (Table 4.7).
* `participationUnexposed`: Equation 12.1.

## Main results

* `oddsRatio_selected`, `oddsRatio_source_eq`: `OR_obs = OR_src * sOR`, hence Equation 4.2
  `OR_src = OR_obs / sOR`; `oddsRatio_selected_gt_iff`: the direction of the bias is that of
  `sOR` relative to one; `selectionOddsRatio_multiplicative` and
  `selected_indep_of_multiplicative` (built on `Bias.stratum_indep_of_multiplicative`):
  multiplicative selection does not bias the odds ratio.
* `ipw_selected`, `oddsRatio_ipw`: weighting by `1 / S` recovers the source table and gives
  `OR_obs / sOR`; `proj_eq_source`, `projection_ipw_selectionOddsRatio`: the projection,
  selection odds ratio and weighting methods agree.
* `orProj_mono_left`, `orProj_anti_right`, `orProj_mem_Icc`, `identifiedSet_orProj`: Equation
  4.1 is monotone in the assumed prevalences, and its identified set over `[0, 1]²` is the
  interval between the corners `(0, 1)` and `(1, 0)`.
* `partRD_sub_sourceRD`: with `U` independent of exposure and participation depending on `U`
  only, the selection bias of the risk difference is `1 - π` times the variation across
  exposure of the participation to disease risk difference (the condition of Hernán 2017 quoted
  in the book); `partRD_eq_of_const`, `partRR_eq_of_const`: no bias on a scale on which `U`
  does not modify the effect; `Examples.example43`: the book's counterexample (0 versus 0.1).
* `adjRate_eq_of_same_rate`, `adjRate_lost_as_followed`: the mediant identity;
  `adjRateRatio_mem_Icc`, `adjRateDiff_mem_Icc`: extreme scenarios for loss to follow-up;
  `sum_ipw_eq`, `ipw_rate`: inverse probability of follow-up weighting over strata.
* `participationUnexposed_eq` and its admissibility conditions; `Examples.eq121_inadmissible`.

## Worked examples and printed values

The section `Examples` checks Tables 4.1, 4.3, 4.5, 4.6, 4.7, Equation 4.1 and the values of
Equation 12.1 by `norm_num`. Two printed rows of Table 4.7 ("all lost died", "no lost died")
do not follow from the stated person-time (`Examples.table47_all_died`,
`Examples.table47_none_died`), and neither the diagonal rows of Table 4.7 nor the "all exposed"
and "all unexposed" rows of Table 4.3 are the extremes of the adjustment
(`Examples.table47_extremes`, `Examples.orProj_stang_corners`).

## References

* M. P. Fox, R. F. MacLehose and T. L. Lash, *Applying Quantitative Bias Analysis to
  Epidemiologic Data*, second edition, Springer (2021), Chapter 4 (Tables 4.1 to 4.7,
  Equations 4.1 and 4.2) and Chapter 12 (Equation 12.1).
* M. A. Hernán (2017), as cited by Fox, MacLehose and Lash (2021), Chapter 4, for selection
  bias without colliders.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace SelectionAdjustment

open Bias

/-- A two-by-two table of real cell counts (or probabilities), indexed by disease status `d`
(first argument; `true` for cases) and exposure status `e` (second argument; `true` for
exposed). -/
abbrev Table := Bool → Bool → ℝ

/-- The odds ratio of a two-by-two table: `t 1 1 * t 0 0 / (t 1 0 * t 0 1)`, the exposed cases
times the unexposed noncases over the unexposed cases times the exposed noncases. It is only
meaningful when the four cells are positive; every theorem below that uses it says so. -/
noncomputable def oddsRatio (t : Table) : ℝ :=
  t true true * t false false / (t true false * t false true)

/-- The selection model of Fox, MacLehose and Lash (2021), Table 4.4: the participants' table is
the source table with each cell multiplied by its selection proportion,
`obs d e = S d e * src d e`, where `S d e` is the probability that a source member with disease
status `d` and exposure status `e` participates. -/
def selected (S src : Table) : Table := fun d e ↦ S d e * src d e

/-- The selection odds ratio `sOR = S_{case,1} S_{control,0} / (S_{case,0} S_{control,1})`
(Fox, MacLehose and Lash 2021, text before Equation 4.2). It is undefined (Lean returns a junk
value) when a selection proportion is zero. -/
noncomputable def selectionOddsRatio (S : Table) : ℝ := oddsRatio S

/-- Inverse probability of participation weighting: each observed cell is divided by its
selection proportion (Fox, MacLehose and Lash 2021, "Bias Analysis Using Inverse Probability of
Participation Weighting"). -/
noncomputable def ipw (S obs : Table) : Table := fun d e ↦ obs d e / S d e

/-- The odds ratio among participants factors as the source odds ratio times the selection odds
ratio: `OR_obs = OR_src * sOR`. This is the identity behind Equation 4.2 of Fox, MacLehose and
Lash (2021). -/
theorem oddsRatio_selected (S src : Table) :
    oddsRatio (selected S src) = oddsRatio src * selectionOddsRatio S := by
  simp only [oddsRatio, selectionOddsRatio, selected]
  rw [div_mul_div_comm]
  ring_nf

/-- Equation 4.2 of Fox, MacLehose and Lash (2021): if the participants' table arises from a
source table with positive cells by the selection model and all selection proportions are
positive, then the source odds ratio, a positive number, is recovered as
`OR_src = OR_obs / sOR`. -/
theorem oddsRatio_source_eq (S src : Table) (hS : ∀ d e, 0 < S d e)
    (hsrc : ∀ d e, 0 < src d e) :
    0 < oddsRatio src ∧ oddsRatio src = oddsRatio (selected S src) / selectionOddsRatio S := by
  have h : selectionOddsRatio S ≠ 0 := by
    simp only [selectionOddsRatio, oddsRatio]
    have := hS true true; have := hS false false; have := hS true false; have := hS false true
    positivity
  refine ⟨?_, ?_⟩
  · simp only [oddsRatio]
    have := hsrc true true; have := hsrc false false; have := hsrc true false
    have := hsrc false true
    positivity
  · rw [oddsRatio_selected, mul_div_assoc, div_self h, mul_one]

/-- Inverse probability of participation weighting recovers the source table: if
`obs = selected S src` with positive selection proportions, then `obs d e / S d e = src d e`
for every cell. This is a finite, cellwise analogue (proved directly, not derived from it) of
the weighting identity `ipw_identity` of `CausalInference.MissingData.Weighting`. -/
theorem ipw_selected (S src : Table) (hS : ∀ d e, S d e ≠ 0) :
    ipw S (selected S src) = src := by
  funext d e
  simp only [ipw, selected]
  field_simp [hS d e]

/-- The odds ratio of the weighted table equals the observed odds ratio divided by the selection
odds ratio: for any observed table with positive cells and positive selection proportions, the
inverse probability weighting estimate and the selection odds ratio estimate of Equation 4.2
coincide. -/
theorem oddsRatio_ipw (S obs : Table) (hS : ∀ d e, 0 < S d e) (hobs : ∀ d e, 0 < obs d e) :
    oddsRatio (ipw S obs) = oddsRatio obs / selectionOddsRatio S := by
  have key := (oddsRatio_source_eq S (ipw S obs) hS
    fun d e ↦ div_pos (hobs d e) (hS d e)).2
  rwa [show selected S (ipw S obs) = obs by
    funext d e; simp only [selected, ipw]; field_simp [(hS d e).ne']] at key

/-- Direction of selection bias for the odds ratio: with positive source cells, the participants'
odds ratio exceeds the source odds ratio if and only if the selection odds ratio exceeds one
(`one_lt_selectionOddsRatio_iff` restates the latter without division when the selection
proportions are positive). -/
theorem oddsRatio_selected_gt_iff (S src : Table) (hsrc : ∀ d e, 0 < src d e) :
    oddsRatio src < oddsRatio (selected S src) ↔ 1 < selectionOddsRatio S := by
  have h : 0 < oddsRatio src := by
    simp only [oddsRatio]
    have := hsrc true true; have := hsrc false false; have := hsrc true false
    have := hsrc false true
    positivity
  rw [oddsRatio_selected]
  exact lt_mul_iff_one_lt_right h

/-- With positive selection proportions, the selection odds ratio exceeds one if and only if
`S_{case,0} S_{control,1} < S_{case,1} S_{control,0}`. -/
theorem one_lt_selectionOddsRatio_iff (S : Table) (hS : ∀ d e, 0 < S d e) :
    1 < selectionOddsRatio S ↔ S true false * S false true < S true true * S false false := by
  simp only [selectionOddsRatio, oddsRatio]
  have := hS true false; have := hS false true
  rw [one_lt_div (by positivity)]

/-- Multiplicative selection (`S d e = s d * t e`, selection depending on disease and exposure
through separate factors, for example disease only) gives a selection odds ratio of one, so the
odds ratio is not biased by selection, whatever the source odds ratio. -/
theorem selectionOddsRatio_multiplicative (S : Table) (s t : Bool → ℝ)
    (hS : ∀ d e, S d e = s d * t e) (hs : ∀ d, s d ≠ 0) (ht : ∀ e, t e ≠ 0) :
    selectionOddsRatio S = 1 := by
  simp only [selectionOddsRatio, oddsRatio, hS]
  have := hs true; have := hs false; have := ht true; have := ht false
  field_simp

/-- Multiplicative selection preserves the null on the scale-free independence of
`CausalInference.Bias.Selection`: if disease and exposure are independent in the source
(product table `pD d * pE e`) and `S d e = g e * h d`, they are independent among participants.
This is `stratum_indep_of_multiplicative` read in the notation of this file. -/
theorem selected_indep_of_multiplicative (S : Table) (pD pE g h : Bool → ℝ)
    (hS : ∀ d e, S d e = g e * h d) :
    TableIndep (selected S fun d e ↦ pD d * pE e) := by
  have : selected S (fun d e ↦ pD d * pE e) = stratum pD pE S := by
    funext d e; simp only [selected, stratum]; ring
  rw [this]
  exact stratum_indep_of_multiplicative pD pE S g h hS

/-! ### Projection of the exposure prevalence among nonparticipants -/

/-- The projected source table of Fox, MacLehose and Lash (2021), "Bias Analysis by Projecting
the Exposed Proportion Among Nonparticipants". Row `d` has participants `a d e`, nonparticipants
classified by exposure (by a short questionnaire) `b d e`, and `m d` nonparticipants of unknown
exposure, of whom a fraction `p d` is assumed exposed. -/
def proj (a b : Table) (m p : Bool → ℝ) : Table :=
  fun d e ↦ a d e + b d e + (if e then p d else 1 - p d) * m d

/-- The selection proportions implied by the projection: participants over the projected source
cell (Fox, MacLehose and Lash 2021, Table 4.5). -/
noncomputable def projSel (a b : Table) (m p : Bool → ℝ) : Table :=
  fun d e ↦ a d e / proj a b m p d e

/-- The projection is the data-generating description: if the source table consists of the
participants, the classified nonparticipants, and an unclassified part `c` split according to
the projection assumption (`c d 1 = p d * m d`, `c d 0 = (1 - p d) * m d`), then the projected
table is the source table and the participants arise from it by the selection model with the
implied selection proportions. -/
theorem proj_eq_source (a b c : Table) (m p : Bool → ℝ)
    (hc1 : ∀ d, c d true = p d * m d) (hc0 : ∀ d, c d false = (1 - p d) * m d)
    (hpos : ∀ d e, 0 < a d e + b d e + c d e) :
    proj a b m p = (fun d e ↦ a d e + b d e + c d e) ∧
      a = selected (projSel a b m p) (fun d e ↦ a d e + b d e + c d e) := by
  have hP : proj a b m p = fun d e ↦ a d e + b d e + c d e := by
    funext d e; cases e <;> simp [proj, hc1, hc0]
  refine ⟨hP, ?_⟩
  funext d e
  simp only [selected, projSel, hP]
  field_simp [(hpos d e).ne']

/-- The three methods of Fox, MacLehose and Lash (2021) agree ("they are all mathematically
equivalent"): with positive participant cells and positive projected cells, inverse probability
of participation weighting with the projection-implied selection proportions reproduces the
projected table, and the odds ratio of the projected table equals the observed odds ratio
divided by the selection odds ratio (Equation 4.2). -/
theorem projection_ipw_selectionOddsRatio (a b : Table) (m p : Bool → ℝ)
    (ha : ∀ d e, 0 < a d e) (hP : ∀ d e, 0 < proj a b m p d e) :
    ipw (projSel a b m p) a = proj a b m p ∧
      oddsRatio (proj a b m p) = oddsRatio a / selectionOddsRatio (projSel a b m p) := by
  have hS : ∀ d e, 0 < projSel a b m p d e := fun d e ↦ div_pos (ha d e) (hP d e)
  have hipw : ipw (projSel a b m p) a = proj a b m p := by
    funext d e
    simp only [ipw, projSel]
    field_simp [(ha d e).ne', (hP d e).ne']
  refine ⟨hipw, ?_⟩
  rw [← hipw]
  exact oddsRatio_ipw _ a hS ha

/-- The bias-adjusted odds ratio of the projection method as a function of the assumed exposed
proportions `p1` among unclassified nonparticipating cases and `p0` among unclassified
nonparticipating controls (Fox, MacLehose and Lash 2021, Equation 4.1 when `p1`, `p0` are the
short-questionnaire proportions; Table 4.3 for other choices). -/
noncomputable def orProj (a b : Table) (m : Bool → ℝ) (p1 p0 : ℝ) : ℝ :=
  oddsRatio (proj a b m fun d ↦ if d then p1 else p0)

/-- The building block `(x + p m) / (y + (1 - p) m)`: the odds of exposure in one row after
allocating a fraction `p` of `m` unclassified members to the exposed. -/
noncomputable def rowOdds (x y m p : ℝ) : ℝ := (x + p * m) / (y + (1 - p) * m)

theorem rowOdds_pos {x y m p : ℝ} (hx : 0 < x) (hy : 0 < y) (hm : 0 ≤ m) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : 0 < rowOdds x y m p := by
  unfold rowOdds
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The row odds are nondecreasing in the allocated fraction `p` on the unit interval. -/
theorem rowOdds_mono {x y m p q : ℝ} (hx : 0 < x) (hy : 0 < y) (hm : 0 ≤ m)
    (hpq : p ≤ q) (hq1 : q ≤ 1) : rowOdds x y m p ≤ rowOdds x y m q := by
  unfold rowOdds
  have h1 : 0 ≤ 1 - p := by linarith
  have h2 : 0 ≤ 1 - q := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hpq) hm) (by positivity : 0 ≤ x + y + m)]

/-- The projected odds ratio is the product of the case row odds in `p1` and the reciprocal of
the control row odds in `p0`. -/
theorem orProj_eq (a b : Table) (m : Bool → ℝ) (p1 p0 : ℝ) :
    orProj a b m p1 p0 =
      rowOdds (a true true + b true true) (a true false + b true false) (m true) p1 *
        rowOdds (a false false + b false false) (a false true + b false true) (m false)
          (1 - p0) := by
  simp only [orProj, oddsRatio, proj, rowOdds, ite_true, ite_false, Bool.false_eq_true]
  rw [div_mul_div_comm]
  ring_nf

variable {a b : Table} {m : Bool → ℝ}

/-- The projected odds ratio is nondecreasing in the assumed exposed proportion `p1` among
unclassified nonparticipating cases. -/
theorem orProj_mono_left (hk : ∀ d e, 0 < a d e + b d e) (hm : ∀ d, 0 ≤ m d) {p1 p1' p0 : ℝ}
    (h01 : p1 ≤ p1') (h1 : p1' ≤ 1) (hp0 : 0 ≤ p0) (hp0' : p0 ≤ 1) :
    orProj a b m p1 p0 ≤ orProj a b m p1' p0 := by
  rw [orProj_eq, orProj_eq]
  exact mul_le_mul_of_nonneg_right (rowOdds_mono (hk _ _) (hk _ _) (hm _) h01 h1)
    (rowOdds_pos (hk _ _) (hk _ _) (hm _) (by linarith) (by linarith)).le

/-- The projected odds ratio is nonincreasing in the assumed exposed proportion `p0` among
unclassified nonparticipating controls. -/
theorem orProj_anti_right (hk : ∀ d e, 0 < a d e + b d e) (hm : ∀ d, 0 ≤ m d) {p1 p0 p0' : ℝ}
    (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1) (h0 : 0 ≤ p0) (h01 : p0 ≤ p0') :
    orProj a b m p1 p0' ≤ orProj a b m p1 p0 := by
  rw [orProj_eq, orProj_eq]
  exact mul_le_mul_of_nonneg_left
    (rowOdds_mono (hk _ _) (hk _ _) (hm _) (by linarith) (by linarith))
    (rowOdds_pos (hk _ _) (hk _ _) (hm _) hp1 hp1').le

/-- Extreme scenarios bound the projection: over all assumed exposed proportions
`(p1, p0) ∈ [0, 1]²`, the adjusted odds ratio lies between its values at `(0, 1)` (no
unclassified case exposed, every unclassified control exposed) and at `(1, 0)`. The scenarios
"all exposed" `(1, 1)` and "all unexposed" `(0, 0)` of Table 4.3 are in general not the
extremes (see `Examples.orProj_stang_corners`). -/
theorem orProj_mem_Icc (hk : ∀ d e, 0 < a d e + b d e) (hm : ∀ d, 0 ≤ m d) {p1 p0 : ℝ}
    (hp1 : 0 ≤ p1) (hp1' : p1 ≤ 1) (hp0 : 0 ≤ p0) (hp0' : p0 ≤ 1) :
    orProj a b m p1 p0 ∈ Set.Icc (orProj a b m 0 1) (orProj a b m 1 0) := by
  constructor
  · exact (orProj_mono_left hk hm hp1 hp1' zero_le_one le_rfl).trans
      (orProj_anti_right hk hm hp1 hp1' hp0 hp0')
  · exact (orProj_anti_right hk hm hp1 hp1' le_rfl hp0).trans
      (orProj_mono_left hk hm hp1' le_rfl le_rfl zero_le_one)

/-- The identified set of the selection-adjusted odds ratio when the exposed proportions among
unclassified nonparticipants are unrestricted in `[0, 1]²` (the data, fixed here, carry no
information about them) is exactly the interval between the two extreme scenarios. -/
theorem identifiedSet_orProj (hk : ∀ d e, 0 < a d e + b d e) (hm : ∀ d, 0 ≤ m d) :
    identifiedSet (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (fun _ ↦ ())
        (fun q ↦ orProj a b m q.1 q.2) () =
      Set.Icc (orProj a b m 0 1) (orProj a b m 1 0) := by
  ext t
  simp only [mem_identifiedSet, Set.mem_prod, Set.mem_Icc, true_and, Prod.exists]
  constructor
  · rintro ⟨p1, p0, ⟨⟨h1, h1'⟩, h0, h0'⟩, rfl⟩
    exact orProj_mem_Icc hk hm h1 h1' h0 h0'
  · intro ht
    set g : ℝ → ℝ := fun s ↦ orProj a b m s (1 - s) with hg
    have hcont : ContinuousOn g (Set.Icc 0 1) := by
      have hgeq : g = fun s ↦
          rowOdds (a true true + b true true) (a true false + b true false) (m true) s *
            rowOdds (a false false + b false false) (a false true + b false true) (m false)
              (1 - (1 - s)) := by
        funext s; change orProj a b m s (1 - s) = _; rw [orProj_eq]
      rw [hgeq]
      unfold rowOdds
      apply ContinuousOn.mul <;> apply ContinuousOn.div <;>
        first
        | exact Continuous.continuousOn (by fun_prop)
        | intro s hs
          apply ne_of_gt
          have h1 : 0 ≤ s := hs.1
          have h2 : 0 ≤ 1 - s := by linarith [hs.2]
          nlinarith [hk true true, hk true false, hk false true, hk false false,
            mul_nonneg h1 (hm true), mul_nonneg h2 (hm true), mul_nonneg h1 (hm false),
            mul_nonneg h2 (hm false)]
    have hIVT := intermediate_value_Icc zero_le_one hcont
    have hg0 : g 0 = orProj a b m 0 1 := by simp [hg]
    have hg1 : g 1 = orProj a b m 1 0 := by simp [hg]
    rw [hg0, hg1] at hIVT
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hIVT ht
    exact ⟨s, 1 - s, ⟨⟨hs0, hs1⟩, by linarith, by linarith⟩, hs⟩

/-! ### Selection bias without a collider: effect modification by a cause of participation -/

section EffectModification

open Finset

variable {ι : Type*} [Fintype ι]

/-- The weighted mean `∑ q u * r u / ∑ q u` of a stratum-specific risk `r` under nonnegative
stratum weights `q` (a risk in a population whose distribution of `U` is proportional to `q`). -/
noncomputable def mixRisk (q r : ι → ℝ) : ℝ := (∑ u, q u * r u) / ∑ u, q u

/-- The setting of Fox, MacLehose and Lash (2021), Figure 4.3 (after Hernán 2017): `U` affects
disease and participation only. `q e u` is the source distribution of `U` in exposure arm `e`,
`s u = P(P = 1 | U = u)` is participation depending on `U` only, and `r e u` is the risk of
disease given `E = e`, `U = u`, unchanged by conditioning on participation because participation
depends on `U` only. This is the risk among participants in arm `e`. -/
noncomputable def partRisk (q : Bool → ι → ℝ) (s : ι → ℝ) (r : Bool → ι → ℝ) (e : Bool) : ℝ :=
  mixRisk (fun u ↦ q e u * s u) (r e)

/-- The risk among nonparticipants in arm `e` in the setting of `partRisk`. -/
noncomputable def nonpartRisk (q : Bool → ι → ℝ) (s : ι → ℝ) (r : Bool → ι → ℝ)
    (e : Bool) : ℝ :=
  mixRisk (fun u ↦ q e u * (1 - s u)) (r e)

/-- The source risk is the participation-weighted average of the participants' and
nonparticipants' risks: with `π = ∑ q s / ∑ q`, `mixRisk q r = π * part + (1 - π) * nonpart`. -/
theorem mixRisk_eq_participation (q s r : ι → ℝ) (hq : ∑ u, q u ≠ 0)
    (hp : ∑ u, q u * s u ≠ 0) (hn : ∑ u, q u * (1 - s u) ≠ 0) :
    mixRisk q r = (∑ u, q u * s u) / (∑ u, q u) * mixRisk (fun u ↦ q u * s u) r +
      (1 - (∑ u, q u * s u) / (∑ u, q u)) * mixRisk (fun u ↦ q u * (1 - s u)) r := by
  have hsplit : ∑ u, q u * (1 - s u) = ∑ u, q u - ∑ u, q u * s u := by
    rw [← sum_sub_distrib]; congr 1; funext u; ring
  have hsplit' : ∑ u, q u * (1 - s u) * r u = ∑ u, q u * r u - ∑ u, q u * s u * r u := by
    rw [← sum_sub_distrib]; congr 1; funext u; ring
  unfold mixRisk
  rw [hsplit, hsplit']
  rw [hsplit] at hn
  field_simp
  ring

/-- Hernán's condition on the risk difference scale (Fox, MacLehose and Lash 2021, "Depicting
Selection Bias Using Causal Graphs"). If `U` is independent of exposure in the source
(`q 1 = q 0`) and participation depends on `U` only, the selection bias of the risk difference
equals `1 - π` times the variation across exposure arms of the participation to disease risk
difference: `RD_part - RD_source = (1 - π) * (RD_{PD | E = 1} - RD_{PD | E = 0})`, where
`RD_{PD | E = e}` is the risk among participants minus the risk among nonparticipants in arm `e`
and `π` is the participation proportion. -/
theorem partRD_sub_sourceRD (q : Bool → ι → ℝ) (s : ι → ℝ) (r : Bool → ι → ℝ)
    (hindep : q true = q false) (hq : ∑ u, q false u ≠ 0)
    (hp : ∑ u, q false u * s u ≠ 0) (hn : ∑ u, q false u * (1 - s u) ≠ 0) :
    (partRisk q s r true - partRisk q s r false) -
        (mixRisk (q true) (r true) - mixRisk (q false) (r false)) =
      (1 - (∑ u, q false u * s u) / ∑ u, q false u) *
        ((partRisk q s r true - nonpartRisk q s r true) -
          (partRisk q s r false - nonpartRisk q s r false)) := by
  simp only [partRisk, nonpartRisk, hindep]
  rw [mixRisk_eq_participation (q false) s (r true) hq hp hn,
    mixRisk_eq_participation (q false) s (r false) hq hp hn]
  ring

/-- No selection bias of the risk difference when participation depends on `U` only, `U` is
independent of exposure, and the stratum risk differences are all equal (no effect modification
by `U` on the difference scale): the participants' risk difference equals the source risk
difference. -/
theorem partRD_eq_of_const (q : Bool → ι → ℝ) (s : ι → ℝ) (r : Bool → ι → ℝ) (c : ℝ)
    (hindep : q true = q false) (hq : ∑ u, q false u ≠ 0) (hp : ∑ u, q false u * s u ≠ 0)
    (hδ : ∀ u, r true u - r false u = c) :
    partRisk q s r true - partRisk q s r false =
      mixRisk (q true) (r true) - mixRisk (q false) (r false) := by
  have key : ∀ w : ι → ℝ, ∑ u, w u ≠ 0 → mixRisk w (r true) - mixRisk w (r false) = c := by
    intro w hw
    unfold mixRisk
    rw [div_sub_div_same, ← sum_sub_distrib, div_eq_iff hw, mul_sum]
    congr 1; funext u
    rw [← mul_sub, hδ u, mul_comm]
  simp only [partRisk, hindep]
  rw [key _ hp, key _ hq]

/-- No selection bias of the risk ratio under the same structure when the stratum risk ratios
are all equal to `ρ` (`r 1 u = ρ * r 0 u`): the participants' risk ratio equals the source risk
ratio. Positivity of the risks among the unexposed is assumed so that both ratios are defined. -/
theorem partRR_eq_of_const (q : Bool → ι → ℝ) (s : ι → ℝ) (r : Bool → ι → ℝ) (ρ : ℝ)
    (hindep : q true = q false) (hq : ∑ u, q false u ≠ 0) (hp : ∑ u, q false u * s u ≠ 0)
    (hr0 : ∑ u, q false u * r false u ≠ 0) (hr0' : ∑ u, q false u * s u * r false u ≠ 0)
    (hρ : ∀ u, r true u = ρ * r false u) :
    partRisk q s r true / partRisk q s r false =
      mixRisk (q true) (r true) / mixRisk (q false) (r false) := by
  have key : ∀ w : ι → ℝ, ∑ u, w u ≠ 0 → ∑ u, w u * r false u ≠ 0 →
      mixRisk w (r true) / mixRisk w (r false) = ρ := by
    intro w hw hwr
    unfold mixRisk
    rw [div_div_div_cancel_right₀ hw, div_eq_iff hwr, mul_sum]
    congr 1; funext u
    rw [hρ u]; ring
  simp only [partRisk, hindep]
  rw [key _ hp hr0', key _ hq hr0]

end EffectModification

/-! ### Loss to follow-up -/

section LossToFollowUp

open Finset

/-- The bias-adjusted rate of one exposure group after crediting the lost to follow-up with `x`
deaths and `t` person-years: `(d + x) / (T + t)`, where `d` deaths and `T` person-years were
observed among the followed (Fox, MacLehose and Lash 2021, "Bias Analysis by Modeling
Outcomes", Table 4.7). -/
noncomputable def adjRate (d T x t : ℝ) : ℝ := (d + x) / (T + t)

/-- The mediant identity behind the "lost as followed" row of Table 4.7: if the lost contribute
deaths and person-time at the observed rate `r` (`d = r T`, `x = r t`), the adjusted rate is
`r`. -/
theorem adjRate_eq_of_same_rate {d T x t r : ℝ} (hd : d = r * T) (hx : x = r * t)
    (hT : T + t ≠ 0) : adjRate d T x t = r := by
  unfold adjRate
  rw [div_eq_iff hT, hd, hx]
  ring

/-- "Lost as followed" in the book's form: `n` followed with `d` deaths and `T` person-years,
`l` lost, each credited with the observed mean person-time `T / n` and the observed risk
`d / n`; the adjusted rate equals the observed rate `d / T`. -/
theorem adjRate_lost_as_followed {d T n l : ℝ} (hT : 0 < T) (hn : 0 < n) (hl : 0 ≤ l) :
    adjRate d T (d / n * l) (T / n * l) = d / T := by
  apply adjRate_eq_of_same_rate (r := d / T)
  · field_simp
  · field_simp
  · positivity

/-- The adjusted rate is nondecreasing in the number `x` of deaths credited to the lost. -/
theorem adjRate_mono {d T t x x' : ℝ} (hT : 0 < T + t) (hx : x ≤ x') :
    adjRate d T x t ≤ adjRate d T x' t := by
  unfold adjRate
  gcongr

/-- Extreme scenarios for the rate ratio under loss to follow-up, with the person-time credited
to the lost held fixed (as in Table 4.7): if `x1 ∈ [0, l1]` deaths are credited to the `l1` lost
exposed and `x0 ∈ [0, l0]` to the `l0` lost unexposed, the adjusted rate ratio lies between its
value with no lost exposed death and all lost unexposed dead, and its value with all lost
exposed dead and no lost unexposed death. The diagonal scenarios "all lost died" and "no lost
died" of Table 4.7 are in general not the extremes (see `Examples.table47_extremes`). -/
theorem adjRateRatio_mem_Icc {d1 T1 t1 d0 T0 t0 l1 l0 x1 x0 : ℝ} (hd1 : 0 ≤ d1)
    (hd0 : 0 < d0) (h1 : 0 < T1 + t1) (h0 : 0 < T0 + t0) (hx1 : 0 ≤ x1) (hx1' : x1 ≤ l1)
    (hx0 : 0 ≤ x0) (hx0' : x0 ≤ l0) :
    adjRate d1 T1 x1 t1 / adjRate d0 T0 x0 t0 ∈
      Set.Icc (adjRate d1 T1 0 t1 / adjRate d0 T0 l0 t0)
        (adjRate d1 T1 l1 t1 / adjRate d0 T0 0 t0) := by
  have p0 : ∀ y, 0 ≤ y → 0 < adjRate d0 T0 y t0 := fun y hy ↦ by
    unfold adjRate; positivity
  have n1 : ∀ y, 0 ≤ y → 0 ≤ adjRate d1 T1 y t1 := fun y hy ↦ by
    unfold adjRate; positivity
  constructor
  · exact div_le_div₀ (n1 x1 hx1) (adjRate_mono h1 hx1) (p0 x0 hx0)
      (adjRate_mono h0 hx0')
  · exact div_le_div₀ (n1 l1 (hx1.trans hx1')) (adjRate_mono h1 hx1') (p0 0 le_rfl)
      (adjRate_mono h0 hx0)

/-- Extreme scenarios for the rate difference under loss to follow-up, as in
`adjRateRatio_mem_Icc`. -/
theorem adjRateDiff_mem_Icc {d1 T1 t1 d0 T0 t0 l1 l0 x1 x0 : ℝ} (h1 : 0 < T1 + t1)
    (h0 : 0 < T0 + t0) (hx1 : 0 ≤ x1) (hx1' : x1 ≤ l1) (hx0 : 0 ≤ x0) (hx0' : x0 ≤ l0) :
    adjRate d1 T1 x1 t1 - adjRate d0 T0 x0 t0 ∈
      Set.Icc (adjRate d1 T1 0 t1 - adjRate d0 T0 l0 t0)
        (adjRate d1 T1 l1 t1 - adjRate d0 T0 0 t0) := by
  constructor
  · exact sub_le_sub (adjRate_mono h1 hx1) (adjRate_mono h0 hx0')
  · exact sub_le_sub (adjRate_mono h1 hx1') (adjRate_mono h0 hx0)

/-- Inverse probability of follow-up weighting over a finite set of strata `h` (for example
exposure by hospital): if in each stratum the followed contribution is the full-cohort
contribution times the follow-up probability `π h ≠ 0` (follow-up at random within strata), the
weighted total `∑ obs h / π h` equals the full-cohort total. Applied to deaths and to
person-time it recovers the full-cohort rate (`ipw_rate`). This is a finite analogue (proved
directly, not derived from it) of `ipcw_identity` of `CausalInference.MissingData.Weighting`. -/
theorem sum_ipw_eq {κ : Type*} [Fintype κ] (π obs full : κ → ℝ) (hπ : ∀ h, π h ≠ 0)
    (hobs : ∀ h, obs h = π h * full h) : ∑ h, obs h / π h = ∑ h, full h := by
  congr 1; funext h
  rw [hobs, mul_div_cancel_left₀ _ (hπ h)]

/-- The weighted rate recovers the full-cohort rate when deaths and person-time are both
thinned by the stratum follow-up probabilities: the weighted deaths and the weighted
person-time equal the full-cohort deaths and person-time separately, so the weighted rate is
the full-cohort rate (which is defined when the full-cohort person-time is positive). -/
theorem ipw_rate {κ : Type*} [Fintype κ] (π dObs TObs dFull TFull : κ → ℝ)
    (hπ : ∀ h, π h ≠ 0) (hd : ∀ h, dObs h = π h * dFull h)
    (hT : ∀ h, TObs h = π h * TFull h) :
    ∑ h, dObs h / π h = ∑ h, dFull h ∧ ∑ h, TObs h / π h = ∑ h, TFull h ∧
      (∑ h, dObs h / π h) / (∑ h, TObs h / π h) = (∑ h, dFull h) / ∑ h, TFull h := by
  rw [sum_ipw_eq π dObs dFull hπ hd, sum_ipw_eq π TObs TFull hπ hT]
  exact ⟨rfl, rfl, rfl⟩

end LossToFollowUp

/-! ### Participation proportions from an overall participation rate -/

/-- Equation 12.1 of Fox, MacLehose and Lash (2021): the participation proportion among the
unexposed, `p_{AD-} = p_obs / ((1 - w) + R w)`, from the overall participation proportion
`p_obs`, the exposure prevalence `w`, and the participation ratio `R` of exposed to unexposed. -/
noncomputable def participationUnexposed (pobs w R : ℝ) : ℝ := pobs / ((1 - w) + R * w)

/-- Equation 12.1 recovers the participation proportions: if the overall participation is the
mixture `p_obs = (1 - w) p0 + w p1` with `p1 = R p0`, then `p0 = p_obs / ((1 - w) + R w)` and
`p1 = R p0`. -/
theorem participationUnexposed_eq {pobs w R p0 : ℝ} (hden : (1 - w) + R * w ≠ 0)
    (hmix : pobs = (1 - w) * p0 + w * (R * p0)) : participationUnexposed pobs w R = p0 := by
  unfold participationUnexposed
  rw [div_eq_iff hden, hmix]
  ring

/-- Admissibility of Equation 12.1: with a positive denominator, the computed participation
proportion among the unexposed is at most one if and only if `p_obs ≤ (1 - w) + R w`. -/
theorem participationUnexposed_le_one_iff {pobs w R : ℝ} (hden : 0 < (1 - w) + R * w) :
    participationUnexposed pobs w R ≤ 1 ↔ pobs ≤ (1 - w) + R * w := by
  unfold participationUnexposed
  rw [div_le_one hden]

/-- Admissibility of the exposed participation proportion `R p0`: with a positive denominator,
it is at most one if and only if `R p_obs ≤ (1 - w) + R w`. -/
theorem participationExposed_le_one_iff {pobs w R : ℝ} (hden : 0 < (1 - w) + R * w) :
    R * participationUnexposed pobs w R ≤ 1 ↔ R * pobs ≤ (1 - w) + R * w := by
  unfold participationUnexposed
  rw [← mul_div_assoc, div_le_one hden]

/-! ### Worked examples -/

namespace Examples

/-! #### Table 4.1: collider selection under the null -/

/-- The source ("all eligible") table of Fox, MacLehose and Lash (2021), Table 4.1: 100 exposed
and 100 unexposed leukemia cases, 900 exposed and 900 unexposed noncases. -/
def src41 : Table := fun d _ ↦ if d then 100 else 900

/-- The participation proportions of Table 4.1: 80/100, 60/100, 400/900 and 200/900. -/
noncomputable def sel41 : Table := fun d e ↦
  if d then (if e then 80 / 100 else 60 / 100) else (if e then 400 / 900 else 200 / 900)

/-- The participants' table of Table 4.1 is the selection model applied to the source:
80, 60, 400, 200. -/
theorem selected41 : selected sel41 src41 =
    fun d e ↦ if d then (if e then 80 else 60) else (if e then 400 else 200) := by
  funext d e; cases d <;> cases e <;> norm_num [selected, sel41, src41]

/-- In the source of Table 4.1 exposure and disease are independent (odds ratio one). -/
theorem src41_indep : TableIndep src41 := by
  rw [tableIndep_bool_iff]; norm_num [src41]

/-- Among the participants of Table 4.1 they are dependent, with odds ratio
`(80 * 200) / (400 * 60) = 2/3` (printed 0.67), which is the selection odds ratio. -/
theorem selected41_not_indep_oddsRatio :
    ¬ TableIndep (selected sel41 src41) ∧ oddsRatio (selected sel41 src41) = 2 / 3 ∧
      selectionOddsRatio sel41 = 2 / 3 := by
  rw [tableIndep_bool_iff, selected41]
  refine ⟨by norm_num, by norm_num [oddsRatio], by norm_num [selectionOddsRatio, oddsRatio, sel41]⟩

/-- The participation odds ratios of Table 4.1: with exposure,
`(480/520) / (260/740) = 444/169` (printed 2.63); with leukemia, `(140/600) / (60/1200) = 14/3`
(printed 4.67). -/
theorem participation41 :
    (480 / 520 : ℝ) / (260 / 740) = 444 / 169 ∧ (140 / 600 : ℝ) / (60 / 1200) = 14 / 3 ∧
      (2.62 : ℝ) < 444 / 169 ∧ (444 / 169 : ℝ) < 2.63 := by
  norm_num

/-! #### Figure 4.3: selection bias without a collider -/

/-- Equal source weights of `U` in both exposure arms. -/
noncomputable def q43 (_ : Bool) (_ : Bool) : ℝ := 1 / 2

/-- Participation depending on `U` only: `3/5` if `U = 1`, `1/5` if `U = 0`, so that
participants are 75% `U = 1`. -/
noncomputable def s43 (u : Bool) : ℝ := if u then 3 / 5 else 1 / 5

/-- Stratum risks with risk difference `0.2` when `U = 1` and `-0.2` when `U = 0`. -/
noncomputable def r43 (e u : Bool) : ℝ := if e == u then 2 / 5 else 1 / 5

/-- The example of Fox, MacLehose and Lash (2021) after Figure 4.3: participants are 75% and 25%
`U = 1` and `U = 0` while the source is 50% and 50%; the source risk difference is `0` and the
participants' risk difference is `0.1`, although participation depends on `U` only (no
collider). The participants' risks are `0.35` and `0.25`, so the risk ratio is also biased
(`1` in the source, `7/5` among participants). Effect modification by `U` cannot be dropped
from `partRD_eq_of_const` or `partRR_eq_of_const`. -/
theorem example43 :
    q43 false true * s43 true / (∑ u, q43 false u * s43 u) = 3 / 4 ∧
      mixRisk (q43 true) (r43 true) - mixRisk (q43 false) (r43 false) = 0 ∧
      partRisk q43 s43 r43 true - partRisk q43 s43 r43 false = 1 / 10 ∧
      mixRisk (q43 true) (r43 true) / mixRisk (q43 false) (r43 false) = 1 ∧
      partRisk q43 s43 r43 true / partRisk q43 s43 r43 false = 7 / 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [mixRisk, partRisk, q43, s43, r43, Fintype.sum_bool]

/-! #### Stang et al.: mobile phone use and uveal melanoma (Tables 4.2, 4.3, 4.5) -/

/-- Participants of Table 4.2: cases 136 regular users and 107 nonusers, controls 297 and 165. -/
def stangA : Table := fun d e ↦
  if d then (if e then 136 else 107) else (if e then 297 else 165)

/-- Nonparticipants who answered the short questionnaire (Table 4.2): cases 3 and 7, controls
72 and 212. -/
def stangB : Table := fun d e ↦
  if d then (if e then 3 else 7) else (if e then 72 else 212)

/-- Nonparticipants without the short questionnaire (Table 4.2): 17 cases and 379 controls. -/
def stangM (d : Bool) : ℝ := if d then 17 else 379

/-- The crude odds ratio among participants, `(136/297)/(107/165) = 680/963` (printed 0.71),
and among short-questionnaire nonparticipants, `(3/72)/(7/212) = 53/42` (printed 1.26). -/
theorem stang_crude :
    oddsRatio stangA = 680 / 963 ∧ oddsRatio stangB = 53 / 42 ∧
      (0.70 : ℝ) < 680 / 963 ∧ (680 / 963 : ℝ) < 0.71 ∧
      (1.26 : ℝ) < 53 / 42 ∧ (53 / 42 : ℝ) < 1.27 := by
  norm_num [oddsRatio, stangA, stangB]

/-- Equation 4.1: projecting the short-questionnaire prevalences `3/10` and `72/284` onto the
unclassified nonparticipants gives the bias-adjusted odds ratio `7501846/4619271`, about
`1.624` (printed 1.62). -/
theorem stang_eq41 :
    orProj stangA stangB stangM (3 / 10) (72 / 284) = 7501846 / 4619271 ∧
      (1.62 : ℝ) < 7501846 / 4619271 ∧ (7501846 / 4619271 : ℝ) < 1.63 := by
  norm_num [orProj, oddsRatio, proj, stangA, stangB, stangM]

/-- The selection proportions of Table 4.5, exactly `1360/1441`, `1070/1259`, `781/1223` and
`3905/15618` (printed 0.94, 0.85, 0.64, 0.25), with selection odds ratio about `0.435` (printed
0.43). -/
theorem stang_selection :
    projSel stangA stangB stangM (fun d ↦ if d then 3 / 10 else 72 / 284) =
        (fun d e ↦ if d then (if e then 1360 / 1441 else 1070 / 1259)
          else (if e then 781 / 1223 else 3905 / 15618)) ∧
      (0.43 : ℝ) < selectionOddsRatio
          (fun d e ↦ if d then (if e then 1360 / 1441 else 1070 / 1259)
            else (if e then 781 / 1223 else 3905 / 15618)) ∧
      selectionOddsRatio
          (fun d e ↦ if d then (if e then 1360 / 1441 else 1070 / 1259)
            else (if e then 781 / 1223 else 3905 / 15618)) < (0.44 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · funext d e
    cases d <;> cases e <;> norm_num [projSel, proj, stangA, stangB, stangM]
  · norm_num [selectionOddsRatio, oddsRatio]
  · norm_num [selectionOddsRatio, oddsRatio]

/-- The three methods agree on the Stang data (Equation 4.1, Equation 4.2, and inverse
probability of participation weighting): the observed odds ratio divided by the selection odds
ratio of Table 4.5 is the projected odds ratio of Equation 4.1. The weighting display after
Table 4.5 is garbled in the source; this is the identity it intends. -/
theorem stang_three_methods :
    oddsRatio stangA /
        selectionOddsRatio (projSel stangA stangB stangM fun d ↦ if d then 3 / 10 else 72 / 284)
      = orProj stangA stangB stangM (3 / 10) (72 / 284) ∧
      ipw (projSel stangA stangB stangM fun d ↦ if d then 3 / 10 else 72 / 284) stangA =
        proj stangA stangB stangM fun d ↦ if d then 3 / 10 else 72 / 284 := by
  have ha : ∀ d e, 0 < stangA d e := by
    intro d e; cases d <;> cases e <;> norm_num [stangA]
  have hP : ∀ d e, 0 < proj stangA stangB stangM (fun d ↦ if d then 3 / 10 else 72 / 284) d e := by
    intro d e; cases d <;> cases e <;> norm_num [proj, stangA, stangB, stangM]
  obtain ⟨h1, h2⟩ := projection_ipw_selectionOddsRatio stangA stangB stangM _ ha hP
  exact ⟨h2.symm, h1⟩

/-- The rounded display after Table 4.5, `0.71 * (0.85 * 0.64) / (0.94 * 0.25)`, evaluates to
about `1.645`, not the printed 1.62; the book notes that unrounded components must be used. -/
theorem stang_rounded_display :
    (1.64 : ℝ) < 0.71 * (0.85 * 0.64) / (0.94 * 0.25) ∧
      0.71 * (0.85 * 0.64) / (0.94 * 0.25) < (1.65 : ℝ) := by
  norm_num

/-- The scenarios of Table 4.3: "no questionnaire as full participants" (prevalences `136/243`
and `297/462`) gives about `1.02`; "all unexposed" `(0, 0)` gives `11676/5371`, about `2.17`;
"all exposed" `(1, 1)` gives `4901/7106`, about `0.69` (all as printed). -/
theorem stang_table43 :
    orProj stangA stangB stangM (136 / 243) (297 / 462) = 28762933 / 28133513 ∧
      orProj stangA stangB stangM 0 0 = 11676 / 5371 ∧
      orProj stangA stangB stangM 1 1 = 4901 / 7106 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [orProj, oddsRatio, proj, stangA, stangB, stangM]

/-- The extremes over all exposed proportions in `[0, 1]²` are `(0, 1)`, giving
`52403/97988`, about `0.53`, and `(1, 0)`, giving `2184/779`, about `2.80`. These lie strictly
outside the "all exposed" and "all unexposed" values `0.69` and `2.17` of Table 4.3, so those
two scenarios are not limits of the selection bias when the case and control prevalences may
differ. -/
theorem orProj_stang_corners :
    orProj stangA stangB stangM 0 1 = 52403 / 97988 ∧
      orProj stangA stangB stangM 1 0 = 2184 / 779 ∧
      orProj stangA stangB stangM 0 1 < orProj stangA stangB stangM 1 1 ∧
      orProj stangA stangB stangM 0 0 < orProj stangA stangB stangM 1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [orProj, oddsRatio, proj, stangA, stangB, stangM]

/-! #### Table 4.7: loss to follow-up -/

/-- Observed rates of Table 4.6: `40/687` and `65/2560` per person-year, rate difference about
`3.3` per 100 person-years and rate ratio `20480/8931`, about `2.29` (printed 2.3). -/
theorem table46 :
    (0.032 : ℝ) < 40 / 687 - 65 / 2560 ∧ (40 / 687 - 65 / 2560 : ℝ) < 0.033 ∧
      (40 / 687 : ℝ) / (65 / 2560) = 20480 / 8931 := by
  norm_num

/-- "Lost as followed" in Table 4.7: crediting the 13 and 46 lost with the observed mean
person-time (`687/104` and `2560/286` years) and the observed risk leaves both rates
unchanged, hence also the rate difference and ratio. -/
theorem table47_lost_as_followed :
    adjRate 40 687 (40 / 104 * 13) (687 / 104 * 13) = 40 / 687 ∧
      adjRate 65 2560 (65 / 286 * 46) (2560 / 286 * 46) = 65 / 2560 :=
  ⟨adjRate_lost_as_followed (by norm_num) (by norm_num) (by norm_num),
    adjRate_lost_as_followed (by norm_num) (by norm_num) (by norm_num)⟩

/-- Printed error in Table 4.7, "all lost died": with the exact credited person-time
(`687/104` and `2560/286` years per lost participant) the rate ratio is about `1.84` and the
rate difference about `3.1` per 100 person-years, not the printed 2.4 and 4.4. -/
theorem table47_all_died :
    (1.83 : ℝ) < adjRate 40 687 13 (687 / 104 * 13) / adjRate 65 2560 46 (2560 / 286 * 46) ∧
      adjRate 40 687 13 (687 / 104 * 13) / adjRate 65 2560 46 (2560 / 286 * 46) < 1.84 ∧
      (0.031 : ℝ) < adjRate 40 687 13 (687 / 104 * 13) - adjRate 65 2560 46 (2560 / 286 * 46) ∧
      adjRate 40 687 13 (687 / 104 * 13) - adjRate 65 2560 46 (2560 / 286 * 46) < 0.032 := by
  norm_num [adjRate]

/-- Printed error in Table 4.7, "no lost died": with the exact credited person-time the rate
ratio is about `2.37` and the rate difference about `3.0` per 100 person-years, not the printed
2.3 and 2.7. Crediting 12 years to every lost participant instead gives about `2.27` and `2.66`,
which matches the printed row. -/
theorem table47_none_died :
    (2.36 : ℝ) < adjRate 40 687 0 (687 / 104 * 13) / adjRate 65 2560 0 (2560 / 286 * 46) ∧
      adjRate 40 687 0 (687 / 104 * 13) / adjRate 65 2560 0 (2560 / 286 * 46) < 2.37 ∧
      (0.0298 : ℝ) < adjRate 40 687 0 (687 / 104 * 13) - adjRate 65 2560 0 (2560 / 286 * 46) ∧
      adjRate 40 687 0 (687 / 104 * 13) - adjRate 65 2560 0 (2560 / 286 * 46) < 0.0299 ∧
      (2.27 : ℝ) < adjRate 40 687 0 (12 * 13) / adjRate 65 2560 0 (12 * 46) ∧
      adjRate 40 687 0 (12 * 13) / adjRate 65 2560 0 (12 * 46) < 2.28 ∧
      (0.0265 : ℝ) < adjRate 40 687 0 (12 * 13) - adjRate 65 2560 0 (12 * 46) ∧
      adjRate 40 687 0 (12 * 13) - adjRate 65 2560 0 (12 * 46) < 0.0266 := by
  norm_num [adjRate]

/-- The diagonal rows of Table 4.7 do not bound the rate ratio: the extreme scenarios of
`adjRateRatio_mem_Icc` (all 13 lost exposed died and no lost unexposed died; no lost exposed
died and all 46 lost unexposed died) give about `3.14` and `1.39`, outside the interval between
the "all lost died" (`1.84`) and "no lost died" (`2.37`) values. -/
theorem table47_extremes :
    (3.13 : ℝ) < adjRate 40 687 13 (687 / 104 * 13) / adjRate 65 2560 0 (2560 / 286 * 46) ∧
      adjRate 40 687 0 (687 / 104 * 13) / adjRate 65 2560 46 (2560 / 286 * 46) < 1.39 := by
  norm_num [adjRate]

/-! #### Equation 12.1 -/

/-- Equation 12.1 for the controls of Chien et al. (Fox, MacLehose and Lash 2021, text before
Table 12.4): `0.738 / ((1 - 0.12) + 0.8 * 0.12) = 369/488`, about `0.756`, and `0.8` times it
about `0.605`; for the cases `0.806 / ((1 - 0.12) + 0.9 * 0.12) = 31/38`, about `0.816`, and
`0.9` times it about `0.734` (all as printed in Table 12.4). -/
theorem eq121_chien :
    participationUnexposed 0.738 0.12 0.8 = 369 / 488 ∧
      (0.604 : ℝ) < 0.8 * (369 / 488) ∧ 0.8 * (369 / 488 : ℝ) < 0.605 ∧
      participationUnexposed 0.806 0.12 0.9 = 31 / 38 ∧
      (0.734 : ℝ) < 0.9 * (31 / 38) ∧ 0.9 * (31 / 38 : ℝ) < 0.735 := by
  norm_num [participationUnexposed]

/-- Equation 12.1 can return an inadmissible participation proportion: with `p_obs = 0.9`,
`w = 0.5` and `R = 0.5`, it gives `p_{AD-} = 1.2 > 1`. -/
theorem eq121_inadmissible : participationUnexposed 0.9 0.5 0.5 = 1.2 ∧
    1 < participationUnexposed 0.9 0.5 0.5 := by
  norm_num [participationUnexposed]

end Examples

end SelectionAdjustment

end BiasAnalysis

end CausalInference
