/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.DifferenceInDifferences.TwoPeriod

/-!
# Difference in differences with repeated cross sections

The two by two design of `TwoPeriod.lean` assumes panel data: one population `(Ω, μ)` whose
units carry both periods' outcomes. With repeated cross sections no unit is observed twice. The
data are, for each period `t`, the joint law `ρ t` on `Bool × ℝ` of the group indicator and the
observed outcome in the sample drawn in period `t`, and the cross-section difference in
differences `rcsDid ρ` is built from the four group means of these two laws. The latent panel
population `(Ω, μ)` with its potential outcomes is not observed; the estimand (the ATT) is a
functional of it.

Probability setting: a finite measure `μ` on a measurable space `Ω` for the latent population,
and measures on `Bool × ℝ` for the period samples; conditional means are taken against
`ProbabilityTheory.cond`. The identification results of `TwoPeriod.lean` assume panel data;
this file transfers them to repeated cross sections under stable composition.

## Main definitions

* `RepeatedCrossSection.rcsDid`: the cross-section difference in differences of two sample laws.
* `RepeatedCrossSection.StableComposition`: in each period and each group, the sample law of the
  observed outcome equals the population law (no systematic composition change within groups).
* `RepeatedCrossSection.SamplesPopulation`: the stronger assumption that the whole period-`t`
  sample law of `(G, Yobs t)` is the population law.

## Main results

* `RepeatedCrossSection.rcsDid_eq_did`: under stable composition, the cross-section difference in
  differences equals the panel difference in differences `TwoPeriod.did`.
* `RepeatedCrossSection.att_eq_rcsDid`: hence, under the assumptions of `TwoPeriod.att_eq_did`
  for the latent population, the ATT equals the cross-section difference in differences.
* `RepeatedCrossSection.cex_rcsDid_ne_att`: a four-unit population with a time-invariant
  individual effect, satisfying consistency, no anticipation, parallel trends, and overlap, whose
  period samples reweight the population so that the composition of the treated group changes
  between periods; the cross-section difference in differences is `1` while the ATT and the
  panel difference in differences are `0`.

Source: NICE DSU Technical Support Document 17 (Faria, Hernandez Alava, Manca, Wailoo, 2015),
Section 2.5.1 and the note to Question 23: with repeated cross sections the difference in
differences removes the average individual effect only if there are no systematic changes in
the composition of the groups.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CausalInference

namespace RepeatedCrossSection

open TwoPeriod TwoPeriod.Period

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event `{group = g}` in the sample space `Bool × ℝ` of (group, observed outcome). -/
def groupEvent (g : Bool) : Set (Bool × ℝ) := Prod.fst ⁻¹' {g}

theorem measurableSet_groupEvent (g : Bool) : MeasurableSet (groupEvent g) :=
  measurable_fst (MeasurableSet.singleton g)

/-- The mean observed outcome of group `g` under a sample law `ν` on `Bool × ℝ`. -/
noncomputable def groupMean (ν : Measure (Bool × ℝ)) (g : Bool) : ℝ :=
  ∫ p, p.2 ∂ν[|groupEvent g]

/-- **Cross-section difference in differences.** Given the sample laws `ρ pre` and `ρ post` of
(group, observed outcome) in the two periods, `(E_post[Y | G = 1] - E_pre[Y | G = 1]) -
(E_post[Y | G = 0] - E_pre[Y | G = 0])`. -/
noncomputable def rcsDid (ρ : Period → Measure (Bool × ℝ)) : ℝ :=
  (groupMean (ρ post) true - groupMean (ρ pre) true)
    - (groupMean (ρ post) false - groupMean (ρ pre) false)

/-- The population law of (group, observed outcome) in period `t`. -/
noncomputable def popLaw (μ : Measure Ω) (G : Ω → Bool) (Yobs : Period → Ω → ℝ) (t : Period) :
    Measure (Bool × ℝ) :=
  μ.map fun ω => (G ω, Yobs t ω)

/-- **Stable composition within groups.** In each period `t` and each group `g`, the sample law
of (group, observed outcome) conditioned on the group equals the population law conditioned on
the group: each period's sample of group `g` is representative of group `g` of the population.
Group shares may differ between the samples and the population. -/
def StableComposition (μ : Measure Ω) (G : Ω → Bool) (Yobs : Period → Ω → ℝ)
    (ρ : Period → Measure (Bool × ℝ)) : Prop :=
  ∀ t g, (ρ t)[|groupEvent g] = (popLaw μ G Yobs t)[|groupEvent g]

/-- **Representative samples.** In each period the sample law of (group, observed outcome) is
the population law. -/
def SamplesPopulation (μ : Measure Ω) (G : Ω → Bool) (Yobs : Period → Ω → ℝ)
    (ρ : Period → Measure (Bool × ℝ)) : Prop :=
  ∀ t, ρ t = popLaw μ G Yobs t

theorem stableComposition_of_samplesPopulation {μ : Measure Ω} {G : Ω → Bool}
    {Yobs : Period → Ω → ℝ} {ρ : Period → Measure (Bool × ℝ)}
    (h : SamplesPopulation μ G Yobs ρ) : StableComposition μ G Yobs ρ := fun t _ => by rw [h t]

/-- Conditioning commutes with pushforward: for a measurable map `φ` and a measurable set `s`,
`(μ.map φ)[|s] = (μ[|φ ⁻¹' s]).map φ`. -/
theorem map_cond {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {φ : α → β} (hφ : Measurable φ) {s : Set β} (hs : MeasurableSet s) :
    (μ.map φ)[|s] = (μ[|φ ⁻¹' s]).map φ := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul,
    ← Measure.restrict_map hφ hs, Measure.map_apply hφ hs]
  exact hφ.aemeasurable

/-- The group mean of the population law in period `t` is the conditional mean of the observed
outcome given the group, `E[Yobs t | G = g]`. -/
theorem groupMean_popLaw {μ : Measure Ω} {G : Ω → Bool} {Yobs : Period → Ω → ℝ}
    (hG : Measurable G) (hY : ∀ t, Measurable (Yobs t)) (t : Period) (g : Bool) :
    groupMean (popLaw μ G Yobs t) g = ∫ ω, Yobs t ω ∂μ[|{ω | G ω = g}] := by
  have hφ : Measurable fun ω => (G ω, Yobs t ω) := hG.prodMk (hY t)
  rw [groupMean, popLaw, map_cond hφ (measurableSet_groupEvent g),
    integral_map hφ.aemeasurable measurable_snd.aestronglyMeasurable]
  rfl

/-- **Repeated cross sections recover the panel difference in differences.** If `G` and every
observed outcome are measurable and composition is stable within groups, the cross-section
difference in differences of the sample laws equals the panel difference in differences of the
latent population. This is a change of variables: it needs no positivity or integrability,
because both sides are built from the same conditional measures; `att_eq_rcsDid` adds the
hypotheses under which these are genuine means. -/
theorem rcsDid_eq_did {μ : Measure Ω} {G : Ω → Bool} {Yobs : Period → Ω → ℝ}
    {ρ : Period → Measure (Bool × ℝ)} (hG : Measurable G) (hY : ∀ t, Measurable (Yobs t))
    (hst : StableComposition μ G Yobs ρ) : rcsDid ρ = did μ G Yobs := by
  have h : ∀ t g, groupMean (ρ t) g = ∫ ω, Yobs t ω ∂μ[|{ω | G ω = g}] := fun t g => by
    rw [groupMean, hst t g, ← groupMean, groupMean_popLaw hG hY]
  rw [rcsDid, did, h, h, h, h]
  rfl

/-- **Identification of the ATT from repeated cross sections.** Assume, for the latent panel
population on a probability space, consistency, no anticipation, parallel trends, overlap
`0 < P(G = 1) < 1`, and integrable potential outcomes, as in `TwoPeriod.att_eq_did`; assume
`G` and the observed outcomes are measurable and composition is stable within groups. Then the
ATT equals the cross-section difference in differences of the two sample laws. -/
theorem att_eq_rcsDid {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} {ρ : Period → Measure (Bool × ℝ)}
    (hG : Measurable G) (hYobs : ∀ t, Measurable (Yobs t)) (hcons : Consistency G Y Yobs)
    (hNA : NoAnticipation μ G Y) (hPT : ParallelTrends μ G Y) (hpos : 0 < μ (treated G))
    (hlt : μ (treated G) < 1) (hY : ∀ t d, Integrable (Y t d) μ)
    (hst : StableComposition μ G Yobs ρ) : att μ G Y = rcsDid ρ := by
  rw [rcsDid_eq_did hG hYobs hst]
  exact att_eq_did (hG (MeasurableSet.singleton true)) hcons hNA hPT hpos hlt hY

/-- If a finite measure `ν` gives no mass outside `S`, the event `s` has positive mass, and `f`
equals `k` on `s ∩ S`, then the conditional mean of `f` given `s` is `k`. -/
theorem integral_cond_eq_of_eqOn_support {ν : Measure Ω} [IsFiniteMeasure ν] {s S : Set Ω}
    (hs : MeasurableSet s) (hS : ν Sᶜ = 0) (hνs : ν s ≠ 0) {f : Ω → ℝ} {k : ℝ}
    (h : ∀ ω ∈ s ∩ S, f ω = k) : ∫ ω, f ω ∂ν[|s] = k := by
  have := cond_isProbabilityMeasure (μ := ν) hνs
  have hS' : ∀ᵐ ω ∂ν[|s], ω ∈ S :=
    cond_absolutelyContinuous.ae_le
      ((measure_eq_zero_iff_ae_notMem.mp hS).mono fun _ h => not_not.mp h)
  rw [integral_congr_ae (g := fun _ => k) ?_]
  · simp
  filter_upwards [ae_cond_mem hs, hS'] with ω h1 h2 using h ω ⟨h1, h2⟩

/-! ### A counterexample: composition changes within the treated group -/

section Counterexample

/-- The latent population: units `(g, h)` with group `g` and a time-invariant type `h`, each of
probability `1 / 4`. -/
noncomputable def cexPop : Measure (Bool × Bool) := uniformOn Set.univ

instance : IsProbabilityMeasure cexPop := by
  unfold cexPop
  infer_instance

/-- The group of unit `(g, h)` is `g`. -/
def cexG : Bool × Bool → Bool := Prod.fst

/-- Potential outcomes: a unit of type `h = true` has outcome `1` and a unit of type `h = false`
outcome `0`, in both periods and along both treatment paths (a time-invariant individual effect
and no treatment effect). -/
def cexY (_t : Period) (_d : Bool) (ω : Bool × Bool) : ℝ := if ω.2 then 1 else 0

/-- Observed outcomes, defined by consistency. -/
def cexYobs (t : Period) (ω : Bool × Bool) : ℝ := cexY t (cexG ω) ω

/-- The units sampled in each period. In the pre period the sampled treated unit has type
`false`; in the post period it has type `true`. The sampled comparison unit has type `false` in
both periods. -/
def cexSupport : Period → Set (Bool × Bool)
  | .pre => {(true, false), (false, false)}
  | .post => {(true, true), (false, false)}

/-- The period samples: uniform on the sampled units, a reweighting of the population. -/
noncomputable def cexSample (t : Period) : Measure (Bool × Bool) := uniformOn (cexSupport t)

/-- The sample laws of (group, observed outcome). -/
noncomputable def cexρ (t : Period) : Measure (Bool × ℝ) := popLaw (cexSample t) cexG cexYobs t

theorem cexSupport_finite (t : Period) : (cexSupport t).Finite := by
  cases t <;> simp [cexSupport]

instance (t : Period) : IsProbabilityMeasure (cexSample t) := by
  unfold cexSample
  exact isProbabilityMeasure_uniformOn (cexSupport_finite t) (by cases t <;> simp [cexSupport])

theorem cex_measurable_G : Measurable cexG := measurable_fst

theorem cex_measurable_Yobs (t : Period) : Measurable (cexYobs t) := .of_discrete

theorem cex_consistency : Consistency cexG cexY cexYobs := fun _ _ => rfl

theorem cex_noAnticipation : NoAnticipation cexPop cexG cexY := rfl

theorem cex_parallelTrends : ParallelTrends cexPop cexG cexY := by
  simp [ParallelTrends, cexY]

theorem cex_att : att cexPop cexG cexY = 0 := by
  simp [att, cexY]

/-- Each group has positive mass under each sample. -/
theorem cexSample_group_ne_zero (t : Period) (g : Bool) :
    cexSample t {ω | cexG ω = g} ≠ 0 := by
  rw [cexSample, Ne, uniformOn_eq_zero_iff (cexSupport_finite t)]
  cases t <;> cases g <;>
    simp [cexSupport, cexG, Set.eq_empty_iff_forall_notMem]

/-- Each group has positive mass under each sample law of (group, observed outcome). -/
theorem cexρ_group_ne_zero (t : Period) (g : Bool) : cexρ t (groupEvent g) ≠ 0 := by
  rw [cexρ, popLaw, Measure.map_apply ((cex_measurable_G).prodMk (cex_measurable_Yobs t))
    (measurableSet_groupEvent g)]
  exact cexSample_group_ne_zero t g

theorem cex_groupMean (t : Period) (g : Bool) :
    groupMean (cexρ t) g = if g && t == .post then 1 else 0 := by
  rw [cexρ, groupMean_popLaw cex_measurable_G cex_measurable_Yobs]
  refine integral_cond_eq_of_eqOn_support (S := cexSupport t) .of_discrete ?_
    (cexSample_group_ne_zero t g) ?_
  · rw [cexSample, uniformOn_eq_zero_iff (cexSupport_finite t)]
    simp
  · cases t <;> cases g <;> simp [cexSupport, cexYobs, cexY, cexG]

/-- In the counterexample the cross-section difference in differences is `1`. -/
theorem cex_rcsDid : rcsDid cexρ = 1 := by
  simp [rcsDid, cex_groupMean]

theorem cex_treated : treated cexG = {ω | ω.1 = true} := rfl

theorem cex_treated_pos : 0 < cexPop (treated cexG) := by
  rw [pos_iff_ne_zero, cexPop, Ne, uniformOn_eq_zero_iff Set.finite_univ]
  simp [cex_treated, Set.eq_empty_iff_forall_notMem]

theorem cex_treated_lt_one : cexPop (treated cexG) < 1 := by
  have hT : MeasurableSet (treated cexG) := .of_discrete
  have hC : cexPop (treated cexG)ᶜ ≠ 0 := by
    rw [cexPop, Ne, uniformOn_eq_zero_iff Set.finite_univ]
    simp [cex_treated, Set.eq_empty_iff_forall_notMem]
  rw [prob_compl_eq_one_sub hT, Ne, tsub_eq_zero_iff_le, not_le] at hC
  exact hC

/-- **Counterexample: composition change.** The latent population satisfies consistency, no
anticipation, parallel trends, and overlap, and every potential outcome is integrable; its ATT
and its panel difference in differences are `0`. The period samples are reweightings of the
population in which every group has positive mass, but the treated group is sampled from type
`false` units in the pre period and from type `true` units in the post period. The
cross-section difference in differences is `1`, so it does not recover the ATT, and stable
composition fails. -/
theorem cex_rcsDid_ne_att :
    Consistency cexG cexY cexYobs ∧ NoAnticipation cexPop cexG cexY ∧
      ParallelTrends cexPop cexG cexY ∧ 0 < cexPop (treated cexG) ∧
      cexPop (treated cexG) < 1 ∧ (∀ t g, cexρ t (groupEvent g) ≠ 0) ∧
      att cexPop cexG cexY = 0 ∧ did cexPop cexG cexYobs = 0 ∧ rcsDid cexρ = 1 ∧
      ¬ StableComposition cexPop cexG cexYobs cexρ := by
  have hdid : did cexPop cexG cexYobs = 0 := by
    rw [← cex_att]
    exact (att_eq_did (μ := cexPop) .of_discrete cex_consistency cex_noAnticipation
      cex_parallelTrends cex_treated_pos cex_treated_lt_one
      fun _ _ => Integrable.of_finite).symm
  refine ⟨cex_consistency, cex_noAnticipation, cex_parallelTrends, cex_treated_pos,
    cex_treated_lt_one, cexρ_group_ne_zero, cex_att, hdid, cex_rcsDid, fun hst => ?_⟩
  have := rcsDid_eq_did cex_measurable_G cex_measurable_Yobs hst
  rw [cex_rcsDid, hdid] at this
  norm_num at this

end Counterexample

end RepeatedCrossSection

end CausalInference
