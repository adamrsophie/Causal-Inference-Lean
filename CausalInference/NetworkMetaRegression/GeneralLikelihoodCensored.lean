/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Count

/-!
# The right censored likelihood as the density of the observed data

**Time scale: continuous.** An event time `T` with density `f` with respect to Lebesgue measure
and a censoring time `C` are observed through the pair `(min T C, 1{T ≤ C})`
(`censoredObservation`): the observed time and the event indicator. Write
`S(t) = P(T > t)` and `G(t) = P(C ≥ t)`.

* **The law of the observed pair under independent censoring** (`map_censoredObservation_prod`):
  if `T` and `C` are independent (`P_{(T, C)} = P_T ⊗ P_C`), with no hypothesis on the law of `C`,
  an observed event at a time in `A` has probability `∫_A f(t) G(t) dt` and a censoring at a time
  in `A` has probability `∫_A S(c) P_C(dc)`. So the censored part is dominated by the censoring law
  itself; administrative censoring at a fixed time (a point mass) is allowed.
* **The density** (`map_censoredObservation_prod_withDensity`): if `C` has a density `g`, the
  observed pair has density `[f(t) G(t)]^δ [S(t) g(t)]^(1 - δ)` with respect to Lebesgue measure
  times the counting measure on `{false, true}`. It factors as the censored likelihood
  contribution `f(t)^δ S(t)^(1 - δ)` (`censoredContribution`) times the censoring factor
  `G(t)^δ g(t)^(1 - δ)` (`censoringContribution`), which does not involve the law of `T`. The
  form `h(t)^δ S(t)` with the hazard `h = f / S` holds where `S(t) ≠ 0`
  (`censoredContribution_eq_hazard`).
* **Random variables** (`map_censoredObservation_of_indepFun`): the same statement for
  independent random variables `T` and `C` on a probability space.
* **Instances**: an exponential event time with rate `λ` under administrative censoring at `τ` is
  censored with probability `e^{-λτ}` (`expMeasure_censored_dirac`); under exponential censoring
  with rate `κ` the observed pair has density `λ e^{-(λ+κ)t}` at events and `κ e^{-(λ+κ)t}` at
  censorings, `t ≥ 0` (`censoredDensity_expMeasure`).

## Main definitions

* `censoredObservation`, `censoredContribution`, `censoringContribution`.

## Main results

* `map_censoredObservation_prod`, `map_censoredObservation_prod_withDensity`,
  `map_censoredObservation_of_indepFun`, `censoredContribution_eq_hazard`,
  `expMeasure_censored_dirac`, `censoredDensity_expMeasure`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The **observed data** of an event time `t` and a censoring time `c`: the observed time
`min t c` and the event indicator `1{t ≤ c}`. -/
noncomputable def censoredObservation (z : ℝ × ℝ) : ℝ × Bool := (min z.1 z.2, decide (z.1 ≤ z.2))

theorem measurable_censoredObservation : Measurable censoredObservation :=
  (measurable_fst.min measurable_snd).prodMk
    (measurable_to_countable' fun b => by
      cases b
      · simpa [Set.preimage, not_le] using measurableSet_lt measurable_snd measurable_fst
      · simpa [Set.preimage] using measurableSet_le measurable_fst measurable_snd)

/-- The **censored likelihood contribution** `f(t)^δ S(t)^(1 - δ)` of an observation `(t, δ)`:
the event density at an event, the survival at a censoring. -/
noncomputable def censoredContribution (f S : ℝ → ℝ) (t : ℝ) (δ : Bool) : ℝ :=
  if δ then f t else S t

/-- The **censoring factor** `G(t)^δ g(t)^(1 - δ)`: the censoring survival `G(t) = P(C ≥ t)` at an
event, the censoring density at a censoring. -/
noncomputable def censoringContribution (G g : ℝ → ℝ) (t : ℝ) (δ : Bool) : ℝ :=
  if δ then G t else g t

/-- The contribution in hazard form: where `S(t) ≠ 0`, `f(t)^δ S(t)^(1 - δ) = h(t)^δ S(t)` with
the hazard `h = f / S`. This holds by algebra. -/
theorem censoredContribution_eq_hazard (f S : ℝ → ℝ) {t : ℝ} (hS : S t ≠ 0) (δ : Bool) :
    censoredContribution f S t δ = (f t / S t) ^ δ.toNat * S t := by
  cases δ <;> simp [censoredContribution, div_mul_cancel₀ _ hS]

/-- Two measures on `ℝ × Bool` that agree on every `A ×ˢ {b}` with `A` measurable are equal. -/
theorem measure_ext_prod_bool {μ ν : Measure (ℝ × Bool)}
    (h : ∀ A : Set ℝ, MeasurableSet A → ∀ b, μ (A ×ˢ {b}) = ν (A ×ˢ {b})) : μ = ν := by
  ext E hE
  have hs : ∀ b, MeasurableSet ((fun t => (t, b)) ⁻¹' E) := fun b =>
    measurable_prodMk_right hE
  have hE' : E = ((fun t => (t, true)) ⁻¹' E) ×ˢ {true} ∪
      ((fun t => (t, false)) ⁻¹' E) ×ˢ {false} := by
    ext ⟨t, b⟩
    cases b <;> simp
  have hd : Disjoint (((fun t => (t, true)) ⁻¹' E) ×ˢ ({true} : Set Bool))
      (((fun t => (t, false)) ⁻¹' E) ×ˢ {false}) := by
    rw [Set.disjoint_prod]; right; simp
  have hm : MeasurableSet (((fun t => (t, false)) ⁻¹' E) ×ˢ ({false} : Set Bool)) :=
    (hs false).prod (measurableSet_singleton _)
  rw [hE', measure_union hd hm, measure_union hd hm, h _ (hs true), h _ (hs false)]

/-- **The law of the observed pair under independent censoring.** Let the event time have the law
`μT` with density `f ≥ 0` (measurable) with respect to Lebesgue measure and let the censoring time
have any σ-finite law `μC`, independent of the event time (the joint law is `μT ⊗ μC`). Then the
observed pair `(min T C, 1{T ≤ C})` has the law of an event at a time with density
`t ↦ f(t) μC([t, ∞))` with respect to Lebesgue measure plus a censoring at a time with density
`c ↦ μT((c, ∞))` with respect to `μC`. -/
theorem map_censoredObservation_prod {f : ℝ → ℝ} (hf : Measurable f) (μC : Measure ℝ)
    [SFinite μC] :
    ((volume.withDensity fun t => ENNReal.ofReal (f t)).prod μC).map censoredObservation =
      (volume.withDensity fun t => ENNReal.ofReal (f t) * μC (Ici t)).map (fun t => (t, true)) +
        (μC.withDensity fun c => (volume.withDensity fun t => ENNReal.ofReal (f t)) (Ioi c)).map
          (fun c => (c, false)) := by
  set μT := volume.withDensity fun t => ENNReal.ofReal (f t) with hμT
  have hGm : Measurable fun t : ℝ => μC (Ici t) :=
    Antitone.measurable fun a b hab => measure_mono (Ici_subset_Ici.mpr hab)
  have hSm : Measurable fun c : ℝ => μT (Ioi c) :=
    Antitone.measurable fun a b hab => measure_mono (Ioi_subset_Ioi hab)
  refine measure_ext_prod_bool fun A hA b => ?_
  have hAb : MeasurableSet (A ×ˢ ({b} : Set Bool)) := hA.prod (measurableSet_singleton b)
  rw [Measure.map_apply measurable_censoredObservation hAb, FunLike.coe_add, Pi.add_apply,
    Measure.map_apply measurable_prodMk_right hAb, Measure.map_apply measurable_prodMk_right hAb]
  have hmin : Measurable fun z : ℝ × ℝ => min z.1 z.2 := measurable_fst.min measurable_snd
  cases b
  · -- a censoring
    have hset : censoredObservation ⁻¹' (A ×ˢ {false}) = {z : ℝ × ℝ | min z.1 z.2 ∈ A ∧ z.2 < z.1}
      := by ext z; simp [censoredObservation, not_le]
    have hE : MeasurableSet {z : ℝ × ℝ | min z.1 z.2 ∈ A ∧ z.2 < z.1} :=
      (hmin hA).inter (measurableSet_lt measurable_snd measurable_fst)
    have h1 : (fun t : ℝ => (t, true)) ⁻¹' (A ×ˢ {false}) = ∅ := by ext; simp
    have h2 : (fun t : ℝ => (t, false)) ⁻¹' (A ×ˢ {false}) = A := by ext; simp
    rw [hset, h1, h2, measure_empty, zero_add, Measure.prod_apply_symm hE,
      withDensity_apply _ hA, ← lintegral_indicator hA]
    refine lintegral_congr fun c => ?_
    by_cases hc : c ∈ A
    · rw [indicator_of_mem hc]
      congr 1
      ext t
      simp only [mem_preimage, mem_ofPred_eq, mem_Ioi]
      exact ⟨fun h => h.2, fun h => ⟨by rwa [min_eq_right h.le], h⟩⟩
    · rw [indicator_of_notMem hc]
      convert measure_empty (μ := μT)
      ext t
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      rw [min_eq_right h2.le] at h1
      exact hc h1
  · -- an event
    have hset : censoredObservation ⁻¹' (A ×ˢ {true}) = {z : ℝ × ℝ | min z.1 z.2 ∈ A ∧ z.1 ≤ z.2}
      := by ext z; simp [censoredObservation]
    have hE : MeasurableSet {z : ℝ × ℝ | min z.1 z.2 ∈ A ∧ z.1 ≤ z.2} :=
      (hmin hA).inter (measurableSet_le measurable_fst measurable_snd)
    have h1 : (fun t : ℝ => (t, true)) ⁻¹' (A ×ˢ {true}) = A := by ext; simp
    have h2 : (fun t : ℝ => (t, false)) ⁻¹' (A ×ˢ {true}) = ∅ := by ext; simp
    rw [hset, h1, h2, measure_empty, add_zero, Measure.prod_apply hE, withDensity_apply _ hA,
      hμT, lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal]
    · rw [← lintegral_indicator hA]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ A
      · rw [indicator_of_mem ht]
        simp only [Pi.mul_apply]
        congr 1
        congr 1
        ext c
        simp only [mem_preimage, mem_ofPred_eq, mem_Ici]
        exact ⟨fun h => h.2, fun h => ⟨by rwa [min_eq_left h], h⟩⟩
      · rw [indicator_of_notMem ht]
        simp only [Pi.mul_apply]
        convert mul_zero (ENNReal.ofReal (f t))
        convert measure_empty (μ := μC)
        ext c
        simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        rw [min_eq_left h2] at h1
        exact ht h1
    · exact measurable_measure_prodMk_left hE

/-- **The censored likelihood is the density of the observed pair.** Let the event time and the
censoring time be independent with finite laws `μT`, `μC` with measurable densities `f`, `g` with
respect to Lebesgue measure, and let `S(t) = μT((t, ∞))` and `G(t) = μC([t, ∞))`. Then the observed
pair `(min T C, 1{T ≤ C})` has density
`(t, δ) ↦ [f(t)^δ S(t)^(1 - δ)] [G(t)^δ g(t)^(1 - δ)]` with respect to Lebesgue measure times the
counting measure: the censored likelihood contribution times a censoring factor that does not
involve the law of the event time. -/
theorem map_censoredObservation_prod_withDensity {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) [hT : IsFiniteMeasure (volume.withDensity fun t => ENNReal.ofReal (f t))]
    [hC : IsFiniteMeasure (volume.withDensity fun t => ENNReal.ofReal (g t))] :
    ((volume.withDensity fun t => ENNReal.ofReal (f t)).prod
        (volume.withDensity fun t => ENNReal.ofReal (g t))).map censoredObservation =
      (volume.prod Measure.count).withDensity fun z => ENNReal.ofReal
        (censoredContribution f (fun t => (volume.withDensity fun t => ENNReal.ofReal (f t)).real
            (Ioi t)) z.1 z.2 *
          censoringContribution (fun t => (volume.withDensity fun t => ENNReal.ofReal (g t)).real
            (Ici t)) g z.1 z.2) := by
  set μT := volume.withDensity fun t => ENNReal.ofReal (f t) with hμT
  set μC := volume.withDensity fun t => ENNReal.ofReal (g t) with hμC
  have hGm : Measurable fun t : ℝ => μC.real (Ici t) :=
    Antitone.measurable fun a b hab => measureReal_mono (Ici_subset_Ici.mpr hab)
  have hSm : Measurable fun c : ℝ => μT.real (Ioi c) :=
    Antitone.measurable fun a b hab => measureReal_mono (Ioi_subset_Ioi hab)
  have hρ : Measurable fun z : ℝ × Bool => ENNReal.ofReal
      (censoredContribution f (fun t => μT.real (Ioi t)) z.1 z.2 *
        censoringContribution (fun t => μC.real (Ici t)) g z.1 z.2) := by
    refine ENNReal.measurable_ofReal.comp (measurable_from_prod_countable_left fun b => ?_)
    cases b
    · exact (hSm.mul hg)
    · exact (hf.mul hGm)
  rw [map_censoredObservation_prod hf μC]
  refine measure_ext_prod_bool fun A hA b => ?_
  have hAb : MeasurableSet (A ×ˢ ({b} : Set Bool)) := hA.prod (measurableSet_singleton b)
  rw [FunLike.coe_add, Pi.add_apply, Measure.map_apply measurable_prodMk_right hAb,
    Measure.map_apply measurable_prodMk_right hAb, withDensity_apply _ hAb,
    setLIntegral_prod _ hρ.aemeasurable]
  have hin : ∀ t, ∫⁻ δ in ({b} : Set Bool), ENNReal.ofReal
      (censoredContribution f (fun t => μT.real (Ioi t)) t δ *
        censoringContribution (fun t => μC.real (Ici t)) g t δ) ∂Measure.count =
      ENNReal.ofReal (censoredContribution f (fun t => μT.real (Ioi t)) t b *
        censoringContribution (fun t => μC.real (Ici t)) g t b) := fun t => by
    rw [Measure.restrict_singleton, Measure.count_singleton, one_smul, lintegral_dirac]
  simp_rw [hin]
  cases b
  · have h1 : (fun t : ℝ => (t, true)) ⁻¹' (A ×ˢ {false}) = ∅ := by ext; simp
    have h2 : (fun t : ℝ => (t, false)) ⁻¹' (A ×ˢ {false}) = A := by ext; simp
    rw [h1, h2, measure_empty, zero_add, withDensity_apply _ hA, hμC,
      setLIntegral_withDensity_eq_setLIntegral_mul _ hg.ennreal_ofReal
        (by simpa [hμT] using (Antitone.measurable fun a b hab =>
          measure_mono (Ioi_subset_Ioi hab) : Measurable fun c : ℝ => μT (Ioi c))) hA]
    refine setLIntegral_congr_fun hA fun t _ => ?_
    simp only [Pi.mul_apply, censoredContribution, censoringContribution, Bool.false_eq_true,
      ↓reduceIte]
    rw [ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal, mul_comm, ← hμT]
  · have h1 : (fun t : ℝ => (t, true)) ⁻¹' (A ×ˢ {true}) = A := by ext; simp
    have h2 : (fun t : ℝ => (t, false)) ⁻¹' (A ×ˢ {true}) = ∅ := by ext; simp
    rw [h1, h2, measure_empty, add_zero, withDensity_apply _ hA]
    refine setLIntegral_congr_fun hA fun t _ => ?_
    simp only [censoredContribution, censoringContribution, ↓reduceIte]
    rw [ENNReal.ofReal_mul' measureReal_nonneg, ofReal_measureReal]

/-- **The observed data of independent random variables.** If the event time `T` and the
censoring time `C` are independent random variables on a probability space, `T` with law
`volume.withDensity f` (`f` measurable) and `C` with any law `μC`, then the observed pair
`(min T C, 1{T ≤ C})` has the law of `map_censoredObservation_prod`. -/
theorem map_censoredObservation_of_indepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T C : Ω → ℝ} (hT : Measurable T) (hC : Measurable C)
    (hind : IndepFun T C P) {f : ℝ → ℝ} (hf : Measurable f)
    (hTlaw : P.map T = volume.withDensity fun t => ENNReal.ofReal (f t)) :
    P.map (fun ω => censoredObservation (T ω, C ω)) =
      (volume.withDensity fun t => ENNReal.ofReal (f t) * (P.map C) (Ici t)).map
          (fun t => (t, true)) +
        ((P.map C).withDensity fun c => (volume.withDensity fun t => ENNReal.ofReal (f t))
          (Ioi c)).map (fun c => (c, false)) := by
  have hjoint : P.map (fun ω => (T ω, C ω)) = (P.map T).prod (P.map C) :=
    (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hC.aemeasurable).1 hind
  have e : (fun ω => censoredObservation (T ω, C ω)) =
      censoredObservation ∘ fun ω => (T ω, C ω) := rfl
  rw [e, ← Measure.map_map measurable_censoredObservation (hT.prodMk hC), hjoint, hTlaw]
  exact map_censoredObservation_prod hf (P.map C)

/-! ### Exponential event times -/

/-- The exponential law with rate `r` is Lebesgue measure with the exponential density. -/
theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity fun t => ENNReal.ofReal (exponentialPDFReal r t) := rfl

/-- The survival of the exponential law with rate `r > 0` is `P(T > t) = e^{-rt}` for `t ≥ 0`. -/
theorem expMeasure_real_Ioi {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    (expMeasure r).real (Ioi t) = Real.exp (-(r * t)) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real,
    cdf_expMeasure_eq hr, ite_eq_left ht]
  ring

/-- The exponential law has no atoms, so `P(T ≥ t) = P(T > t) = e^{-rt}` for `t ≥ 0`. -/
theorem expMeasure_real_Ici {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    (expMeasure r).real (Ici t) = Real.exp (-(r * t)) := by
  have h0 : expMeasure r {t} = 0 := by
    rw [expMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
  rw [measureReal_def, ← measure_congr (Ioi_ae_eq_Ici' h0), ← measureReal_def,
    expMeasure_real_Ioi hr ht]

/-- **Administrative censoring of an exponential event time.** For an exponential event time
with rate `r > 0` and censoring at the fixed time `τ ≥ 0` (a point mass, which has no density), the
observation is censored with probability `e^{-rτ}` and is an observed event with probability
`1 - e^{-rτ}`. -/
theorem expMeasure_censored_dirac {r τ : ℝ} (hr : 0 < r) (hτ : 0 ≤ τ) :
    ((expMeasure r).prod (Measure.dirac τ)).map censoredObservation (univ ×ˢ {false}) =
        ENNReal.ofReal (Real.exp (-(r * τ))) ∧
      ((expMeasure r).prod (Measure.dirac τ)).map censoredObservation (univ ×ˢ {true}) =
        ENNReal.ofReal (1 - Real.exp (-(r * τ))) := by
  have := isProbabilityMeasure_expMeasure hr
  have hc : ((expMeasure r).prod (Measure.dirac τ)).map censoredObservation (univ ×ˢ {false}) =
      ENNReal.ofReal (Real.exp (-(r * τ))) := by
    rw [expMeasure_eq_withDensity, map_censoredObservation_prod
      (measurable_exponentialPDFReal r) (Measure.dirac τ), FunLike.coe_add, Pi.add_apply,
      Measure.map_apply measurable_prodMk_right (MeasurableSet.univ.prod
        (measurableSet_singleton _)),
      Measure.map_apply measurable_prodMk_right (MeasurableSet.univ.prod
        (measurableSet_singleton _))]
    have h1 : (fun t : ℝ => (t, true)) ⁻¹' (univ ×ˢ {false}) = ∅ := by ext; simp
    have h2 : (fun t : ℝ => (t, false)) ⁻¹' (univ ×ˢ {false}) = univ := by ext; simp
    rw [h1, h2, measure_empty, zero_add, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, lintegral_dirac, ← expMeasure_eq_withDensity,
      ← ofReal_measureReal, expMeasure_real_Ioi hr hτ]
  refine ⟨hc, ?_⟩
  have hcompl : ((univ : Set ℝ) ×ˢ ({true} : Set Bool))ᶜ = univ ×ˢ {false} := by
    ext ⟨t, b⟩; cases b <;> simp
  rw [← compl_compl ((univ : Set ℝ) ×ˢ ({true} : Set Bool)), prob_compl_eq_one_sub
    (MeasurableSet.univ.prod (measurableSet_singleton _)).compl, hcompl, hc,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]

/-- **Exponential event and censoring times.** For independent exponential event and censoring
times with rates `r > 0` and `k > 0`, the observed pair has density `r e^{-(r+k)t}` at an event
and `k e^{-(r+k)t}` at a censoring, `t ≥ 0`, and `0` at negative times, with respect to Lebesgue
measure times the counting measure. -/
theorem censoredDensity_expMeasure {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    ((expMeasure r).prod (expMeasure k)).map censoredObservation =
      (volume.prod Measure.count).withDensity fun z => ENNReal.ofReal
        (if 0 ≤ z.1 then (if z.2 then r else k) * Real.exp (-((r + k) * z.1)) else 0) := by
  have := isProbabilityMeasure_expMeasure hr
  have := isProbabilityMeasure_expMeasure hk
  have hT : IsFiniteMeasure (volume.withDensity fun t => ENNReal.ofReal (exponentialPDFReal r t))
    := by rw [← expMeasure_eq_withDensity]; infer_instance
  have hC : IsFiniteMeasure (volume.withDensity fun t => ENNReal.ofReal (exponentialPDFReal k t))
    := by rw [← expMeasure_eq_withDensity]; infer_instance
  rw [expMeasure_eq_withDensity r, expMeasure_eq_withDensity k,
    map_censoredObservation_prod_withDensity (measurable_exponentialPDFReal r)
      (measurable_exponentialPDFReal k)]
  congr 1
  funext z
  congr 1
  rw [← expMeasure_eq_withDensity, ← expMeasure_eq_withDensity]
  simp only [censoredContribution, censoringContribution, exponentialPDFReal, gammaPDFReal]
  by_cases ht : 0 ≤ z.1
  · rw [ite_eq_left ht]
    cases z.2
    · simp only [Bool.false_eq_true, ↓reduceIte, ite_eq_left ht, expMeasure_real_Ioi hr ht]
      rw [Real.rpow_one, Real.Gamma_one, sub_self, Real.rpow_zero]
      rw [show -((r + k) * z.1) = -(r * z.1) + -(k * z.1) by ring, Real.exp_add]
      ring
    · simp only [↓reduceIte, ite_eq_left ht, expMeasure_real_Ici hk ht]
      rw [Real.rpow_one, Real.Gamma_one, sub_self, Real.rpow_zero]
      rw [show -((r + k) * z.1) = -(r * z.1) + -(k * z.1) by ring, Real.exp_add]
      ring
  · rw [ite_eq_right ht]
    cases z.2 <;> simp [ite_eq_right ht]

end NetworkMetaRegression

end CausalInference
