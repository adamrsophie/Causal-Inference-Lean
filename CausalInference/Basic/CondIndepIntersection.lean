/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.CondIndepGraphoid
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The intersection law of conditional independence

For random variables on a probability space (Mathlib's `ProbabilityTheory.CondIndepFun`, which
needs `StandardBorelSpace Ω`), `X ⫫ Y | (Z, W)` and `X ⫫ W | (Z, Y)` imply `X ⫫ (Y, W) | Z`
under a positivity condition. The condition used here is that the law of `(Z, Y, W)` and the
product `P_Z ⊗ P_Y ⊗ P_W` of its marginals are mutually absolutely continuous. A strictly
positive joint density of `(X, Y, Z, W)` with respect to a product of σ-finite measures implies
it. Without a positivity condition the law fails, and a concrete countermodel is given.

## Main definitions

* `uniformBool`: the uniform probability measure on `Bool`.

## Main results

* `exists_eq_comp_fst_of_ae_eq`: under a product law, a function of `(z, w)` that agrees almost
  everywhere with a function of `(z, y)` is almost everywhere a function of `z` alone.
* `condIndepFun_intersection`: the intersection law under mutual absolute continuity.
* `intersection_positivity_of_ac`, `intersection_positivity_of_density`: the positivity
  condition from an equivalent product reference measure, and from a strictly positive density.
* `condIndepFun_intersection_of_density`: the intersection law under a strictly positive joint
  density.
* `not_condIndepFun_intersection`: the countermodel without positivity (`X = Y = W` a fair coin,
  `Z` constant).

## References

* A. P. Dawid, *Conditional independence in statistical theory*, Journal of the Royal Statistical
  Society B 41 (1979).
* J. Pearl, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann (1988).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### The analytic core -/

section Core

variable {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- **A function of `(z, w)` equal to a function of `(z, y)` depends on `z` alone.** Under a
product `P_Z ⊗ (P_Y ⊗ P_W)` of an s-finite measure and two probability measures, if
`a(z, w) = b(z, y)` almost everywhere, then `a(z, w) = c(z)` almost everywhere for the measurable
`c(z) = ∫ a(z, w) dP_W(w)`: by Fubini, for almost every `z` the section `a(z, ·)` is almost
everywhere the constant `b(z, y₀)`. -/
theorem exists_eq_comp_fst_of_ae_eq {PZ : Measure γ} {PY : Measure β} {PW : Measure δ}
    [SFinite PZ] [IsProbabilityMeasure PY] [IsProbabilityMeasure PW] {a : γ × δ → ℝ}
    {b : γ × β → ℝ} (ha : Measurable a)
    (h : ∀ᵐ p ∂PZ.prod (PY.prod PW), a (p.1, p.2.2) = b (p.1, p.2.1)) :
    ∃ c : γ → ℝ, Measurable c ∧ ∀ᵐ p ∂PZ.prod (PY.prod PW), a (p.1, p.2.2) = c p.1 := by
  set c : γ → ℝ := fun z => ∫ w, a (z, w) ∂PW
  have hc : Measurable c := ha.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨c, hc, ?_⟩
  have hz : ∀ᵐ z ∂PZ, ∀ᵐ w ∂PW, a (z, w) = c z := by
    filter_upwards [Measure.ae_ae_of_ae_prod h] with z hzq
    obtain ⟨y₀, hy₀⟩ := (Measure.ae_ae_of_ae_prod hzq).exists
    have hcz : c z = b (z, y₀) := by
      simp only [c]
      rw [integral_congr_ae hy₀]
      simp
    filter_upwards [hy₀] with w hw
    rw [hw, hcz]
  have hS : MeasurableSet {p : γ × β × δ | a (p.1, p.2.2) = c p.1} :=
    measurableSet_eq_fun (ha.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (hc.comp measurable_fst)
  rw [Measure.ae_prod_iff_ae_ae hS]
  filter_upwards [hz] with z hw
  have hS' : MeasurableSet {q : β × δ | a (z, q.2) = c z} :=
    measurableSet_eq_fun (ha.comp (measurable_const.prodMk measurable_snd)) measurable_const
  rw [Measure.ae_prod_iff_ae_ae hS']
  exact Filter.Eventually.of_forall fun _ => hw

end Core

/-! ### The intersection law -/

section Intersection

variable {Ω α β γ δ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → α} {Y : Ω → β} {Z : Ω → γ} {W : Ω → δ}

/-- **The intersection law**, under the positivity condition that the law of `(Z, Y, W)` and the
product `P_Z ⊗ P_Y ⊗ P_W` of its marginals are mutually absolutely continuous:
`X ⫫ Y | (Z, W)` and `X ⫫ W | (Z, Y)` give `X ⫫ (Y, W) | Z`. For a measurable `A`, both
hypotheses identify `E[1_A(X) | Y, Z, W]`, once with a function `a(Z, W)` and once with a
function `b(Z, Y)`; positivity carries `a = b` to the product law, where it forces
`a(Z, W) = c(Z)` (`exists_eq_comp_fst_of_ae_eq`), and the tower property identifies `c(Z)` with
`E[1_A(X) | Z]`. Without positivity the law fails (`not_condIndepFun_intersection`). -/
theorem condIndepFun_intersection [StandardBorelSpace Ω] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (hpos : μ.map (fun ω => (Z ω, Y ω, W ω)) ≪ (μ.map Z).prod ((μ.map Y).prod (μ.map W)))
    (hpos' : (μ.map Z).prod ((μ.map Y).prod (μ.map W)) ≪ μ.map (fun ω => (Z ω, Y ω, W ω)))
    (h₁ : CondIndepFun (MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance)
      (hZ.prodMk hW).comap_le X Y μ)
    (h₂ : CondIndepFun (MeasurableSpace.comap (fun ω => (Z ω, Y ω)) inferInstance)
      (hZ.prodMk hY).comap_le X W μ) :
    CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X
      (fun ω => (Y ω, W ω)) μ := by
  refine condIndepFun_of_forall_condExp_indicator_sup_eq hX (hY.prodMk hW) fun A hA => ?_
  set F : Ω → ℝ := fun ω => A.indicator (1 : α → ℝ) (X ω) with hFdef
  have h1 := condExp_indicator_sup_eq_of_condIndepFun h₁ hX hY hA
  have h2 := condExp_indicator_sup_eq_of_condIndepFun h₂ hX hW hA
  have e1 : MeasurableSpace.comap Y inferInstance ⊔
      MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance =
      MeasurableSpace.comap (fun ω => (Y ω, W ω)) inferInstance ⊔
        MeasurableSpace.comap Z inferInstance := by
    simp only [comap_prodMk_eq_sup]
    ac_rfl
  have e2 : MeasurableSpace.comap W inferInstance ⊔
      MeasurableSpace.comap (fun ω => (Z ω, Y ω)) inferInstance =
      MeasurableSpace.comap (fun ω => (Y ω, W ω)) inferInstance ⊔
        MeasurableSpace.comap Z inferInstance := by
    simp only [comap_prodMk_eq_sup]
    ac_rfl
  rw [e1] at h1
  rw [e2] at h2
  have h𝒢 : MeasurableSpace.comap (fun ω => (Y ω, W ω)) inferInstance ⊔
      MeasurableSpace.comap Z inferInstance ≤ mΩ :=
    sup_le (hY.prodMk hW).comap_le hZ.comap_le
  have hZ𝒢 : MeasurableSpace.comap Z inferInstance ≤
      MeasurableSpace.comap (fun ω => (Y ω, W ω)) inferInstance ⊔
        MeasurableSpace.comap Z inferInstance := le_sup_right
  obtain ⟨a, ha, hae⟩ := Measurable.exists_eq_measurable_comp (stronglyMeasurable_condExp
    (μ := μ) (m := MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance)
    (f := F)).measurable
  obtain ⟨b, hb, hbe⟩ := Measurable.exists_eq_measurable_comp (stronglyMeasurable_condExp
    (μ := μ) (m := MeasurableSpace.comap (fun ω => (Z ω, Y ω)) inferInstance)
    (f := F)).measurable
  rw [hae] at h1
  rw [hbe] at h2
  have hab : ∀ᵐ ω ∂μ, a (Z ω, W ω) = b (Z ω, Y ω) := by
    filter_upwards [h1, h2] with ω ha1 hb2
    exact ha1.symm.trans hb2
  have hZYW : Measurable fun ω => (Z ω, Y ω, W ω) := hZ.prodMk (hY.prodMk hW)
  have hSab : MeasurableSet {p : γ × β × δ | a (p.1, p.2.2) = b (p.1, p.2.1)} :=
    measurableSet_eq_fun (ha.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (hb.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  have hρ : ∀ᵐ p ∂μ.map (fun ω => (Z ω, Y ω, W ω)), a (p.1, p.2.2) = b (p.1, p.2.1) :=
    (ae_map_iff hZYW.aemeasurable hSab).2 hab
  obtain ⟨c, hc, hcπ⟩ := exists_eq_comp_fst_of_ae_eq ha (hpos'.ae_le hρ)
  have hcμ : ∀ᵐ ω ∂μ, a (Z ω, W ω) = c (Z ω) :=
    ae_of_ae_map (p := fun p : γ × β × δ => a (p.1, p.2.2) = c p.1) hZYW.aemeasurable
      (hpos.ae_le hcπ)
  have hφ : μ[F | MeasurableSpace.comap (fun ω => (Y ω, W ω)) inferInstance ⊔
      MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun ω => c (Z ω) := by
    filter_upwards [h1, hcμ] with ω ha1 hc1
    exact ha1.trans hc1
  have hcZ : StronglyMeasurable[MeasurableSpace.comap Z inferInstance] fun ω => c (Z ω) :=
    (hc.comp (comap_measurable Z)).stronglyMeasurable
  have hZc : μ[F | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun ω => c (Z ω) := by
    refine (condExp_condExp_of_le hZ𝒢 h𝒢).symm.trans ((condExp_congr_ae hφ).trans ?_)
    rw [condExp_of_stronglyMeasurable hZ.comap_le hcZ (integrable_condExp.congr hφ)]
  exact hφ.trans hZc.symm

omit mΩ [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  [IsProbabilityMeasure μ] in
/-- Two measures with the same null measurable sets are mutually absolutely continuous. -/
theorem absolutelyContinuous_and_of_null_iff {E : Type*} [MeasurableSpace E] {m₁ m₂ : Measure E}
    (h : ∀ S : Set E, MeasurableSet S → (m₁ S = 0 ↔ m₂ S = 0)) : m₁ ≪ m₂ ∧ m₂ ≪ m₁ :=
  ⟨Measure.AbsolutelyContinuous.mk fun S hS h0 => (h S hS).2 h0,
    Measure.AbsolutelyContinuous.mk fun S hS h0 => (h S hS).1 h0⟩

/-- **The positivity condition from an equivalent product reference.** If the law of
`(X, Z, Y, W)` and a product `ν_X ⊗ ν_Z ⊗ ν_Y ⊗ ν_W` of σ-finite measures are mutually absolutely
continuous, then so are the law of `(Z, Y, W)` and the product of its marginals: both have the
null sets of `ν_Z ⊗ ν_Y ⊗ ν_W`. -/
theorem intersection_positivity_of_ac (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hW : Measurable W) {νX : Measure α} {νZ : Measure γ} {νY : Measure β}
    {νW : Measure δ} [SigmaFinite νX] [SigmaFinite νZ] [SigmaFinite νY] [SigmaFinite νW]
    (h4a : μ.map (fun ω => (X ω, Z ω, Y ω, W ω)) ≪ νX.prod (νZ.prod (νY.prod νW)))
    (h4b : νX.prod (νZ.prod (νY.prod νW)) ≪ μ.map (fun ω => (X ω, Z ω, Y ω, W ω))) :
    μ.map (fun ω => (Z ω, Y ω, W ω)) ≪ (μ.map Z).prod ((μ.map Y).prod (μ.map W)) ∧
      (μ.map Z).prod ((μ.map Y).prod (μ.map W)) ≪ μ.map (fun ω => (Z ω, Y ω, W ω)) := by
  have hZYW : Measurable fun ω => (Z ω, Y ω, W ω) := hZ.prodMk (hY.prodMk hW)
  have hXZYW : Measurable fun ω => (X ω, Z ω, Y ω, W ω) := hX.prodMk hZYW
  set ν3 := νZ.prod (νY.prod νW)
  set L3 := μ.map fun ω => (Z ω, Y ω, W ω)
  have hL3 : ∀ S, MeasurableSet S →
      L3 S = μ.map (fun ω => (X ω, Z ω, Y ω, W ω)) (Set.univ ×ˢ S) := fun S hS => by
    rw [Measure.map_apply hZYW hS, Measure.map_apply hXZYW (MeasurableSet.univ.prod hS),
      Set.mk_preimage_prod, Set.preimage_univ, Set.univ_inter]
  have h1 : (μ.map (fun ω => (X ω, Z ω, Y ω, W ω))) Set.univ ≠ 0 := by
    rw [Measure.map_apply hXZYW MeasurableSet.univ, Set.preimage_univ, measure_univ]
    exact one_ne_zero
  have hνX : νX Set.univ ≠ 0 := by
    intro h0
    refine h1 (h4a ?_)
    rw [← Set.univ_prod_univ, Measure.prod_prod, h0, zero_mul]
  have h3 : ∀ S, MeasurableSet S → (L3 S = 0 ↔ ν3 S = 0) := by
    intro S hS
    rw [hL3 S hS]
    constructor
    · intro h0
      have := h4b h0
      rw [Measure.prod_prod, mul_eq_zero] at this
      exact this.resolve_left hνX
    · intro h0
      exact h4a (by rw [Measure.prod_prod, h0, mul_zero])
  have hL3ν := absolutelyContinuous_and_of_null_iff h3
  have hν3 : ν3 Set.univ ≠ 0 := fun h0 => by
    have := (h3 _ MeasurableSet.univ).2 h0
    rw [Measure.map_apply hZYW MeasurableSet.univ, Set.preimage_univ, measure_univ] at this
    exact one_ne_zero this
  have hu : νZ Set.univ ≠ 0 ∧ νY Set.univ ≠ 0 ∧ νW Set.univ ≠ 0 := by
    simp only [ν3, ← Set.univ_prod_univ, Measure.prod_prod, ne_eq, mul_eq_zero, not_or] at hν3
    exact ⟨hν3.1, hν3.2.1, hν3.2.2⟩
  have hPZ : ∀ A, MeasurableSet A → (μ.map Z A = 0 ↔ νZ A = 0) := by
    intro A hA
    have e : μ.map Z A = L3 (A ×ˢ Set.univ) := by
      rw [Measure.map_apply hZ hA, Measure.map_apply hZYW (hA.prod MeasurableSet.univ),
        Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]
    rw [e, h3 _ (hA.prod MeasurableSet.univ), Measure.prod_prod, ← Set.univ_prod_univ,
      Measure.prod_prod, mul_eq_zero, mul_eq_zero, or_iff_left (not_or.2 ⟨hu.2.1, hu.2.2⟩)]
  have hPY : ∀ B, MeasurableSet B → (μ.map Y B = 0 ↔ νY B = 0) := by
    intro B hB
    have e : μ.map Y B = L3 (Set.univ ×ˢ (B ×ˢ Set.univ)) := by
      rw [Measure.map_apply hY hB,
        Measure.map_apply hZYW (MeasurableSet.univ.prod (hB.prod MeasurableSet.univ)),
        Set.mk_preimage_prod, Set.mk_preimage_prod]
      simp
    rw [e, h3 _ (MeasurableSet.univ.prod (hB.prod MeasurableSet.univ)), Measure.prod_prod,
      Measure.prod_prod]
    simp [hu.1, hu.2.2]
  have hPW : ∀ D, MeasurableSet D → (μ.map W D = 0 ↔ νW D = 0) := by
    intro D hD
    have e : μ.map W D = L3 (Set.univ ×ˢ (Set.univ ×ˢ D)) := by
      rw [Measure.map_apply hW hD,
        Measure.map_apply hZYW (MeasurableSet.univ.prod (MeasurableSet.univ.prod hD)),
        Set.mk_preimage_prod, Set.mk_preimage_prod]
      simp
    rw [e, h3 _ (MeasurableSet.univ.prod (MeasurableSet.univ.prod hD)), Measure.prod_prod,
      Measure.prod_prod]
    simp [hu.1, hu.2.1]
  obtain ⟨hZa, hZb⟩ := absolutelyContinuous_and_of_null_iff hPZ
  obtain ⟨hYa, hYb⟩ := absolutelyContinuous_and_of_null_iff hPY
  obtain ⟨hWa, hWb⟩ := absolutelyContinuous_and_of_null_iff hPW
  have hπa : (μ.map Z).prod ((μ.map Y).prod (μ.map W)) ≪ ν3 := hZa.prod (hYa.prod hWa)
  have hπb : ν3 ≪ (μ.map Z).prod ((μ.map Y).prod (μ.map W)) := hZb.prod (hYb.prod hWb)
  exact ⟨hL3ν.1.trans hπb, hπa.trans hL3ν.2⟩

/-- **The positivity condition from a strictly positive density.** If the law of `(X, Y, Z, W)`
has a density `q` with respect to a product `ν_X ⊗ ν_Y ⊗ ν_Z ⊗ ν_W` of σ-finite measures and
`q > 0` almost everywhere for that product, then the law of `(Z, Y, W)` and the product of its
marginals are mutually absolutely continuous. -/
theorem intersection_positivity_of_density (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hW : Measurable W) {νX : Measure α} {νY : Measure β} {νZ : Measure γ}
    {νW : Measure δ} [SigmaFinite νX] [SigmaFinite νY] [SigmaFinite νZ] [SigmaFinite νW]
    {q : α × β × γ × δ → ℝ≥0∞} (hq : Measurable q)
    (hlaw : μ.map (fun ω => (X ω, Y ω, Z ω, W ω)) =
      (νX.prod (νY.prod (νZ.prod νW))).withDensity q)
    (hqpos : ∀ᵐ p ∂νX.prod (νY.prod (νZ.prod νW)), 0 < q p) :
    μ.map (fun ω => (Z ω, Y ω, W ω)) ≪ (μ.map Z).prod ((μ.map Y).prod (μ.map W)) ∧
      (μ.map Z).prod ((μ.map Y).prod (μ.map W)) ≪ μ.map (fun ω => (Z ω, Y ω, W ω)) := by
  have hXYZW : Measurable fun ω => (X ω, Y ω, Z ω, W ω) :=
    hX.prodMk (hY.prodMk (hZ.prodMk hW))
  have hp : MeasurePreserving
      (fun r : β × γ × δ => (r.2.1, r.1, r.2.2)) (νY.prod (νZ.prod νW))
        (νZ.prod (νY.prod νW)) :=
    (measurePreserving_prodAssoc νZ νY νW).comp ((Measure.measurePreserving_swap.prod
      (MeasurePreserving.id νW)).comp
        (MeasurePreserving.symm _ (measurePreserving_prodAssoc νY νZ νW)))
  have hE := (MeasurePreserving.id νX).prod hp
  have hmap : μ.map (fun ω => (X ω, Z ω, Y ω, W ω)) =
      (μ.map (fun ω => (X ω, Y ω, Z ω, W ω))).map
        (Prod.map id fun r : β × γ × δ => (r.2.1, r.1, r.2.2)) := by
    rw [Measure.map_map hE.measurable hXYZW]
    rfl
  have h4a : μ.map (fun ω => (X ω, Y ω, Z ω, W ω)) ≪ νX.prod (νY.prod (νZ.prod νW)) := by
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have h4b : νX.prod (νY.prod (νZ.prod νW)) ≪ μ.map (fun ω => (X ω, Y ω, Z ω, W ω)) := by
    rw [hlaw]
    exact withDensity_absolutelyContinuous' hq.aemeasurable (hqpos.mono fun p hp => hp.ne')
  refine intersection_positivity_of_ac hX hY hZ hW (νX := νX) (νZ := νZ) (νY := νY) (νW := νW)
    ?_ ?_
  · rw [hmap, ← hE.map_eq]
    exact h4a.map hE.measurable
  · rw [hmap, ← hE.map_eq]
    exact h4b.map hE.measurable

/-- **The intersection law under a strictly positive joint density**: if the law of
`(X, Y, Z, W)` has a density with respect to a product of σ-finite measures that is positive
almost everywhere for that product, then `X ⫫ Y | (Z, W)` and `X ⫫ W | (Z, Y)` give
`X ⫫ (Y, W) | Z`. -/
theorem condIndepFun_intersection_of_density [StandardBorelSpace Ω] (hX : Measurable X)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W) {νX : Measure α}
    {νY : Measure β} {νZ : Measure γ} {νW : Measure δ} [SigmaFinite νX] [SigmaFinite νY]
    [SigmaFinite νZ] [SigmaFinite νW] {q : α × β × γ × δ → ℝ≥0∞} (hq : Measurable q)
    (hlaw : μ.map (fun ω => (X ω, Y ω, Z ω, W ω)) =
      (νX.prod (νY.prod (νZ.prod νW))).withDensity q)
    (hqpos : ∀ᵐ p ∂νX.prod (νY.prod (νZ.prod νW)), 0 < q p)
    (h₁ : CondIndepFun (MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance)
      (hZ.prodMk hW).comap_le X Y μ)
    (h₂ : CondIndepFun (MeasurableSpace.comap (fun ω => (Z ω, Y ω)) inferInstance)
      (hZ.prodMk hY).comap_le X W μ) :
    CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X
      (fun ω => (Y ω, W ω)) μ :=
  have h := intersection_positivity_of_density hX hY hZ hW hq hlaw hqpos
  condIndepFun_intersection hX hY hZ hW h.1 h.2 h₁ h₂

end Intersection

/-! ### Intersection fails without positivity -/

section Countermodel

/-- The uniform probability measure on `Bool`, `P{true} = P{false} = 1/2`. -/
noncomputable def uniformBool : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure uniformBool :=
  ⟨by
    simp only [uniformBool, smul_apply, add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

theorem uniformBool_singleton (b : Bool) : uniformBool {b} = 2⁻¹ := by
  cases b <;> simp [uniformBool]

/-- **Intersection fails without positivity.** On `Ω = Bool` with the uniform law, let
`X = Y = W` be the coin and `Z` constant. Then `X ⫫ Y | (Z, W)` and `X ⫫ W | (Z, Y)` hold,
because `X` is a function of the conditioning variable, but `X ⫫ (Y, W) | Z` fails: given a
constant it is independence of the coin from itself, and
`P(X = 1, Y = 1) = 1/2 ≠ 1/4 = P(X = 1) P(Y = 1)`. The law of `(Z, Y, W)` sits on the diagonal,
which has mass `0` under the product of the marginals. Since `Y = W`, the two hypotheses are
the same statement, stated twice to match `condIndepFun_intersection`. -/
theorem not_condIndepFun_intersection :
    CondIndepFun (MeasurableSpace.comap (fun ω : Bool => ((), ω)) inferInstance)
        ((measurable_const.prodMk measurable_id).comap_le) (id : Bool → Bool) id uniformBool ∧
      CondIndepFun (MeasurableSpace.comap (fun ω : Bool => ((), ω)) inferInstance)
        ((measurable_const.prodMk measurable_id).comap_le) (id : Bool → Bool) id uniformBool ∧
      ¬ CondIndepFun (MeasurableSpace.comap (fun _ : Bool => ()) inferInstance)
        measurable_const.comap_le (id : Bool → Bool) (fun ω => (ω, ω)) uniformBool := by
  have hci : CondIndepFun (MeasurableSpace.comap (fun ω : Bool => ((), ω)) inferInstance)
      ((measurable_const.prodMk measurable_id).comap_le) (id : Bool → Bool) id uniformBool :=
    condIndepFun_of_measurable_left
      (measurable_snd.comp (comap_measurable (fun ω : Bool => ((), ω)))) measurable_id
  refine ⟨hci, hci, fun H => ?_⟩
  have H' := (condIndepFun_comap_const_iff_indepFun (μ := uniformBool) (U := id)
    (V := fun ω : Bool => (ω, ω)) measurable_id (measurable_id.prodMk measurable_id) ()).1 H
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at H'
  have h := H' {true} (Prod.fst ⁻¹' {true}) (measurableSet_singleton true)
    (measurable_fst (measurableSet_singleton true))
  have e1 : (id : Bool → Bool) ⁻¹' {true} ∩ (fun ω => (ω, ω)) ⁻¹' (Prod.fst ⁻¹' {true}) =
      {true} := by
    ext ω
    simp
  have e2 : (fun ω : Bool => (ω, ω)) ⁻¹' (Prod.fst ⁻¹' {true}) = {true} := by
    ext ω
    simp
  rw [e1, e2, Set.preimage_id, uniformBool_singleton] at h
  have h' := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h'
  norm_num at h'

end Countermodel

end CausalInference
