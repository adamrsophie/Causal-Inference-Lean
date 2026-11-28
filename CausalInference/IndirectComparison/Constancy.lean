/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Basic

/-!
# Constancy of relative and absolute effects

**Marginal constancy across studies.** A family of populations `P j` (the populations of the
studies of a network, and a target) has **constant relative effects** on the scale `g` for a set
`S` of ordered pairs of treatments when, for each pair `(a, b) ∈ S`, the marginal effect
`g(E_j[Y(b)]) - g(E_j[Y(a)])` is the same in every population (`ConstantRelativeEffects`). For the
two direct contrasts of an indirect comparison this is all that is needed: the indirect
comparison `d_ac(P_k) - d_bc(P_l)` read from two trials is the contrast `d_ab` of every
population (`marginalEffect_eq_sub_of_constant`). Two constant contrasts of a triangle force the
third (`marginalEffect_eq_of_two`), while the within population consistency equation alone does
not give constancy (`consistency_not_constant_example`).

**Conditional constancy.** Between two populations `P` and `Q`:

* **absolute constancy** of the arm `t` is structural invariance: one function is a version of
  `E[Y(t) | X]` in both (`Transport.StructurallyInvariant`, whose form for populations is
  `Population.isCommonRegression_iff`);
* **relative constancy** on the scale `g` for `(a, b)`: there are versions of the four
  conditional means whose conditional effects equal one function `τ` almost everywhere under each
  covariate law (`RelativeConstancy`).

Absolute constancy of both arms gives relative constancy on every scale
(`relativeConstancy_of_structurallyInvariant`), not conversely
(`relativeConstancy_not_structurallyInvariant`). Under relative constancy and overlap of the
covariate laws, every version of the source conditional effect is one of the target
(`RelativeConstancy.ae_eq`), so the target average conditional effect is the source conditional
effect averaged over the target covariate law, or reweighted by the density ratio in the source
(`linkConditional_eq_of_relativeConstancy`).

## Main definitions

* `ConstantRelativeEffects g P S`, `RelativeConstancy g P Q a b`.

## Main results

* `ConstantRelativeEffects.exists_networkContrast`, `marginalEffect_eq_sub_of_constant`,
  `marginalEffect_eq_of_two`, `consistency_not_constant_example`.
* `relativeConstancy_of_structurallyInvariant`, `relativeConstancy_not_structurallyInvariant`,
  `RelativeConstancy.ae_eq`, `linkConditional_eq_of_relativeConstancy`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure Transport

/-! ### Constancy of marginal relative effects across populations -/

section Marginal

variable {J ι 𝒳 : Type*} {Ω : J → Type*} [∀ j, MeasurableSpace (Ω j)]

/-- The populations `P j` have **constant relative effects** on the scale `g` for the ordered
pairs of treatments in `S`: for `(a, b) ∈ S` the marginal effect of `b` relative to `a` is the
same in every population. -/
def ConstantRelativeEffects (g : ℝ → ℝ) (P : ∀ j, Population (Ω j) 𝒳 ι) (S : Set (ι × ι)) :
    Prop :=
  ∀ p ∈ S, ∀ j j', (P j).marginalEffect g p.1 p.2 = (P j').marginalEffect g p.1 p.2

variable {g : ℝ → ℝ} {P : ∀ j, Population (Ω j) 𝒳 ι}

/-- **The network contrast is well defined under constancy**: if the relative effects are
constant for all pairs, there is one number `d a b` per ordered pair, the effect in every
population. -/
theorem ConstantRelativeEffects.exists_networkContrast [Nonempty J]
    (h : ConstantRelativeEffects g P Set.univ) :
    ∃ d : ι → ι → ℝ, ∀ a b j, (P j).marginalEffect g a b = d a b := by
  obtain ⟨j₀⟩ := ‹Nonempty J›
  exact ⟨fun a b => (P j₀).marginalEffect g a b, fun a b j => h (a, b) trivial j j₀⟩

/-- Contrasts add along paths in one population: `d_ab = d_ac - d_bc`. -/
theorem Population.marginalEffect_eq_sub {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Population Ω' 𝒳 ι) (a b c : ι) :
    Q.marginalEffect g a b = Q.marginalEffect g a c - Q.marginalEffect g b c := by
  simp only [Population.marginalEffect]; ring

/-- **The indirect comparison under constancy of the two direct contrasts.** If the effects of
the common comparator `c` relative to `a` and relative to `b` are constant across the
populations, then the indirect comparison `d_ac(P_k) - d_bc(P_l)`, read from any two
populations, is the effect `d_ab` of `b` relative to `a` in every population `P_j`. -/
theorem marginalEffect_eq_sub_of_constant {a b c : ι}
    (h : ConstantRelativeEffects g P {(a, c), (b, c)}) (j k l : J) :
    (P j).marginalEffect g a b = (P k).marginalEffect g a c - (P l).marginalEffect g b c := by
  rw [(P j).marginalEffect_eq_sub a b c, h (a, c) (by simp) j k, h (b, c) (by simp) j l]

/-- **Two constant contrasts of a triangle force the third.** -/
theorem marginalEffect_eq_of_two {a b c : ι} (j j' : J)
    (hac : (P j).marginalEffect g a c = (P j').marginalEffect g a c)
    (hbc : (P j).marginalEffect g b c = (P j').marginalEffect g b c) :
    (P j).marginalEffect g a b = (P j').marginalEffect g a b := by
  rw [(P j).marginalEffect_eq_sub a b c, (P j').marginalEffect_eq_sub a b c, hac, hbc]

end Marginal

/-- A population on a one point space with constant potential outcomes `v t`. -/
noncomputable def pointPopulation {ι : Type*} (v : ι → ℝ) : Population Unit Unit ι :=
  ⟨Measure.dirac (), id, fun t _ => v t⟩

instance {ι : Type*} (v : ι → ℝ) : IsProbabilityMeasure (pointPopulation v).μ := by
  unfold pointPopulation; infer_instance

theorem pointPopulation_armMean {ι : Type*} (v : ι → ℝ) (t : ι) :
    (pointPopulation v).armMean t = v t := by
  simp [Population.armMean, pointPopulation]

/-- **The consistency equation does not give constancy.** Two populations with arm means
`(0, 1, 2)` and `(0, 2, 4)` for the treatments `0, 1, 2` satisfy `d_01 = d_02 - d_12` on the
identity scale (as every population does), yet the effect `d_01` is `1` in the first and `2` in
the second. -/
theorem consistency_not_constant_example :
    let P : Fin 2 → Population Unit Unit (Fin 3) := fun j =>
      pointPopulation fun t => if j = 0 then (t : ℝ) else 2 * t
    (∀ j, (P j).marginalEffect id 0 1 =
      (P j).marginalEffect id 0 2 - (P j).marginalEffect id 1 2) ∧
    (P 0).marginalEffect id 0 1 = 1 ∧ (P 1).marginalEffect id 0 1 = 2 ∧
    ¬ ConstantRelativeEffects id P {(0, 1)} := by
  intro P
  have e0 : (P 0).marginalEffect id 0 1 = 1 := by
    simp [P, Population.marginalEffect, pointPopulation_armMean]
  have e1 : (P 1).marginalEffect id 0 1 = 2 := by
    simp [P, Population.marginalEffect, pointPopulation_armMean]
  refine ⟨fun j => (P j).marginalEffect_eq_sub 0 1 2, e0, e1, fun h => ?_⟩
  have := h (0, 1) rfl 0 1
  rw [e0, e1] at this
  norm_num at this

/-! ### Conditional constancy between two populations -/

section Conditional

variable {Ω₁ Ω₂ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- **Conditional constancy of the relative effect** of `b` against `a` on the scale `g` from `P`
to `Q`: there are a function `τ` and conditional mean functions of `Y(a)` and `Y(b)` in each
population whose conditional effects on the scale `g` equal `τ` almost everywhere under the
covariate law of that population. -/
def RelativeConstancy (g : ℝ → ℝ) (P : Population Ω₁ 𝒳 ι) (Q : Population Ω₂ 𝒳 ι) (a b : ι) :
    Prop :=
  ∃ τ ma mb ma' mb' : 𝒳 → ℝ, P.IsCondMean a ma ∧ P.IsCondMean b mb ∧ Q.IsCondMean a ma' ∧
    Q.IsCondMean b mb' ∧ (∀ᵐ x ∂P.covLaw, linkContrast g ma mb x = τ x) ∧
    ∀ᵐ x ∂Q.covLaw, linkContrast g ma' mb' x = τ x

variable {g : ℝ → ℝ} {P : Population Ω₁ 𝒳 ι} {Q : Population Ω₂ 𝒳 ι} {a b : ι}

/-- **Absolute constancy implies relative constancy**: if the conditional means of `Y(a)` and of
`Y(b)` are each common to the two populations, the conditional effect is common on every
scale. -/
theorem relativeConstancy_of_structurallyInvariant
    (ha : StructurallyInvariant P.μ P.X (P.Y a) Q.μ Q.X (Q.Y a))
    (hb : StructurallyInvariant P.μ P.X (P.Y b) Q.μ Q.X (Q.Y b)) :
    RelativeConstancy g P Q a b := by
  obtain ⟨ma, hma⟩ := ha
  obtain ⟨mb, hmb⟩ := hb
  rw [Population.isCommonRegression_iff] at hma hmb
  exact ⟨linkContrast g ma mb, ma, mb, ma, mb, hma.1, hmb.1, hma.2, hmb.2,
    Filter.Eventually.of_forall fun _ => rfl, Filter.Eventually.of_forall fun _ => rfl⟩

/-- **Relative constancy from a population to itself**, given conditional mean functions of the
two arms. -/
theorem RelativeConstancy.refl {ma mb : 𝒳 → ℝ} (ha : P.IsCondMean a ma) (hb : P.IsCondMean b mb) :
    RelativeConstancy g P P a b :=
  ⟨linkContrast g ma mb, ma, mb, ma, mb, ha, hb, ha, hb, Filter.Eventually.of_forall fun _ => rfl,
    Filter.Eventually.of_forall fun _ => rfl⟩

/-- A function of the covariates is its own conditional mean function. -/
theorem Population.isCondMean_of_eq_comp {Ω : Type*} [MeasurableSpace Ω]
    {R : Population Ω 𝒳 ι} [IsFiniteMeasure R.μ] {t : ι} {m : 𝒳 → ℝ} (hX : Measurable R.X)
    (hm : Measurable m) (hY : R.Y t = fun ω => m (R.X ω)) (hi : Integrable (R.Y t) R.μ) :
    R.IsCondMean t m := by
  refine ⟨hm, ?_⟩
  rw [hY] at hi ⊢
  exact (condExp_of_stronglyMeasurable hX.comap_le
    (hm.comp (comap_measurable R.X)).stronglyMeasurable hi).symm.eventuallyEq

/-- **Relative constancy does not imply absolute constancy.** Two one point populations with
means `(0, 1)` and `(1, 2)` for the arms `0, 1` have the same conditional effect `1` on the
identity scale, but no common conditional mean of the arm `0`. -/
theorem relativeConstancy_not_structurallyInvariant :
    RelativeConstancy id (pointPopulation fun t : Fin 2 => (t : ℝ))
        (pointPopulation fun t : Fin 2 => (t : ℝ) + 1) 0 1 ∧
      ¬ StructurallyInvariant (pointPopulation fun t : Fin 2 => (t : ℝ)).μ
        (pointPopulation fun t : Fin 2 => (t : ℝ)).X
        ((pointPopulation fun t : Fin 2 => (t : ℝ)).Y 0)
        (pointPopulation fun t : Fin 2 => (t : ℝ) + 1).μ
        (pointPopulation fun t : Fin 2 => (t : ℝ) + 1).X
        ((pointPopulation fun t : Fin 2 => (t : ℝ) + 1).Y 0) := by
  have hc : ∀ (v : Fin 2 → ℝ) (t : Fin 2), (pointPopulation v).IsCondMean t (fun _ => v t) :=
    fun v t => Population.isCondMean_of_eq_comp measurable_id measurable_const rfl
      (integrable_const _)
  refine ⟨⟨fun _ => 1, _, _, _, _, hc _ 0, hc _ 1, hc _ 0, hc _ 1,
    Filter.Eventually.of_forall fun _ => by simp [linkContrast],
    Filter.Eventually.of_forall fun _ => by simp [linkContrast]⟩, ?_⟩
  rintro ⟨m, hm⟩
  rw [Population.isCommonRegression_iff] at hm
  have e₁ := hm.1.ae_eq measurable_id (hc _ 0)
  have e₂ := hm.2.ae_eq measurable_id (hc _ 0)
  simp only [Population.covLaw, pointPopulation, Measure.map_id, ae_dirac_eq,
    Filter.eventually_pure] at e₁ e₂
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero, zero_add] at e₁ e₂
  rw [e₁] at e₂
  norm_num at e₂

/-- **Relative constancy carries the source conditional effect to the target.** Under relative
constancy from `P` to `Q` and overlap `Q_X ≪ P_X`, any conditional mean functions of `P` and of
`Q` have the same conditional effect on the scale `g` for `Q_X`-almost every covariate value. -/
theorem RelativeConstancy.ae_eq (hcc : RelativeConstancy g P Q a b) (hX₁ : Measurable P.X)
    (hX₂ : Measurable Q.X) (hov : Q.covLaw ≪ P.covLaw) {ma mb ma' mb' : 𝒳 → ℝ}
    (ha : P.IsCondMean a ma) (hb : P.IsCondMean b mb) (ha' : Q.IsCondMean a ma')
    (hb' : Q.IsCondMean b mb') :
    ∀ᵐ x ∂Q.covLaw, linkContrast g ma mb x = linkContrast g ma' mb' x := by
  obtain ⟨τ, na, nb, na', nb', hna, hnb, hna', hnb', h₁, h₂⟩ := hcc
  have e₁ : ∀ᵐ x ∂Q.covLaw, linkContrast g ma mb x = τ x := by
    refine hov.ae_le ?_
    filter_upwards [ha.ae_eq hX₁ hna, hb.ae_eq hX₁ hnb, h₁] with x hxa hxb hx
    simp only [linkContrast] at hx ⊢
    rw [hxa, hxb, hx]
  filter_upwards [e₁, ha'.ae_eq hX₂ hna', hb'.ae_eq hX₂ hnb', h₂] with x hx hxa hxb hx'
  simp only [linkContrast] at hx hx' ⊢
  rw [hx, hxa, hxb, hx']

/-- **Conditional transport under relative constancy.** Under relative constancy from the source
`P` to the target `Q`, overlap `Q_X ≪ P_X` and a measurable link, the target average conditional
effect is the source conditional effect averaged over the target covariate law, and the source
mean of the density ratio times the source conditional effect:
`Δ_ab(Q) = ∫ τ_ab dQ_X = E_P[w(X) τ_ab(X)]`. -/
theorem linkConditional_eq_of_relativeConstancy [IsFiniteMeasure P.μ] [IsFiniteMeasure Q.μ]
    (hg : Measurable g) (hcc : RelativeConstancy g P Q a b) (hX₁ : Measurable P.X)
    (hX₂ : Measurable Q.X) (hov : Q.covLaw ≪ P.covLaw) {ma mb ma' mb' : 𝒳 → ℝ}
    (ha : P.IsCondMean a ma) (hb : P.IsCondMean b mb) (ha' : Q.IsCondMean a ma')
    (hb' : Q.IsCondMean b mb') :
    linkConditional g Q.covLaw ma' mb' = ∫ x, linkContrast g ma mb x ∂Q.covLaw ∧
      linkConditional g Q.covLaw ma' mb' =
        ∫ ω, densityRatio P.μ P.X Q.μ Q.X (P.X ω) * linkContrast g ma mb (P.X ω) ∂P.μ := by
  have h1 : linkConditional g Q.covLaw ma' mb' = ∫ x, linkContrast g ma mb x ∂Q.covLaw :=
    integral_congr_ae ((hcc.ae_eq hX₁ hX₂ hov ha hb ha' hb').mono fun _ hx => hx.symm)
  refine ⟨h1, h1.trans ?_⟩
  exact integral_densityRatio_mul hX₁ hov ((hg.comp hb.1).sub (hg.comp ha.1))

end Conditional

end IndirectComparison

end CausalInference
