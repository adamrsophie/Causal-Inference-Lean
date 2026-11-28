/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.IdentifiabilityTwoStudy

/-!
# Identifiability in a general network

Studies `j : J` compare the treatments `arms j`, with baseline arm `base j`; every arm `(j, k)`
has a known covariate law `F (j, k)`. The data are the aggregate means of all arms and, for some
arms, the individual level surfaces.

## Main results

* `MultilevelModel.network_identifiable_of_slopes`: once the slope vectors `β₁ + β₂,k` are known,
  equal aggregate means in a connected network give equal study intercepts `μ` and equal
  effects `γ` (strictly increasing inverse link, integrable aggregate integrands). The step from
  cell intercepts to `(μ, γ)` is `NetworkMetaAnalysis.armAdditive_ident`.
* `MultilevelModel.network_slopes_of_class`: under class effect modifiers (the interactions are
  shared within each class of non-reference treatments), individual data on one arm of the
  reference and on one arm of some treatment of each class, of full affine rank, give the
  slopes. Shared effect modifiers are the case of one class
  (`MultilevelModel.network_identifiable_of_shared`).
* `MultilevelModel.network_identifiable_of_class`: the two steps together.
* `MultilevelModel.network_not_identifiable_of_not_reachable`: in a network whose contrast graph
  does not join `s` and `t`, every model has a second model with the same slopes and the same
  aggregate mean on every arm, on every link, but a different effect `γ_t - γ_s`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
* S. Dias, A. J. Sutton, A. E. Ades and N. J. Welton, *Evidence synthesis for decision making 2:
  a generalized linear modeling framework for pairwise and network meta-analysis of randomized
  controlled trials*, Medical Decision Making 33 (2013).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory NetworkMetaAnalysis

namespace MultilevelModel

variable {J K : Type*} {p : ℕ} {arms : J → Finset K} {base : J → K}
  {F : ArmIndex arms → Measure (Fin p → ℝ)} {ginv : ℝ → ℝ} {M M' : MultilevelModel J K p}

/-- **Identifiability of intercepts and effects from aggregate means, given the slopes.** In a
finite network with baseline arms `base j ∈ arms j` whose contrast graph is connected, let `M`
and `M'` be anchored at `r` (`γ_r = 0`) and have the same slope vector `β₁ + β₂,k` for every
`k`; let `g⁻¹` be strictly increasing and every arm law `F x` a probability law under which
`g⁻¹(s + xᵀ(β₁ + β₂,k))` is integrable for every `s` (for `M`). Equal aggregate means on every
arm give `μ = μ'` and `γ = γ'`. -/
theorem network_identifiable_of_slopes [Finite J] [Finite K] (hbase : ∀ j, base j ∈ arms j)
    (r : K) (hcon : (armContrastGraph arms base).Connected) (hmono : StrictMono ginv)
    [∀ x, IsProbabilityMeasure (F x)] (hγ : M.γ r = 0) (hγ' : M'.γ r = 0)
    (hslope : ∀ k, M.β₁ + M.β₂ k = M'.β₁ + M'.β₂ k)
    (hint : ∀ x : ArmIndex arms, ∀ s,
      Integrable (fun y => ginv (s + y ⬝ᵥ (M.β₁ + M.β₂ x.1.2))) (F x))
    (agd : ∀ x : ArmIndex arms,
      M.armMean ginv (M.μ x.1.1) (F x) x.1.2 = M'.armMean ginv (M'.μ x.1.1) (F x) x.1.2) :
    M.μ = M'.μ ∧ M.γ = M'.γ :=
  armAdditive_ident hbase r hcon hγ hγ' fun x =>
    intercept_eq_of_armMean_eq hmono (hslope x.1.2) (hint x) (agd x)

/-- **The slopes from individual data under class effect modifiers.** Let `M`, `M'` be anchored
at `r` and have class effect modifiers for the classes `cls` of the non-reference treatments;
let `g⁻¹` be strictly increasing. Suppose the individual data contain an arm `xr` of `r` and,
for every non-reference treatment `k`, an arm `xc k` of some treatment `k' ≠ r` of the class of
`k` (one arm may serve a whole class), each with an arm law of full affine rank and almost
everywhere equal surfaces. Then `β₁ = β₁'` and `β₂ = β₂'`. -/
theorem network_slopes_of_class {C : Type*} {r : K} {cls : K → C} (hmono : StrictMono ginv)
    (hM : M.IsAnchoredAt r) (hM' : M'.IsAnchoredAt r) (hc : M.ClassEffectModifiers r cls)
    (hc' : M'.ClassEffectModifiers r cls) (xr : ArmIndex arms) (hxr : xr.1.2 = r)
    (hrr : AffineRank (F xr))
    (ipdr : M.surface ginv (M.μ xr.1.1) xr.1.2 =ᵐ[F xr] M'.surface ginv (M'.μ xr.1.1) xr.1.2)
    (xc : ∀ k, k ≠ r → ArmIndex arms) (hxc : ∀ k hk, (xc k hk).1.2 ≠ r ∧
      cls (xc k hk).1.2 = cls k)
    (hrc : ∀ k hk, AffineRank (F (xc k hk)))
    (ipdc : ∀ k hk, M.surface ginv (M.μ (xc k hk).1.1) (xc k hk).1.2 =ᵐ[F (xc k hk)]
      M'.surface ginv (M'.μ (xc k hk).1.1) (xc k hk).1.2) :
    M.β₁ = M'.β₁ ∧ M.β₂ = M'.β₂ := by
  have h1 : M.β₁ = M'.β₁ := by
    have := (cell_eq_of_ae_surface_eq hmono hrr ipdr).2
    rwa [hxr, hM.2, hM'.2, add_zero, add_zero] at this
  refine ⟨h1, funext fun k => ?_⟩
  by_cases hk : k = r
  · rw [hk, hM.2, hM'.2]
  · obtain ⟨hne, hcl⟩ := hxc k hk
    have h2 := (cell_eq_of_ae_surface_eq hmono (hrc k hk) (ipdc k hk)).2
    rw [h1] at h2
    have h3 := add_left_cancel h2
    rw [(classEffectModifiers_iff M r cls).1 hc k _ hk hne hcl.symm,
      (classEffectModifiers_iff M' r cls).1 hc' k _ hk hne hcl.symm]
    exact h3

/-- **Identifiability in a network under class effect modifiers**: the hypotheses of
`network_slopes_of_class` for the individual data and of `network_identifiable_of_slopes` for
the aggregate data give equal `μ`, `β₁`, `γ` and `β₂`. -/
theorem network_identifiable_of_class [Finite J] [Finite K] {C : Type*} {r : K} {cls : K → C}
    (hbase : ∀ j, base j ∈ arms j) (hcon : (armContrastGraph arms base).Connected)
    (hmono : StrictMono ginv) [∀ x, IsProbabilityMeasure (F x)] (hM : M.IsAnchoredAt r)
    (hM' : M'.IsAnchoredAt r) (hc : M.ClassEffectModifiers r cls)
    (hc' : M'.ClassEffectModifiers r cls) (xr : ArmIndex arms) (hxr : xr.1.2 = r)
    (hrr : AffineRank (F xr))
    (ipdr : M.surface ginv (M.μ xr.1.1) xr.1.2 =ᵐ[F xr] M'.surface ginv (M'.μ xr.1.1) xr.1.2)
    (xc : ∀ k, k ≠ r → ArmIndex arms) (hxc : ∀ k hk, (xc k hk).1.2 ≠ r ∧
      cls (xc k hk).1.2 = cls k)
    (hrc : ∀ k hk, AffineRank (F (xc k hk)))
    (ipdc : ∀ k hk, M.surface ginv (M.μ (xc k hk).1.1) (xc k hk).1.2 =ᵐ[F (xc k hk)]
      M'.surface ginv (M'.μ (xc k hk).1.1) (xc k hk).1.2)
    (hint : ∀ x : ArmIndex arms, ∀ s,
      Integrable (fun y => ginv (s + y ⬝ᵥ (M.β₁ + M.β₂ x.1.2))) (F x))
    (agd : ∀ x : ArmIndex arms,
      M.armMean ginv (M.μ x.1.1) (F x) x.1.2 = M'.armMean ginv (M'.μ x.1.1) (F x) x.1.2) :
    M = M' := by
  obtain ⟨h1, h2⟩ :=
    network_slopes_of_class hmono hM hM' hc hc' xr hxr hrr ipdr xc hxc hrc ipdc
  obtain ⟨h3, h4⟩ := network_identifiable_of_slopes hbase r hcon hmono hM.1 hM'.1
    (fun k => by rw [h1, h2]) hint agd
  exact MultilevelModel.ext h3 h1 h4 h2

/-- **Identifiability under shared effect modifiers**: the case of a single class. Individual
data on one arm of the reference and one arm of one non-reference treatment `t` suffice for the
slopes, and the aggregate means of a connected network then give the whole model. -/
theorem network_identifiable_of_shared [Finite J] [Finite K] {r : K}
    (hbase : ∀ j, base j ∈ arms j) (hcon : (armContrastGraph arms base).Connected)
    (hmono : StrictMono ginv) [∀ x, IsProbabilityMeasure (F x)] (hM : M.IsAnchoredAt r)
    (hM' : M'.IsAnchoredAt r) (hS : M.SharedEffectModifiers {k | k ≠ r})
    (hS' : M'.SharedEffectModifiers {k | k ≠ r}) (xr : ArmIndex arms) (hxr : xr.1.2 = r)
    (hrr : AffineRank (F xr))
    (ipdr : M.surface ginv (M.μ xr.1.1) xr.1.2 =ᵐ[F xr] M'.surface ginv (M'.μ xr.1.1) xr.1.2)
    (xt : ArmIndex arms) (hxt : xt.1.2 ≠ r) (hrt : AffineRank (F xt))
    (ipdt : M.surface ginv (M.μ xt.1.1) xt.1.2 =ᵐ[F xt] M'.surface ginv (M'.μ xt.1.1) xt.1.2)
    (hint : ∀ x : ArmIndex arms, ∀ s,
      Integrable (fun y => ginv (s + y ⬝ᵥ (M.β₁ + M.β₂ x.1.2))) (F x))
    (agd : ∀ x : ArmIndex arms,
      M.armMean ginv (M.μ x.1.1) (F x) x.1.2 = M'.armMean ginv (M'.μ x.1.1) (F x) x.1.2) :
    M = M' := by
  have hcls : ∀ N : MultilevelModel J K p, N.SharedEffectModifiers {k | k ≠ r} →
      N.ClassEffectModifiers r (fun _ => ()) := fun N hN c s hs t ht => hN s hs.1 t ht.1
  exact network_identifiable_of_class (cls := fun _ => ()) hbase hcon hmono hM hM'
    (hcls M hS) (hcls M' hS') xr hxr hrr ipdr (fun _ _ => xt) (fun _ _ => ⟨hxt, rfl⟩)
    (fun _ _ => hrt) (fun _ _ => ipdt) hint agd

/-- **A disconnected network does not identify the effects.** If the contrast graph does not
join `s` and `t`, every model `M` with `γ_r = 0` has a second model `M'`, with the same slopes and
`γ'_r = 0`, whose aggregate mean equals that of `M` on every arm under every arm law, for every
inverse link, while `γ'_t - γ'_s ≠ γ_t - γ_s`. -/
theorem network_not_identifiable_of_not_reachable [Finite J] [Finite K] (r : K) {s t : K}
    (hst : ¬(armContrastGraph arms base).Reachable s t) (M : MultilevelModel J K p)
    (hγ : M.γ r = 0) :
    ∃ M' : MultilevelModel J K p, M'.β₁ = M.β₁ ∧ M'.β₂ = M.β₂ ∧ M'.γ r = 0 ∧
      (∀ (ginv : ℝ → ℝ) (G : ArmIndex arms → Measure (Fin p → ℝ)) (x : ArmIndex arms),
        M'.armMean ginv (M'.μ x.1.1) (G x) x.1.2 = M.armMean ginv (M.μ x.1.1) (G x) x.1.2) ∧
      M'.γ t - M'.γ s ≠ M.γ t - M.γ s := by
  obtain ⟨a', f', hf', hcell, hne⟩ := armAdditive_not_ident_of_not_reachable r hst M.μ hγ
  refine ⟨⟨a', M.β₁, f', M.β₂⟩, rfl, rfl, hf', fun ginv G x => ?_, hne⟩
  simp only [armMean, surface, eta_eq_affine]
  rw [hcell x]

end MultilevelModel

end NetworkMetaRegression

end CausalInference
