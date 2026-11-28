/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredLocalIdentification
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Level sets of maps of locally constant rank

Let `f : E → V` be a map between finite dimensional real normed spaces with a continuous
derivative `D x` near `x₀`, and suppose that near `x₀` the rank of `D x` does not exceed the rank
`r` of `D x₀` (the rank is lower semicontinuous, so this is the condition that the rank is
locally constant). Then the level set `f⁻¹(f x₀)` contains, near `x₀`, the image of a
neighborhood of `0` in `ker (D x₀)` under an injective map `φ` that is `C¹` at `0` with
injective derivative there and `φ 0 = x₀`. In particular, when `r < dim E`, every neighborhood of
`x₀` contains a point `x ≠ x₀` with `f x = f x₀`.

The proof projects `f` onto `W = range (D x₀)` along a complement. The projected map `g` has
surjective derivative at `x₀`, hence near `x₀` (`eventually_surjective_of_continuousAt_clm`), and
the implicit function theorem for `g` in a splitting `E = ker (D x₀) ⊕ C` gives `φ` with
`g ∘ φ` constant. Near `x₀` the kernel of `Dg x` has dimension `dim E - r ≤ dim ker (D x)`, and
`ker (D x) ⊆ ker (Dg x)`, so the two kernels agree; the derivative of `g ∘ φ = const` then lies
in `ker (D (φ k))`, so `f ∘ φ` has zero derivative on a ball and is constant there.

For the unanchored network this applies to the subgroup means of the comparator arm: if their
derivative has locally constant rank below `p + 1`, the parameters `(β₂,b, γ_b)` are not point
identified on any neighborhood. This covers cases where the derivative is not onto, for example
two subgroups with the same covariate law (`not_pointIdentified_withArm_constRank_instance`),
where `not_pointIdentified_withArm_subgroupMeans` does not apply.

## Main definitions

None: the file proves facts about level sets and the subgroup means.

## Main results

* `eventually_surjective_of_continuousAt_clm`.
* `exists_levelSet_chart_of_finrank_range_le`, `exists_ne_eq_of_finrank_range_le`.
* `subgroupMeans_not_locally_identified_of_finrank_range_le`,
  `not_pointIdentified_withArm_subgroupMeans_of_finrank_range_eq`.
* `not_pointIdentified_withArm_constRank_instance`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology Set

section ConstantRank

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Surjectivity is an open condition** for a family of continuous linear maps into a finite
dimensional space that is continuous at `x₀`: with a right inverse `S` of `T x₀`, the maps
`T x ∘ S` are units for `x` near `x₀`. -/
theorem eventually_surjective_of_continuousAt_clm {X W : Type*} [TopologicalSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {T : X → E →L[ℝ] W}
    {x₀ : X} (hT : ContinuousAt T x₀) (h0 : Function.Surjective (T x₀)) :
    ∀ᶠ x in 𝓝 x₀, Function.Surjective (T x) := by
  obtain ⟨S, hS⟩ := (T x₀).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 h0)
  have hc : ContinuousAt (fun x => (T x).comp S) x₀ := hT.clm_comp continuousAt_const
  have hopen : {u : W →L[ℝ] W | IsUnit u} ∈ 𝓝 ((T x₀).comp S) := by
    rw [hS]
    exact Units.isOpen.mem_nhds isUnit_one
  filter_upwards [hc.preimage_mem_nhds hopen] with x hx
  obtain ⟨b, hb⟩ := (show IsUnit ((T x).comp S) from hx).exists_right_inv
  intro w
  refine ⟨S (b w), ?_⟩
  have := congrArg (fun u : W →L[ℝ] W => u w) hb
  simpa using this

variable [FiniteDimensional ℝ E]

/-- **The level set of a map of locally constant rank contains a `C¹` chart of the kernel.** Let
`f : E → V` have the derivative `D x` at every `x` of a neighborhood `U` of `x₀`, with `D`
continuous on `U`, and let the rank of `D x` not exceed the rank of `D x₀` on `U`. Then there is
an injective map `φ : ker (D x₀) → E`, `C¹` at `0` with injective derivative there, with
`φ 0 = x₀` and `f (φ k) = f x₀` for all `k` near `0`. -/
theorem exists_levelSet_chart_of_finrank_range_le {f : E → V} {D : E → E →L[ℝ] V} {U : Set E}
    {x₀ : E} (hU : U ∈ 𝓝 x₀) (hf : ∀ x ∈ U, HasFDerivAt f (D x) x) (hDc : ContinuousOn D U)
    (hrk : ∀ x ∈ U, Module.finrank ℝ (LinearMap.range (D x : E →ₗ[ℝ] V)) ≤
      Module.finrank ℝ (LinearMap.range (D x₀ : E →ₗ[ℝ] V))) :
    ∃ φ : LinearMap.ker (D x₀ : E →ₗ[ℝ] V) → E, φ 0 = x₀ ∧ Function.Injective φ ∧
      ContDiffAt ℝ 1 φ 0 ∧ Function.Injective (fderiv ℝ φ 0) ∧
      ∀ᶠ k in 𝓝 0, f (φ k) = f x₀ := by
  classical
  set W := LinearMap.range (D x₀ : E →ₗ[ℝ] V) with hWdef
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl W
  set π : V →L[ℝ] W := LinearMap.toContinuousLinearMap (Submodule.projectionOnto W W' hW)
  have hπ : ∀ w : W, π w = w := fun w => Submodule.projectionOnto_apply_left hW w
  set Dg : E → E →L[ℝ] W := fun x => π.comp (D x) with hDg
  have hπD : ∀ v, π (D x₀ v) = ⟨D x₀ v, v, rfl⟩ := fun v => hπ ⟨D x₀ v, v, rfl⟩
  have hsurj0 : Function.Surjective (Dg x₀) := by
    rintro ⟨w, v, hv⟩
    refine ⟨v, ?_⟩
    change π (D x₀ v) = ⟨w, v, hv⟩
    rw [hπD]
    exact Subtype.ext hv
  have hDg0 : ∀ v, Dg x₀ v = 0 ↔ D x₀ v = 0 := fun v => by
    change π (D x₀ v) = 0 ↔ _
    rw [hπD]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsurj : ∀ᶠ x in 𝓝 x₀, Function.Surjective (Dg x) :=
    eventually_surjective_of_continuousAt_clm
      (continuousAt_const.clm_comp (hDc.continuousAt hU)) hsurj0
  have hker : ∀ᶠ x in 𝓝 x₀, ∀ v, Dg x v = 0 → D x v = 0 := by
    filter_upwards [hsurj, hU] with x hx hxU
    have hle : LinearMap.ker (D x : E →ₗ[ℝ] V) ≤ LinearMap.ker (Dg x : E →ₗ[ℝ] W) :=
      fun v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        change π (D x v) = 0
        rw [show D x v = 0 from hv, map_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker (D x : E →ₗ[ℝ] V)
    have h2 := LinearMap.finrank_range_add_finrank_ker (Dg x : E →ₗ[ℝ] W)
    rw [LinearMap.range_eq_top.2 hx, finrank_top] at h2
    have h4 := hrk x hxU
    have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro v hv
    have : v ∈ LinearMap.ker (Dg x : E →ₗ[ℝ] W) := hv
    rw [← heq] at this
    exact this
  -- the splitting `E = K ⊕ C` with `K = ker (D x₀)`
  set K := LinearMap.ker (D x₀ : E →ₗ[ℝ] V) with hKdef
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl K
  set e : (K × C) ≃L[ℝ] E := (Submodule.prodEquivOfIsCompl K C hKC).toContinuousLinearEquiv
  have he : ∀ q : K × C, e q = (q.1 : E) + q.2 := fun q => rfl
  set ft : K × C → W := fun q => π (f (x₀ + e q)) with hft
  set u : Set (K × C) := (fun q => x₀ + e q) ⁻¹' U
  have hcp : Continuous fun q : K × C => x₀ + e q := continuous_const.add e.continuous
  have hu : u ∈ 𝓝 (0 : K × C) := hcp.continuousAt.preimage_mem_nhds (by simpa using hU)
  have hftd : ∀ q ∈ u, HasFDerivAt ft ((Dg (x₀ + e q)).comp (e : K × C →L[ℝ] E)) q := by
    intro q hq
    have h1 : HasFDerivAt (fun q : K × C => x₀ + e q) (e : K × C →L[ℝ] E) q :=
      e.hasFDerivAt.const_add x₀
    exact π.hasFDerivAt.comp q ((hf _ hq).comp q h1)
  have hftc : ContDiffAt ℝ 1 ft 0 := by
    refine contDiffAt_one_iff.2 ⟨fun q => (Dg (x₀ + e q)).comp (e : K × C →L[ℝ] E), u, hu, ?_,
      hftd⟩
    exact (continuousOn_const.clm_comp (hDc.comp hcp.continuousOn fun q hq => hq)).clm_comp
      continuousOn_const
  have hfd0 : fderiv ℝ ft 0 = (Dg x₀).comp (e : K × C →L[ℝ] E) := by
    simpa using (hftd 0 (mem_of_mem_nhds hu)).fderiv
  -- the partial derivative along `C` is invertible
  set L : C →L[ℝ] W := (Dg x₀).comp C.subtypeL
  have hLinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun c hc => ?_
    have hcK : (c : E) ∈ K := (hDg0 c).1 hc
    exact Subtype.ext (Submodule.disjoint_def.1 hKC.disjoint (c : E) hcK c.2)
  have hLsurj : Function.Surjective L := by
    intro w
    obtain ⟨v, hv⟩ := hsurj0 w
    obtain ⟨⟨k, c⟩, hkc⟩ := e.surjective v
    refine ⟨c, ?_⟩
    have hk : Dg x₀ k = 0 := (hDg0 k).2 k.2
    change Dg x₀ c = w
    rw [← hv, ← hkc, he, map_add, hk, zero_add]
  have hinv : (fderiv ℝ ft 0 ∘L ContinuousLinearMap.inr ℝ K C).IsInvertible := by
    refine ⟨(LinearEquiv.ofBijective (L : C →ₗ[ℝ] W) ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv,
      ?_⟩
    ext c
    rw [hfd0]
    simp [L, he]
  set ψ := ContDiffAt.implicitFunction hftc one_ne_zero hinv
  have hψ0 : ψ 0 = 0 := ContDiffAt.implicitFunction_apply_self hftc one_ne_zero hinv
  have hψc : ContDiffAt ℝ 1 ψ 0 := ContDiffAt.contDiffAt_implicitFunction hftc one_ne_zero hinv
  have hψeq : ∀ᶠ k in 𝓝 (0 : K), ft (k, ψ k) = ft 0 :=
    ContDiffAt.eventually_apply_implicitFunction hftc one_ne_zero hinv
  set φ : K → E := fun k => x₀ + e (k, ψ k) with hφdef
  have hφ0 : φ 0 = x₀ := by simp [hφdef, hψ0]
  have hφinj : Function.Injective φ := fun k k' h =>
    congrArg Prod.fst (e.injective (add_left_cancel h))
  have hφc : ContDiffAt ℝ 1 φ 0 :=
    contDiffAt_const.add (e.contDiff.contDiffAt.comp 0 (contDiffAt_id.prodMk hψc))
  have hφd : ∀ k, DifferentiableAt ℝ ψ k → HasFDerivAt φ
      ((e : K × C →L[ℝ] E).comp ((ContinuousLinearMap.id ℝ K).prod (fderiv ℝ ψ k))) k :=
    fun k hk => ((e : K × C →L[ℝ] E).hasFDerivAt.comp k
      ((hasFDerivAt_id k).prodMk hk.hasFDerivAt)).const_add x₀
  have hφd0 := hφd 0 (hψc.differentiableAt one_ne_zero)
  refine ⟨φ, hφ0, hφinj, hφc, ?_, ?_⟩
  · rw [hφd0.fderiv]
    intro v w h
    exact congrArg Prod.fst (e.injective h)
  -- `f ∘ φ` is locally constant
  have hgood : ∀ᶠ k in 𝓝 (0 : K), DifferentiableAt ℝ ψ k ∧ φ k ∈ U ∧
      (∀ v, Dg (φ k) v = 0 → D (φ k) v = 0) ∧ π (f (φ k)) = π (f x₀) := by
    have hU' : U ∈ 𝓝 (φ 0) := hφ0 ▸ hU
    have hker' : {x | ∀ v, Dg x v = 0 → D x v = 0} ∈ 𝓝 (φ 0) := hφ0 ▸ hker
    filter_upwards [(hψc.eventually (by simp)).mono fun k hk => hk.differentiableAt one_ne_zero,
      hφc.continuousAt.preimage_mem_nhds hU', hφc.continuousAt.preimage_mem_nhds hker', hψeq]
      with k h1 h2 h3 h4
    refine ⟨h1, h2, h3, ?_⟩
    have h5 : ft 0 = π (f x₀) := by simp [hft]
    rw [← h5, ← h4]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hgood
  filter_upwards [Metric.ball_mem_nhds (0 : K) hε] with k hk
  have hderiv : ∀ k' ∈ Metric.ball (0 : K) ε,
      HasFDerivAt (fun k => f (φ k)) (0 : K →L[ℝ] V) k' := by
    intro k' hk'
    obtain ⟨h1, h2, h3, -⟩ := hball hk'
    have hcomp := (hf _ h2).comp k' (hφd k' h1)
    have hconst : HasFDerivAt (fun k => π (f (φ k))) (0 : K →L[ℝ] W) k' := by
      refine (hasFDerivAt_const (π (f x₀)) k').congr_of_eventuallyEq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hk'] with k'' hk''
      exact (hball hk'').2.2.2
    have huniq := (π.hasFDerivAt.comp k' hcomp).unique hconst
    refine hcomp.congr_fderiv ?_
    ext v
    have := congrArg (fun T : K →L[ℝ] W => T v) huniq
    simpa using h3 _ (by simpa [hDg] using this)
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun k => f (φ k)) (fun k' hk' => (hderiv k' hk').hasFDerivWithinAt)
    (fun _ _ => (norm_zero).le) (convex_ball (0 : K) ε) (Metric.mem_ball_self hε) hk
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, hφ0] at hmv
  exact hmv

/-- **A level set of a map of locally constant rank below the dimension is not a point near
`x₀`.** Under the hypotheses of `exists_levelSet_chart_of_finrank_range_le`, if the rank of
`D x₀` is less than `dim E`, every neighborhood of `x₀` contains a point `x ≠ x₀` with
`f x = f x₀`. -/
theorem exists_ne_eq_of_finrank_range_le {f : E → V} {D : E → E →L[ℝ] V} {U : Set E}
    {x₀ : E} (hU : U ∈ 𝓝 x₀) (hf : ∀ x ∈ U, HasFDerivAt f (D x) x) (hDc : ContinuousOn D U)
    (hrk : ∀ x ∈ U, Module.finrank ℝ (LinearMap.range (D x : E →ₗ[ℝ] V)) ≤
      Module.finrank ℝ (LinearMap.range (D x₀ : E →ₗ[ℝ] V)))
    (hlt : Module.finrank ℝ (LinearMap.range (D x₀ : E →ₗ[ℝ] V)) < Module.finrank ℝ E) :
    ∀ U' ∈ 𝓝 x₀, ∃ x ∈ U', x ≠ x₀ ∧ f x = f x₀ := by
  intro U' hU'
  obtain ⟨φ, hφ0, hinj, hφc, -, hev⟩ := exists_levelSet_chart_of_finrank_range_le hU hf hDc hrk
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (D x₀ : E →ₗ[ℝ] V)) := by
    have := LinearMap.finrank_range_add_finrank_ker (D x₀ : E →ₗ[ℝ] V)
    omega
  obtain ⟨k, hk⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have h1 : ∀ᶠ k' in 𝓝 0, φ k' ∈ U' :=
    hφc.continuousAt.preimage_mem_nhds (by rwa [hφ0])
  have hW : ∀ᶠ k' in 𝓝 0, φ k' ∈ U' ∧ f (φ k') = f x₀ := h1.and hev
  have ht : Tendsto (fun t : ℝ => t • k) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t • k) (𝓝 0) (𝓝 ((0 : ℝ) • k)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ⟨hW1, hW2⟩, ht0⟩ := ((ht.eventually hW).and self_mem_nhdsWithin).exists
  refine ⟨φ (t • k), hW1, fun h => ?_, hW2⟩
  have := hinj (h.trans hφ0.symm)
  exact hk ((smul_eq_zero.mp this).resolve_left ht0)

end ConstantRank

/-! ### The subgroup means of the comparator arm -/

section Subgroup

variable {p Z : ℕ} {F : Fin Z → Measure (Fin p → ℝ)} [∀ z, IsFiniteMeasure (F z)]
  {ginv ginv' : ℝ → ℝ} {C : ℝ} (hd : ∀ t, HasDerivAt ginv (ginv' t) t) (hd' : Continuous ginv')
  (hbd : ∀ t, |ginv' t| ≤ C) (hF : ∀ z i, Integrable (fun x : Fin p → ℝ => x i) (F z))
include hd hd' hbd hF

/-- **Subgroup means of locally constant rank below `p + 1`: no local identification.** For an
inverse link with continuous derivative bounded by `C` and subgroup laws with integrable
coordinates, if near `w₀` the rank of the derivative of the subgroup means does not exceed its
rank at `w₀`, and that rank is less than `p + 1`, then every neighborhood of `w₀` contains a
`w ≠ w₀` with the same subgroup means. The derivative need not be onto. -/
theorem subgroupMeans_not_locally_identified_of_finrank_range_le {α : ℝ} {β₁ : Fin p → ℝ}
    {w₀ : (Fin p → ℝ) × ℝ}
    (hrk : ∀ᶠ w in 𝓝 w₀, Module.finrank ℝ (LinearMap.range
        (subgroupMeansDeriv F ginv' α β₁ w : (Fin p → ℝ) × ℝ →ₗ[ℝ] (Fin Z → ℝ))) ≤
      Module.finrank ℝ (LinearMap.range
        (subgroupMeansDeriv F ginv' α β₁ w₀ : (Fin p → ℝ) × ℝ →ₗ[ℝ] (Fin Z → ℝ))))
    (hlt : Module.finrank ℝ (LinearMap.range
        (subgroupMeansDeriv F ginv' α β₁ w₀ : (Fin p → ℝ) × ℝ →ₗ[ℝ] (Fin Z → ℝ))) < p + 1) :
    ∀ U ∈ 𝓝 w₀, ∃ w ∈ U, w ≠ w₀ ∧
      subgroupMeans F ginv α β₁ w = subgroupMeans F ginv α β₁ w₀ :=
  exists_ne_eq_of_finrank_range_le hrk
    (fun w _ => (hasStrictFDerivAt_subgroupMeans hd hd' hbd hF w).hasFDerivAt)
    (continuous_subgroupMeansDeriv hd' hbd hF).continuousOn (fun _ hw => hw)
    (by simpa using hlt)

/-- **The comparator arm is not identified when the subgroup means have locally constant rank
below `p + 1`.** Under the hypotheses on `g⁻¹` and the subgroup laws of
`subgroupMeans_not_locally_identified_of_finrank_range_le`, if the derivative of the subgroup
means of `b` (baseline `μ_{j_B}`) has rank `r` at every `w` near `w₀ = (β₂,b, γ_b)` of `M`, and
`r < p + 1`, then `(β₂,b, γ_b)` is not point identified from the subgroup means of `b` in study
`j_B` among the models `M.withArm b w` with `w` in any neighborhood of `w₀`. -/
theorem not_pointIdentified_withArm_subgroupMeans_of_finrank_range_eq {J K : Type*}
    [DecidableEq K] (M : MultilevelModel J K p) (b : K) (jB : J) {r : ℕ}
    (hrk : ∀ᶠ w in 𝓝 (M.β₂ b, M.γ b), Module.finrank ℝ (LinearMap.range
        (subgroupMeansDeriv F ginv' (M.μ jB) M.β₁ w : (Fin p → ℝ) × ℝ →ₗ[ℝ] (Fin Z → ℝ))) = r)
    (hr : r < p + 1) {U : Set ((Fin p → ℝ) × ℝ)} (hU : U ∈ 𝓝 (M.β₂ b, M.γ b)) :
    ¬PointIdentified (M.withArm b '' U)
      (fun N => fun z => N.armMean ginv (N.μ jB) (F z) b) (fun N => (N.β₂ b, N.γ b)) := by
  intro h
  have hr0 := mem_of_mem_nhds hrk
  simp only [Set.mem_ofPred_eq] at hr0
  obtain ⟨w, hw, hne, heq⟩ := subgroupMeans_not_locally_identified_of_finrank_range_le hd hd'
    hbd hF (hrk.mono fun w hw => by rw [hw, hr0]) (by rw [hr0]; exact hr) U hU
  have hw₀ : M.withArm b (M.β₂ b, M.γ b) = M := MultilevelModel.withArm_self M b
  have := h _ ⟨w, hw, rfl⟩ _ ⟨_, mem_of_mem_nhds hU, rfl⟩ (by
    simp only [MultilevelModel.subgroupMeans_withArm]
    rw [hw₀] at *
    simpa [← MultilevelModel.subgroupMeans_withArm, hw₀] using heq)
  apply hne
  simpa [MultilevelModel.withArm] using this

end Subgroup

/-! ### Two subgroups with the same covariate law -/

/-- The derivative of the subgroup means for the identity link and two subgroups with the law
`δ_0` is `v ↦ (v₂, v₂)` at every point. -/
theorem subgroupMeansDeriv_twoDirac_apply (α : ℝ) (β₁ : Fin 1 → ℝ) (w v : (Fin 1 → ℝ) × ℝ)
    (z : Fin 2) :
    subgroupMeansDeriv (fun _ : Fin 2 => Measure.dirac (fun _ => (0 : ℝ))) (fun _ => 1) α β₁ w v
      z = v.2 := by
  rw [subgroupMeansDeriv_apply (C := 1) continuous_const (fun _ => by simp)
    (fun _ _ => integrable_dirac (by simp))]
  simp [dotProduct]

/-- **Instance of non-identification under constant rank, where the derivative is not onto.**
The model `⟨0, 0, 0, 0⟩` with two studies and two treatments indexed by `Bool`, one covariate,
the identity link, comparator `b = false` in study `true`, two subgroups with the same law `δ_0`
and the neighborhood `Set.univ`. The derivative `v ↦ (v₂, v₂)` of the subgroup means is the same
at every point, its rank is less than `2 = p + 1` (the direction `(1, 0)` is in its kernel), and
it is not onto `ℝ²`, so `not_pointIdentified_withArm_subgroupMeans` does not apply; the
parameters `(β₂,b, γ_b)` are not point identified. -/
theorem not_pointIdentified_withArm_constRank_instance :
    (∀ w₀ : (Fin 1 → ℝ) × ℝ, LinearMap.range
        (subgroupMeansDeriv (fun _ : Fin 2 => Measure.dirac (fun _ => (0 : ℝ))) (fun _ => 1) 0 0
          w₀ : (Fin 1 → ℝ) × ℝ →ₗ[ℝ] (Fin 2 → ℝ)) ≠ ⊤) ∧
      ¬PointIdentified (((⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).withArm false) '' Set.univ)
        (fun N => fun _ : Fin 2 => N.armMean id (N.μ true) (Measure.dirac fun _ => 0) false)
        (fun N => (N.β₂ false, N.γ false)) := by
  set D := subgroupMeansDeriv (fun _ : Fin 2 => Measure.dirac (fun _ => (0 : ℝ)))
    (fun _ => (1 : ℝ)) 0 (0 : Fin 1 → ℝ)
  have hF : ∀ (z : Fin 2) (i : Fin 1), Integrable (fun x : Fin 1 → ℝ => x i)
      (Measure.dirac (fun _ => (0 : ℝ))) := fun _ _ => integrable_dirac (by simp)
  refine ⟨fun w₀ htop => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop (fun z => if z = 0 then 1 else 0)
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp only [ContinuousLinearMap.coe_coe, D, subgroupMeansDeriv_twoDirac_apply] at h0 h1
    norm_num at h0 h1
    linarith
  · have hconst : ∀ w w₀ : (Fin 1 → ℝ) × ℝ, D w = D w₀ := fun _ _ => rfl
    set w₀ : (Fin 1 → ℝ) × ℝ :=
      ((⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).β₂ false,
        (⟨0, 0, 0, 0⟩ : MultilevelModel Bool Bool 1).γ false)
    have hker : LinearMap.ker (D w₀ : (Fin 1 → ℝ) × ℝ →ₗ[ℝ] (Fin 2 → ℝ)) ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      refine ⟨(fun _ => 1, 0), ?_, fun h => by simpa using congrFun (congrArg Prod.fst h) 0⟩
      rw [LinearMap.mem_ker]
      funext z
      simp [D, subgroupMeansDeriv_twoDirac_apply]
    have hlt : Module.finrank ℝ (LinearMap.range
        (D w₀ : (Fin 1 → ℝ) × ℝ →ₗ[ℝ] (Fin 2 → ℝ))) < 1 + 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker
        (D w₀ : (Fin 1 → ℝ) × ℝ →ₗ[ℝ] (Fin 2 → ℝ))
      have h2 : 0 < Module.finrank ℝ (LinearMap.ker
          (D w₀ : (Fin 1 → ℝ) × ℝ →ₗ[ℝ] (Fin 2 → ℝ))) :=
        Nat.pos_of_ne_zero fun h => hker (Submodule.finrank_eq_zero.1 h)
      simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self] at h1
      omega
    exact not_pointIdentified_withArm_subgroupMeans_of_finrank_range_eq
      (F := fun _ => Measure.dirac fun _ => 0) (C := 1) (fun t => hasDerivAt_id t)
      continuous_const (fun _ => by simp) hF _ false true
      (Eventually.of_forall fun w => rfl) hlt Filter.univ_mem

end NetworkMetaRegression

end CausalInference
