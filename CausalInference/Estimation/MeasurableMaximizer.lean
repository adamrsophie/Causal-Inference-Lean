/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Order.Compact

/-!
# Measurable selection of a maximizer

Let `f ω ξ` be a real function of a point `ω` of a measurable space and of a parameter
`ξ ∈ ℝ^κ`, `κ` finite, measurable in `ω` for each `ξ ∈ K` and continuous in `ξ` on a compact
nonempty set `K` for each `ω`. Then some measurable `ξ̂ : Ω → ℝ^κ` has `ξ̂ ω ∈ K` and maximizes
`f ω` over `K` for every `ω` (`exists_measurable_forall_isMaxOn`). The maximizer need not be
unique; `ξ̂ ω` is the lexicographically least point of the set of maximizers, for an order of the
coordinates.

The proof has two steps.

* **Selection from a compact valued map.** Let `A ω ⊆ ℝ^κ` be compact and nonempty for every
  `ω`, and let `{ω | A ω ∩ F ≠ ∅}` be measurable for every closed `F` (`HasMeasurableHits`).
  Then the least value of a coordinate over `A ω` is measurable in `ω`
  (`measurable_sInf_image_eval`), the points of `A ω` where that coordinate is least form a map
  with the same properties (`HasMeasurableHits.inter_eval_eq_sInf`), and after fixing every
  coordinate in turn one point is left: a measurable selection
  (`exists_measurable_forall_mem_of_hasMeasurableHits`).
* **The set of maximizers has measurable hits.** The supremum of `f ω` over a compact set is
  the supremum over a countable dense subset, so it is measurable in `ω`
  (`measurable_sSup_image_of_continuousOn`), and the maximizers over `K` meet a closed `F` iff
  `sup_K f ω ≤ sup_{K ∩ F} f ω`.

The minimization form is `exists_measurable_forall_isMinOn`. The instance
`exists_measurable_isMaxOn_mul_abs` has a parameter `ω` for which the maximizer is not unique.

## Main definitions

* `HasMeasurableHits`.

## Main results

* `measurable_sInf_image_eval`, `HasMeasurableHits.inter_eval_eq_sInf`,
  `exists_measurable_forall_mem_of_hasMeasurableHits`.
* `measurable_sSup_image_of_continuousOn`, `exists_measurable_forall_isMaxOn`,
  `exists_measurable_forall_isMinOn`.
* `exists_measurable_isMaxOn_mul_abs`.

## References

* K. Kuratowski and C. Ryll-Nardzewski (1965), *A general theorem on selectors*.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalInference

variable {Ω κ : Type*} [MeasurableSpace Ω] [Finite κ]

/-! ### Selection from a compact valued map -/

/-- A set valued map `A : Ω → Set (ℝ^κ)` **has measurable hits** if for every closed `F` the
set `{ω | A ω ∩ F ≠ ∅}` of points where `A ω` meets `F` is measurable. -/
def HasMeasurableHits (A : Ω → Set (κ → ℝ)) : Prop :=
  ∀ F : Set (κ → ℝ), IsClosed F → MeasurableSet {ω | (A ω ∩ F).Nonempty}

omit [Finite κ] in
/-- A map with measurable hits, intersected with a fixed closed set, has measurable hits. -/
lemma HasMeasurableHits.inter_closed {A : Ω → Set (κ → ℝ)} (hA : HasMeasurableHits A)
    {F : Set (κ → ℝ)} (hF : IsClosed F) : HasMeasurableHits fun ω ↦ A ω ∩ F := fun F' hF' ↦ by
  simpa only [inter_assoc] using hA _ (hF.inter hF')

omit [Finite κ] in
/-- **The least value of a coordinate is measurable.** For a compact nonempty valued map with
measurable hits, `ω ↦ min {ξ_k : ξ ∈ A ω}` is measurable: `min ≤ t` iff `A ω` meets the closed
set `{ξ_k ≤ t}`. -/
lemma measurable_sInf_image_eval {A : Ω → Set (κ → ℝ)} (hAc : ∀ ω, IsCompact (A ω))
    (hAne : ∀ ω, (A ω).Nonempty) (hA : HasMeasurableHits A) (k : κ) :
    Measurable fun ω ↦ sInf ((fun ξ : κ → ℝ ↦ ξ k) '' A ω) := by
  refine measurable_of_Iic fun t ↦ ?_
  have hset : (fun ω ↦ sInf ((fun ξ : κ → ℝ ↦ ξ k) '' A ω)) ⁻¹' Iic t =
      {ω | (A ω ∩ {ξ | ξ k ≤ t}).Nonempty} := by
    ext ω
    have hc : IsCompact ((fun ξ : κ → ℝ ↦ ξ k) '' A ω) := (hAc ω).image (continuous_apply k)
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
    constructor
    · intro hle
      obtain ⟨ξ, hξ, hξe⟩ := hc.sInf_mem ((hAne ω).image _)
      exact ⟨ξ, hξ, (le_of_eq hξe).trans hle⟩
    · rintro ⟨ξ, hξ, hξt⟩
      exact (csInf_le hc.bddBelow (mem_image_of_mem _ hξ)).trans hξt
  rw [hset]
  exact hA _ (isClosed_le (continuous_apply k) continuous_const)

omit [Finite κ] in
/-- **Fixing a coordinate at its least value keeps the hits measurable.** For a compact nonempty
valued map `A` with measurable hits and `c ω = min {ξ_k : ξ ∈ A ω}`, the map
`ω ↦ A ω ∩ {ξ_k = c ω}` has measurable hits. Its hitting set of a closed `F` is the set of `ω`
where `A ω ∩ F ∩ {ξ_k ≤ r}` is nonempty for every rational `r > c ω`, by compactness. -/
lemma HasMeasurableHits.inter_eval_eq_sInf {A : Ω → Set (κ → ℝ)} (hAc : ∀ ω, IsCompact (A ω))
    (hAne : ∀ ω, (A ω).Nonempty) (hA : HasMeasurableHits A) (k : κ) :
    HasMeasurableHits fun ω ↦ A ω ∩ {ξ | ξ k = sInf ((fun ξ : κ → ℝ ↦ ξ k) '' A ω)} := by
  intro F hF
  set c : Ω → ℝ := fun ω ↦ sInf ((fun ξ : κ → ℝ ↦ ξ k) '' A ω) with hcdef
  have hcm : Measurable c := measurable_sInf_image_eval hAc hAne hA k
  have hset : {ω | (A ω ∩ {ξ | ξ k = c ω} ∩ F).Nonempty} =
      ⋂ r : ℚ, ({ω | c ω < r}ᶜ ∪ {ω | (A ω ∩ (F ∩ {ξ | ξ k ≤ r})).Nonempty}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, not_lt]
    constructor
    · rintro ⟨ξ, ⟨hξA, hξk⟩, hξF⟩ r
      by_cases hr : (r : ℝ) ≤ c ω
      · exact Or.inl hr
      · exact Or.inr ⟨ξ, hξA, hξF, show ξ k ≤ r by rw [hξk]; exact (not_le.1 hr).le⟩
    · intro h
      have hbdd : BddBelow ((fun ξ : κ → ℝ ↦ ξ k) '' A ω) :=
        ((hAc ω).image (continuous_apply k)).bddBelow
      -- `A ω ∩ F` is nonempty: take a rational above `c ω`
      obtain ⟨r₀, hr₀⟩ := exists_rat_gt (c ω)
      obtain ⟨ξ₀, hξ₀A, hξ₀F, -⟩ := (h r₀).resolve_left (not_le.2 hr₀)
      have hcF : IsCompact ((fun ξ : κ → ℝ ↦ ξ k) '' (A ω ∩ F)) :=
        ((hAc ω).inter_right hF).image (continuous_apply k)
      obtain ⟨ξ, ⟨hξA, hξF⟩, hξe⟩ := hcF.sInf_mem ⟨_, mem_image_of_mem _ ⟨hξ₀A, hξ₀F⟩⟩
      have hle : ξ k ≤ c ω := by
        refine le_of_forall_lt_rat_imp_le fun r hr ↦ ?_
        obtain ⟨η, hηA, hηF, hηr⟩ := (h r).resolve_left (not_le.2 hr)
        change ξ k = _ at hξe
        rw [hξe]
        exact (csInf_le hcF.bddBelow (mem_image_of_mem _ ⟨hηA, hηF⟩)).trans hηr
      exact ⟨ξ, ⟨hξA, le_antisymm hle (csInf_le hbdd (mem_image_of_mem _ hξA))⟩, hξF⟩
  rw [hset]
  exact MeasurableSet.iInter fun r ↦ (measurableSet_lt hcm measurable_const).compl.union
    (hA _ (hF.inter (isClosed_le (continuous_apply k) continuous_const)))

/-- **Measurable selection from a compact valued map.** A map `A : Ω → Set (ℝ^κ)` with compact
nonempty values and measurable hits has a measurable selection `g`, `g ω ∈ A ω` for every `ω`:
the lexicographically least point, obtained by fixing the coordinates one at a time at their
least values. -/
theorem exists_measurable_forall_mem_of_hasMeasurableHits {A : Ω → Set (κ → ℝ)}
    (hAc : ∀ ω, IsCompact (A ω)) (hAne : ∀ ω, (A ω).Nonempty) (hA : HasMeasurableHits A) :
    ∃ g : Ω → κ → ℝ, Measurable g ∧ ∀ ω, g ω ∈ A ω := by
  classical
  have := Fintype.ofFinite κ
  have key : ∀ s : Finset κ, ∃ B : Ω → Set (κ → ℝ), (∀ ω, B ω ⊆ A ω) ∧
      (∀ ω, IsCompact (B ω)) ∧ (∀ ω, (B ω).Nonempty) ∧ HasMeasurableHits B ∧
      ∀ j ∈ s, ∃ c : Ω → ℝ, Measurable c ∧ ∀ ω, ∀ ξ ∈ B ω, ξ j = c ω := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨A, fun _ ↦ subset_rfl, hAc, hAne, hA, by simp⟩
    · intro k s _ ih
      obtain ⟨B, hsub, hc, hne, hhit, hcoord⟩ := ih
      refine ⟨fun ω ↦ B ω ∩ {ξ | ξ k = sInf ((fun ξ : κ → ℝ ↦ ξ k) '' B ω)},
        fun ω ↦ inter_subset_left.trans (hsub ω),
        fun ω ↦ (hc ω).inter_right (isClosed_eq (continuous_apply _) continuous_const),
        fun ω ↦ ?_, hhit.inter_eval_eq_sInf hc hne k, fun j hj ↦ ?_⟩
      · obtain ⟨ξ, hξ, hξe⟩ :=
          ((hc ω).image (continuous_apply k)).sInf_mem ((hne ω).image _)
        exact ⟨ξ, hξ, hξe⟩
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact ⟨_, measurable_sInf_image_eval hc hne hhit j, fun ω ξ hξ ↦ hξ.2⟩
        · obtain ⟨c, hcm, hc'⟩ := hcoord j hj
          exact ⟨c, hcm, fun ω ξ hξ ↦ hc' ω ξ hξ.1⟩
  obtain ⟨B, hsub, -, hne, -, hcoord⟩ := key Finset.univ
  choose c hcm hc using fun j : κ ↦ hcoord j (Finset.mem_univ j)
  refine ⟨fun ω j ↦ c j ω, Measurable.of_eval hcm, fun ω ↦ ?_⟩
  obtain ⟨ξ, hξ⟩ := hne ω
  have hξc : ξ = fun j ↦ c j ω := funext fun j ↦ hc j ω ξ hξ
  change (fun j ↦ c j ω) ∈ A ω
  rw [← hξc]
  exact hsub ω hξ

/-! ### Measurable selection of a maximizer -/

/-- **The supremum over a compact set of a function continuous in the parameter is measurable.**
If `f ω ξ` is measurable in `ω` for each `ξ ∈ S` and continuous in `ξ` on `S`, `S` compact and
nonempty, then `ω ↦ sup_{ξ ∈ S} f ω ξ` is measurable: it exceeds `t` iff `f ω d > t` for some `d`
in a countable dense subset of `S`. -/
lemma measurable_sSup_image_of_continuousOn {f : Ω → (κ → ℝ) → ℝ} {S : Set (κ → ℝ)}
    (hfm : ∀ ξ ∈ S, Measurable fun ω ↦ f ω ξ) (hS : IsCompact S) (hSne : S.Nonempty)
    (hfc : ∀ ω, ContinuousOn (f ω) S) : Measurable fun ω ↦ sSup (f ω '' S) := by
  obtain ⟨D, hDS, hDc, hSD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  refine measurable_of_Ioi fun t ↦ ?_
  have hset : (fun ω ↦ sSup (f ω '' S)) ⁻¹' Ioi t = ⋃ d ∈ D, {ω | t < f ω d} := by
    ext ω
    simp only [mem_preimage, mem_Ioi, mem_iUnion, exists_prop, mem_ofPred_eq]
    rw [lt_csSup_iff ((hS.image_of_continuousOn (hfc ω)).bddAbove) (hSne.image _)]
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, hts⟩
      obtain ⟨U, hUo, hsU, hU⟩ := mem_nhdsWithin.1 ((hfc ω s hs) (lt_mem_nhds hts))
      obtain ⟨d, hdU, hdD⟩ := mem_closure_iff.1 (hSD hs) U hUo hsU
      exact ⟨d, hdD, hU ⟨hdU, hDS hdD⟩⟩
    · rintro ⟨d, hdD, htd⟩
      exact ⟨f ω d, mem_image_of_mem _ (hDS hdD), htd⟩
  rw [hset]
  exact MeasurableSet.biUnion hDc fun d hd ↦ measurableSet_lt measurable_const (hfm d (hDS hd))

/-- **Measurable selection of a maximizer.** Let `K ⊆ ℝ^κ` be compact and nonempty and let
`f ω ξ` be measurable in `ω` for each `ξ ∈ K` and continuous in `ξ` on `K` for each `ω`. Then
some measurable `g : Ω → ℝ^κ` has `g ω ∈ K` and `g ω` maximizes `f ω` over `K`, for every `ω`.
No uniqueness of the maximizer is assumed. -/
theorem exists_measurable_forall_isMaxOn {f : Ω → (κ → ℝ) → ℝ} {K : Set (κ → ℝ)}
    (hfm : ∀ ξ ∈ K, Measurable fun ω ↦ f ω ξ) (hK : IsCompact K) (hKne : K.Nonempty)
    (hfc : ∀ ω, ContinuousOn (f ω) K) :
    ∃ g : Ω → κ → ℝ, Measurable g ∧ ∀ ω, g ω ∈ K ∧ IsMaxOn (f ω) K (g ω) := by
  set A : Ω → Set (κ → ℝ) := fun ω ↦ K ∩ f ω ⁻¹' Ici (sSup (f ω '' K)) with hAdef
  have hmem : ∀ ω ξ, ξ ∈ A ω ↔ ξ ∈ K ∧ IsMaxOn (f ω) K ξ := by
    intro ω ξ
    have hbdd := (hK.image_of_continuousOn (hfc ω)).bddAbove
    constructor
    · rintro ⟨hξ, hle⟩
      exact ⟨hξ, isMaxOn_iff.2 fun ξ' hξ' ↦ (le_csSup hbdd (mem_image_of_mem _ hξ')).trans hle⟩
    · rintro ⟨hξ, hmax⟩
      refine ⟨hξ, csSup_le (hKne.image _) ?_⟩
      rintro _ ⟨ξ', hξ', rfl⟩
      exact isMaxOn_iff.1 hmax ξ' hξ'
  have hAc : ∀ ω, IsCompact (A ω) := fun ω ↦
    hK.of_isClosed_subset ((hfc ω).preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici)
      inter_subset_left
  have hAne : ∀ ω, (A ω).Nonempty := fun ω ↦ by
    obtain ⟨ξ, hξ, hmax⟩ := hK.exists_isMaxOn hKne (hfc ω)
    exact ⟨ξ, (hmem ω ξ).2 ⟨hξ, hmax⟩⟩
  have hhit : HasMeasurableHits A := by
    intro F hF
    by_cases hKF : (K ∩ F).Nonempty
    · have h1 := measurable_sSup_image_of_continuousOn hfm hK hKne hfc
      have h2 := measurable_sSup_image_of_continuousOn (S := K ∩ F)
        (fun ξ hξ ↦ hfm ξ (mem_of_mem_inter_left hξ)) (hK.inter_right hF) hKF
        fun ω ↦ (hfc ω).mono inter_subset_left
      have hset : {ω | (A ω ∩ F).Nonempty} =
          {ω | sSup (f ω '' K) ≤ sSup (f ω '' (K ∩ F))} := by
        ext ω
        have hcKF : IsCompact (f ω '' (K ∩ F)) :=
          (hK.inter_right hF).image_of_continuousOn ((hfc ω).mono inter_subset_left)
        simp only [mem_ofPred_eq]
        constructor
        · rintro ⟨ξ, ⟨hξK, hξM⟩, hξF⟩
          exact (show sSup (f ω '' K) ≤ f ω ξ from hξM).trans
            (le_csSup hcKF.bddAbove (mem_image_of_mem _ ⟨hξK, hξF⟩))
        · intro hle
          obtain ⟨ξ, ⟨hξK, hξF⟩, hξe⟩ := hcKF.sSup_mem (hKF.image _)
          refine ⟨ξ, ⟨hξK, ?_⟩, hξF⟩
          change sSup (f ω '' K) ≤ f ω ξ
          rw [hξe]
          exact hle
      rw [hset]
      exact measurableSet_le h1 h2
    · have hset : {ω | (A ω ∩ F).Nonempty} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨ξ, ⟨hξK, -⟩, hξF⟩
        exact hKF ⟨ξ, hξK, hξF⟩
      rw [hset]
      exact MeasurableSet.empty
  obtain ⟨g, hgm, hg⟩ := exists_measurable_forall_mem_of_hasMeasurableHits hAc hAne hhit
  exact ⟨g, hgm, fun ω ↦ (hmem ω (g ω)).1 (hg ω)⟩

/-- **Measurable selection of a minimizer**: under the hypotheses of
`exists_measurable_forall_isMaxOn`, some measurable `g` has `g ω ∈ K` minimizing `f ω` over
`K` for every `ω`. -/
theorem exists_measurable_forall_isMinOn {f : Ω → (κ → ℝ) → ℝ} {K : Set (κ → ℝ)}
    (hfm : ∀ ξ ∈ K, Measurable fun ω ↦ f ω ξ) (hK : IsCompact K) (hKne : K.Nonempty)
    (hfc : ∀ ω, ContinuousOn (f ω) K) :
    ∃ g : Ω → κ → ℝ, Measurable g ∧ ∀ ω, g ω ∈ K ∧ IsMinOn (f ω) K (g ω) := by
  obtain ⟨g, hgm, hg⟩ := exists_measurable_forall_isMaxOn (f := fun ω ξ ↦ -f ω ξ)
    (fun ξ hξ ↦ (hfm ξ hξ).neg) hK hKne fun ω ↦ (hfc ω).neg
  refine ⟨g, hgm, fun ω ↦ ⟨(hg ω).1, isMinOn_iff.2 fun ξ hξ ↦ ?_⟩⟩
  have := isMaxOn_iff.1 (hg ω).2 ξ hξ
  exact neg_le_neg_iff.1 this

/-! ### An instance with a maximizer that is not unique -/

/-- **A measurable maximizer where the maximizer is not unique.** For `f ω ξ = ω |ξ₀|` on
`K = [-1, 1]` (in `ℝ^1`), a measurable selection of a maximizer exists; at `ω = 1` both `-1` and
`1` maximize `f 1` over `K`, so the set of maximizers is not a single point. -/
theorem exists_measurable_isMaxOn_mul_abs :
    (∃ g : ℝ → Fin 1 → ℝ, Measurable g ∧ ∀ ω, g ω ∈ Icc (-1) 1 ∧
      IsMaxOn (fun ξ : Fin 1 → ℝ ↦ ω * |ξ 0|) (Icc (-1) 1) (g ω)) ∧
    IsMaxOn (fun ξ : Fin 1 → ℝ ↦ 1 * |ξ 0|) (Icc (-1) 1) (fun _ ↦ 1) ∧
    IsMaxOn (fun ξ : Fin 1 → ℝ ↦ 1 * |ξ 0|) (Icc (-1) 1) (fun _ ↦ -1) ∧
    (fun _ ↦ (1 : ℝ) : Fin 1 → ℝ) ≠ fun _ ↦ -1 := by
  have hmax : ∀ ξ ∈ Icc (-1 : Fin 1 → ℝ) 1, 1 * |ξ 0| ≤ 1 := fun ξ hξ ↦ by
    rw [one_mul, abs_le]
    exact ⟨hξ.1 0, hξ.2 0⟩
  refine ⟨exists_measurable_forall_isMaxOn (fun ξ _ ↦ measurable_id.mul_const _) isCompact_Icc
    ⟨0, fun _ ↦ by norm_num, fun _ ↦ by norm_num⟩
    fun ω ↦ (continuous_const.mul (continuous_abs.comp (continuous_apply 0))).continuousOn,
    isMaxOn_iff.2 fun ξ hξ ↦ by simpa using hmax ξ hξ,
    isMaxOn_iff.2 fun ξ hξ ↦ by simpa using hmax ξ hξ, fun h ↦ ?_⟩
  have := congrFun h 0
  norm_num at this

end CausalInference
