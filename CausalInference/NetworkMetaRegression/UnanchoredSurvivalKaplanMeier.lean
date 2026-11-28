/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import CausalInference.Survival.KaplanMeier

/-!
# Reconstruction of event data from a published Kaplan Meier curve

**Time scale: continuous.** In an unanchored comparison of time to event outcomes one arm is
available as individual data and the other only as a published Kaplan Meier curve, often with the
numbers at risk at the event times. This file treats the reconstruction of event data from such a
publication.

A sample of `N` observations is a map `s : ι → ℝ × Bool` (observed time, event indicator). The
number at risk at `τ` counts the observed times `≥ τ` (a censoring tied with an event time is at
risk there), the number of events at `τ` counts the events observed at `τ`, and the Kaplan Meier
estimator is the product over the distinct observed event times `τ ≤ t` of `1 - d(τ) / n(τ)`
(`sampleKaplanMeier`). No factor of this product divides by zero: an observed event at `τ` is at
risk at `τ` (`sampleAtRisk_pos_of_event`).

A publication reports increasing event times `t_1 < ⋯ < t_m`, the event counts `d_j` and the
numbers at risk `n_j > 0`; its curve is `∏_{t_j ≤ t} (1 - d_j / n_j)` (`publishedKaplanMeier`).

## Main definitions

* `sampleAtRisk`, `sampleEvents`, `sampleCensorings`, `sampleKaplanMeier`.
* `publishedKaplanMeier`.

## Main results

* `sampleKaplanMeier_natCast`: with integer observed times the estimator is
  `Survival.kaplanMeier`.
* `publishedKaplanMeier_inversion`: the curve and the numbers at risk determine the event counts,
  `d_j = n_j (1 - Ŝ(t_j) / Ŝ(t_{j-1}))`, when no event time before the last one exhausts the
  risk set; `publishedKaplanMeier_counts_unique`: two event count sequences with the same curve
  and the same numbers at risk agree.
* `sampleCensorings_eq`: in a sample with the published numbers at risk and event counts, the
  number of censorings in `[t_j, t_{j+1})` is `n_j - d_j - n_{j+1}`.
* `sampleAtRisk_of_counts`, `sampleKaplanMeier_eq_published`,
  `sampleKaplanMeier_reconstruction`: a pseudo sample with the reported counts in each interval
  `[t_j, t_{j+1})` has the published curve at every time, wherever its censorings sit.
* `sampleKaplanMeier_censoring_not_identified`: the curve does not identify the censoring times;
  two samples with the same curve have different exponential censored likelihoods at every rate.
* `publishedKaplanMeier_instance`: the reconstruction with all hypotheses discharged on three
  event times.

## References

* E. L. Kaplan and P. Meier, *Nonparametric estimation from incomplete observations*, Journal of
  the American Statistical Association 53 (1958).
* P. Guyot, A. E. Ades, M. J. N. M. Ouwens and N. J. Welton, *Enhanced secondary analysis of
  survival data: reconstructing the data from published Kaplan-Meier survival curves*, BMC
  Medical Research Methodology 12:9 (2012).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open Finset

/-! ### Kaplan Meier estimator of a sample -/

section Sample

variable {ι : Type*} [Fintype ι]

/-- The **number at risk** at time `τ` in a sample of (observed time, event indicator) pairs: the
observations with observed time `≥ τ`. -/
noncomputable def sampleAtRisk (s : ι → ℝ × Bool) (τ : ℝ) : ℕ :=
  (univ.filter fun i => τ ≤ (s i).1).card

/-- The **number of events** observed at time `τ`. -/
noncomputable def sampleEvents (s : ι → ℝ × Bool) (τ : ℝ) : ℕ :=
  (univ.filter fun i => (s i).1 = τ ∧ (s i).2 = true).card

/-- The **number of censorings** observed in the interval `[a, b)`. -/
noncomputable def sampleCensorings (s : ι → ℝ × Bool) (a b : ℝ) : ℕ :=
  (univ.filter fun i => a ≤ (s i).1 ∧ (s i).1 < b ∧ (s i).2 = false).card

/-- The **Kaplan Meier (product limit) estimator** of a sample at time `t`: the product over the
distinct observed event times `τ ≤ t` of `1 - d(τ) / n(τ)`. -/
noncomputable def sampleKaplanMeier (s : ι → ℝ × Bool) (t : ℝ) : ℝ :=
  ∏ τ ∈ (univ.filter fun i => (s i).2 = true ∧ (s i).1 ≤ t).image (fun i => (s i).1),
    (1 - (sampleEvents s τ : ℝ) / sampleAtRisk s τ)

/-- An observed event time has a positive number at risk, so no factor of the Kaplan Meier
product divides by zero. -/
theorem sampleAtRisk_pos_of_event (s : ι → ℝ × Bool) {i : ι} :
    0 < sampleAtRisk s (s i).1 :=
  card_pos.2 ⟨i, by simp⟩

/-- The number of events at `τ` is at most the number at risk at `τ`. -/
theorem sampleEvents_le_sampleAtRisk (s : ι → ℝ × Bool) (τ : ℝ) :
    sampleEvents s τ ≤ sampleAtRisk s τ :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.1.symm.le

/-- Every factor of the Kaplan Meier product lies in `[0, 1]`, hence so does the estimator. -/
theorem sampleKaplanMeier_mem_Icc (s : ι → ℝ × Bool) (t : ℝ) :
    0 ≤ sampleKaplanMeier s t ∧ sampleKaplanMeier s t ≤ 1 := by
  have hfac : ∀ τ : ℝ, 0 ≤ 1 - (sampleEvents s τ : ℝ) / sampleAtRisk s τ ∧
      1 - (sampleEvents s τ : ℝ) / sampleAtRisk s τ ≤ 1 := fun τ => by
    have hle : (sampleEvents s τ : ℝ) ≤ sampleAtRisk s τ := by
      exact_mod_cast sampleEvents_le_sampleAtRisk s τ
    refine ⟨sub_nonneg.2 (div_le_one_of_le₀ hle (Nat.cast_nonneg _)), ?_⟩
    have : 0 ≤ (sampleEvents s τ : ℝ) / sampleAtRisk s τ := by positivity
    linarith
  exact ⟨prod_nonneg fun τ _ => (hfac τ).1, prod_le_one₀ (fun τ _ => (hfac τ).1)
    fun τ _ => (hfac τ).2⟩

end Sample

/-! ### Integer observed times -/

/-- **Bridge to the estimator on integer times.** For a data set `d` with integer observed times,
the Kaplan Meier estimator of the sample with the times read as reals is the estimator
`Survival.kaplanMeier d k` at every integer time `k`: the factors at times without events are
`1` on both sides. -/
theorem sampleKaplanMeier_natCast {N : ℕ} (d : Fin N → ℕ × Bool) (k : ℕ) :
    sampleKaplanMeier (fun i => (((d i).1 : ℝ), (d i).2)) k = Survival.kaplanMeier d k := by
  classical
  set F := univ.filter fun i => (d i).2 = true ∧ (d i).1 ≤ k with hF
  have hfilt : (univ.filter fun i : Fin N => ((fun i => (((d i).1 : ℝ), (d i).2)) i).2 = true ∧
      ((fun i => (((d i).1 : ℝ), (d i).2)) i).1 ≤ (k : ℝ)) = F := by
    rw [hF]
    congr 1
    ext i
    simp only [Nat.cast_le]
  have hev : ∀ m : ℕ, sampleEvents (fun i => (((d i).1 : ℝ), (d i).2)) m =
      Survival.eventCount d m := fun m => by
    unfold sampleEvents Survival.eventCount
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, Nat.cast_inj]
  have hrisk : ∀ m : ℕ, sampleAtRisk (fun i => (((d i).1 : ℝ), (d i).2)) m =
      Survival.atRiskCount d m := fun m => by
    unfold sampleAtRisk Survival.atRiskCount
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, Nat.cast_le]
  unfold sampleKaplanMeier
  rw [hfilt, show F.image (fun i => ((d i).1 : ℝ)) = (F.image fun i => (d i).1).image
      (fun m : ℕ => (m : ℝ)) by rw [image_image]; rfl,
    prod_image fun a _ b _ h => Nat.cast_injective h]
  simp only [hev, hrisk]
  unfold Survival.kaplanMeier
  refine prod_subset (fun m hm => ?_) fun m _ hm => ?_
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 hm
    rw [hF, mem_filter] at hi
    exact mem_range.2 (Nat.lt_succ_of_le hi.2.2)
  · have h0 : Survival.eventCount d m = 0 := by
      unfold Survival.eventCount
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro i - ⟨h1, h2⟩
      refine hm (mem_image.2 ⟨i, ?_, h1⟩)
      rw [hF, mem_filter]
      exact ⟨mem_univ _, h2, h1 ▸ Nat.lt_succ_iff.1 (mem_range.1 ‹_›)⟩
    simp [h0]

/-! ### The published curve -/

/-- The **published Kaplan Meier curve** of event times `t_j`, event counts `d_j` and numbers at
risk `n_j`, `j = 1, …, m`: the product of `1 - d_j / n_j` over the event times `t_j ≤ t`. -/
noncomputable def publishedKaplanMeier (tt : ℕ → ℝ) (d n : ℕ → ℕ) (m : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ (Icc 1 m).filter (fun j => tt j ≤ t), (1 - (d j : ℝ) / n j)

/-- At the event time `t_j` (`j ≤ m`) of increasing event times the published curve is the
product of the first `j` factors. -/
theorem publishedKaplanMeier_apply {tt : ℕ → ℝ} (htt : StrictMono tt) (d n : ℕ → ℕ) {m j : ℕ}
    (hj : j ≤ m) :
    publishedKaplanMeier tt d n m (tt j) = ∏ i ∈ Icc 1 j, (1 - (d i : ℝ) / n i) := by
  unfold publishedKaplanMeier
  congr 1
  ext i
  simp only [mem_filter, mem_Icc, htt.le_iff_le]
  omega

/-- The published curve is positive up to `t_j` when `d_i < n_i` for every `i ≤ j`. -/
theorem publishedKaplanMeier_pos {tt : ℕ → ℝ} (htt : StrictMono tt) {d n : ℕ → ℕ} {m j : ℕ}
    (hj : j ≤ m) (hlt : ∀ i ∈ Icc 1 j, d i < n i) :
    0 < publishedKaplanMeier tt d n m (tt j) := by
  rw [publishedKaplanMeier_apply htt d n hj]
  refine prod_pos fun i hi => ?_
  have h := hlt i hi
  have hn : (0 : ℝ) < n i := by exact_mod_cast (Nat.zero_le _).trans_lt h
  rw [sub_pos, div_lt_one hn]
  exact_mod_cast h

/-- At the event times before the last one, `d_j < n_j` forces `n_j > 0`; with `n_m > 0` every
number at risk is positive. -/
theorem publishedAtRisk_pos {d n : ℕ → ℕ} {m : ℕ} (hnm : 0 < n m)
    (hlt : ∀ j ∈ Ico 1 m, d j < n j) : ∀ j ∈ Icc 1 m, 0 < n j := by
  intro j hj
  obtain ⟨h1, h2⟩ := mem_Icc.1 hj
  rcases h2.lt_or_eq with h | rfl
  · exact (Nat.zero_le _).trans_lt (hlt j (mem_Ico.2 ⟨h1, h⟩))
  · exact hnm

/-- **Inversion of the published curve.** For increasing event times, a positive number at risk
at the last event time and `d_j < n_j` at every event time before the last one, the published
curve is `1` at `t_0` and the event counts are `d_j = n_j (1 - Ŝ(t_j) / Ŝ(t_{j-1}))`,
`j = 1, …, m`: the curve and the numbers at risk determine the event counts. -/
theorem publishedKaplanMeier_inversion {tt : ℕ → ℝ} (htt : StrictMono tt) {d n : ℕ → ℕ} {m : ℕ}
    (hnm : 0 < n m) (hlt : ∀ j ∈ Ico 1 m, d j < n j) :
    publishedKaplanMeier tt d n m (tt 0) = 1 ∧
      ∀ j ∈ Icc 1 m, (d j : ℝ) = n j * (1 - publishedKaplanMeier tt d n m (tt j) /
        publishedKaplanMeier tt d n m (tt (j - 1))) := by
  refine ⟨by rw [publishedKaplanMeier_apply htt d n (Nat.zero_le _)]; simp, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := mem_Icc.1 hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hP : publishedKaplanMeier tt d n m (tt k) ≠ 0 :=
    (publishedKaplanMeier_pos htt (by omega) fun i hi => hlt i (by
      simp only [mem_Icc, mem_Ico] at hi ⊢; omega)).ne'
  have hn' : (n (k + 1) : ℝ) ≠ 0 := by have := publishedAtRisk_pos hnm hlt _ hj; positivity
  have e : publishedKaplanMeier tt d n m (tt (k + 1)) =
      publishedKaplanMeier tt d n m (tt k) * (1 - (d (k + 1) : ℝ) / n (k + 1)) := by
    rw [publishedKaplanMeier_apply htt d n h2, publishedKaplanMeier_apply htt d n (by omega),
      prod_Icc_succ_top (by omega)]
  rw [e]
  field_simp
  ring

/-- **The event counts are unique**: two event count sequences with the same numbers at risk
that give the same published curve at the event times agree, when the first leaves survivors at
every event time before the last one and the last number at risk is positive. -/
theorem publishedKaplanMeier_counts_unique {tt : ℕ → ℝ} (htt : StrictMono tt) {d d' n : ℕ → ℕ}
    {m : ℕ} (hnm : 0 < n m) (hlt : ∀ j ∈ Ico 1 m, d j < n j)
    (heq : ∀ j ≤ m, publishedKaplanMeier tt d n m (tt j) =
      publishedKaplanMeier tt d' n m (tt j)) :
    ∀ j ∈ Icc 1 m, d j = d' j := by
  intro j hj
  obtain ⟨h1, h2⟩ := mem_Icc.1 hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hP : publishedKaplanMeier tt d n m (tt k) ≠ 0 :=
    (publishedKaplanMeier_pos htt (by omega) fun i hi => hlt i (by
      simp only [mem_Icc, mem_Ico] at hi ⊢; omega)).ne'
  have hn' : (n (k + 1) : ℝ) ≠ 0 := by have := publishedAtRisk_pos hnm hlt _ hj; positivity
  have e : ∀ d : ℕ → ℕ, publishedKaplanMeier tt d n m (tt (k + 1)) =
      publishedKaplanMeier tt d n m (tt k) * (1 - (d (k + 1) : ℝ) / n (k + 1)) := fun d => by
    rw [publishedKaplanMeier_apply htt d n h2, publishedKaplanMeier_apply htt d n (by omega),
      prod_Icc_succ_top (by omega)]
  have h := heq (k + 1) h2
  rw [e d, e d', ← heq k (by omega)] at h
  have h' := mul_left_cancel₀ hP h
  have : (d (k + 1) : ℝ) = d' (k + 1) := by
    field_simp at h'
    linarith
  exact_mod_cast this

/-! ### Censoring counts and reconstruction -/

section Reconstruction

variable {ι : Type*} [Fintype ι]

/-- The observations at or after `a` split into those in `[a, b)` and those at or after `b`. -/
theorem sampleAtRisk_eq_add (s : ι → ℝ × Bool) {a b : ℝ} (hab : a ≤ b) :
    sampleAtRisk s a =
      (univ.filter fun i => a ≤ (s i).1 ∧ (s i).1 < b).card + sampleAtRisk s b := by
  classical
  unfold sampleAtRisk
  rw [← card_union_of_disjoint (disjoint_filter.2 fun i _ h1 h2 => absurd h2 (not_le.2 h1.2))]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_union]
  constructor
  · intro h
    by_cases h' : (s i).1 < b
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr (not_lt.1 h')
  · rintro (h | h)
    · exact h.1
    · exact hab.trans h

/-- **Inversion into censoring counts.** In a sample whose events in `[t_j, t_{j+1})` all occur
at `t_j`, with `n_j` at risk at `t_j`, `n_{j+1}` at risk at `t_{j+1}` and `d_j` events at `t_j`,
the number of censorings in `[t_j, t_{j+1})` is `n_j - d_j - n_{j+1}`. -/
theorem sampleCensorings_eq (s : ι → ℝ × Bool) {a b : ℝ} (hab : a < b)
    (hev : ∀ i, (s i).2 = true → a ≤ (s i).1 → (s i).1 < b → (s i).1 = a) {na nb d : ℕ}
    (hna : sampleAtRisk s a = na) (hnb : sampleAtRisk s b = nb) (hd : sampleEvents s a = d) :
    (sampleCensorings s a b : ℤ) = na - d - nb := by
  classical
  have hsplit := sampleAtRisk_eq_add s hab.le
  have hint : (univ.filter fun i => a ≤ (s i).1 ∧ (s i).1 < b).card =
      sampleEvents s a + sampleCensorings s a b := by
    unfold sampleEvents sampleCensorings
    rw [← card_union_of_disjoint (disjoint_filter.2 fun i _ h1 h2 => by
      rw [h1.2] at h2; exact Bool.noConfusion h2.2.2)]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      cases hb : (s i).2
      · exact Or.inr ⟨h1, h2, rfl⟩
      · exact Or.inl ⟨hev i hb h1 h2, rfl⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, -⟩)
      · exact ⟨h1.ge, h1 ▸ hab⟩
      · exact ⟨h1, h2⟩
  omega

/-- **The numbers at risk of a pseudo sample.** If a sample has, in each interval
`[t_j, t_{j+1})`, `j = 1, …, m`, exactly `n_j - n_{j+1}` observations and `n_{m+1}` observations
at or after `t_{m+1}`, then it has `n_j` at risk at every `t_j`, `j = 1, …, m + 1`. -/
theorem sampleAtRisk_of_counts (s : ι → ℝ × Bool) {tt : ℕ → ℝ} (htt : StrictMono tt)
    {n : ℕ → ℕ} {m : ℕ}
    (hint : ∀ j ∈ Icc 1 m,
      (univ.filter fun i => tt j ≤ (s i).1 ∧ (s i).1 < tt (j + 1)).card + n (j + 1) = n j)
    (hlast : sampleAtRisk s (tt (m + 1)) = n (m + 1)) :
    ∀ j ∈ Icc 1 (m + 1), sampleAtRisk s (tt j) = n j := by
  have key : ∀ k ≤ m, sampleAtRisk s (tt (m + 1 - k)) = n (m + 1 - k) := by
    intro k
    induction k with
    | zero => intro _; simpa using hlast
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      rw [show m + 1 - k = (m + 1 - (k + 1)) + 1 by omega] at ih'
      rw [sampleAtRisk_eq_add s (htt.monotone (Nat.le_succ (m + 1 - (k + 1)))), ih']
      exact hint _ (mem_Icc.2 ⟨by omega, by omega⟩)
  intro j hj
  have hj' := mem_Icc.1 hj
  have := key (m + 1 - j) (by omega)
  rwa [show m + 1 - (m + 1 - j) = j by omega] at this

/-- **A sample with the published counts has the published curve.** If every event of a sample
occurs at one of the increasing times `t_j`, and the sample has `d_j` events and `n_j` at risk at
each `t_j`, then its Kaplan Meier estimator equals the published curve at every time. -/
theorem sampleKaplanMeier_eq_published (s : ι → ℝ × Bool) {tt : ℕ → ℝ} (htt : StrictMono tt)
    {d n : ℕ → ℕ} {m : ℕ} (hev : ∀ i, (s i).2 = true → ∃ j ∈ Icc 1 m, (s i).1 = tt j)
    (hd : ∀ j ∈ Icc 1 m, sampleEvents s (tt j) = d j)
    (hn : ∀ j ∈ Icc 1 m, sampleAtRisk s (tt j) = n j) (t : ℝ) :
    sampleKaplanMeier s t = publishedKaplanMeier tt d n m t := by
  classical
  have hE : (univ.filter fun i => (s i).2 = true ∧ (s i).1 ≤ t).image (fun i => (s i).1) =
      ((Icc 1 m).filter fun j => 0 < d j ∧ tt j ≤ t).image tt := by
    ext τ
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, ⟨hb, hle⟩, rfl⟩
      obtain ⟨j, hj, hji⟩ := hev i hb
      refine ⟨j, ⟨hj, ?_, hji ▸ hle⟩, hji.symm⟩
      rw [← hd j hj]
      exact card_pos.2 ⟨i, by simp [hji, hb]⟩
    · rintro ⟨j, ⟨hj, hdpos, hle⟩, rfl⟩
      rw [← hd j hj] at hdpos
      obtain ⟨i, hi⟩ := card_pos.1 hdpos
      simp only [mem_filter, mem_univ, true_and] at hi
      exact ⟨i, ⟨hi.2, hi.1 ▸ hle⟩, hi.1⟩
  unfold sampleKaplanMeier
  rw [hE, prod_image htt.injective.injOn]
  unfold publishedKaplanMeier
  rw [prod_congr rfl fun j hj => by
    rw [hd j (mem_filter.1 hj).1, hn j (mem_filter.1 hj).1]]
  refine prod_subset (fun j hj => ?_) fun j hj hj' => ?_
  · simp only [mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.2⟩
  · have hd0 : d j = 0 := by
      by_contra h0
      exact hj' (mem_filter.2 ⟨(mem_filter.1 hj).1, Nat.pos_of_ne_zero h0,
        (mem_filter.1 hj).2⟩)
    simp [hd0]

/-- **Exact reconstruction.** A pseudo sample with its events only at the increasing times `t_j`,
`d_j` events at each `t_j`, `n_j - n_{j+1}` observations in each `[t_j, t_{j+1})` and `n_{m+1}`
observations from `t_{m+1}` on has the published Kaplan Meier curve at every time, wherever its
censorings sit inside the intervals. -/
theorem sampleKaplanMeier_reconstruction (s : ι → ℝ × Bool) {tt : ℕ → ℝ} (htt : StrictMono tt)
    {d n : ℕ → ℕ} {m : ℕ} (hev : ∀ i, (s i).2 = true → ∃ j ∈ Icc 1 m, (s i).1 = tt j)
    (hd : ∀ j ∈ Icc 1 m, sampleEvents s (tt j) = d j)
    (hint : ∀ j ∈ Icc 1 m,
      (univ.filter fun i => tt j ≤ (s i).1 ∧ (s i).1 < tt (j + 1)).card + n (j + 1) = n j)
    (hlast : sampleAtRisk s (tt (m + 1)) = n (m + 1)) (t : ℝ) :
    sampleKaplanMeier s t = publishedKaplanMeier tt d n m t :=
  sampleKaplanMeier_eq_published s htt hev hd (fun j hj => sampleAtRisk_of_counts s htt hint
    hlast j (mem_Icc.2 ⟨(mem_Icc.1 hj).1, (mem_Icc.1 hj).2.trans (Nat.le_succ m)⟩)) t

end Reconstruction

/-! ### The curve does not identify the censoring times -/

/-- **The censoring times are not identified by the curve.** The samples
`{(1, event), (2, censored)}` and `{(1, event), (3, censored)}` are different and have the same
Kaplan Meier curve, but for every rate `λ > 0` their exponential censored likelihoods
`∏ λ^δ e^{-λ t}` differ. So the reconstruction reproduces the curve, not the sample, and a
statistic that uses the exact censoring times is not determined by the publication. -/
theorem sampleKaplanMeier_censoring_not_identified :
    let s : Fin 2 → ℝ × Bool := ![(1, true), (2, false)]
    let s' : Fin 2 → ℝ × Bool := ![(1, true), (3, false)]
    s ≠ s' ∧ (∀ t, sampleKaplanMeier s t = sampleKaplanMeier s' t) ∧
      ∀ l : ℝ, 0 < l → (∏ i, (if (s i).2 then l else 1) * Real.exp (-(l * (s i).1))) ≠
        ∏ i, (if (s' i).2 then l else 1) * Real.exp (-(l * (s' i).1)) := by
  intro s s'
  have htt : StrictMono (fun j : ℕ => (j : ℝ)) := fun a b h => Nat.cast_lt.2 h
  have hgen : ∀ c : ℝ, 1 < c → ∀ t,
      sampleKaplanMeier ![((1 : ℝ), true), (c, false)] t =
        publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) (fun _ => 2) 1 t := by
    intro c hc t
    refine sampleKaplanMeier_eq_published _ htt ?_ ?_ ?_ t
    · intro i hi
      fin_cases i
      · exact ⟨1, by simp, by simp⟩
      · simp at hi
    · intro j hj
      obtain rfl : j = 1 := by simpa using hj
      unfold sampleEvents
      rw [card_eq_one]
      refine ⟨0, ?_⟩
      ext i
      fin_cases i <;> simp
    · intro j hj
      obtain rfl : j = 1 := by simpa using hj
      unfold sampleAtRisk
      rw [filter_true_of_mem fun i _ => by fin_cases i <;> simp; linarith]
      simp
  refine ⟨fun h => ?_, fun t => ?_, fun l hl => ?_⟩
  · have := congrArg (fun f => (f 1).1) h
    norm_num [s, s'] at this
  · rw [hgen 2 (by norm_num), hgen 3 (by norm_num)]
  · simp only [s, s', Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ite_true,
      Bool.false_eq_true, ite_false, one_mul]
    intro h
    have h' := mul_left_cancel₀ (by positivity : l * Real.exp (-(l * 1)) ≠ 0) h
    have := Real.exp_injective h'
    nlinarith

/-! ### An instance -/

/-- The pseudo sample of the instance: events at `1`, `2`, `3` and censorings at `3/2`, `5/2`. -/
noncomputable def reconstructedSample : Fin 5 → ℝ × Bool :=
  ![(1, true), (3 / 2, false), (2, true), (5 / 2, false), (3, true)]

/-- The reported numbers at risk of the instance: `5`, `3`, `1` at the times `1`, `2`, `3`, and
`0` afterwards. -/
def reportedAtRisk (j : ℕ) : ℕ := if j = 1 then 5 else if j = 2 then 3 else if j = 3 then 1 else 0

/-- **The reconstruction with every hypothesis discharged.** For the event times `t_j = j`, one
event at each of `t_1, t_2, t_3` and the numbers at risk `5, 3, 1`: the pseudo sample
`reconstructedSample` has the published curve at every time; the curve takes the values `4/5`,
`8/15`, `0` at the event times; the inversion formula returns the event count `1` at each event
time; every event count sequence with the same curve and numbers at risk is the constant `1`;
and the censorings of the pseudo sample in `[1, 2)` and `[2, 3)` number `n_j - d_j - n_{j+1}`,
which is `1` in each interval. -/
theorem publishedKaplanMeier_instance :
    (∀ t, sampleKaplanMeier reconstructedSample t =
      publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) reportedAtRisk 3 t) ∧
    publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) reportedAtRisk 3 1 = 4 / 5 ∧
    publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) reportedAtRisk 3 2 = 8 / 15 ∧
    publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) reportedAtRisk 3 3 = 0 ∧
    (∀ j ∈ Icc 1 3, ((1 : ℕ) : ℝ) = reportedAtRisk j *
      (1 - publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) reportedAtRisk 3 j /
        publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) reportedAtRisk 3 ↑(j - 1))) ∧
    (∀ d' : ℕ → ℕ, (∀ j : ℕ, j ≤ 3 →
      publishedKaplanMeier (fun j : ℕ => (j : ℝ)) (fun _ => 1) reportedAtRisk 3 (j : ℝ) =
        publishedKaplanMeier (fun j : ℕ => (j : ℝ)) d' reportedAtRisk 3 (j : ℝ)) →
      ∀ j ∈ Icc 1 3, d' j = 1) ∧
    sampleCensorings reconstructedSample 1 2 = 1 ∧
    sampleCensorings reconstructedSample 2 3 = 1 := by
  have htt : StrictMono (fun j : ℕ => (j : ℝ)) := fun a b h => Nat.cast_lt.2 h
  have hcard : ∀ p : Fin 5 → Prop, [DecidablePred p] →
      (univ.filter p).card = (if p 0 then 1 else 0) + (if p 1 then 1 else 0) +
        (if p 2 then 1 else 0) + (if p 3 then 1 else 0) + (if p 4 then 1 else 0) := fun p _ => by
    rw [card_filter, Fin.sum_univ_five]
  have hlt : ∀ j ∈ Ico 1 3, (fun _ => 1) j < reportedAtRisk j := by
    intro j hj
    simp only [mem_Ico] at hj
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;> decide
  have hnm : 0 < reportedAtRisk 3 := by decide
  have hev : ∀ i, (reconstructedSample i).2 = true →
      ∃ j ∈ Icc 1 3, (reconstructedSample i).1 = ((j : ℕ) : ℝ) := by
    intro i hi
    fin_cases i
    · exact ⟨1, by norm_num, by norm_num [reconstructedSample]⟩
    · simp [reconstructedSample] at hi
    · exact ⟨2, by norm_num, by norm_num [reconstructedSample]⟩
    · simp [reconstructedSample] at hi
    · exact ⟨3, by norm_num, by norm_num [reconstructedSample]⟩
  have hd : ∀ j ∈ Icc 1 3, sampleEvents reconstructedSample ((j : ℕ) : ℝ) = 1 := by
    intro j hj
    simp only [mem_Icc] at hj
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;>
      · unfold sampleEvents; rw [hcard]; norm_num [reconstructedSample]
  have hint : ∀ j ∈ Icc 1 3, (univ.filter fun i => ((j : ℕ) : ℝ) ≤ (reconstructedSample i).1 ∧
      (reconstructedSample i).1 < ((j + 1 : ℕ) : ℝ)).card + reportedAtRisk (j + 1) =
        reportedAtRisk j := by
    intro j hj
    simp only [mem_Icc] at hj
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;>
      · rw [hcard]; norm_num [reconstructedSample, reportedAtRisk]
  have hlast : sampleAtRisk reconstructedSample ((3 + 1 : ℕ) : ℝ) = reportedAtRisk (3 + 1) := by
    unfold sampleAtRisk; rw [hcard]; norm_num [reconstructedSample, reportedAtRisk]
  have hrisk := sampleAtRisk_of_counts reconstructedSample htt hint hlast
  have hcens : ∀ j : ℕ, j ∈ Icc 1 2 →
      (sampleCensorings reconstructedSample (j : ℝ) ((j + 1 : ℕ) : ℝ) : ℤ) =
      reportedAtRisk j - 1 - reportedAtRisk (j + 1) := by
    intro j hj
    have hj' := mem_Icc.1 hj
    refine sampleCensorings_eq reconstructedSample (by push_cast; linarith) (fun i hi h1 h2 => ?_)
      (hrisk j (mem_Icc.2 ⟨hj'.1, by omega⟩))
      (by exact_mod_cast hrisk (j + 1) (mem_Icc.2 ⟨by omega, by omega⟩))
      (hd j (mem_Icc.2 ⟨hj'.1, by omega⟩))
    obtain ⟨k, hk, hik⟩ := hev i hi
    rw [hik] at h1 h2 ⊢
    have h1' : j ≤ k := by exact_mod_cast h1
    have h2' : k < j + 1 := by exact_mod_cast h2
    rw [show k = j by omega]
  refine ⟨fun t => sampleKaplanMeier_reconstruction reconstructedSample htt hev hd hint hlast t,
    ?_, ?_, ?_, (publishedKaplanMeier_inversion htt hnm hlt).2,
    fun d' heq => fun j hj => ((publishedKaplanMeier_counts_unique htt hnm hlt heq) j hj).symm,
    ?_, ?_⟩
  · rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, publishedKaplanMeier_apply htt _ _ (by norm_num)]
    simp [reportedAtRisk]
    norm_num
  · rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, publishedKaplanMeier_apply htt _ _ (by norm_num)]
    simp [prod_Icc_succ_top, reportedAtRisk]
    norm_num
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, publishedKaplanMeier_apply htt _ _ le_rfl]
    simp [prod_Icc_succ_top, reportedAtRisk]
  · have := hcens 1 (by simp)
    norm_num [reportedAtRisk] at this
    exact this
  · have := hcens 2 (by simp)
    norm_num [reportedAtRisk] at this
    exact this

end NetworkMetaRegression

end CausalInference
