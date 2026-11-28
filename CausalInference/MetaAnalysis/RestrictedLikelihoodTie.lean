/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedLikelihoodTieBounds

/-!
# Meta-analysis: the restricted maximum likelihood estimate need not be unique

With equal within study variances (`isMaxOn_restrictedLogLik_const_iff`) and with two studies
(`isMaxOn_restrictedLogLik_fin_two_iff`) the restricted likelihood of the between study variance
has exactly one maximizer on `[0, ∞)`. This file shows that with three studies and unequal
variances it can have **two distinct global maximizers**.

**The family.** Take the variances `v = (1/10, 1/10, 10)` and the scaled estimates
`y_s = s (0, 1/2, 10)`, `s ∈ [0, 1]`. By `restrictedLogLik_eq_zero_sub_cochranQ` and
`cochranQ_smul`,

`F(s, t) = ℓ_R(t; y_s) = -½ log P(t) - (s² / 2) Q(t)`,

with `P(t) = (1/10 + t)² + 2 (1/10 + t)(10 + t)` free of the data and `Q(t)` Cochran's `Q` of
`(0, 1/2, 10)` with the weights `1 / (vᵢ + t)`. Split `[0, ∞)` at `c = 1/5` and let
`L(s) = sup_{[0, c]} F(s, ·)` (`twoPeakTieLeft`) and `R(s) = sup_{[c, ∞)} F(s, ·)`
(`twoPeakTieRight`). Both suprema are attained: on `[0, c]` by compactness, on `[c, ∞)` because
`F(s, t) → -∞` (`exists_isMaxOn_Ici_restrictedLogLik`).

* **Continuity.** `0 ≤ Q(t) ≤ Q(0)` on `[0, ∞)` (`cochranQ_le_of_le`), so
  `|F(s, t) - F(s', t)| ≤ Q(0) |s - s'|` for `s, s' ∈ [0, 1]`, uniformly in `t`, and `L` and `R` are
  Lipschitz on `[0, 1]` (`lipschitzOnWith_sSup_image_of_isMaxOn`).
* **At `s = 0`** the data vanish, `F(0, t) = -½ log P(t)` is strictly decreasing, and
  `L(0) > R(0)`.
* **At `s = 1`** (the two peak instance of `restrictedLogLik_twoPeak`) `F(1, 20) > F(1, t)` on
  `[0, 2]` (`restrictedLogLik_twoPeak_lt_twenty`), so `R(1) > L(1)`.

The intermediate value theorem gives `s* ∈ (0, 1)` with `L(s*) = R(s*)`; a maximizer `t₁` of
`F(s*, ·)` on `[0, c]` and a maximizer `t₂` on `[c, ∞)` are then both maximizers on `[0, ∞)`. They
differ: the restricted score at `c` is affine in `s²` (`restrictedScore_smul`) and negative at
`s = 0` (`-40/23`) and at `s = 1` (`-1805/4761`), hence negative for every `s ∈ [0, 1]`, so `c` is
not a maximizer on `[0, c]` and `t₂ > c ≥ t₁` (`exists_two_isMaxOn_restrictedLogLik_twoPeak`).

The scale `s*` is not explicit: it is obtained from the intermediate value theorem. The data
`y_{s*}` are therefore given by an existence statement; the variances and the direction
`(0, 1/2, 10)` of the data are explicit.

## Main definitions

* `twoPeakTieLeft`, `twoPeakTieRight`.

## Main results

* `lipschitzOnWith_sSup_image_of_isMaxOn`.
* `lipschitzOnWith_twoPeakTieLeft`, `lipschitzOnWith_twoPeakTieRight`,
  `twoPeakTieRight_lt_twoPeakTieLeft_zero`, `twoPeakTieLeft_lt_twoPeakTieRight_one`.
* `exists_two_isMaxOn_restrictedLogLik_twoPeak`, `exists_two_isMaxOn_restrictedLogLik`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Set

/-! ### Suprema of a family of functions -/

/-- The supremum of the values of `f` on `A` is the value at a maximizer. -/
theorem sSup_image_eq_of_isMaxOn {f : ℝ → ℝ} {A : Set ℝ} {t : ℝ} (ht : t ∈ A)
    (hmax : IsMaxOn f A t) : sSup (f '' A) = f t :=
  IsGreatest.csSup_eq ⟨mem_image_of_mem f ht, by rintro _ ⟨u, hu, rfl⟩; exact hmax hu⟩

/-- **Lipschitz suprema**: if `f s` attains its maximum on `A` for every `s ∈ I`, and
`f s t ≤ f s' t + K |s - s'|` for all `s, s' ∈ I` and `t ∈ A`, then `s ↦ sup_A f s` is Lipschitz
with constant `K` on `I`. -/
theorem lipschitzOnWith_sSup_image_of_isMaxOn {f : ℝ → ℝ → ℝ} {A I : Set ℝ} {K : ℝ}
    (hmax : ∀ s ∈ I, ∃ t ∈ A, IsMaxOn (f s) A t)
    (hlip : ∀ s ∈ I, ∀ s' ∈ I, ∀ t ∈ A, f s t ≤ f s' t + K * dist s s') :
    LipschitzOnWith (Real.toNNReal K) (fun s => sSup (f s '' A)) I := by
  refine LipschitzOnWith.of_le_add_mul' K fun s hs s' hs' => ?_
  obtain ⟨t, ht, hmt⟩ := hmax s hs
  obtain ⟨t', ht', hmt'⟩ := hmax s' hs'
  simp only [sSup_image_eq_of_isMaxOn ht hmt, sSup_image_eq_of_isMaxOn ht' hmt']
  have h1 := hlip s hs s' hs' t ht
  have h2 : f s' t ≤ f s' t' := hmt' ht
  linarith

/-! ### The family `y_s = s (0, 1/2, 10)` -/

/-- `F(s, t) = -½ log P(t) - (s² / 2) Q(t)` for `t ≥ 0`. -/
theorem restrictedLogLik_twoPeakVar_smul (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    restrictedLogLik twoPeakVar (s • twoPeakEst) t = -(1 / 2) * Real.log (twoPeakDet t) -
      s ^ 2 / 2 * cochranQ (fun i => twoPeakVar i + t) twoPeakEst := by
  rw [restrictedLogLik_twoPeakVar_eq _ ht, cochranQ_smul]
  ring

/-- **Uniform Lipschitz bound in the scale**: for `s, s' ∈ [0, 1]` and `t ≥ 0`,
`F(s, t) ≤ F(s', t) + Q(0) |s - s'|`. -/
theorem restrictedLogLik_twoPeakVar_smul_le {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    restrictedLogLik twoPeakVar (s • twoPeakEst) t ≤
      restrictedLogLik twoPeakVar (s' • twoPeakEst) t +
        cochranQ (fun i => twoPeakVar i + 0) twoPeakEst * dist s s' := by
  rw [restrictedLogLik_twoPeakVar_smul s ht, restrictedLogLik_twoPeakVar_smul s' ht,
    Real.dist_eq]
  have hQ0 := cochranQ_nonneg (twoPeakVar_add_pos ht) twoPeakEst
  have hQt := cochranQ_le_of_le (twoPeakVar_add_pos le_rfl) ht twoPeakEst
  have h1 : (s' ^ 2 - s ^ 2) / 2 ≤ |s - s'| := by
    rcases abs_cases (s - s') with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [hs.1, hs.2, hs'.1, hs'.2]
  have h2 : (s' ^ 2 - s ^ 2) / 2 * cochranQ (fun i => twoPeakVar i + t) twoPeakEst ≤
      |s - s'| * cochranQ (fun i => twoPeakVar i + 0) twoPeakEst :=
    (mul_le_mul_of_nonneg_right h1 hQ0).trans (mul_le_mul_of_nonneg_left hQt (abs_nonneg _))
  linarith

/-- The supremum `L(s)` of `F(s, ·)` on `[0, 1/5]`. -/
noncomputable def twoPeakTieLeft (s : ℝ) : ℝ :=
  sSup (restrictedLogLik twoPeakVar (s • twoPeakEst) '' Icc 0 (1 / 5))

/-- The supremum `R(s)` of `F(s, ·)` on `[1/5, ∞)`. -/
noncomputable def twoPeakTieRight (s : ℝ) : ℝ :=
  sSup (restrictedLogLik twoPeakVar (s • twoPeakEst) '' Ici (1 / 5))

/-- The variances `(1/10, 1/10, 10)` are positive. -/
theorem twoPeakVar_pos (i : Fin 3) : 0 < twoPeakVar i := by
  simpa using twoPeakVar_add_pos le_rfl i

/-- `F(s, ·)` attains its maximum on `[0, 1/5]`. -/
theorem exists_isMaxOn_twoPeakTieLeft (s : ℝ) :
    ∃ t ∈ Icc (0 : ℝ) (1 / 5), IsMaxOn (restrictedLogLik twoPeakVar (s • twoPeakEst))
      (Icc 0 (1 / 5)) t := by
  have hcont : ContinuousOn (restrictedLogLik twoPeakVar (s • twoPeakEst)) (Icc 0 (1 / 5)) :=
    fun t ht => (hasDerivAt_restrictedLogLik (s • twoPeakEst)
      (twoPeakVar_add_pos ht.1)).continuousAt.continuousWithinAt
  exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (by norm_num)) hcont

/-- `F(s, ·)` attains its maximum on `[1/5, ∞)`. -/
theorem exists_isMaxOn_twoPeakTieRight (s : ℝ) :
    ∃ t ∈ Ici (1 / 5 : ℝ), IsMaxOn (restrictedLogLik twoPeakVar (s • twoPeakEst))
      (Ici (1 / 5)) t := by
  obtain ⟨t, ht, hmax⟩ := exists_isMaxOn_Ici_restrictedLogLik twoPeakVar_pos (by simp)
    (s • twoPeakEst) (a := 1 / 5) (by norm_num)
  exact ⟨t, ht, hmax⟩

/-- **`L` is Lipschitz on `[0, 1]`**, with constant `Q(0)`. -/
theorem lipschitzOnWith_twoPeakTieLeft :
    LipschitzOnWith (Real.toNNReal (cochranQ (fun i => twoPeakVar i + 0) twoPeakEst))
      twoPeakTieLeft (Icc 0 1) :=
  lipschitzOnWith_sSup_image_of_isMaxOn (fun s _ => exists_isMaxOn_twoPeakTieLeft s)
    fun _ hs _ hs' _ ht => restrictedLogLik_twoPeakVar_smul_le hs hs' ht.1

/-- **`R` is Lipschitz on `[0, 1]`**, with constant `Q(0)`. -/
theorem lipschitzOnWith_twoPeakTieRight :
    LipschitzOnWith (Real.toNNReal (cochranQ (fun i => twoPeakVar i + 0) twoPeakEst))
      twoPeakTieRight (Icc 0 1) :=
  lipschitzOnWith_sSup_image_of_isMaxOn (fun s _ => exists_isMaxOn_twoPeakTieRight s)
    fun _ hs _ hs' t ht => restrictedLogLik_twoPeakVar_smul_le hs hs' (le_trans (by norm_num) ht)

/-- `P` is strictly increasing on `[0, ∞)`. -/
theorem twoPeakDet_lt {a t : ℝ} (ha : 0 ≤ a) (hat : a < t) : twoPeakDet a < twoPeakDet t := by
  unfold twoPeakDet; nlinarith

/-- **At `s = 0`**: `R(0) < L(0)`. With zero data `F(0, t) = -½ log P(t)` is strictly
decreasing. -/
theorem twoPeakTieRight_lt_twoPeakTieLeft_zero : twoPeakTieRight 0 < twoPeakTieLeft 0 := by
  obtain ⟨t₁, ht₁, hm₁⟩ := exists_isMaxOn_twoPeakTieLeft 0
  obtain ⟨t₂, ht₂, hm₂⟩ := exists_isMaxOn_twoPeakTieRight 0
  have ht₂' : (0 : ℝ) ≤ t₂ := le_trans (by norm_num) ht₂
  rw [twoPeakTieLeft, twoPeakTieRight, sSup_image_eq_of_isMaxOn ht₁ hm₁,
    sSup_image_eq_of_isMaxOn ht₂ hm₂]
  have h0 : restrictedLogLik twoPeakVar ((0 : ℝ) • twoPeakEst) 0 ≤
      restrictedLogLik twoPeakVar ((0 : ℝ) • twoPeakEst) t₁ := hm₁ ⟨le_rfl, by norm_num⟩
  rw [restrictedLogLik_twoPeakVar_smul 0 le_rfl] at h0
  rw [restrictedLogLik_twoPeakVar_smul 0 ht₂']
  have hlt := Real.log_lt_log (twoPeakDet_pos le_rfl)
    (twoPeakDet_lt le_rfl (lt_of_lt_of_le (by norm_num) ht₂))
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul,
    sub_zero] at h0 ⊢
  linarith

/-- **At `s = 1`**: `L(1) < R(1)`, since `F(1, 20) > F(1, t)` on `[0, 2]`. -/
theorem twoPeakTieLeft_lt_twoPeakTieRight_one : twoPeakTieLeft 1 < twoPeakTieRight 1 := by
  obtain ⟨t₁, ht₁, hm₁⟩ := exists_isMaxOn_twoPeakTieLeft 1
  obtain ⟨t₂, ht₂, hm₂⟩ := exists_isMaxOn_twoPeakTieRight 1
  rw [twoPeakTieLeft, twoPeakTieRight, sSup_image_eq_of_isMaxOn ht₁ hm₁,
    sSup_image_eq_of_isMaxOn ht₂ hm₂]
  have h20 : restrictedLogLik twoPeakVar ((1 : ℝ) • twoPeakEst) 20 ≤
      restrictedLogLik twoPeakVar ((1 : ℝ) • twoPeakEst) t₂ := hm₂ (by norm_num)
  have hlt := restrictedLogLik_twoPeak_lt_twenty ht₁.1 (Or.inl (ht₁.2.trans (by norm_num)))
  rw [one_smul] at h20 ⊢
  linarith

/-- The restricted score at `1/5` of the data `(0, 1/2, 10)` and of zero data. -/
theorem restrictedScore_twoPeak_fifth :
    restrictedScore twoPeakVar twoPeakEst (1 / 5) = -1805 / 4761 ∧
      restrictedScore twoPeakVar 0 (1 / 5) = -40 / 23 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [restrictedScore, cochranQSlope, ivwEstimate, PopulationAdjustment.weightedMean,
      ivWeight, Fin.sum_univ_three, twoPeakVar, twoPeakEst, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Pi.zero_apply]
    norm_num

/-- **Two distinct global maximizers**: for the variances `v = (1/10, 1/10, 10)` there is a
scale `s ∈ (0, 1)` such that the restricted log likelihood of the data `s (0, 1/2, 10)` has a
maximizer `t₁ ∈ [0, 1/5]` and a maximizer `t₂ > 1/5` on `[0, ∞)`. The scale is not explicit: it
comes from the intermediate value theorem applied to `L - R`. -/
theorem exists_two_isMaxOn_restrictedLogLik_twoPeak :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 / 5 ∧ 1 / 5 < t₂ ∧
      IsMaxOn (restrictedLogLik twoPeakVar (s • twoPeakEst)) (Ici 0) t₁ ∧
      IsMaxOn (restrictedLogLik twoPeakVar (s • twoPeakEst)) (Ici 0) t₂ := by
  have hD : ContinuousOn (fun s => twoPeakTieLeft s - twoPeakTieRight s) (Icc 0 1) :=
    lipschitzOnWith_twoPeakTieLeft.continuousOn.sub lipschitzOnWith_twoPeakTieRight.continuousOn
  have h0 := twoPeakTieRight_lt_twoPeakTieLeft_zero
  have h1 := twoPeakTieLeft_lt_twoPeakTieRight_one
  obtain ⟨s, hs, hsD⟩ := intermediate_value_Icc' zero_le_one hD
    (show (0 : ℝ) ∈ Icc (twoPeakTieLeft 1 - twoPeakTieRight 1)
      (twoPeakTieLeft 0 - twoPeakTieRight 0) from ⟨by linarith, by linarith⟩)
  simp only at hsD
  have hs0 : s ≠ 0 := by rintro rfl; linarith
  have hs1 : s ≠ 1 := by rintro rfl; linarith
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩
  set F := restrictedLogLik twoPeakVar (s • twoPeakEst) with hF
  obtain ⟨t₁, ht₁, hm₁⟩ := exists_isMaxOn_twoPeakTieLeft s
  obtain ⟨t₂, ht₂, hm₂⟩ := exists_isMaxOn_twoPeakTieRight s
  have hLR : F t₁ = F t₂ := by
    have := hsD
    rw [twoPeakTieLeft, twoPeakTieRight, sSup_image_eq_of_isMaxOn ht₁ hm₁,
      sSup_image_eq_of_isMaxOn ht₂ hm₂] at this
    linarith
  have hglob : ∀ u ∈ Ici (0 : ℝ), F u ≤ F t₁ := by
    intro u hu
    rcases le_or_gt u (1 / 5) with h | h
    · exact hm₁ ⟨hu, h⟩
    · rw [hLR]; exact hm₂ (mem_Ici.2 h.le)
  have hm₁' : IsMaxOn F (Ici 0) t₁ := fun u hu => hglob u hu
  have hm₂' : IsMaxOn F (Ici 0) t₂ := fun u hu => by rw [← hLR]; exact hglob u hu
  -- the restricted score at `1/5` is negative, so `1/5` is not a maximizer
  obtain ⟨sc1, sc0⟩ := restrictedScore_twoPeak_fifth
  have hscore : restrictedScore twoPeakVar (s • twoPeakEst) (1 / 5) < 0 := by
    rw [restrictedScore_smul, sc1, sc0]
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    have hs2' : s ^ 2 ≤ 1 := by nlinarith [hsI.1, hsI.2]
    nlinarith
  have hnot : ¬ IsMaxOn F (Icc 0 (1 / 5)) (1 / 5) :=
    not_isMaxOn_Icc_right_of_hasDerivAt
      (hasDerivAt_restrictedLogLik (s • twoPeakEst) (twoPeakVar_add_pos (by norm_num)))
      hscore (by norm_num)
  have ht₂c : 1 / 5 < t₂ := by
    refine lt_of_le_of_ne ht₂ fun h => hnot ?_
    rw [h]
    exact hm₂'.of_subset Icc_subset_Ici_self
  exact ⟨s, hsI, t₁, t₂, ht₁.1, ht₁.2, ht₂c, hm₁', hm₂'⟩

/-- **The restricted maximum likelihood estimate need not be unique**: there are positive within
study variances and estimates of three studies for which the restricted log likelihood has two
distinct maximizers on `[0, ∞)`. The data are `s (0, 1/2, 10)` for a nonexplicit `s ∈ (0, 1)`
(`exists_two_isMaxOn_restrictedLogLik_twoPeak`). -/
theorem exists_two_isMaxOn_restrictedLogLik :
    ∃ v y : Fin 3 → ℝ, (∀ i, 0 < v i) ∧ ∃ t₁ t₂ : ℝ, t₁ ∈ Ici 0 ∧ t₂ ∈ Ici 0 ∧ t₁ ≠ t₂ ∧
      IsMaxOn (restrictedLogLik v y) (Ici 0) t₁ ∧ IsMaxOn (restrictedLogLik v y) (Ici 0) t₂ := by
  obtain ⟨s, -, t₁, t₂, h0, h1, h2, hm₁, hm₂⟩ := exists_two_isMaxOn_restrictedLogLik_twoPeak
  exact ⟨twoPeakVar, s • twoPeakEst, twoPeakVar_pos, t₁, t₂, h0, le_trans h0 (h1.trans h2.le),
    (lt_of_le_of_lt h1 h2).ne, hm₁, hm₂⟩

end MetaAnalysis

end CausalInference
