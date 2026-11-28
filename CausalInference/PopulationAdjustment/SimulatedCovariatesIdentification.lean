/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.SimulatedCovariatesBinary
public import CausalInference.PopulationAdjustment.StandardizationConsistencyMarginal

/-!
# Identification by standardization over simulated covariates

The simulated comparison standardizes the outcome surface of the trial arm over the simulated
covariate law `nortaLaw R μ` instead of the target covariate law `Q_X`. The construction
reproduces the target margins exactly (`map_eval_nortaLaw`) and, for a pair of coordinates, a
Gaussian copula pair law (`map_pair_nortaLaw`). So the standardized mean under the simulated
law equals the target arm mean whenever the conditional mean surface depends on the covariate
law only through what the construction reproduces:

* an **additive surface** `c + ∑_j f_j(x_j)` needs only the margins
  (`integral_nortaLaw_eq_armMean_of_additive`): any correlation matrix `R` works;
* a surface with **one interacting pair** `c + ∑_j f_j(x_j) + g(x_a, x_b)` needs, in addition,
  that the target pair `(X_a, X_b)` has the Gaussian copula with parameter `R_{ab}`
  (`integral_nortaLaw_eq_armMean_of_pair`).

**A model where it fails.** For two binary covariates any surface with a nonzero interaction
contrast `I(f)` has a simulated standardized mean different from the target mean when the
product moment is not reproduced: for the target `dependentCoinLaw` (fair coins with Pearson
correlation `1/2`) simulated with Gaussian correlation `1/2`, the difference is
`I(f) (1/3 - 3/8) = -I(f)/24` (`integral_nortaLaw_half_sub_dependentCoin`). The logistic
surface `σ(x₀ + x₁)` is such a surface (`integral_logistic_nortaLaw_half_ne`).

## Main results

* `integral_additive_eq_of_margins`, `integral_pair_eq_of_laws`: equality of integrals under
  two laws with equal margins (equal pair laws).
* `integral_nortaLaw_eq_armMean_of_additive`, `integral_nortaLaw_eq_armMean_of_pair`.
* `integral_nortaLaw_half_sub_dependentCoin`, `integral_logistic_nortaLaw_half_ne`.

## References

* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Set BiasAnalysis.Distributions IndirectComparison
  Transport

variable {ι : Type*} [Fintype ι]

/-! ### Integrals that depend on margins and pair laws only -/

section Laws

variable {ν₁ ν₂ : Measure (ι → ℝ)} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]

omit [Fintype ι] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] in
/-- A function of one coordinate has the same integral under two laws with the same margin. -/
theorem integral_eval_eq_of_map_eq {j : ι} (h : ν₁.map (fun x => x j) = ν₂.map (fun x => x j))
    {f : ℝ → ℝ} (hi : Integrable f (ν₂.map fun x => x j)) :
    Integrable (fun x => f (x j)) ν₁ ∧ ∫ x, f (x j) ∂ν₁ = ∫ x, f (x j) ∂ν₂ := by
  have hf₁ : AEStronglyMeasurable f (ν₁.map fun x => x j) := h ▸ hi.aestronglyMeasurable
  refine ⟨(integrable_map_measure hf₁ (measurable_pi_apply j).aemeasurable).1 (h ▸ hi), ?_⟩
  rw [← integral_map (measurable_pi_apply j).aemeasurable hf₁, h,
    integral_map (measurable_pi_apply j).aemeasurable hi.aestronglyMeasurable]

/-- **An additive surface has the same integral under two laws with the same margins.** If
`ν₁` and `ν₂` have equal coordinate margins and each `f_j` is integrable against the `j`th
margin, then `∫ (c + ∑_j f_j(x_j)) dν₁ = ∫ (c + ∑_j f_j(x_j)) dν₂`, and the surface is
integrable under both laws. -/
theorem integral_additive_eq_of_margins
    (hmarg : ∀ j, ν₁.map (fun x => x j) = ν₂.map (fun x => x j)) (c : ℝ) {f : ι → ℝ → ℝ}
    (hf : ∀ j, Integrable (f j) (ν₂.map fun x => x j)) :
    Integrable (fun x => c + ∑ j, f j (x j)) ν₁ ∧ Integrable (fun x => c + ∑ j, f j (x j)) ν₂ ∧
      ∫ x, (c + ∑ j, f j (x j)) ∂ν₁ = ∫ x, (c + ∑ j, f j (x j)) ∂ν₂ := by
  have h₂ : ∀ j, Integrable (fun x => f j (x j)) ν₂ := fun j =>
    (integrable_map_measure (hf j).aestronglyMeasurable (measurable_pi_apply j).aemeasurable).1
      (hf j)
  have hE : ∀ j, Integrable (fun x => f j (x j)) ν₁ ∧
      ∫ x, f j (x j) ∂ν₁ = ∫ x, f j (x j) ∂ν₂ := fun j =>
    integral_eval_eq_of_map_eq (hmarg j) (hf j)
  have hs₁ : Integrable (fun x => ∑ j, f j (x j)) ν₁ := integrable_finsetSum _ fun j _ => (hE j).1
  have hs₂ : Integrable (fun x => ∑ j, f j (x j)) ν₂ := integrable_finsetSum _ fun j _ => h₂ j
  refine ⟨(integrable_const c).add hs₁, (integrable_const c).add hs₂, ?_⟩
  rw [integral_add (integrable_const c) hs₁, integral_add (integrable_const c) hs₂,
    integral_finsetSum _ fun j _ => (hE j).1, integral_finsetSum _ fun j _ => h₂ j]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => (hE j).2

omit [Fintype ι] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] in
/-- Equal pair laws give equal margins of both coordinates of the pair. -/
theorem map_eval_eq_of_map_pair_eq {a b : ι}
    (hpair : ν₁.map (fun x => (x a, x b)) = ν₂.map (fun x => (x a, x b))) :
    ν₁.map (fun x => x a) = ν₂.map (fun x => x a) ∧
      ν₁.map (fun x => x b) = ν₂.map (fun x => x b) := by
  have hm : Measurable fun x : ι → ℝ => (x a, x b) := by fun_prop
  have h1 := congrArg (Measure.map Prod.fst) hpair
  have h2 := congrArg (Measure.map Prod.snd) hpair
  rw [Measure.map_map measurable_fst hm, Measure.map_map measurable_fst hm] at h1
  rw [Measure.map_map measurable_snd hm, Measure.map_map measurable_snd hm] at h2
  exact ⟨h1, h2⟩

omit [Fintype ι] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] in
/-- Equal margins outside a pair and equal pair laws give equal margins everywhere. -/
theorem map_eval_eq_of_margins_pair {a b : ι}
    (hmarg : ∀ j, j ≠ a → j ≠ b → ν₁.map (fun x => x j) = ν₂.map (fun x => x j))
    (hpair : ν₁.map (fun x => (x a, x b)) = ν₂.map (fun x => (x a, x b))) (j : ι) :
    ν₁.map (fun x => x j) = ν₂.map (fun x => x j) := by
  by_cases ha : j = a
  · subst ha; exact (map_eval_eq_of_map_pair_eq hpair).1
  by_cases hb : j = b
  · subst hb; exact (map_eval_eq_of_map_pair_eq hpair).2
  exact hmarg j ha hb

/-- **A surface with one interacting pair has the same integral under two laws with the same
pair law and the same margins outside the pair.** -/
theorem integral_pair_eq_of_laws {a b : ι}
    (hmarg : ∀ j, j ≠ a → j ≠ b → ν₁.map (fun x => x j) = ν₂.map (fun x => x j))
    (hpair : ν₁.map (fun x => (x a, x b)) = ν₂.map (fun x => (x a, x b))) (c : ℝ)
    {f : ι → ℝ → ℝ} (hf : ∀ j, Integrable (f j) (ν₂.map fun x => x j)) {g : ℝ × ℝ → ℝ}
    (hg : Integrable g (ν₂.map fun x => (x a, x b))) :
    ∫ x, (c + ∑ j, f j (x j) + g (x a, x b)) ∂ν₁ =
      ∫ x, (c + ∑ j, f j (x j) + g (x a, x b)) ∂ν₂ := by
  obtain ⟨h₁, h₂, he⟩ :=
    integral_additive_eq_of_margins (map_eval_eq_of_margins_pair hmarg hpair) c hf
  have hm : Measurable fun x : ι → ℝ => (x a, x b) := by fun_prop
  have hg₁ : Integrable g (ν₁.map fun x => (x a, x b)) := hpair ▸ hg
  have hgi₁ : Integrable (fun x => g (x a, x b)) ν₁ :=
    (integrable_map_measure hg₁.aestronglyMeasurable hm.aemeasurable).1 hg₁
  have hgi₂ : Integrable (fun x => g (x a, x b)) ν₂ :=
    (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).1 hg
  rw [integral_add h₁ hgi₁, integral_add h₂ hgi₂, he]
  congr 1
  rw [← integral_map (f := g) hm.aemeasurable hg₁.aestronglyMeasurable, hpair,
    integral_map hm.aemeasurable hg.aestronglyMeasurable]

end Laws

/-! ### Identification of the target arm mean -/

section Identification

variable [DecidableEq ι] {Ω₁ Ω₂ κ' : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {T : Trial Ω₁ (ι → ℝ) Bool} {Q : Population Ω₂ (ι → ℝ) κ'} {R : Matrix ι ι ℝ}
  {μ : ι → Measure ℝ}

/-- **The simulated standardized mean of an additive surface depends on the margins only**:
`∫ (c + ∑_j f_j(x_j)) d(nortaLaw R μ) = c + ∑_j ∫ f_j dμ_j`, for every correlation matrix `R`. -/
theorem integral_nortaLaw_additive (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    [∀ j, IsProbabilityMeasure (μ j)] (c : ℝ) {f : ι → ℝ → ℝ}
    (hf : ∀ j, Integrable (f j) (μ j)) :
    ∫ x, (c + ∑ j, f j (x j)) ∂nortaLaw R μ = c + ∑ j, ∫ t, f j t ∂μ j := by
  have hi : ∀ j, Integrable (fun x : ι → ℝ => f j (x j)) (nortaLaw R μ) := fun j => by
    have h := hf j
    rw [← map_eval_nortaLaw (μ := μ) hR hdiag j] at h
    exact (integrable_map_measure h.aestronglyMeasurable
      (measurable_pi_apply j).aemeasurable).1 h
  rw [integral_add (integrable_const c) (integrable_finsetSum _ fun j _ => hi j),
    integral_finsetSum _ fun j _ => hi j]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  exact Finset.sum_congr rfl fun j _ =>
    integral_nortaLaw_eval hR hdiag j (hf j).aestronglyMeasurable

/-- **Identification by simulated covariates, additive surface.** Let the conditional mean of
`Y(t)` in the trial be additive, `m(x) = c + ∑_j f_j(x_j)`, and transported to treatment `s` of
the target (absolute constancy) with overlap, and let the simulation use the target margins
`μ_j` and any correlation matrix `R`. Then the simulated standardized mean `∫ m d(nortaLaw R μ)`
is the target mean `E_Q[Y(s)]`: the simulated law has the target margins, and an additive
surface integrates through the margins only. -/
theorem integral_nortaLaw_eq_armMean_of_additive [IsProbabilityMeasure Q.μ]
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) [∀ j, IsProbabilityMeasure (μ j)]
    (hmarg : ∀ j, Q.covLaw.map (fun x => x j) = μ j) (hX₁ : Measurable T.X)
    (hX₂ : Measurable Q.X) {t : Bool} {s : κ'} (hYQ : Integrable (Q.Y s) Q.μ) {m : (ι → ℝ) → ℝ}
    (hm : T.IsCondMean t m) (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s))
    (hov : Q.covLaw ≪ T.covLaw) {c : ℝ} {f : ι → ℝ → ℝ} (hadd : ∀ x, m x = c + ∑ j, f j (x j))
    (hf : ∀ j, Integrable (f j) (μ j)) :
    ∫ x, m x ∂nortaLaw R μ = Q.armMean s := by
  have : IsProbabilityMeasure Q.covLaw :=
    (Measure.isProbabilityMeasure_map_iff hX₂.aemeasurable).2 inferInstance
  obtain ⟨-, hQ⟩ := integral_covLaw_eq_armMean_of_trial hX₁ hX₂ hYQ hm hsi hov
  have hmm : ∀ j, (nortaLaw R μ).map (fun x => x j) = Q.covLaw.map (fun x => x j) := fun j => by
    rw [map_eval_nortaLaw hR hdiag j, hmarg j]
  obtain ⟨-, -, he⟩ := integral_additive_eq_of_margins hmm c (f := f) fun j => by
    rw [hmarg j]; exact hf j
  simp_rw [hadd]
  rw [he, ← hQ]
  simp_rw [hadd]

/-- **Identification by simulated covariates, one interacting pair.** As in
`integral_nortaLaw_eq_armMean_of_additive`, for a conditional mean surface
`m(x) = c + ∑_j f_j(x_j) + g(x_a, x_b)`: if the target pair `(X_a, X_b)` has the law of
`(Q_a(Φ(Z₀)), Q_b(Φ(Z₁)))` with `Z` standard bivariate normal with correlation `R_{ab}` (the
target pair has margins `μ_a, μ_b` and the Gaussian copula with that parameter) and the other
target margins are `μ_j`, the simulated standardized mean is the target mean. -/
theorem integral_nortaLaw_eq_armMean_of_pair [IsProbabilityMeasure Q.μ]
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) [∀ j, IsProbabilityMeasure (μ j)] {a b : ι}
    (hmarg : ∀ j, j ≠ a → j ≠ b → Q.covLaw.map (fun x => x j) = μ j)
    (hpair : Q.covLaw.map (fun x => (x a, x b)) =
      (bivariateNormal (R a b)).map (fun z => (quantile (μ a) (cdf (gaussianReal 0 1) (z 0)),
        quantile (μ b) (cdf (gaussianReal 0 1) (z 1)))))
    (hX₁ : Measurable T.X) (hX₂ : Measurable Q.X) {t : Bool} {s : κ'}
    (hYQ : Integrable (Q.Y s) Q.μ) {m : (ι → ℝ) → ℝ} (hm : T.IsCondMean t m)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    {c : ℝ} {f : ι → ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (hform : ∀ x, m x = c + ∑ j, f j (x j) + g (x a, x b)) (hf : ∀ j, Integrable (f j) (μ j))
    (hg : Integrable g (Q.covLaw.map fun x => (x a, x b))) :
    ∫ x, m x ∂nortaLaw R μ = Q.armMean s := by
  have : IsProbabilityMeasure Q.covLaw :=
    (Measure.isProbabilityMeasure_map_iff hX₂.aemeasurable).2 inferInstance
  obtain ⟨-, hQ⟩ := integral_covLaw_eq_armMean_of_trial hX₁ hX₂ hYQ hm hsi hov
  have hmm : ∀ j, j ≠ a → j ≠ b →
      (nortaLaw R μ).map (fun x => x j) = Q.covLaw.map (fun x => x j) := fun j ha hb => by
    rw [map_eval_nortaLaw hR hdiag j, hmarg j ha hb]
  have hpp : (nortaLaw R μ).map (fun x => (x a, x b)) = Q.covLaw.map (fun x => (x a, x b)) := by
    rw [map_pair_nortaLaw hR hdiag, hpair]
  have hQm : ∀ j, Q.covLaw.map (fun x => x j) = μ j := fun j => by
    rw [← map_eval_eq_of_margins_pair hmm hpp j, map_eval_nortaLaw hR hdiag j]
  have he := integral_pair_eq_of_laws hmm hpp c (f := f) (fun j => by rw [hQm j]; exact hf j) hg
  simp_rw [hform]
  rw [he, ← hQ]
  simp_rw [hform]

end Identification

/-! ### Binary covariates with an interaction: the simulated mean is not the target mean -/

/-- **The simulated standardized mean misses the target mean by `-I(f)/24`.** For every surface
`f` on two binary covariates, the target `dependentCoinLaw` (fair coins with Pearson correlation
`1/2`) and its simulation with fair coin margins and Gaussian correlation `1/2` give
`∫ f d(simulated) - ∫ f d(target) = I(f)(1/3 - 3/8) = -I(f)/24`, with `I(f)` the interaction
contrast. The margins agree; only the product moment differs. -/
theorem integral_nortaLaw_half_sub_dependentCoin (f : (Fin 2 → ℝ) → ℝ) :
    ∫ x, f x ∂nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin) - ∫ x, f x ∂dependentCoinLaw =
      -binaryInteraction f / 24 := by
  have hR := corrMatrix_posSemidef (ρ := 1 / 2) (by norm_num)
  obtain ⟨-, h₁⟩ := integral_binary_expand
    (Filter.eventually_and.2 ⟨ae_nortaLaw_fairCoin_binary (corrMatrix (1 / 2)) 0,
      ae_nortaLaw_fairCoin_binary (corrMatrix (1 / 2)) 1⟩) f
  obtain ⟨-, h₂⟩ := integral_binary_expand ae_dependentCoinLaw_binary f
  rw [h₁, h₂, integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _),
    integral_eval_nortaLaw_fairCoin hR (corrMatrix_diag _), integral_mul_nortaLaw_half,
    integral_eval_dependentCoinLaw, integral_eval_dependentCoinLaw, integral_mul_dependentCoinLaw]
  ring

/-- **A logistic surface with an interaction is not identified by the simulation.** For the
surface `σ(x₀ + x₁)` the simulated standardized mean differs from the target mean, although the
simulated law has the target margins and the Gaussian correlation equals the target Pearson
correlation `1/2`. -/
theorem integral_logistic_nortaLaw_half_ne :
    ∫ x, Real.sigmoid (x 0 + x 1) ∂nortaLaw (corrMatrix (1 / 2)) (fun _ => fairCoin) ≠
      ∫ x, Real.sigmoid (x 0 + x 1) ∂dependentCoinLaw := by
  intro h
  have := integral_nortaLaw_half_sub_dependentCoin fun x => Real.sigmoid (x 0 + x 1)
  rw [h, sub_self] at this
  exact binaryInteraction_logistic_ne_zero (by linarith)

end PopulationAdjustment

end CausalInference
