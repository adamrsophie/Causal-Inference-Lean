/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Distance.Basic
public import CausalInference.IndirectComparison.SmallestNetwork
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The Wasserstein distance and the transport bias of a Lipschitz outcome surface

The **Wasserstein distance of order one** between two probability laws `P` and `Q` on a metric
space is the least expected distance `∫ ρ(x, y) dγ(x, y)` over the couplings `γ` of `P` and
`Q`, the laws on the product with marginals `P` and `Q`. The cost is integrated in `ℝ≥0∞`, so
the distance is defined for all laws; it is finite when both laws have a finite first moment.

If the common regression `g` of the outcome on the covariates is `L`-Lipschitz, the transport
bias is at most `L W₁(P₁, P₂)`: for every coupling, the bias is `E_γ[g(X) - g(Y)]`. Unlike the
distances between covariate summaries, `W₁` depends on the whole covariate laws: the distance
between the means is at most `W₁`, and two laws with equal means can be at positive
Wasserstein distance.

## Main definitions

* `couplings P Q`: the couplings of `P` and `Q`.
* `wasserstein1 P Q`: the Wasserstein distance of order one, in `ℝ≥0∞`.

## Main results

* `wasserstein1_ne_top`: finiteness under finite first moments.
* `eNorm_integral_sub_le_wasserstein1`, `abs_integral_sub_le_wasserstein1`: the Lipschitz
  bound for two laws.
* `abs_transportBias_le_wasserstein1`: the Lipschitz bound on the transport bias.
* `norm_integral_sub_le_wasserstein1`, `chebyshev_covMean_le_wasserstein1`,
  `euclidean_mean_le_wasserstein1`: the gap of the means is at most `W₁`.
* `wasserstein1_spreadLaw_dirac`, `exists_eq_mean_wasserstein1_pos`: two laws with equal means
  at Wasserstein distance `1`.

## References

* L. V. Kantorovich and G. S. Rubinstein, *On a space of completely additive functions*,
  Vestnik Leningrad University 13 (1958).
* C. Villani, *Optimal Transport: Old and New*, Springer (2009).
-/

@[expose] public section

namespace CausalInference

namespace Transport

namespace Distance

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section Couplings

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **couplings** of two laws `P` and `Q`: the laws on `𝒳 × 𝒳` with marginals `P` and
`Q`. -/
def couplings (P Q : Measure 𝒳) : Set (Measure (𝒳 × 𝒳)) :=
  {γ | γ.map Prod.fst = P ∧ γ.map Prod.snd = Q}

/-- The **Wasserstein distance of order one** `W₁(P, Q) = inf_γ ∫ ρ(x, y) dγ(x, y)`, the
infimum over the couplings `γ` of `P` and `Q`, with the cost integrated in `ℝ≥0∞`
(Kantorovich and Rubinstein 1958; Villani 2009). -/
noncomputable def wasserstein1 [PseudoEMetricSpace 𝒳] (P Q : Measure 𝒳) : ℝ≥0∞ :=
  ⨅ γ ∈ couplings P Q, ∫⁻ z, edist z.1 z.2 ∂γ

/-- The product law is a coupling of two probability laws. -/
theorem prod_mem_couplings (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : P.prod Q ∈ couplings P Q := by
  refine ⟨?_, ?_⟩ <;> simp

/-- For a coupling `γ` of `(P, Q)`, `E_P f = E_γ f(X)`, and `f(X)` is `γ`-integrable. -/
theorem integral_eq_of_mem_couplings_fst {P Q : Measure 𝒳} {γ : Measure (𝒳 × 𝒳)}
    (hγ : γ ∈ couplings P Q) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : 𝒳 → E}
    (hfm : AEStronglyMeasurable f (γ.map Prod.fst)) (hf : Integrable f P) :
    ∫ x, f x ∂P = ∫ z, f z.1 ∂γ ∧ Integrable (fun z : 𝒳 × 𝒳 ↦ f z.1) γ := by
  rw [← hγ.1] at hf ⊢
  exact ⟨integral_map measurable_fst.aemeasurable hfm,
    (integrable_map_measure hfm measurable_fst.aemeasurable).1 hf⟩

/-- For a coupling `γ` of `(P, Q)`, `E_Q f = E_γ f(Y)`, and `f(Y)` is `γ`-integrable. -/
theorem integral_eq_of_mem_couplings_snd {P Q : Measure 𝒳} {γ : Measure (𝒳 × 𝒳)}
    (hγ : γ ∈ couplings P Q) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : 𝒳 → E}
    (hfm : AEStronglyMeasurable f (γ.map Prod.snd)) (hf : Integrable f Q) :
    ∫ x, f x ∂Q = ∫ z, f z.2 ∂γ ∧ Integrable (fun z : 𝒳 × 𝒳 ↦ f z.2) γ := by
  rw [← hγ.2] at hf ⊢
  exact ⟨integral_map measurable_snd.aemeasurable hfm,
    (integrable_map_measure hfm measurable_snd.aemeasurable).1 hf⟩

variable [PseudoMetricSpace 𝒳] [OpensMeasurableSpace 𝒳]

/-- **Finite first moments make the Wasserstein distance finite**: the product coupling has
cost at most `E_P ρ(X, x₀) + E_Q ρ(x₀, Y)`. -/
theorem wasserstein1_ne_top (P Q : Measure 𝒳) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (x₀ : 𝒳) (hP : Integrable (fun x ↦ dist x x₀) P) (hQ : Integrable (fun x ↦ dist x x₀) Q) :
    wasserstein1 P Q ≠ ⊤ := by
  have hfin : ∀ (R : Measure 𝒳), Integrable (fun x ↦ dist x x₀) R →
      ∫⁻ x, edist x x₀ ∂R < ⊤ := fun R h ↦ by
    have := h.2
    rw [HasFiniteIntegral] at this
    refine lt_of_eq_of_lt (lintegral_congr fun x ↦ ?_) this
    rw [edist_dist, Real.eNorm_eq_ofReal dist_nonneg]
  have hm : Measurable fun x : 𝒳 ↦ edist x x₀ := (continuous_id.edist continuous_const).measurable
  refine ne_top_of_le_ne_top ?_ (iInf₂_le _ (prod_mem_couplings P Q))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun z : 𝒳 × 𝒳 ↦ edist_triangle z.1 x₀ z.2)
  rw [lintegral_add_left (f := fun z : 𝒳 × 𝒳 ↦ edist z.1 x₀) (hm.comp measurable_fst)]
  have e1 : ∫⁻ z : 𝒳 × 𝒳, edist z.1 x₀ ∂P.prod Q = ∫⁻ x, edist x x₀ ∂P := by
    rw [← lintegral_map hm measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have e2 : ∫⁻ z : 𝒳 × 𝒳, edist x₀ z.2 ∂P.prod Q = ∫⁻ x, edist x x₀ ∂Q := by
    simp_rw [edist_comm x₀]
    rw [← lintegral_map hm measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  rw [e1, e2]
  exact ENNReal.add_ne_top.2 ⟨(hfin P hP).ne, (hfin Q hQ).ne⟩

/-- A Lipschitz function is integrable under a probability law with a finite first moment. -/
theorem integrable_of_lipschitzWith {P : Measure 𝒳} [IsProbabilityMeasure P]
    {x₀ : 𝒳} (hP : Integrable (fun x ↦ dist x x₀) P) {g : 𝒳 → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) : Integrable g P := by
  refine Integrable.mono' ((integrable_const |g x₀|).add (hP.const_mul L))
    hg.continuous.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
  have hd := hg.dist_le_mul x x₀
  rw [Real.dist_eq] at hd
  change |g x| ≤ |g x₀| + L * dist x x₀
  have := abs_add_le (g x - g x₀) (g x₀)
  rw [sub_add_cancel] at this
  linarith

/-- **The Lipschitz bound, extended real form.** For an `L`-Lipschitz `g` and probability laws
with finite first moments, `‖∫ g dP - ∫ g dQ‖ₑ ≤ L W₁(P, Q)`: for every coupling `γ`,
`∫ g dP - ∫ g dQ = E_γ[g(X) - g(Y)]` and `|g(X) - g(Y)| ≤ L ρ(X, Y)`. -/
theorem eNorm_integral_sub_le_wasserstein1 (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (x₀ : 𝒳) (hP : Integrable (fun x ↦ dist x x₀) P)
    (hQ : Integrable (fun x ↦ dist x x₀) Q) {g : 𝒳 → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) :
    ‖∫ x, g x ∂P - ∫ x, g x ∂Q‖ₑ ≤ L * wasserstein1 P Q := by
  have hgm : Measurable g := hg.continuous.measurable
  have key : ∀ γ ∈ couplings P Q,
      ‖∫ x, g x ∂P - ∫ x, g x ∂Q‖ₑ ≤ L * ∫⁻ z, edist z.1 z.2 ∂γ := fun γ hγ ↦ by
    obtain ⟨e1, i1⟩ := integral_eq_of_mem_couplings_fst hγ hgm.aestronglyMeasurable
      (integrable_of_lipschitzWith hP hg)
    obtain ⟨e2, i2⟩ := integral_eq_of_mem_couplings_snd hγ hgm.aestronglyMeasurable
      (integrable_of_lipschitzWith hQ hg)
    rw [e1, e2, ← integral_sub i1 i2]
    calc ‖∫ z, (g z.1 - g z.2) ∂γ‖ₑ ≤ ∫⁻ z, ‖g z.1 - g z.2‖ₑ ∂γ :=
          eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ z, L * edist z.1 z.2 ∂γ := lintegral_mono fun z ↦ by
          rw [← eDist_eq_eNorm_sub]; exact hg z.1 z.2
      _ = L * ∫⁻ z, edist z.1 z.2 ∂γ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
  by_cases hL : (L : ℝ≥0∞) = 0
  · have := key _ (prod_mem_couplings P Q)
    rw [hL, zero_mul] at this ⊢
    exact this
  · have hdiv : ‖∫ x, g x ∂P - ∫ x, g x ∂Q‖ₑ / L ≤ wasserstein1 P Q :=
      le_iInf₂ fun γ hγ ↦ ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact key γ hγ)
    calc ‖∫ x, g x ∂P - ∫ x, g x ∂Q‖ₑ = ‖∫ x, g x ∂P - ∫ x, g x ∂Q‖ₑ / L * L :=
          (ENNReal.div_mul_cancel hL ENNReal.coe_ne_top).symm
      _ ≤ wasserstein1 P Q * L := by gcongr
      _ = L * wasserstein1 P Q := mul_comm _ _

/-- **The Lipschitz bound for two laws.** For an `L`-Lipschitz `g` and probability laws with
finite first moments (so that `W₁` is finite), `|∫ g dP - ∫ g dQ| ≤ L W₁(P, Q)`. -/
theorem abs_integral_sub_le_wasserstein1 (P Q : Measure 𝒳) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (x₀ : 𝒳) (hP : Integrable (fun x ↦ dist x x₀) P)
    (hQ : Integrable (fun x ↦ dist x x₀) Q) {g : 𝒳 → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) :
    |∫ x, g x ∂P - ∫ x, g x ∂Q| ≤ L * (wasserstein1 P Q).toReal := by
  have h := eNorm_integral_sub_le_wasserstein1 P Q x₀ hP hQ hg
  have hW := wasserstein1_ne_top P Q x₀ hP hQ
  rw [Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hW), ENNReal.toReal_mul, ENNReal.coe_toReal] at h
  exact h

/-- **The Lipschitz bound on the transport bias.** If an `L`-Lipschitz `g` is a common
regression of integrable outcomes on the covariates and the covariate laws `Pᵢ = μᵢ ∘ Xᵢ⁻¹`
have finite first moments, then `|E₁[Y₁] - E₂[Y₂]| ≤ L W₁(P₁, P₂)`. -/
theorem abs_transportBias_le_wasserstein1 {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁}
    {mΩ₂ : MeasurableSpace Ω₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳} {Y₁ : Ω₁ → ℝ} {Y₂ : Ω₂ → ℝ}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hY₁ : Integrable Y₁ μ₁)
    (hY₂ : Integrable Y₂ μ₂) (x₀ : 𝒳) (h₁ : Integrable (fun x ↦ dist x x₀) (μ₁.map X₁))
    (h₂ : Integrable (fun x ↦ dist x x₀) (μ₂.map X₂)) {g : 𝒳 → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hcom : IsCommonRegression μ₁ X₁ Y₁ μ₂ X₂ Y₂ g) :
    |transportBias μ₁ Y₁ μ₂ Y₂| ≤ L * (wasserstein1 (μ₁.map X₁) (μ₂.map X₂)).toReal := by
  have : IsProbabilityMeasure (μ₁.map X₁) :=
    (Measure.isProbabilityMeasure_map_iff hX₁.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (μ₂.map X₂) :=
    (Measure.isProbabilityMeasure_map_iff hX₂.aemeasurable).2 inferInstance
  rw [(transportBias_eq_integral_sub hX₁ hX₂ hY₁ hY₂ hcom).2.2]
  exact abs_integral_sub_le_wasserstein1 _ _ x₀ h₁ h₂ hg

end Couplings

/-! ### The gap of the means is at most the Wasserstein distance -/

section Mean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **The gap of the means is at most `W₁`, extended real form.** In a normed space,
`‖E_P X - E_Q X‖ₑ ≤ W₁(P, Q)` for laws with integrable identity: for every coupling, the gap is
`E_γ[X - Y]` and `‖E_γ[X - Y]‖ ≤ E_γ ‖X - Y‖`. -/
theorem eNorm_integral_sub_le_wasserstein1_id [CompleteSpace E] (P Q : Measure E)
    (hP : Integrable id P) (hQ : Integrable id Q) :
    ‖(∫ x, x ∂P) - ∫ x, x ∂Q‖ₑ ≤ wasserstein1 P Q := by
  refine le_iInf₂ fun γ hγ ↦ ?_
  obtain ⟨e1, i1⟩ := integral_eq_of_mem_couplings_fst (f := fun x ↦ x) hγ
    aestronglyMeasurable_id hP
  obtain ⟨e2, i2⟩ := integral_eq_of_mem_couplings_snd (f := fun x ↦ x) hγ
    aestronglyMeasurable_id hQ
  rw [e1, e2, ← integral_sub i1 i2]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun z ↦ (eDist_eq_eNorm_sub _ _).symm

/-- **The gap of the means is at most `W₁`.** In a normed space, for probability laws with
integrable identity, `‖E_P X - E_Q X‖ ≤ W₁(P, Q)`. -/
theorem norm_integral_sub_le_wasserstein1 [CompleteSpace E] (P Q : Measure E)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hP : Integrable id P)
    (hQ : Integrable id Q) :
    ‖(∫ x, x ∂P) - ∫ x, x ∂Q‖ ≤ (wasserstein1 P Q).toReal := by
  have hd : ∀ (R : Measure E), Integrable id R → Integrable (fun x ↦ dist x 0) R :=
    fun R h ↦ by simpa only [dist_zero_right, id_eq] using h.norm
  have hW := wasserstein1_ne_top P Q 0 (hd P hP) (hd Q hQ)
  have h := eNorm_integral_sub_le_wasserstein1_id P Q hP hQ
  rwa [← ofReal_norm, ENNReal.ofReal_le_iff_le_toReal hW] at h

end Mean

variable {p : ℕ}

/-- **The Chebyshev distance of the covariate means is at most `W₁`.** On `ℝ^p` with its sup
metric, for probability laws with integrable coordinates,
`max_ℓ |x̄₁ ℓ - x̄₂ ℓ| ≤ W₁(P₁, P₂)` with `x̄ᵢ = covMean Pᵢ` (unit scales). -/
theorem chebyshev_covMean_le_wasserstein1 (P₁ P₂ : Measure (Fin p → ℝ))
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₁)
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₂) :
    chebyshev 1 (IndirectComparison.covMean P₂) (IndirectComparison.covMean P₁) ≤
      (wasserstein1 P₁ P₂).toReal := by
  have h := norm_integral_sub_le_wasserstein1 P₁ P₂ (Integrable.of_eval h₁)
    (Integrable.of_eval h₂)
  refine le_of_eq_of_le ?_ h
  rw [chebyshev, stdGap_one]
  congr 1
  funext l
  simp only [Pi.sub_apply, IndirectComparison.covMean]
  rw [eval_integral h₁, eval_integral h₂]

/-- **The Euclidean distance of the means is at most `W₁`.** On `EuclideanSpace ℝ (Fin p)`, for
probability laws with integrable identity,
`d_E(x̄₂, x̄₁) ≤ W₁(P₁, P₂)` with `x̄ᵢ ℓ = ∫ x ℓ dPᵢ`. -/
theorem euclidean_mean_le_wasserstein1 (P₁ P₂ : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] (h₁ : Integrable id P₁)
    (h₂ : Integrable id P₂) :
    euclidean (fun l ↦ ∫ x, x l ∂P₂) (fun l ↦ ∫ x, x l ∂P₁) ≤ (wasserstein1 P₁ P₂).toReal := by
  have hc : ∀ (P : Measure (EuclideanSpace ℝ (Fin p))), Integrable id P → ∀ l,
      ∫ x, x l ∂P = (∫ x, x ∂P) l := fun P h l ↦
    (EuclideanSpace.proj (𝕜 := ℝ) l).integral_comp_comm h
  refine le_of_eq_of_le ?_ (norm_integral_sub_le_wasserstein1 P₁ P₂ h₁ h₂)
  rw [euclidean_eq_norm]
  congr 1
  ext l
  simp only [Pi.sub_apply, PiLp.sub_apply, hc P₁ h₁, hc P₂ h₂]

/-- The mean bounds applied to Dirac laws (all hypotheses verified). -/
example (v w : Fin 2 → ℝ) :
    chebyshev 1 (IndirectComparison.covMean (Measure.dirac w))
        (IndirectComparison.covMean (Measure.dirac v)) ≤
      (wasserstein1 (Measure.dirac v) (Measure.dirac w)).toReal :=
  chebyshev_covMean_le_wasserstein1 _ _ (fun _ ↦ integrable_dirac eNorm_lt_top)
    (fun _ ↦ integrable_dirac eNorm_lt_top)

example (v w : EuclideanSpace ℝ (Fin 2)) :
    euclidean (fun l ↦ ∫ x, x l ∂Measure.dirac w) (fun l ↦ ∫ x, x l ∂Measure.dirac v) ≤
      (wasserstein1 (Measure.dirac v) (Measure.dirac w)).toReal :=
  euclidean_mean_le_wasserstein1 _ _ (integrable_dirac eNorm_lt_top)
    (integrable_dirac eNorm_lt_top)

/-! ### Equal means at positive Wasserstein distance -/

/-- `|x|` is `1`-Lipschitz on `ℝ`. -/
theorem lipschitzWith_abs : LipschitzWith 1 fun x : ℝ ↦ |x| := by
  have : (fun x : ℝ ↦ |x|) = norm := funext fun x ↦ (Real.norm_eq_abs x).symm
  rw [this]
  exact lipschitzWith_one_norm

/-- **The Wasserstein distance of the two point law to `δ₀` is `1`**:
`W₁(½ δ₋₁ + ½ δ₁, δ₀) = 1`. The product coupling moves each half unit of mass a distance one;
the lower bound is the Lipschitz bound for `|x|`, whose means are `1` and `0`. -/
theorem wasserstein1_spreadLaw_dirac : wasserstein1 spreadLaw (Measure.dirac 0) = 1 := by
  apply le_antisymm
  · refine (iInf₂_le _ (prod_mem_couplings _ _)).trans (le_of_eq ?_)
    rw [Measure.prod_dirac, lintegral_map (continuous_fst.edist continuous_snd).measurable
      measurable_prodMk_right, lintegral_spreadLaw]
    simp [edist_dist, ENNReal.inv_two_add_inv_two]
  · have h := eNorm_integral_sub_le_wasserstein1 spreadLaw (Measure.dirac (0 : ℝ)) 0
      (integrable_spreadLaw _) (integrable_dirac eNorm_lt_top) lipschitzWith_abs
    rw [integral_spreadLaw, integral_dirac] at h
    norm_num at h
    exact h

/-- **Equal means do not give a zero Wasserstein distance.** The two point law
`½ δ₋₁ + ½ δ₁` and `δ₀` have the same mean `0` and Wasserstein distance `1`; in particular no
bound `W₁ ≤ C |x̄₁ - x̄₂|` holds. -/
theorem exists_eq_mean_wasserstein1_pos :
    ∫ x, x ∂spreadLaw = ∫ x, x ∂(Measure.dirac (0 : ℝ)) ∧
      (wasserstein1 spreadLaw (Measure.dirac 0)).toReal = 1 ∧
      ∀ C : ℝ, ¬ (wasserstein1 spreadLaw (Measure.dirac 0)).toReal ≤
        C * |∫ x, x ∂spreadLaw - ∫ x, x ∂(Measure.dirac (0 : ℝ))| := by
  have hm : ∫ x, x ∂spreadLaw = ∫ x, x ∂(Measure.dirac (0 : ℝ)) := by
    rw [integral_spreadLaw, integral_dirac]; norm_num
  refine ⟨hm, by rw [wasserstein1_spreadLaw_dirac]; rfl, fun C ↦ ?_⟩
  rw [wasserstein1_spreadLaw_dirac, hm, sub_self, abs_zero, mul_zero]
  norm_num

/-- **The Lipschitz bound on the transport bias with all hypotheses verified, and tight.**
Source covariate law `½ δ₋₁ + ½ δ₁`, target covariate law `δ₀`, outcome `|X|` with the
`1`-Lipschitz common regression `|x|`: the transport bias is `1 = 1 · W₁`. -/
theorem abs_transportBias_le_wasserstein1_example :
    transportBias spreadLaw (fun x : ℝ ↦ |x|) (Measure.dirac 0) (fun x : ℝ ↦ |x|) = 1 ∧
      |transportBias spreadLaw (fun x : ℝ ↦ |x|) (Measure.dirac 0) (fun x : ℝ ↦ |x|)| ≤
        (1 : ℝ≥0) * (wasserstein1 (spreadLaw.map id) ((Measure.dirac (0 : ℝ)).map id)).toReal ∧
      (wasserstein1 (spreadLaw.map id) ((Measure.dirac (0 : ℝ)).map id)).toReal = 1 := by
  have hW : (wasserstein1 (spreadLaw.map id) ((Measure.dirac (0 : ℝ)).map id)).toReal = 1 := by
    rw [Measure.map_id, Measure.map_id, wasserstein1_spreadLaw_dirac]; rfl
  refine ⟨?_, ?_, hW⟩
  · rw [transportBias, integral_spreadLaw, integral_dirac]; norm_num
  · refine abs_transportBias_le_wasserstein1 measurable_id measurable_id
      (integrable_spreadLaw _) (integrable_dirac eNorm_lt_top) 0 ?_ ?_ lipschitzWith_abs
      (isCommonRegression_id lipschitzWith_abs.continuous.measurable (integrable_spreadLaw _)
        (integrable_dirac eNorm_lt_top))
    · rw [Measure.map_id]; exact integrable_spreadLaw _
    · rw [Measure.map_id]; exact integrable_dirac eNorm_lt_top

end Distance

end Transport

end CausalInference
