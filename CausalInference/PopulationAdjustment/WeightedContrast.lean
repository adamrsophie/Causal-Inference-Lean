/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.EffectiveSampleSize
public import CausalInference.IndirectComparison.AnchoredPredictor
public import CausalInference.PointTreatment.SampleEstimators

/-!
# Population adjustment: weighted arm means and the anchored weighted comparison

The individual data `(xᵢ, aᵢ, yᵢ)`, `i < n`, of the trial of `a` against the common comparator
`c` are reweighted by weights `wᵢ`. The **weighted arm mean** of the arm `t` is
`∑ᵢ wᵢ 1{aᵢ = t} yᵢ / ∑ᵢ wᵢ 1{aᵢ = t}` (`weightedArmMean`), the weighted mean of the outcomes
with the weights restricted to the arm (`armWeights`). With the orientation of this library
(`IndirectComparison.indirectEstimate`), the weighted estimate of the effect of `c` relative to `a`
on the scale `g` is `d̂_ac = g(μ̂_c) - g(μ̂_a)` (`weightedContrast`), and the anchored
comparison of `a` and `b` subtracts the effect `d̂_bc` of `c` relative to `b` reported by the
aggregate data trial: `indirectEstimate d̂_ac d̂_bc` (`anchoredWeightedEstimate`).

* **Sample and population.** The population form `lawWeightedArmMean P w t` is the ratio
  `E_P[w(X) 1{A = t} Y] / E_P[w(X) 1{A = t}]` under a law `P` of `(X, A, Y)`; the sample form is
  its value at the empirical law (`lawWeightedArmMean_ipdEmpirical`). The weighted arm mean is a
  ratio of sample means (`weightedArmMean_eq_div_sampleMean`), and the library's Hájek estimator
  is the weighted arm mean with weights `1 / π̂_a(Wᵢ)` (`sampleHajekArmMean_eq_weightedArmMean`).
* **A constant factor cancels** (`weightedArmMean_smul`), so weights proportional to the tilting
  weights give the same estimate.
* **Agreement with the outcome model under a linear model.** If the outcomes follow the linear
  predictor of an anchored model, `yᵢ = η_{aᵢ}(zᵢ) + eᵢ`, and the weights balance the covariates
  of each arm at `x̄`, the weighted contrast is the outcome model contrast `η_c(x̄) - η_a(x̄)`
  plus the difference of the weighted mean residuals (`weightedContrast_eq_predictor_sub`), and
  equals it when the residuals vanish. This is the finite sample form, under a linear model, of
  the agreement of matching adjusted indirect comparison and simulated treatment comparison, two
  methods reviewed by Phillippo and coauthors (2018).

## Main definitions

* `armWeights`, `weightedArmMean`, `lawWeightedArmMean`.
* `weightedContrast`, `lawWeightedContrast`, `anchoredWeightedEstimate`.

## Main results

* `weightedArmMean_smul`, `lawWeightedArmMean_ipdEmpirical`, `lawWeightedContrast_ipdEmpirical`.
* `weightedArmMean_eq_div_sampleMean`, `sampleHajekArmMean_eq_weightedArmMean`.
* `weightedMean_affine`, `weightedArmMean_predictor`, `weightedContrast_eq_predictor_sub`.
* `anchoredWeightedEstimate_eq`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory Finset IndirectComparison

/-! ### Weighted arm means -/

section ArmMeans

variable {n : ℕ} {ι' : Type*} [DecidableEq ι']

/-- The weights restricted to the arm `t`: `wᵢ 1{aᵢ = t}`. -/
def armWeights (w : Fin n → ℝ) (a : Fin n → ι') (t : ι') : Fin n → ℝ :=
  fun i => if a i = t then w i else 0

/-- The **weighted arm mean** `∑ᵢ wᵢ 1{aᵢ = t} yᵢ / ∑ᵢ wᵢ 1{aᵢ = t}`. The results assume a
nonzero total weight in the arm where they divide. -/
noncomputable def weightedArmMean (w : Fin n → ℝ) (a : Fin n → ι') (y : Fin n → ℝ) (t : ι') : ℝ :=
  weightedMean (armWeights w a t) y

/-- A nonzero factor of the weights cancels in the weighted arm mean. -/
theorem weightedArmMean_smul {c : ℝ} (hc : c ≠ 0) (w : Fin n → ℝ) (a : Fin n → ι')
    (y : Fin n → ℝ) (t : ι') :
    weightedArmMean (fun i => c * w i) a y t = weightedArmMean w a y t := by
  have : armWeights (fun i => c * w i) a t = fun i => c * armWeights w a t i := by
    funext i; simp only [armWeights]; split_ifs <;> simp
  rw [weightedArmMean, this, weightedMean_smul hc]
  rfl

/-- The **weighted estimate of the effect of `tc` relative to `ta`** on the scale `g`,
`g(μ̂_tc) - g(μ̂_ta)`: with `ta = a` and `tc = c` it is `d̂_ac`. -/
noncomputable def weightedContrast (g : ℝ → ℝ) (w : Fin n → ℝ) (a : Fin n → ι') (y : Fin n → ℝ)
    (ta tc : ι') : ℝ :=
  g (weightedArmMean w a y tc) - g (weightedArmMean w a y ta)

/-- The **anchored weighted comparison** of `a` and `b` through `c`: the weighted estimate
`d̂_ac` from the individual data minus the estimate `d̂_bc` of the aggregate data trial, as the
`indirectEstimate` of the two. The data are random (`Ω` is the sample space); for fixed data
take `Ω = Unit`. -/
noncomputable def anchoredWeightedEstimate {Ω : Type*} (g : ℝ → ℝ) (w : Ω → Fin n → ℝ)
    (a : Ω → Fin n → ι') (y : Ω → Fin n → ℝ) (ta tc : ι') (dbc : Ω → ℝ) : Ω → ℝ :=
  indirectEstimate (fun ω => weightedContrast g (w ω) (a ω) (y ω) ta tc) dbc

theorem anchoredWeightedEstimate_eq {Ω : Type*} (g : ℝ → ℝ) (w : Ω → Fin n → ℝ)
    (a : Ω → Fin n → ι') (y : Ω → Fin n → ℝ) (ta tc : ι') (dbc : Ω → ℝ) (ω : Ω) :
    anchoredWeightedEstimate g w a y ta tc dbc ω =
      g (weightedArmMean (w ω) (a ω) (y ω) tc) - g (weightedArmMean (w ω) (a ω) (y ω) ta) -
        dbc ω := rfl

end ArmMeans

/-! ### The population form and the empirical law -/

section Population

variable {𝒳 ι' : Type*} [MeasurableSpace 𝒳] [MeasurableSpace ι'] [DecidableEq ι']

/-- The **population weighted arm mean** under a law `P` of `(X, A, Y)` with the weight function
`w`: `E_P[w(X) 1{A = t} Y] / E_P[w(X) 1{A = t}]`. -/
noncomputable def lawWeightedArmMean (P : Measure (𝒳 × ι' × ℝ)) (w : 𝒳 → ℝ) (t : ι') : ℝ :=
  (∫ z, (if z.2.1 = t then w z.1 else 0) * z.2.2 ∂P) / ∫ z, (if z.2.1 = t then w z.1 else 0) ∂P

/-- The population weighted contrast `g(m_tc) - g(m_ta)` of the weighted arm means. -/
noncomputable def lawWeightedContrast (g : ℝ → ℝ) (P : Measure (𝒳 × ι' × ℝ)) (w : 𝒳 → ℝ)
    (ta tc : ι') : ℝ :=
  g (lawWeightedArmMean P w tc) - g (lawWeightedArmMean P w ta)

variable [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass ι'] {n : ℕ}

/-- **The weighted arm mean is the population weighted arm mean of the empirical law.** -/
theorem lawWeightedArmMean_ipdEmpirical (hn : 0 < n) (x : Fin n → 𝒳) (a : Fin n → ι')
    (y : Fin n → ℝ) (w : 𝒳 → ℝ) (t : ι') :
    lawWeightedArmMean (Trial.ipdEmpirical x a y) w t =
      weightedArmMean (fun i => w (x i)) a y t := by
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  rw [lawWeightedArmMean, integral_ipdEmpirical, integral_ipdEmpirical, mul_div_mul_left _ _ hn',
    weightedArmMean, weightedMean]
  rfl

/-- The weighted contrast is the population weighted contrast of the empirical law. -/
theorem lawWeightedContrast_ipdEmpirical (hn : 0 < n) (g : ℝ → ℝ) (x : Fin n → 𝒳)
    (a : Fin n → ι') (y : Fin n → ℝ) (w : 𝒳 → ℝ) (ta tc : ι') :
    lawWeightedContrast g (Trial.ipdEmpirical x a y) w ta tc =
      weightedContrast g (fun i => w (x i)) a y ta tc := by
  rw [lawWeightedContrast, lawWeightedArmMean_ipdEmpirical hn, lawWeightedArmMean_ipdEmpirical hn,
    weightedContrast]

end Population

/-! ### Ratios of sample means and the Hájek estimator -/

section SampleMeans

open PointTreatment

variable {Ξ 𝒲 : Type*}

/-- **The weighted arm mean is a ratio of sample means**: for observations `O i = (Wᵢ, Aᵢ, Yᵢ)`
and a weight function `w`, the weighted arm mean of the first `n` observations is
`(n⁻¹ ∑ 1{Aᵢ = t} w(Wᵢ) Yᵢ) / (n⁻¹ ∑ 1{Aᵢ = t} w(Wᵢ))`. -/
theorem weightedArmMean_eq_div_sampleMean (w : 𝒲 → ℝ) (t : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ)
    (n : ℕ) (ξ : Ξ) :
    weightedArmMean (fun i : Fin n => w (O i ξ).1) (fun i => (O i ξ).2.1) (fun i => (O i ξ).2.2) t =
      sampleMean (fun z => armIndObs t z * w z.1 * z.2.2) O n ξ /
        sampleMean (fun z => armIndObs t z * w z.1) O n ξ := by
  rw [weightedArmMean, weightedMean, sampleMean, sampleMean]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  rw [mul_div_mul_left _ _ hn',
    ← Fin.sum_univ_eq_sum_range (fun i => armIndObs t (O i ξ) * w (O i ξ).1 * (O i ξ).2.2) n,
    ← Fin.sum_univ_eq_sum_range (fun i => armIndObs t (O i ξ) * w (O i ξ).1) n]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
    simp only [armWeights, armIndObs] <;> split_ifs <;> simp

/-- **The Hájek estimator is a weighted arm mean**: with the weights `1 / π̂_a(Wᵢ)` of a fitted
score, `sampleHajekArmMean` is the weighted arm mean of the arm `a`. -/
theorem sampleHajekArmMean_eq_weightedArmMean (ê : ℕ → Ξ → 𝒲 → ℝ) (t : Bool)
    (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) :
    sampleHajekArmMean ê t O n ξ =
      weightedArmMean (fun i : Fin n => 1 / armProb (ê n ξ) t (O i ξ).1) (fun i => (O i ξ).2.1)
        (fun i => (O i ξ).2.2) t := by
  rw [weightedArmMean_eq_div_sampleMean (fun x => 1 / armProb (ê n ξ) t x), sampleHajekArmMean,
    sampleIpwArmMean,
    sampleIpwWeightMean]
  congr 1 <;> congr 1 <;> funext z <;> simp only [ipwObs, ipwWeightObs] <;> ring

end SampleMeans

/-! ### Agreement with the outcome model under a linear model -/

section Linear

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-- **A balanced weighted mean of an affine outcome**: if `yᵢ = c₀ + zᵢᵀb + eᵢ` and the weights
balance the `zᵢ` at `t` with a nonzero total, the weighted mean of the outcomes is
`c₀ + tᵀb` plus the weighted mean of the residuals. -/
theorem weightedMean_affine {w y e : ι → ℝ} {z : ι → Fin p → ℝ} {t b : Fin p → ℝ} {c₀ : ℝ}
    (hy : ∀ i, y i = c₀ + z i ⬝ᵥ b + e i) (hbal : MomentBalanced w z t) (hw : ∑ i, w i ≠ 0) :
    weightedMean w y = c₀ + t ⬝ᵥ b + weightedMean w e := by
  have hz : ∑ i, w i * (z i ⬝ᵥ b) = (∑ i, w i) * (t ⬝ᵥ b) := by
    simp only [dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (momentBalanced_iff_sum_mul.1 hbal) j
    calc ∑ i, w i * (z i j * b j) = (∑ i, w i * z i j) * b j := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, w i) * (t j * b j) := by rw [this]; ring
  have hsum : ∑ i, w i * y i = (∑ i, w i) * c₀ + (∑ i, w i) * (t ⬝ᵥ b) + ∑ i, w i * e i := by
    simp only [hy, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hz]
  rw [weightedMean, weightedMean, hsum]
  field_simp

variable {n : ℕ} {ι' : Type*} [DecidableEq ι']

omit [DecidableEq ι'] in
/-- The anchored linear predictor is affine: `η_t(x) = (α + γ_t) + xᵀ(β₁ + β₂,t)`. -/
theorem anchoredModel_predictor_eq (M : AnchoredModel ι' p) (t : ι') (x : Fin p → ℝ) :
    M.predictor t x = (M.α + M.γ t) + x ⬝ᵥ (M.β₁ + M.β₂ t) := by
  simp only [AnchoredModel.predictor, anchoredPredictor, dotProduct, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  ring

/-- **The weighted arm mean under a linear model**: if `yᵢ = η_{aᵢ}(zᵢ) + eᵢ` for the linear
predictor of an anchored model and the weights of the arm `t` balance its covariates at `x̄`
with a nonzero total, the weighted arm mean is `η_t(x̄)` plus the weighted mean residual of the
arm. -/
theorem weightedArmMean_predictor (M : AnchoredModel ι' p) {w y e : Fin n → ℝ}
    {a : Fin n → ι'} {z : Fin n → Fin p → ℝ} {xbar : Fin p → ℝ} (t : ι')
    (hy : ∀ i, y i = M.predictor (a i) (z i) + e i)
    (hbal : MomentBalanced (armWeights w a t) z xbar) (hw : ∑ i, armWeights w a t i ≠ 0) :
    weightedArmMean w a y t = M.predictor t xbar + weightedArmMean w a e t := by
  have hw' : weightedMean (armWeights w a t) y =
      weightedMean (armWeights w a t) (fun i => (M.α + M.γ t) + z i ⬝ᵥ (M.β₁ + M.β₂ t) + e i) := by
    simp only [weightedMean]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [armWeights]
    split_ifs with h
    · rw [hy i, h, anchoredModel_predictor_eq]
    · simp
  rw [weightedArmMean, hw', weightedMean_affine (fun i => rfl) hbal hw,
    anchoredModel_predictor_eq M]
  rfl

/-- **Weighted contrast and outcome model contrast agree under a linear model.** If the outcomes
follow the linear predictor of an anchored model, `yᵢ = η_{aᵢ}(zᵢ) + eᵢ`, and the weights of each
of the arms `ta` and `tc` balance that arm's covariates at `x̄` with nonzero totals, then on the
identity scale the weighted contrast is the outcome model contrast `η_tc(x̄) - η_ta(x̄)` plus the
difference of the weighted mean residuals, `η_tc(x̄) - η_ta(x̄) = (γ_tc - γ_ta) +
x̄ᵀ(β₂,tc - β₂,ta)`, and with vanishing residuals the two contrasts are equal. -/
theorem weightedContrast_eq_predictor_sub (M : AnchoredModel ι' p) {w y e : Fin n → ℝ}
    {a : Fin n → ι'} {z : Fin n → Fin p → ℝ} {xbar : Fin p → ℝ} (ta tc : ι')
    (hy : ∀ i, y i = M.predictor (a i) (z i) + e i)
    (hbala : MomentBalanced (armWeights w a ta) z xbar) (hwa : ∑ i, armWeights w a ta i ≠ 0)
    (hbalc : MomentBalanced (armWeights w a tc) z xbar) (hwc : ∑ i, armWeights w a tc i ≠ 0) :
    weightedContrast id w a y ta tc = M.predictor tc xbar - M.predictor ta xbar +
        (weightedArmMean w a e tc - weightedArmMean w a e ta) ∧
      M.predictor tc xbar - M.predictor ta xbar =
        (M.γ tc - M.γ ta) + xbar ⬝ᵥ (M.β₂ tc - M.β₂ ta) ∧
      ((∀ i, e i = 0) → weightedContrast id w a y ta tc =
        M.predictor tc xbar - M.predictor ta xbar) := by
  have ha := weightedArmMean_predictor M ta hy hbala hwa
  have hc := weightedArmMean_predictor M tc hy hbalc hwc
  refine ⟨by rw [weightedContrast, id, id, ha, hc]; ring, ?_, fun he => ?_⟩
  · rw [anchoredModel_predictor_eq M, anchoredModel_predictor_eq M, dotProduct_add,
      dotProduct_add, dotProduct_sub]
    ring
  · have h0 : ∀ t, weightedArmMean w a e t = 0 := fun t => by
      simp [weightedArmMean, weightedMean, he]
    rw [weightedContrast, id, id, ha, hc, h0, h0]
    ring

end Linear

end PopulationAdjustment

end CausalInference
