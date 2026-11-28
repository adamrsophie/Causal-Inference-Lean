/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapExpansion

/-!
# Bootstrap linearity of the weighted arm mean

Under the model primitives of the asymptotic normality theorem of the weighted arm mean (an
i.i.d. sample, a measurable feature with `‖φ(x) - t‖ ≤ B`, the margin condition, a positive
probability of the arm and a square integrable outcome), the weighted arm mean `T` with
balancing weights from entropy tilting is bootstrap linear with the influence function `IF` of
its asymptotic normality theorem (`isBootstrapLinear_bootstrapArmMean`).

The proof expands the statistic at the resample `y` around the population quantities, not
around the data estimate. With `u = β*(y) - β₀`, `g(z) = 1{s = a} (y - m₀)`,
`G*(y) = n⁻¹ ∑ᵢ w_{β*}(xᵢ) g(zᵢ)` and `D*(y) = n⁻¹ ∑ᵢ w_{β*}(xᵢ) 1{sᵢ = a}`:

* `T(y) - m₀ = G*(y) / D*(y)` as soon as `D*(y) ≠ 0`;
* `√n G* = √n n⁻¹ ∑ᵢ q IF(zᵢ) + Ξ`, where `Ξ` collects the second order term of the tilt, the
  linear expansion of `u` (`bootstrapTilt_linear`) and the bootstrap law of large numbers of
  `n⁻¹ ∑ᵢ w₀ g Δₖ` toward the coupling `cₖ`; `Ξ → 0` in conditional probability, in probability;
* `D* → q` in conditional probability, in probability, with `q = weightedArmMass > 0`.

This gives `√n (T(y) - m₀) - √n n⁻¹ ∑ᵢ IF(yᵢ) → 0`
(`resampleTendstoZero_bootstrapArmMean_sub`). The same statement at the data is the asymptotic
linearity of the data estimate (`sampleBalancedArmMean_isAsymptoticallyLinear`), and the
bootstrap remainder is the difference of the two.

No measurability of the bootstrap dual minimizer in the resample is used: every conditional
probability is bounded through the monotonicity of the outer measure (`ResampleEventually`).

## Main results

* `resampleMean_dotProduct_mulVec`: linearity of the resample mean under `c ⬝ᵥ (A *ᵥ ·)`.
* `resampleBounded_resampleMean`: resample means of square integrable functions are bounded.
* `resampleTendstoZero_bootstrapArmMean_sub`: the linear expansion of `T(y)` around `m₀`.
* `isBootstrapLinear_bootstrapArmMean`: bootstrap linearity of the weighted arm mean.
* `bootstrapArmMean_isBernsteinVonMisesWeak`: the conditional limit law `N(0, σ²)` of the
  bootstrap laws from the model primitives.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, Cambridge University Press, chapter 23.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap PosteriorLimit

variable {p : ℕ}

/-- The resample mean commutes with `c ⬝ᵥ (A *ᵥ ·)`. -/
theorem resampleMean_dotProduct_mulVec {𝒪 : Type*} {n : ℕ} (y : Fin n → 𝒪) (c : Fin p → ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (F : 𝒪 → Fin p → ℝ) :
    resampleMean (fun z => c ⬝ᵥ (A *ᵥ F z)) n y =
      c ⬝ᵥ (A *ᵥ fun j => resampleMean (fun z => F z j) n y) := by
  simp only [dotProduct, Matrix.mulVec, resampleMean_sum, resampleMean_const_mul]

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {O : ℕ → Ω → 𝒪}

/-- **Resample means are bounded** in conditional probability, in probability, for a
measurable square integrable function. -/
theorem resampleBounded_resampleMean [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {f : 𝒪 → ℝ} (hf : Measurable f) (hf2 : MemLp f 2 (P.map (O 0))) :
    ResampleBounded P O fun n _ y => resampleMean f n y :=
  ((resampleTendstoZero_resampleMean_sub_integral hO hf hf2).bounded.add
    (resampleBounded_const (∫ z, f z ∂(P.map (O 0))))).of_le
    (ResampleEventually.of_eventually (Eventually.of_forall fun _ _ _ => by
      rw [sub_add_cancel]))

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **The linear expansion of the bootstrap weighted arm mean.** Under the hypotheses of the
asymptotic normality theorem, `√n (T(y) - m₀) - √n n⁻¹ ∑ᵢ IF(yᵢ) → 0` in conditional
probability, in probability. -/
theorem resampleTendstoZero_bootstrapArmMean_sub [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    ResampleTendstoZero P O fun n _ y =>
      √(n : ℝ) * (bootstrapArmMean φ t a n y -
          tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t)) -
        √(n : ℝ) * resampleMean (weightedArmInfluence (P.map (O 0)) φ t a) n y := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  have hAL := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin a hq hy
  obtain ⟨hBddu, hL⟩ := bootstrapTilt_linear hO hφ hB hδ hmargin
  have huT := resampleTendstoZero_norm_bootstrapTilt_sub hO hφ hB hδ hmargin
  set ν := P.map (O 0) with hν
  set β₀ := tiltMinimizer ν φ t with hβ₀
  set m₀ := tiltArmMean ν φ t a β₀ with hm₀
  set Mi := (tiltedSecondMoment ν φ t β₀)⁻¹ with hMi
  set c := weightedCoupling ν φ t a with hc
  set qa := weightedArmMass ν φ t a with hqa
  set IF := weightedArmInfluence ν φ t a with hIF
  set w₀ : 𝒳 → ℝ := tiltWeight φ t 0 β₀ with hw₀
  have hqa0 : 0 < qa := integral_armIndObs_mul_tiltWeight_pos hφ hB β₀ hq
  set B' := |B| with hB'
  have hBB' : ∀ x, ‖φ x - t‖ ≤ B' := fun x => (hB x).trans (le_abs_self B)
  set W := Real.exp (p * (‖β₀‖ * B')) with hW
  have hΔ : ∀ x j, |φ x j - t j| ≤ B' := fun x j => abs_apply_le_of_norm_le (hBB' x) j
  have hwb : ∀ x, |w₀ x| ≤ W := fun x => by
    rw [abs_of_pos (tiltWeight_pos _ _ _ _ _)]
    exact (tiltWeight_mem_Icc (hBB' x) (le_refl ‖β₀‖)).2
  have hW0 : 0 ≤ W := by positivity
  set r₀ := 1 / (p * B' + 1) with hr₀
  have hr₀0 : 0 < r₀ := by positivity
  have hpu : ∀ v : Fin p → ℝ, ‖v‖ < r₀ → p * (‖v‖ * B') ≤ 1 := fun v hv => by
    have : p * (‖v‖ * B') ≤ p * (r₀ * B') := by gcongr
    refine this.trans ?_
    have h2 : p * (r₀ * B') = r₀ * (p * B') := by ring
    rw [h2, hr₀, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  -- the record functions
  set g : 𝒳 × Bool × ℝ → ℝ := fun z => armIndObs a z * (z.2.2 - m₀) with hg
  have hgm : Measurable g := (measurable_armIndObs a).mul (measurable_snd.snd.sub_const m₀)
  have hy0 : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2 - m₀) 2 ν := hy.sub (memLp_const m₀)
  have hgle : ∀ z, |g z| ≤ |z.2.2 - m₀| := fun z => by
    simp only [hg, abs_mul]
    rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> simp
  have hg2 : MemLp g 2 ν := hy0.of_le hgm.aestronglyMeasurable (ae_of_all _ fun z => by
    simpa only [Real.norm_eq_abs] using hgle z)
  have hag2 : MemLp (fun z => |g z|) 2 ν :=
    hg2.of_le (continuous_abs.measurable.comp hgm).aestronglyMeasurable
    (ae_of_all _ fun z => by simp)
  have hGkm : ∀ k, Measurable fun z : 𝒳 × Bool × ℝ => w₀ z.1 * g z * (φ z.1 k - t k) :=
    fun k => ((measurable_tiltWeight_fst hφ t β₀).mul hgm).mul
      ((measurable_feature_fst hφ k).sub_const _)
  have hGk2 : ∀ k, MemLp (fun z : 𝒳 × Bool × ℝ => w₀ z.1 * g z * (φ z.1 k - t k)) 2 ν :=
    fun k => (hg2.const_mul (W * B')).of_le (hGkm k).aestronglyMeasurable (ae_of_all _ fun z => by
      simp only [Real.norm_eq_abs, abs_mul]
      have hB'0 : 0 ≤ B' := abs_nonneg B
      rw [abs_of_nonneg hW0, abs_of_nonneg hB'0]
      have h1 := hwb z.1
      have h2 := hΔ z.1 k
      have h3 := abs_nonneg (g z)
      have h4 := abs_nonneg (w₀ z.1)
      nlinarith [mul_le_mul h1 h2 (abs_nonneg _) hW0])
  have hDm : Measurable fun z : 𝒳 × Bool × ℝ => w₀ z.1 * armIndObs a z :=
    (measurable_tiltWeight_fst hφ t β₀).mul (measurable_armIndObs a)
  have hD2 : MemLp (fun z : 𝒳 × Bool × ℝ => w₀ z.1 * armIndObs a z) 2 ν :=
    memLp_two_of_abs_le hDm (C := W) fun z => by
      rw [abs_mul]
      rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> simp [hwb z.1, hW0]
  have hIam : Measurable fun z : 𝒳 × Bool × ℝ => |armIndObs a z| :=
    continuous_abs.measurable.comp (measurable_armIndObs a)
  have hIa2 : MemLp (fun z : 𝒳 × Bool × ℝ => |armIndObs a z|) 2 ν :=
    memLp_two_of_abs_le hIam (C := 1) fun z => by
      rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> simp
  -- the limits of the record functions
  have hGk0 : ∀ k, ∫ z, w₀ z.1 * g z * (φ z.1 k - t k) ∂ν = c k := fun k =>
    integral_congr_ae (ae_of_all _ fun z => by simp only [hg]; ring)
  have hD0 : ∫ z, w₀ z.1 * armIndObs a z ∂ν = qa :=
    integral_congr_ae (ae_of_all _ fun z => by ring)
  have hIFm : Measurable IF := hAL.measurable
  have hIF2 : MemLp IF 2 ν :=
    (memLp_map_measure_iff hIFm.aestronglyMeasurable (hO.aemeasurable 0)).2 hAL.memLp
  have hIF0 : ∫ z, IF z ∂ν = 0 := by
    rw [← integral_comp_of_map hO hIFm]; exact hAL.integral_eq_zero
  have hR : ∀ k, ResampleTendstoZero P O fun n _ y =>
      resampleMean (fun z => w₀ z.1 * g z * (φ z.1 k - t k)) n y - c k := fun k => by
    have := resampleTendstoZero_resampleMean_sub_integral hO (hGkm k) (hGk2 k)
    have h0 := hGk0 k
    rw [hν] at h0
    simpa only [h0] using this
  have hDT0 : ResampleTendstoZero P O fun n _ y =>
      resampleMean (fun z => w₀ z.1 * armIndObs a z) n y - qa := by
    have := resampleTendstoZero_resampleMean_sub_integral hO hDm hD2
    have h0 := hD0
    rw [hν] at h0
    simpa only [h0] using this
  have hV : ResampleBounded P O fun n _ y => √(n : ℝ) * resampleMean IF n y := by
    have := resampleBounded_sqrt_mul_resampleMean_sub_integral hO hIFm hIF2
    have h0 := hIF0
    rw [hν] at h0
    simpa only [h0, sub_zero] using this
  have hgB := resampleBounded_resampleMean (f := fun z => |g z|) hO
    (continuous_abs.measurable.comp hgm) hag2
  have hIaB := resampleBounded_resampleMean (f := fun z => |armIndObs a z|) hO hIam hIa2
  -- the pieces of the expansion
  set u : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → Fin p → ℝ :=
    fun n y => bootstrapTilt φ t n y - β₀ with hu
  set s : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → Fin p → ℝ :=
    fun n y j => resampleMean (fun z => w₀ z.1 * (φ z.1 j - t j)) n y with hs
  set ρ : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → Fin p → ℝ :=
    fun n y k => resampleMean (fun z => w₀ z.1 * g z * (φ z.1 k - t k)) n y with hρ
  set G : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → ℝ :=
    fun n y => resampleMean (fun z => tiltWeight φ t 0 (bootstrapTilt φ t n y) z.1 * g z) n y
    with hG
  set D : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → ℝ := fun n y =>
    resampleMean (fun z => tiltWeight φ t 0 (bootstrapTilt φ t n y) z.1 * armIndObs a z) n y
    with hD
  set A0 : (n : ℕ) → (Fin n → 𝒳 × Bool × ℝ) → ℝ :=
    fun n y => resampleMean (fun z => w₀ z.1 * g z) n y with hA0
  have hbt : ∀ n y, bootstrapTilt φ t n y = β₀ + u n y := fun n y => by simp [hu]
  -- the second order term of `G*`
  have hE1 : ResampleTendstoZero P O fun n _ y =>
      √(n : ℝ) * (G n y - A0 n y - ∑ k, u n y k * ρ n y k) := by
    have hY := (((hBddu.mul_tendstoZero huT).mul_bounded hgB).const_mul (W * (p * B') ^ 2))
    refine hY.of_le ((huT r₀ hr₀0).mono fun n ω y hur => ?_)
    rw [abs_norm] at hur
    have hexp := abs_resampleMean_tiltWeight_expansion_le hBB' β₀ (u n y) y g (hpu _ hur)
    rw [← hbt] at hexp
    have hsq := Real.sqrt_nonneg (n : ℝ)
    have hrm : 0 ≤ resampleMean (fun z => |g z|) n y :=
      resampleMean_nonneg y fun i => abs_nonneg _
    have hRHS : 0 ≤ W * (p * B') ^ 2 * (√(n : ℝ) * ‖u n y‖ * ‖u n y‖ *
        resampleMean (fun z => |g z|) n y) := by positivity
    rw [abs_mul, abs_of_nonneg hsq, abs_of_nonneg hRHS]
    calc √(n : ℝ) * |G n y - A0 n y - ∑ k, u n y k * ρ n y k|
        ≤ √(n : ℝ) * (W * (p * (‖u n y‖ * B')) ^ 2 * resampleMean (fun z => |g z|) n y) :=
          mul_le_mul_of_nonneg_left hexp hsq
      _ = _ := by ring
  -- `D* → q`
  have hDT : ResampleTendstoZero P O fun n _ y => D n y - qa := by
    have hY := ((huT.mul_bounded hIaB).const_mul (W * (2 * (p * B'))))
    have h1 : ResampleTendstoZero P O fun n _ y =>
        D n y - resampleMean (fun z => w₀ z.1 * armIndObs a z) n y := by
      refine hY.of_le ((huT r₀ hr₀0).mono fun n ω y hur => ?_)
      rw [abs_norm] at hur
      have hexp := abs_resampleMean_tiltWeight_sub_le hBB' β₀ (u n y) y (armIndObs a)
        (hpu _ hur)
      rw [← hbt] at hexp
      have hrm : 0 ≤ resampleMean (fun z => |armIndObs a z|) n y :=
        resampleMean_nonneg y fun i => abs_nonneg _
      rw [abs_of_nonneg (by positivity : 0 ≤ W * (2 * (p * B')) *
        (‖u n y‖ * resampleMean (fun z => |armIndObs a z|) n y))]
      calc |D n y - resampleMean (fun z => w₀ z.1 * armIndObs a z) n y|
          ≤ W * (2 * (p * (‖u n y‖ * B'))) * resampleMean (fun z => |armIndObs a z|) n y := hexp
        _ = _ := by ring
    have := h1.add hDT0
    simpa only [sub_add_sub_cancel] using this
  -- the remainder `Ξ`
  have hBk : ∀ k, ResampleBounded P O fun n _ y => √(n : ℝ) * u n y k := fun k =>
    hBddu.of_le (ResampleEventually.of_eventually (Eventually.of_forall fun n ω y => by
      rw [abs_mul, abs_mul, abs_norm]
      exact mul_le_mul_of_nonneg_left (abs_apply_le_of_norm_le le_rfl k) (abs_nonneg _)))
  have hXi : ResampleTendstoZero P O fun n _ y =>
      √(n : ℝ) * (G n y - A0 n y - ∑ k, u n y k * ρ n y k) +
        ∑ k, c k * (√(n : ℝ) * (u n y k + (Mi *ᵥ s n y) k)) +
        ∑ k, √(n : ℝ) * u n y k * (ρ n y k - c k) :=
    (hE1.add (ResampleTendstoZero.sum _ fun k _ => (hL k).const_mul (c k))).add
      (ResampleTendstoZero.sum _ fun k _ => (hBk k).mul_tendstoZero (hR k))
  -- the deterministic identities
  have hIFpt : ∀ z, qa * IF z = w₀ z.1 * g z - c ⬝ᵥ (Mi *ᵥ fun j => w₀ z.1 * (φ z.1 j - t j)) :=
    fun z => by
      rw [show IF z = (armIndObs a z * w₀ z.1 * (z.2.2 - m₀) -
          c ⬝ᵥ (Mi *ᵥ fun j => w₀ z.1 * (φ z.1 j - t j))) / qa from rfl,
        mul_div_cancel₀ _ hqa0.ne']
      simp only [hg]; ring
  have hqV : ∀ n (y : Fin n → 𝒳 × Bool × ℝ),
      qa * resampleMean IF n y = A0 n y - c ⬝ᵥ (Mi *ᵥ s n y) := fun n y => by
    rw [← resampleMean_const_mul]
    simp only [hIFpt]
    rw [resampleMean_sub, resampleMean_dotProduct_mulVec]
  have hGid : ∀ n (y : Fin n → 𝒳 × Bool × ℝ), √(n : ℝ) * G n y =
      √(n : ℝ) * (qa * resampleMean IF n y) +
        (√(n : ℝ) * (G n y - A0 n y - ∑ k, u n y k * ρ n y k) +
          ∑ k, c k * (√(n : ℝ) * (u n y k + (Mi *ᵥ s n y) k)) +
          ∑ k, √(n : ℝ) * u n y k * (ρ n y k - c k)) := fun n y => by
    rw [hqV]
    have hsum : ∑ k, c k * (√(n : ℝ) * (u n y k + (Mi *ᵥ s n y) k)) +
        ∑ k, √(n : ℝ) * u n y k * (ρ n y k - c k) =
        √(n : ℝ) * ∑ k, u n y k * ρ n y k + √(n : ℝ) * (c ⬝ᵥ (Mi *ᵥ s n y)) := by
      rw [← Finset.sum_add_distrib, dotProduct, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linear_combination -hsum
  have hTq : ∀ n (y : Fin n → 𝒳 × Bool × ℝ), D n y ≠ 0 →
      bootstrapArmMean φ t a n y - m₀ = G n y / D n y := fun n y hD0 => by
    rw [bootstrapArmMean_eq_div]
    have hDe : resampleMean (fun z => armIndObs a z *
        tiltWeight φ t 0 (bootstrapTilt φ t n y) z.1) n y = D n y := by
      simp only [hD, mul_comm]
    have hGe : G n y = resampleMean (fun z => armIndObs a z *
        tiltWeight φ t 0 (bootstrapTilt φ t n y) z.1 * z.2.2) n y - m₀ * D n y := by
      rw [← hDe, ← resampleMean_const_mul, ← resampleMean_sub]
      simp only [hG, hg]
      congr 1
      funext z
      ring
    rw [hDe, hGe]
    field_simp
  -- the final bound
  have hY := (hXi.abs.add ((hV.abs).mul_tendstoZero hDT.abs)).const_mul (2 / qa)
  refine hY.of_le ((hDT (qa / 2) (by positivity)).mono fun n ω y hDq => ?_)
  have hDpos : qa / 2 < D n y := by
    have := (abs_lt.1 hDq).1
    linarith
  have hD0 : D n y ≠ 0 := (lt_trans (by positivity) hDpos).ne'
  have hDp : 0 < D n y := lt_trans (by positivity) hDpos
  set Xi := √(n : ℝ) * (G n y - A0 n y - ∑ k, u n y k * ρ n y k) +
    ∑ k, c k * (√(n : ℝ) * (u n y k + (Mi *ᵥ s n y) k)) +
    ∑ k, √(n : ℝ) * u n y k * (ρ n y k - c k) with hXidef
  set V := √(n : ℝ) * resampleMean IF n y with hVdef
  have hX : √(n : ℝ) * (bootstrapArmMean φ t a n y - m₀) - V =
      Xi / D n y + V * (qa - D n y) / D n y := by
    rw [hXidef, hVdef, hTq n y hD0, mul_div_assoc', hGid n y]
    field_simp
    ring
  have hinv : 1 / D n y ≤ 2 / qa := by
    rw [div_le_div_iff₀ hDp hqa0]; linarith
  have hRHS : 0 ≤ 2 / qa * (|Xi| + |V| * |D n y - qa|) := by positivity
  change |√(n : ℝ) * (bootstrapArmMean φ t a n y - m₀) - V| ≤
    |2 / qa * (|Xi| + |V| * |D n y - qa|)|
  rw [hX, abs_of_nonneg hRHS]
  calc |Xi / D n y + V * (qa - D n y) / D n y|
      ≤ |Xi| * (1 / D n y) + |V| * |D n y - qa| * (1 / D n y) := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_div, abs_div, abs_mul, abs_sub_comm qa, abs_of_pos hDp]
        ring
    _ ≤ |Xi| * (2 / qa) + |V| * |D n y - qa| * (2 / qa) := by gcongr
    _ = 2 / qa * (|Xi| + |V| * |D n y - qa|) := by ring

/-- **Bootstrap linearity of the weighted arm mean.** Under the hypotheses of the asymptotic
normality theorem of the weighted arm mean (`sampleBalancedArmMean_tendstoInDistribution`), the
weighted arm mean `T` is bootstrap linear with the influence function `IF` of that theorem. -/
theorem isBootstrapLinear_bootstrapArmMean [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    IsBootstrapLinear P O (bootstrapArmMean φ t a) (weightedArmInfluence (P.map (O 0)) φ t a) := by
  have hAL := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin a hq hy
  have hboot := resampleTendstoZero_bootstrapArmMean_sub hO hφ hB hδ hmargin a hq hy
  have hdata := ResampleTendstoZero.of_tendstoInMeasure (O := O) hAL.remainder
  refine isBootstrapLinear_of_resampleTendstoZero ((hboot.sub hdata).of_le
    (ResampleEventually.of_eventually (Eventually.of_forall fun n ω y => le_of_eq ?_)))
  congr 1
  simp only [bootstrapRemainder, sampleMean, ← sampleBalancedArmMean_eq_bootstrapArmMean]
  rw [← sqrt_mul_inv_self]
  ring_nf
  exact (add_zero _).symm

/-- **The conditional limit law of the bootstrap weighted arm mean** from the model primitives:
under the hypotheses of the asymptotic normality theorem the bootstrap laws of the weighted arm
mean satisfy the weak Bernstein and von Mises property with centering `m̂ₙ` and limit
`N(0, σ²)`, `σ² = weightedArmVariance`. -/
theorem bootstrapArmMean_isBernsteinVonMisesWeak [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    IsBernsteinVonMisesWeak P (bootstrapLaw (bootstrapArmMean φ t a) O)
      (sampleBalancedArmMean φ t O a)
      (gaussianReal 0 (weightedArmVariance (P.map (O 0)) φ t a).toNNReal) :=
  isBernsteinVonMisesWeak_bootstrapArmMean hO hφ hB hδ hmargin a hq hy
    (isBootstrapLinear_bootstrapArmMean hO hφ hB hδ hmargin a hq hy)

end PopulationAdjustment

end CausalInference
