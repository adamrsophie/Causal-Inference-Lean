/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.EmpiricalLawMonteCarlo

/-!
# The root `M` rate of the empirical quantile

Draws `D₀, D₁, ...` are i.i.d. under `P` with law `μ = P.map D₀`, for instance draws from a fixed
posterior law. The empirical law of the first `M` draws is `empiricalMeasure D M ω`, its
distribution function is the empirical distribution function `F̂_M`, and its `p` quantile is the
empirical `p` quantile `q̂_M(p)`.

* `measureReal_empiricalMeasure_dev_le`, `cdf_empiricalMeasure_dev_le`: for `M ≥ 1` pairwise
  independent draws with a common law, Chebyshev's inequality gives
  `P{δ ≤ |μ̂_M(A) - μ(A)|} ≤ 1/(4 M δ²)` for every measurable set `A` and `δ > 0`, in particular
  `P{δ ≤ |F̂_M(t) - F(t)|} ≤ 1/(4 M δ²)`. The variance of an indicator is at most `1/4`.
* `sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability`: if `0 < p < 1` and the
  distribution function `F` of `μ` is differentiable at `c = q_μ(p)` with positive derivative,
  then `√M (q̂_M(p) - c)` is bounded in probability. Proof: when `√M |q̂_M(p) - c| ≥ K`, the
  empirical distribution function at `c + h` or at `c - h`, `h = K/(2√M)`, lies on the wrong
  side of `p`, while `F(c ± h)` is at least `F'(c) h / 2` away from `p`; the Chebyshev bound of
  each of the two events is of order `1/(F'(c)² K²)`, uniformly in `M`.
* `ae_data_sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability`,
  `ae_data_sqrt_mul_quantile_empiricalMeasure_comp_sub_boundedInProbability`: the same for a
  family of posterior laws `Q x` indexed by the data, for almost every data value, and for the
  draws `f(D_i)` of a real functional `f` of the posterior draws.
* `sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability_uniform`: the uniform law on
  `[0, 1]`, where `q(p) = p` and `F'(p) = 1`, with an i.i.d. sample that exists.

## Main results

* `EmpiricalLaw.cdf_empiricalMeasure_dev_le`
* `EmpiricalLaw.sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability`

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 21.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal NNReal

namespace CausalInference

namespace EmpiricalLaw

open BiasAnalysis.Distributions

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {P : Measure Ω}

/-! ### The Chebyshev bound -/

/-- **Chebyshev bound for the empirical law of a set.** For `M ≥ 1` pairwise independent draws
with a common law `μ = P.map D₀`, a measurable set `A` and `δ > 0`,
`P{δ ≤ |μ̂_M(A) - μ(A)|} ≤ 1/(4 M δ²)`. -/
theorem measureReal_empiricalMeasure_dev_le [IsProbabilityMeasure P] [MeasurableSingletonClass 𝒪]
    {D : ℕ → Ω → 𝒪} (hind : Pairwise fun i j ↦ IndepFun (D i) (D j) P)
    (hident : ∀ i, IdentDistrib (D i) (D 0) P P) {A : Set 𝒪} (hA : MeasurableSet A) {M : ℕ}
    (hM : 1 ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | δ ≤ |(empiricalMeasure D M ω).real A - (P.map (D 0)).real A|} ≤
      ENNReal.ofReal (1 / (4 * M * δ ^ 2)) := by
  set g : 𝒪 → ℝ := A.indicator 1 with hg
  have hgm : Measurable g := measurable_const.indicator hA
  have hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun x ↦ by
    by_cases hx : x ∈ A <;> simp [hg, hx]
  set X : ℕ → Ω → ℝ := fun i ω ↦ g (D i ω) with hX
  have hXm : ∀ i, AEMeasurable (X i) P := fun i ↦ hgm.comp_aemeasurable (hident i).aemeasurable_fst
  have hX2 : ∀ i, MemLp (X i) 2 P := fun i ↦
    MemLp.of_bound (hXm i).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(hgb (D i ω)).1], (hgb (D i ω)).2⟩)
  set S : Ω → ℝ := fun ω ↦ (M : ℝ)⁻¹ * ∑ i ∈ range M, X i ω with hS
  have hSeq : ∀ ω, (empiricalMeasure D M ω).real A = S ω := fun ω ↦ by
    rw [empiricalMeasure_real_apply D hA, sampleMean]
  have hS2 : MemLp S 2 P := by
    have h : MemLp (fun ω ↦ (M : ℝ)⁻¹ * (∑ i ∈ range M, X i) ω) 2 P :=
      (memLp_finsetSum' _ fun i _ ↦ hX2 i).const_mul _
    convert h using 2 with ω
    simp [hS, Finset.sum_apply]
  have hmean0 : P[X 0] = (P.map (D 0)).real A := by
    rw [hX, ← integral_map (hident 0).aemeasurable_fst hgm.aestronglyMeasurable,
      integral_indicator_one hA]
  have hmean : P[S] = (P.map (D 0)).real A := by
    have hint : ∀ i ∈ range M, Integrable (X i) P := fun i _ ↦ (hX2 i).integrable one_le_two
    rw [hS, integral_const_mul, integral_finsetSum _ hint]
    have : ∀ i ∈ range M, P[X i] = P[X 0] := fun i _ ↦ by
      have := ((hident i).comp hgm).integral_eq
      simpa [hX, Function.comp_def] using this
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, nsmul_eq_mul, hmean0]
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hM)
    field_simp
  have hvar : variance S P ≤ 1 / (4 * M) := by
    have hpair : Set.Pairwise ↑(range M) fun i j ↦ IndepFun (X i) (X j) P :=
      fun i _ j _ hij ↦ (hind hij).comp hgm hgm
    have hsum : variance (∑ i ∈ range M, X i) P = ∑ i ∈ range M, variance (X i) P :=
      IndepFun.variance_sum (fun i _ ↦ hX2 i) hpair
    have hSfun : S = fun ω ↦ (M : ℝ)⁻¹ * (∑ i ∈ range M, X i) ω := by
      funext ω
      simp [hS, Finset.sum_apply]
    rw [hSfun, variance_const_mul, hsum]
    have hle : ∑ i ∈ range M, variance (X i) P ≤ ∑ _i ∈ range M, (1 / 4 : ℝ) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have := variance_le_sq_of_bounded (ae_of_all P fun ω ↦ hgb (D i ω)) (hXm i)
      norm_num at this
      linarith
    rw [Finset.sum_const, card_range, nsmul_eq_mul] at hle
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    calc ((M : ℝ)⁻¹) ^ 2 * ∑ i ∈ range M, variance (X i) P ≤ ((M : ℝ)⁻¹) ^ 2 * (M * (1 / 4)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 / (4 * M) := by field_simp
  have hc := meas_ge_le_variance_div_sq hS2 hδ
  rw [hmean] at hc
  have hset : {ω | δ ≤ |(empiricalMeasure D M ω).real A - (P.map (D 0)).real A|} =
      {ω | δ ≤ |S ω - (P.map (D 0)).real A|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hSeq]
  rw [hset]
  refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
  have hδ2 : 0 < δ ^ 2 := by positivity
  calc variance S P / δ ^ 2 ≤ 1 / (4 * M) / δ ^ 2 := div_le_div_of_nonneg_right hvar hδ2.le
    _ = 1 / (4 * M * δ ^ 2) := by rw [div_div]

/-- The distribution function of the empirical law of `M ≥ 1` real draws is the empirical
distribution function: `F̂_M(t) = M⁻¹ #{i < M : D_i ≤ t}`. -/
lemma cdf_empiricalMeasure (D : ℕ → Ω → ℝ) {M : ℕ} (hM : 1 ≤ M) (ω : Ω) (t : ℝ) :
    cdf (empiricalMeasure D M ω) t = sampleMean ((Iic t).indicator 1) D M ω := by
  have : NeZero M := ⟨by omega⟩
  rw [cdf_eq_real, empiricalMeasure_real_apply D measurableSet_Iic]

/-- **Chebyshev bound for the empirical distribution function.** For `M ≥ 1` pairwise
independent real draws with a common law `μ = P.map D₀`, `t ∈ ℝ` and `δ > 0`,
`P{δ ≤ |F̂_M(t) - F(t)|} ≤ 1/(4 M δ²)`, where `F` is the distribution function of `μ`. -/
theorem cdf_empiricalMeasure_dev_le [IsProbabilityMeasure P] {D : ℕ → Ω → ℝ}
    (hind : Pairwise fun i j ↦ IndepFun (D i) (D j) P)
    (hident : ∀ i, IdentDistrib (D i) (D 0) P P) {M : ℕ} (hM : 1 ≤ M) (t : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    P {ω | δ ≤ |cdf (empiricalMeasure D M ω) t - cdf (P.map (D 0)) t|} ≤
      ENNReal.ofReal (1 / (4 * M * δ ^ 2)) := by
  have : NeZero M := ⟨by omega⟩
  have : IsProbabilityMeasure (P.map (D 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hident 0).aemeasurable_fst).2 inferInstance
  have h := measureReal_empiricalMeasure_dev_le hind hident measurableSet_Iic hM hδ (A := Iic t)
  simpa only [cdf_eq_real] using h

/-! ### The quantile rate -/

/-- If the distribution function is continuous at the `p` quantile, `0 < p < 1`, it takes the
value `p` there. -/
lemma cdf_quantile_of_continuousAt {μ : Measure ℝ} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hF : ContinuousAt (cdf μ) (quantile μ p)) : cdf μ (quantile μ p) = p := by
  refine le_antisymm ?_ (le_cdf_quantile hp)
  have hlt : ∀ y < quantile μ p, cdf μ y ≤ p := fun y hy ↦
    le_of_lt (not_le.1 fun h ↦ absurd ((quantile_le_iff hp y).2 h) (not_le.2 hy))
  exact le_of_tendsto (hF.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall (s := Iio (quantile μ p)) fun y hy ↦ hlt y hy)

/-- **The root `M` rate of the empirical quantile.** For i.i.d. real draws with law
`μ = P.map D₀`, `0 < p < 1`, and a distribution function `F` of `μ` differentiable at the `p`
quantile `c = q_μ(p)` with `F'(c) > 0`, the scaled error `√M (q̂_M(p) - c)` of the empirical
`p` quantile is bounded in probability: `q̂_M(p) - c = O_p(M^{-1/2})`. -/
theorem sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability [IsProbabilityMeasure P]
    {D : ℕ → Ω → ℝ} (hD : IsIIDSample D P) {p d : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hd : HasDerivAt (cdf (P.map (D 0))) d (quantile (P.map (D 0)) p)) (hd0 : 0 < d) :
    BoundedInProbability P
      (fun M ω ↦ √(M : ℝ) * (quantile (empiricalMeasure D M ω) p - quantile (P.map (D 0)) p)) := by
  set μ := P.map (D 0) with hμ
  set c := quantile μ p with hc
  set F : ℝ → ℝ := ⇑(cdf μ) with hF
  have hFc : F c = p := cdf_quantile_of_continuousAt hp hd.continuousAt
  have hind : Pairwise fun i j ↦ IndepFun (D i) (D j) P := fun i j hij ↦ hD.indep.indepFun hij
  obtain ⟨r, hr, hloc⟩ := Metric.eventually_nhds_iff.1
    ((hasDerivAt_iff_isLittleO.1 hd).def (c := d / 2) (by positivity))
  have hup : ∀ h, 0 < h → h < r → p + d / 2 * h ≤ F (c + h) := fun h h0 hr' ↦ by
    have := hloc (y := c + h) (by rw [Real.dist_eq]; simpa [abs_of_pos h0] using hr')
    simp only [Real.norm_eq_abs, add_sub_cancel_left, smul_eq_mul, abs_of_pos h0] at this
    have := (abs_le.1 this).1
    rw [hFc] at this
    nlinarith
  have hlo : ∀ h, 0 < h → h < r → F (c - h) ≤ p - d / 2 * h := fun h h0 hr' ↦ by
    have := hloc (y := c - h) (by rw [Real.dist_eq]; simpa [abs_of_pos h0] using hr')
    simp only [Real.norm_eq_abs, sub_sub_cancel_left, smul_eq_mul, abs_neg, abs_of_pos h0]
      at this
    have := (abs_le.1 this).2
    rw [hFc] at this
    nlinarith
  intro η hη
  by_cases htop : η = ⊤
  · exact ⟨1, one_pos, Eventually.of_forall fun _ ↦ htop ▸ le_top⟩
  set e := η.toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hη.ne' htop
  set K := 3 / (d * √e) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K, hK0, ?_⟩
  have htend : Tendsto (fun M : ℕ ↦ K / 2 / √(M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [htend.eventually (gt_mem_nhds hr), eventually_ge_atTop 1] with M hMr hM
  set h := K / 2 / √(M : ℝ) with hh
  have hsq : 0 < √(M : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hM)
  have hh0 : 0 < h := by positivity
  set δ := d / 2 * h with hδ
  have hδ0 : 0 < δ := by positivity
  have hsub : {ω | K ≤ |√(M : ℝ) * (quantile (empiricalMeasure D M ω) p - c)|} ⊆
      {ω | δ ≤ |cdf (empiricalMeasure D M ω) (c + h) - F (c + h)|} ∪
        {ω | δ ≤ |cdf (empiricalMeasure D M ω) (c - h) - F (c - h)|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, abs_mul, abs_of_pos hsq] at hω
    have h2h : 2 * h ≤ |quantile (empiricalMeasure D M ω) p - c| := by
      rw [hh, show 2 * (K / 2 / √(M : ℝ)) = K / √(M : ℝ) by ring, div_le_iff₀ hsq]
      linarith
    rcases le_abs'.1 h2h with hneg | hpos
    · right
      have hle : quantile (empiricalMeasure D M ω) p ≤ c - h := by linarith
      have hF' := (quantile_le_iff hp _).1 hle
      have := hlo h hh0 hMr
      simp only [Set.mem_ofPred_eq]
      rw [abs_of_nonneg (by linarith)]
      linarith
    · left
      have hgt : ¬ quantile (empiricalMeasure D M ω) p ≤ c + h := by linarith
      have hF' : cdf (empiricalMeasure D M ω) (c + h) < p :=
        not_le.1 fun h' ↦ hgt ((quantile_le_iff hp _).2 h')
      have := hup h hh0 hMr
      simp only [Set.mem_ofPred_eq]
      rw [abs_of_neg (by linarith)]
      linarith
  have hb : ENNReal.ofReal (1 / (4 * M * δ ^ 2)) ≤ ENNReal.ofReal (e / 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have hss : √(M : ℝ) ^ 2 = M := Real.sq_sqrt hM'.le
    have hee : √e ^ 2 = e := Real.sq_sqrt he0.le
    have : 1 / (4 * M * δ ^ 2) = 4 * e / 9 := by
      rw [hδ, hh, hK]
      field_simp
      rw [hss, hee]
      ring
    rw [this]
    linarith
  calc P {ω | K ≤ |√(M : ℝ) * (quantile (empiricalMeasure D M ω) p - c)|}
      ≤ P {ω | δ ≤ |cdf (empiricalMeasure D M ω) (c + h) - F (c + h)|} +
          P {ω | δ ≤ |cdf (empiricalMeasure D M ω) (c - h) - F (c - h)|} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) :=
        add_le_add ((cdf_empiricalMeasure_dev_le hind hD.ident hM _ hδ0).trans hb)
          ((cdf_empiricalMeasure_dev_le hind hD.ident hM _ hδ0).trans hb)
    _ = η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, he,
          ENNReal.ofReal_toReal htop]

/-! ### For almost every data value -/

section Data

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {ρ : Measure 𝒳}

/-- **The quantile rate for almost every data value.** If for `ρ` almost every data value `x`
the draws `D x` are i.i.d. under `P` with law the posterior `Q x`, and the distribution function
of `Q x` has a positive derivative at its `p` quantile, `0 < p < 1`, then for `ρ` almost every
`x` the scaled error `√M (q̂_M(p) - q_{Q x}(p))` is bounded in probability. -/
theorem ae_data_sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability
    [IsProbabilityMeasure P] {Q : 𝒳 → Measure ℝ} {D : 𝒳 → ℕ → Ω → ℝ}
    (hD : ∀ᵐ x ∂ρ, IsIIDSample (D x) P ∧ P.map (D x 0) = Q x) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hd : ∀ᵐ x ∂ρ, ∃ d, 0 < d ∧ HasDerivAt (cdf (Q x)) d (quantile (Q x) p)) :
    ∀ᵐ x ∂ρ, BoundedInProbability P
      (fun M ω ↦ √(M : ℝ) * (quantile (empiricalMeasure (D x) M ω) p - quantile (Q x) p)) := by
  filter_upwards [hD, hd] with x ⟨hx, hQ⟩ ⟨d, hd0, hdx⟩
  rw [← hQ] at hdx ⊢
  exact sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability hx hp hdx hd0

/-- **The quantile rate for a real functional of the posterior draws.** If for `ρ` almost every
data value `x` the draws `D x` are i.i.d. under `P` with law the posterior `Q x` on `𝒪`, `f` is
measurable, and the distribution function of the posterior law `(Q x).map f` of the target `f`
has a positive derivative at its `p` quantile, `0 < p < 1`, then for `ρ` almost every `x` the
empirical `p` quantile of the draws `f(D_i)` is within `O_p(M^{-1/2})` of the posterior `p`
quantile of the target. -/
theorem ae_data_sqrt_mul_quantile_empiricalMeasure_comp_sub_boundedInProbability
    [IsProbabilityMeasure P] {Q : 𝒳 → Measure 𝒪} {D : 𝒳 → ℕ → Ω → 𝒪}
    (hD : ∀ᵐ x ∂ρ, IsIIDSample (D x) P ∧ P.map (D x 0) = Q x) {f : 𝒪 → ℝ} (hf : Measurable f)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hd : ∀ᵐ x ∂ρ, ∃ d, 0 < d ∧ HasDerivAt (cdf ((Q x).map f)) d (quantile ((Q x).map f) p)) :
    ∀ᵐ x ∂ρ, BoundedInProbability P (fun M ω ↦ √(M : ℝ) *
      (quantile (empiricalMeasure (fun i ω ↦ f (D x i ω)) M ω) p - quantile ((Q x).map f) p)) := by
  filter_upwards [hD, hd] with x ⟨hx, hQ⟩ ⟨d, hd0, hdx⟩
  have hmap : P.map (fun ω ↦ f (D x 0 ω)) = (Q x).map f := by
    rw [← hQ, AEMeasurable.map_map_of_aemeasurable hf.aemeasurable (hx.ident 0).aemeasurable_fst]
    rfl
  rw [← hmap] at hdx ⊢
  exact sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability (hx.comp hf) hp hdx hd0

end Data

/-! ### An instance: the uniform law -/

/-- The uniform law on `[0, 1]` has distribution function `F(x) = x` near every `p ∈ (0, 1)`,
quantile `q(p) = p` and derivative `F'(p) = 1`. -/
lemma uniform_quantile_hasDerivAt {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    quantile (volume[|Icc (0 : ℝ) 1]) p = p ∧
      HasDerivAt (cdf (volume[|Icc (0 : ℝ) 1])) 1 p := by
  rw [← trapezoidMeasure_uniform zero_lt_one]
  refine ⟨?_, ?_⟩
  · rw [quantile_trapezoidMeasure le_rfl zero_le_one le_rfl zero_lt_one hp,
      trapezoidSample_uniform zero_lt_one ⟨hp.1.le, hp.2.le⟩]
    ring
  · rw [cdf_trapezoidMeasure le_rfl zero_le_one le_rfl zero_lt_one]
    have := hasDerivAt_trapezoidCDF (a := 0) (b := 0) (c := 1) (d := 1) le_rfl zero_le_one le_rfl
      zero_lt_one (x := p) (Or.inl (Or.inr hp))
    have hpdf : trapezoidPDF 0 0 1 1 p = 1 := by
      have h1 : ¬ p < 0 := not_lt.2 hp.1.le
      simp only [trapezoidPDF, h1, hp.2.le, ↓reduceIte]
      norm_num
    rwa [hpdf] at this

/-- **The instance: the uniform law.** For i.i.d. draws with the uniform law on `[0, 1]` and
`0 < p < 1`, the empirical `p` quantile satisfies `√M (q̂_M(p) - p) = O_p(1)`. Such samples
exist. -/
theorem sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability_uniform {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    (∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {D : ℕ → Ω → ℝ}, IsIIDSample D P → P.map (D 0) = volume[|Icc (0 : ℝ) 1] →
        BoundedInProbability P
          (fun M ω ↦ √(M : ℝ) * (quantile (empiricalMeasure D M ω) p - p))) ∧
      ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ D : ℕ → Ω → ℝ,
        IsProbabilityMeasure P ∧ IsIIDSample D P ∧ P.map (D 0) = volume[|Icc (0 : ℝ) 1] := by
  obtain ⟨hq, hd⟩ := uniform_quantile_hasDerivAt hp
  refine ⟨fun {Ω} _ {P} _ {D} hD hlaw ↦ ?_, ?_⟩
  · rw [← hlaw] at hq hd
    have := sqrt_mul_quantile_empiricalMeasure_sub_boundedInProbability hD hp
      (by rwa [hq]) one_pos
    rwa [hq] at this
  · have : IsProbabilityMeasure (volume[|Icc (0 : ℝ) 1]) := by
      rw [← trapezoidMeasure_uniform zero_lt_one]
      infer_instance
    obtain ⟨Ω, mΩ, P, D, hP, -, hD, hlaw⟩ := exists_isIIDSample (volume[|Icc (0 : ℝ) 1])
    exact ⟨Ω, mΩ, P, D, hP, hD, (hlaw 0).map_eq⟩

end EmpiricalLaw

end CausalInference
