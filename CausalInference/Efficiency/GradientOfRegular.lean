/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.TiltInformation
public import CausalInference.Efficiency.GradientOfRegularLimit

/-!
# The influence function of a regular estimator is a pathwise gradient

Let `T_n` be an estimator computed from `n` observations of a law `Q` on a space `𝒪`, and let
`s` be a bounded measurable score with `E_Q[s] = 0`. The score submodel through `Q` in the
direction `s` is the family of tilts `Q_t = (1 + t s) dQ` (`scoreTilt`), a probability law for
`|t| sup |s| ≤ 1`. Along it, a functional takes the values `p(t)`. The estimator is regular along
the submodel with limit `L` (`TendstoAlongTilt`) if for every local parameter `h`, when the
`n` observations are i.i.d. with law `Q_{h/√n}` (the sample law
`Measure.pi fun _ : Fin n ↦ scoreTilt Q s (h / √n)`), the law of `√n (T_n - p(h/√n))` converges
weakly to `L`, a limit that does not depend on `h`. The tilt `Q_{h/√n}` is a probability law
for all large `n` (`eventually_isProbabilityMeasure_scoreTilt`).

The main theorem (`integral_mul_eq_of_tendstoAlongTilt`): if `T_n` is asymptotically linear at
`p(0)` with influence function `φ`, regular along the submodel, and `p` has derivative `d` at
`0`, then `E_Q[φ s] = d`. Conversely (`tendstoAlongTilt_of_integral_mul_eq`), if `E_Q[φ s] = d`
then `T_n` is regular along the submodel with limit `N(0, E_Q[φ²])`.

The proof runs through local asymptotic normality. The tilts form the parametric family
`tiltFamily` with score `s` at `0` and information `E_Q[s²]`; it satisfies the regularity
conditions of `CausalInference.Estimation.LocalAsymptoticNormality`
(`isRegularAt_tiltFamily`, `isScoreRegular_tiltFamily`), so the log likelihood ratio of
`Q_{h/√n}` against `Q` is `h S_n - h² E_Q[s²] / 2 + o_P(1)` with
`S_n = n^{-1/2} ∑ s(O_i)` (`logLikRatio_tiltFamily_sub_tendstoInMeasure`). Along a subsequence,
`(√n (T_n - p(0)), S_n)` converges in distribution to a law `ρ`; each linear combination of the
coordinates is asymptotically linear, so `ρ` is Gaussian with covariance `E_Q[φ s]`. Le Cam's third
lemma for the sample family (`ParametricFamily.tendsto_integral_pi_law_of_tendstoInDistribution`)
then identifies the limit of `√n (T_n - p(h/√n))` under `Q_{h/√n}` as `N(h (E_Q[φ s] - d), V)`,
using `√n (p(h/√n) - p(0)) → h d`. Regularity forces the shift to vanish.

For a population law `μ` and observed data `O`, `IsRegularAlong` asks for regularity along the
submodels `(1 + t s(O)) dμ` for all `s` in a class `𝒮`, with the functional `Ψ` evaluated at the
tilted population; `IsRegularAlong.integral_mul_eq` is the gradient identity in that form.

## Main definitions

* `TendstoAlongTilt Q s T p L`: regularity of `T` along the submodel of `Q` in the direction `s`.
* `IsRegularAlong μ O Ψ 𝒮 T L`: regularity along the submodels `(1 + t s(O)) dμ`, `s ∈ 𝒮`.

## Main results

* `exists_subseq_tendsto_integral_tilt`: the subsequential limit under the local alternatives.
* `integral_mul_eq_of_tendstoAlongTilt`: the gradient identity `E_Q[φ s] = p'(0)`.
* `tendstoAlongTilt_of_integral_mul_eq`: the converse.
* `IsRegularAlong.integral_mul_eq`: the gradient identity for a population functional.
* `isRegularAlong_of_hasDerivAt`: the converse for a population functional.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov and J. A. Wellner, *Efficient and Adaptive
  Estimation for Semiparametric Models*, Johns Hopkins University Press (1993).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Topology Metric Finset
open scoped ENNReal NNReal BoundedContinuousFunction

section Tilt

variable {𝒪 : Type*} [MeasurableSpace 𝒪]

/-- **Regularity along a score submodel.** For a law `Q` on `𝒪`, a score `s`, an estimator
`T n : (Fin n → 𝒪) → ℝ` and the values `p(t)` of a functional along the submodel
`Q_t = (1 + t s) dQ`: for every local parameter `h` and bounded continuous `f`, when the sample of
size `n` has the law `Measure.pi fun _ : Fin n ↦ Q_{h/√n}` (i.i.d. observations from
`Q_{h/√n}`), `E f(√n (T_n - p(h/√n))) → ∫ f dL`. The limit `L` does not depend on `h`. For a
bounded score, `Q_{h/√n}` is a probability law as soon as `|h/√n| sup |s| ≤ 1`, so for all large
`n` (`eventually_isProbabilityMeasure_scoreTilt`); the values at the finitely many other `n` do
not matter. -/
def TendstoAlongTilt (Q : Measure 𝒪) (s : 𝒪 → ℝ) (T : ∀ n, (Fin n → 𝒪) → ℝ) (p : ℝ → ℝ)
    (L : Measure ℝ) : Prop :=
  ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ ↦ ∫ x, f (√(n : ℝ) * (T n x - p (h / √(n : ℝ))))
    ∂Measure.pi fun _ : Fin n ↦ scoreTilt Q s (h / √(n : ℝ))) atTop (𝓝 (∫ y, f y ∂L))

theorem tendsto_div_sqrt_atTop {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) (h : ℝ) :
    Tendsto (fun k ↦ h / √(m k : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).comp hm)

/-- **The local alternatives are probability laws for all large `n`.** -/
theorem eventually_isProbabilityMeasure_scoreTilt {Q : Measure 𝒪} [IsProbabilityMeasure Q]
    {s : 𝒪 → ℝ} (hs : IsBoundedScore Q id s) (h : ℝ) :
    ∀ᶠ n : ℕ in atTop, IsProbabilityMeasure (scoreTilt Q s (h / √(n : ℝ))) := by
  filter_upwards [(tendsto_div_sqrt_atTop tendsto_id h).eventually (tiltFamily_Θ_mem_nhds hs)]
    with n hn
  exact (tiltFamily Q hs).isProbabilityMeasure_law hn

/-- **The rescaled increment of a differentiable path.** If `p` has derivative `d` at `0` and
`m k → ∞`, then `√m (p(h/√m) - p(0)) → h d`. -/
theorem tendsto_sqrt_mul_sub_of_hasDerivAt {p : ℝ → ℝ} {d : ℝ} (hp : HasDerivAt p d 0) (h : ℝ)
    {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun k ↦ √(m k : ℝ) * (p (h / √(m k : ℝ)) - p 0)) atTop (𝓝 (h * d)) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hp)
  have hpos : ∀ᶠ k in atTop, 0 < m k := hm.eventually (eventually_gt_atTop 0)
  have ht : Tendsto (fun k ↦ h / √(m k : ℝ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_div_sqrt_atTop hm h, ?_⟩
    filter_upwards [hpos] with k hk
    exact div_ne_zero hh (Real.sqrt_pos.2 (Nat.cast_pos.2 hk)).ne'
  refine ((hslope.comp ht).const_mul h).congr' ?_
  filter_upwards [hpos] with k hk
  have hs0 : √(m k : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hk)).ne'
  simp only [Function.comp, zero_add, smul_eq_mul, inv_div]
  field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Os : ℕ → Ω → 𝒪} {Q : Measure 𝒪} [IsProbabilityMeasure Q] {s : 𝒪 → ℝ}
  {T : ∀ n, (Fin n → 𝒪) → ℝ} {p : ℝ → ℝ} {d : ℝ} {φ : 𝒪 → ℝ}

/-- **The limit under the local alternatives along a subsequence.** Let `Os` be an i.i.d. sample
with law `Q`, `s` a bounded score, `T` asymptotically linear at `p(0)` with influence function
`φ`, and `p` differentiable at `0` with derivative `d`. Along every `ψ k → ∞` there is a further
subsequence `m` along which, under the i.i.d. law of `Q_{h/√m}`, the law of
`√m (T_m - p(h/√m))` converges weakly to `N(h (E_Q[φ s] - d), E_Q[φ²])`. -/
theorem exists_subseq_tendsto_integral_tilt (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = Q)
    (hs : IsBoundedScore Q id s) (hT : ∀ n, Measurable (T n))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (p 0) φ Os P)
    (hp : HasDerivAt p d 0) (h : ℝ) (f : ℝ →ᵇ ℝ) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    ∃ φ' : ℕ → ℕ, StrictMono φ' ∧ Tendsto (fun k ↦ ∫ x, f (√(ψ (φ' k) : ℝ) *
        (T (ψ (φ' k)) x - p (h / √(ψ (φ' k) : ℝ))))
        ∂Measure.pi fun _ : Fin (ψ (φ' k)) ↦ scoreTilt Q s (h / √(ψ (φ' k) : ℝ))) atTop
      (𝓝 (∫ x, f (x + h * (∫ z, φ z * s z ∂Q - d))
        ∂gaussianReal 0 (∫ z, φ z ^ 2 ∂Q).toNNReal)) := by
  set I := ∫ z, s z ^ 2 ∂Q with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun z ↦ sq_nonneg _
  have hO0 : AEMeasurable (Os 0) P := hOs.aemeasurable 0
  have hQ : ∀ g : 𝒪 → ℝ, Measurable g → ∫ ω, g (Os 0 ω) ∂P = ∫ z, g z ∂Q := fun g hg ↦ by
    rw [← hlaw, integral_map hO0 hg.aestronglyMeasurable]
  have hsm := hs.1
  have hφm := hAL.measurable
  have hsL2 : MemLp (fun ω ↦ s (Os 0 ω)) 2 P :=
    MemLp.of_bound (hsm.comp_aemeasurable hO0).aestronglyMeasurable hs.bound
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hs.abs_le_bound _)
  have hs0 : P[fun ω ↦ s (Os 0 ω)] = 0 := (hQ s hsm).trans hs.integral_eq_zero
  have hsAL0 := sampleMean_isAsymptoticallyLinear (O := Os) hsm hsL2
  rw [hs0] at hsAL0
  have hsAL : IsAsymptoticallyLinear (sampleMean s Os) 0 s Os P := by
    simpa only [sub_zero] using hsAL0
  have hR : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ Os i ω) P := fun n ↦
    AEMeasurable.of_eval fun i ↦ hOs.aemeasurable i
  have hTm : ∀ n, AEMeasurable (fun ω ↦ T n (fun i ↦ Os i ω)) P := fun n ↦
    (hT n).comp_aemeasurable (hR n)
  have hsmeas : ∀ n, AEMeasurable (sampleMean s Os n) P := fun n ↦ by
    unfold sampleMean
    exact aemeasurable_const.mul
      (Finset.aemeasurable_fun_sum _ fun i _ ↦ hsm.comp_aemeasurable (hOs.aemeasurable i))
  have hφI : P[fun ω ↦ φ (Os 0 ω) ^ 2] = ∫ z, φ z ^ 2 ∂Q := hQ (fun z ↦ φ z ^ 2) (hφm.pow_const 2)
  have hsI : P[fun ω ↦ s (Os 0 ω) ^ 2] = I := hQ (fun z ↦ s z ^ 2) (hsm.pow_const 2)
  set V := (∫ z, φ z ^ 2 ∂Q).toNNReal with hVdef
  have hX := hAL.tendstoInDistribution hOs hTm (P' := gaussianReal 0 V) (Y := id)
    (by rw [hφI]; exact HasLaw.id)
  have hZ := hsAL.tendstoInDistribution hOs hsmeas (P' := gaussianReal 0 I.toNNReal) (Y := id)
    (by rw [hsI]; exact HasLaw.id)
  obtain ⟨φ', hφ', ρ, hjoint, h1, h2⟩ := exists_subseq_tendstoInDistribution_prodMk
    (hX.comp_tendsto_atTop hψ) (hZ.comp_tendsto_atTop hψ)
  refine ⟨φ', hφ', ?_⟩
  set m : ℕ → ℕ := fun k ↦ ψ (φ' k) with hmdef
  have hm : Tendsto m atTop atTop := hψ.comp hφ'.tendsto_atTop
  -- the linear images of the joint limit
  have hlin : ∀ a b : ℝ, (ρ : Measure (ℝ × ℝ)).map (fun q ↦ a * q.1 + b * q.2) =
      gaussianReal 0 (P[fun ω ↦ (a * φ (Os 0 ω) + b * s (Os 0 ω)) ^ 2]).toNNReal := by
    intro a b
    have hc : Continuous (fun q : ℝ × ℝ ↦ a * q.1 + b * q.2) := by fun_prop
    have j1 : TendstoInDistribution (fun k ω ↦
        a * (√(m k : ℝ) * (T (m k) (fun i ↦ Os i ω) - p 0)) +
          b * (√(m k : ℝ) * (sampleMean s Os (m k) ω - 0))) atTop id (fun _ ↦ P)
        ((ρ : Measure (ℝ × ℝ)).map (fun q ↦ a * q.1 + b * q.2)) :=
      (hjoint.continuous_comp hc).of_hasLaw ⟨hc.aemeasurable, rfl⟩ HasLaw.id
    have hAB := (hAL.const_mul a).add (hsAL.const_mul b)
    have j2 := (hAB.tendstoInDistribution hOs
      (fun n ↦ ((hTm n).const_mul a).add ((hsmeas n).const_mul b))
      (P' := gaussianReal 0 (P[fun ω ↦ (a * φ (Os 0 ω) + b * s (Os 0 ω)) ^ 2]).toNNReal)
      (Y := id) HasLaw.id).comp_tendsto_atTop hm
    have j2' : TendstoInDistribution (fun k ω ↦
        a * (√(m k : ℝ) * (T (m k) (fun i ↦ Os i ω) - p 0)) +
          b * (√(m k : ℝ) * (sampleMean s Os (m k) ω - 0))) atTop id (fun _ ↦ P)
        (gaussianReal 0 (P[fun ω ↦ (a * φ (Os 0 ω) + b * s (Os 0 ω)) ^ 2]).toNNReal) := by
      convert j2 using 1
      funext k ω
      ring
    simpa [Measure.map_id] using tendstoInDistribution_unique _ j1 j2'
  have : IsGaussian (ρ : Measure (ℝ × ℝ)) :=
    isGaussian_of_map_linear fun a b ↦ ⟨_, hlin a b⟩
  -- the covariance of the joint limit
  have hφL2 := hAL.memLp
  have iφ2 : Integrable (fun ω ↦ φ (Os 0 ω) ^ 2) P := hφL2.integrable_sq
  have is2 : Integrable (fun ω ↦ s (Os 0 ω) ^ 2) P := hsL2.integrable_sq
  have iφs : Integrable (fun ω ↦ φ (Os 0 ω) * s (Os 0 ω)) P := hφL2.integrable_mul hsL2
  have hcov : ∫ q, q.1 * q.2 ∂(ρ : Measure (ℝ × ℝ)) = ∫ z, φ z * s z ∂Q := by
    have hW := hlin 1 1
    simp only [one_mul] at hW
    rw [integral_fst_mul_snd_of_map_add h1 h2 hW,
      Real.coe_toNNReal _ (integral_nonneg fun ω ↦ sq_nonneg _), hVdef,
      Real.coe_toNNReal _ (integral_nonneg fun z ↦ sq_nonneg _), Real.coe_toNNReal _ hI0,
      ← hφI, ← hsI, ← hQ (fun z ↦ φ z * s z) (hφm.mul hsm)]
    have e : ∀ ω, (φ (Os 0 ω) + s (Os 0 ω)) ^ 2 =
        φ (Os 0 ω) ^ 2 + 2 * (φ (Os 0 ω) * s (Os 0 ω)) + s (Os 0 ω) ^ 2 := fun ω ↦ by ring
    simp only [e]
    have s1 := integral_add (iφ2.add (iφs.const_mul 2)) is2
    have s2 := integral_add iφ2 (iφs.const_mul 2)
    simp only [Pi.add_apply] at s1 s2
    rw [s1, s2, integral_const_mul]
    ring
  -- local asymptotic normality and the joint law with the log likelihood ratio
  have ha := tendsto_sqrt_mul_sub_of_hasDerivAt hp h hm
  have hlan := (logLikRatio_tiltFamily_sub_tendstoInMeasure hs hOs hlaw h).comp_tendsto_atTop hm
  set g : ℝ × ℝ → ℝ × ℝ := fun q ↦ (q.1 - h * d, h * q.2 - h ^ 2 * I / 2) with hg
  have hgc : Continuous g := by fun_prop
  have hj2 : TendstoInDistribution (fun k ω ↦
      (√(m k : ℝ) * (T (m k) (fun i ↦ Os i ω) - p 0) - h * d,
        h * (√(m k : ℝ) * (sampleMean s Os (m k) ω - 0)) - h ^ 2 * I / 2)) atTop id
      (fun _ ↦ P) ((ρ : Measure (ℝ × ℝ)).map g) :=
    (hjoint.continuous_comp hgc).of_hasLaw ⟨hgc.aemeasurable, rfl⟩ HasLaw.id
  have hTs : ∀ n, Measurable fun x : Fin n → 𝒪 ↦ T n x - p (h / √(n : ℝ)) := fun n ↦
    (hT n).sub measurable_const
  have hj3 : TendstoInDistribution (fun k ω ↦
      (√(m k : ℝ) * ((fun n x ↦ T n x - p (h / √(n : ℝ))) (m k) (fun i ↦ Os i ω) - 0),
        (tiltFamily Q hs).logLikRatio Os 0 (0 + h / √(m k : ℝ)) (m k) ω)) atTop id
      (fun _ ↦ P) ((ρ : Measure (ℝ × ℝ)).map g) := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hj2 ?_ fun k ↦
      ((measurable_const.mul ((hTs (m k)).sub measurable_const)).comp_aemeasurable
        (hR (m k))).prodMk
        (ParametricFamily.aemeasurable_logLikRatio hOs _ (m k))
    have hconst : TendstoInMeasure P (fun (k : ℕ) (_ : Ω) ↦
        h * d - √(m k : ℝ) * (p (h / √(m k : ℝ)) - p 0)) atTop 0 :=
      tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
        (ae_of_all _ fun _ ↦ by simpa using (tendsto_const_nhds (x := h * d)).sub ha)
    refine (hconst.prodMk hlan).congr' (Eventually.of_forall fun k ↦
      Eventually.of_forall fun ω ↦ ?_) (Eventually.of_forall fun _ ↦ rfl)
    simp only [Pi.sub_apply, Prod.mk_sub_mk, zero_add, sub_zero, sampleMean]
    refine Prod.ext ?_ ?_
    · simp only
      ring
    · simp only
      rw [← mul_assoc (√(m k : ℝ)), sqrt_mul_inv_self]
  have hmass : ∫ q, Real.exp q.2 ∂((ρ : Measure (ℝ × ℝ)).map g) = 1 := by
    rw [integral_map hgc.aemeasurable (by fun_prop)]
    have e : ∫ q, Real.exp (g q).2 ∂(ρ : Measure (ℝ × ℝ)) =
        ∫ z, Real.exp (h * z - h ^ 2 * I / 2) ∂gaussianReal 0 I.toNNReal := by
      rw [← h2, integral_map measurable_snd.aemeasurable (by fun_prop)]
    rw [e, integral_exp_tilt_gaussianReal h hI0]
  have h3 := ParametricFamily.tendsto_integral_pi_law_of_tendstoInDistribution
    (F := tiltFamily Q hs)
    hOs (hlaw.trans (law_tiltFamily_zero hs).symm) (tiltFamily_Θ_mem_nhds hs)
    (isRegularAt_tiltFamily hs).support hTs hm h hj3 hmass f
  let f' : ℝ →ᵇ ℝ := f.compContinuous ⟨fun y ↦ y - h * d, by fun_prop⟩
  have hlim : ∫ q, f q.1 * Real.exp q.2 ∂((ρ : Measure (ℝ × ℝ)).map g) =
      ∫ x, f (x + h * (∫ z, φ z * s z ∂Q - d)) ∂gaussianReal 0 V := by
    rw [integral_map (f := fun q : ℝ × ℝ ↦ f q.1 * Real.exp q.2) hgc.aemeasurable
      ((f.continuous.comp continuous_fst).mul (by fun_prop)).aestronglyMeasurable]
    have := integral_mul_exp_of_isGaussian hI0 h1 h2 h f'
    simp only [f', BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at this
    simp only [hg]
    rw [this, hcov]
    congr 1
    funext x
    congr 1
    ring
  rw [hlim] at h3
  refine h3.congr' ?_
  filter_upwards [(tendsto_div_sqrt_atTop hm h).eventually (tiltFamily_Θ_mem_nhds hs)] with k hk
  rw [zero_add, ParametricFamily.pi_law _ hk]
  simp only [sub_zero, law_tiltFamily]
  rfl

/-- **The influence function of a regular estimator is a gradient along the submodel.** Let `Os`
be an i.i.d. sample with law `Q`, `s` a bounded score, `T` asymptotically linear at `p(0)` with
influence function `φ`, and `p` differentiable at `0` with derivative `d`. If `T` is regular along
the submodel `(1 + t s) dQ` with some limit `L`, then `E_Q[φ s] = d`. -/
theorem integral_mul_eq_of_tendstoAlongTilt (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = Q)
    (hs : IsBoundedScore Q id s) (hT : ∀ n, Measurable (T n))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (p 0) φ Os P)
    (hp : HasDerivAt p d 0) {L : Measure ℝ} (hreg : TendstoAlongTilt Q s T p L) :
    ∫ z, φ z * s z ∂Q = d := by
  have key : ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h * (∫ z, φ z * s z ∂Q - d))
      ∂gaussianReal 0 (∫ z, φ z ^ 2 ∂Q).toNNReal = ∫ y, f y ∂L := fun h f ↦ by
    obtain ⟨φ', hφ', hlim⟩ := exists_subseq_tendsto_integral_tilt hOs hlaw hs hT hAL hp h f
      (ψ := fun n ↦ n) tendsto_id
    exact tendsto_nhds_unique hlim ((hreg h f).comp hφ'.tendsto_atTop)
  refine sub_eq_zero.1 (eq_zero_of_integral_add_gaussianReal
    (V := (∫ z, φ z ^ 2 ∂Q).toNNReal) fun f ↦ ?_)
  have h1 := key 1 f
  have h0 := key 0 f
  simp only [one_mul, zero_mul, add_zero] at h1 h0
  rw [h1, h0]

/-- **The converse: a gradient gives regularity.** Under the hypotheses of
`exists_subseq_tendsto_integral_tilt`, if `E_Q[φ s] = d` then `T` is regular along the submodel
`(1 + t s) dQ` with limit `N(0, E_Q[φ²])`. -/
theorem tendstoAlongTilt_of_integral_mul_eq (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = Q)
    (hs : IsBoundedScore Q id s) (hT : ∀ n, Measurable (T n))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (p 0) φ Os P)
    (hp : HasDerivAt p d 0) (hd : ∫ z, φ z * s z ∂Q = d) :
    TendstoAlongTilt Q s T p (gaussianReal 0 (∫ z, φ z ^ 2 ∂Q).toNNReal) := by
  intro h f
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨φ', -, hlim⟩ := exists_subseq_tendsto_integral_tilt hOs hlaw hs hT hAL hp h f hns
  refine ⟨φ', ?_⟩
  rw [hd, sub_self, mul_zero] at hlim
  simpa only [add_zero] using hlim

end Tilt

section Population

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-- **Regularity along the score submodels of a population.** For a population law `μ`, observed
data `O : Ω → 𝒪`, a functional `Ψ` of the population law and a class `𝒮` of scores of the
observed data: each `T n` is measurable and, for every `s ∈ 𝒮`, `T` is regular
(`TendstoAlongTilt`) along the submodel through the law `μ.map O` of the observed data in the
direction `s`, with the values `t ↦ Ψ((1 + t s(O)) dμ)` of the functional at the tilted
populations and a limit `L` that depends neither on `s` nor on the local parameter. Explicitly,
for every `s ∈ 𝒮`, `h` and bounded continuous `f`, when the `n` observations are i.i.d. from
`(1 + (h/√n) s) d(μ.map O)` (the law of `O` under the population `(1 + (h/√n) s(O)) dμ`, by
`map_scoreTilt`), `E f(√n (T_n - Ψ((1 + (h/√n) s(O)) dμ))) → ∫ f dL`. For a bounded score the
tilted laws are probability laws once `|h/√n| sup |s| ≤ 1`. Full regularity is the case
`𝒮 = {s | IsBoundedScore μ O s}`. -/
structure IsRegularAlong (μ : Measure Ω) (O : Ω → 𝒪) (Ψ : Measure Ω → ℝ) (𝒮 : Set (𝒪 → ℝ))
    (T : ∀ n, (Fin n → 𝒪) → ℝ) (L : Measure ℝ) : Prop where
  /-- Each `T n` is measurable. -/
  measurable : ∀ n, Measurable (T n)
  /-- Regularity along each submodel in `𝒮`. -/
  tendsto : ∀ s ∈ 𝒮, TendstoAlongTilt (μ.map O) s T
    (fun t ↦ Ψ (scoreTilt μ (fun ω ↦ s (O ω)) t)) L

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {O : Ω → 𝒪} {Ψ : Measure Ω → ℝ}
  {𝒮 : Set (𝒪 → ℝ)} {T : ∀ n, (Fin n → 𝒪) → ℝ} {L : Measure ℝ} {φ : 𝒪 → ℝ}
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} [IsProbabilityMeasure P]
  {Os : ℕ → Ω' → 𝒪}

/-- **The gradient identity for a population functional.** Let `Os` be an i.i.d. sample whose law
is the law `μ.map O` of the observed data, `T` asymptotically linear at `Ψ(μ)` with influence
function `φ` and regular along the submodels in `𝒮`. For a bounded score `s ∈ 𝒮` along which
`t ↦ Ψ((1 + t s(O)) dμ)` has derivative `d` at `0`, `E_μ[φ(O) s(O)] = d`. -/
theorem IsRegularAlong.integral_mul_eq (hO : Measurable O) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map O)
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (Ψ μ) φ Os P)
    (hreg : IsRegularAlong μ O Ψ 𝒮 T L) {s : 𝒪 → ℝ} (hs𝒮 : s ∈ 𝒮)
    (hs : IsBoundedScore μ O s) {d : ℝ}
    (hd : HasDerivAt (fun t ↦ Ψ (scoreTilt μ (fun ω ↦ s (O ω)) t)) d 0) :
    ∫ ω, φ (O ω) * s (O ω) ∂μ = d := by
  have : IsProbabilityMeasure (μ.map O) :=
    (Measure.isProbabilityMeasure_map_iff hO.aemeasurable).2 inferInstance
  have hAL' : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω))
      ((fun t ↦ Ψ (scoreTilt μ (fun ω ↦ s (O ω)) t)) 0) φ Os P := by
    simpa only [scoreTilt_zero] using hAL
  have := integral_mul_eq_of_tendstoAlongTilt hOs hlaw ((isBoundedScore_map_iff hO).2 hs)
    hreg.measurable hAL' hd (hreg.tendsto s hs𝒮)
  rw [← this, integral_map (f := fun z ↦ φ z * s z) hO.aemeasurable
    (hAL.measurable.mul hs.1).aestronglyMeasurable]

/-- **A gradient gives regularity for a population functional.** Let `Os` be an i.i.d. sample
whose law is the law `μ.map O` of the observed data, `T` measurable and asymptotically linear at
`Ψ(μ)` with influence function `φ`, and `𝒮` a class of bounded scores along each of which
`t ↦ Ψ((1 + t s(O)) dμ)` has derivative `E_μ[φ(O) s(O)]` at `0`. Then `T` is regular along the
submodels in `𝒮` with limit `N(0, E_μ[φ(O)²])`. -/
theorem isRegularAlong_of_hasDerivAt (hO : Measurable O) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map O) (hT : ∀ n, Measurable (T n))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (Ψ μ) φ Os P)
    (h𝒮 : ∀ s ∈ 𝒮, IsBoundedScore μ O s)
    (hd : ∀ s ∈ 𝒮, HasDerivAt (fun t ↦ Ψ (scoreTilt μ (fun ω ↦ s (O ω)) t))
      (∫ ω, φ (O ω) * s (O ω) ∂μ) 0) :
    IsRegularAlong μ O Ψ 𝒮 T (gaussianReal 0 (∫ ω, φ (O ω) ^ 2 ∂μ).toNNReal) := by
  have : IsProbabilityMeasure (μ.map O) :=
    (Measure.isProbabilityMeasure_map_iff hO.aemeasurable).2 inferInstance
  refine ⟨hT, fun s hs ↦ ?_⟩
  have hAL' : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω))
      ((fun t ↦ Ψ (scoreTilt μ (fun ω ↦ s (O ω)) t)) 0) φ Os P := by
    simpa only [scoreTilt_zero] using hAL
  have h := tendstoAlongTilt_of_integral_mul_eq hOs hlaw ((isBoundedScore_map_iff hO).2 (h𝒮 s hs))
    hT hAL' (hd s hs) (integral_map (f := fun z ↦ φ z * s z) hO.aemeasurable
      (hAL.measurable.mul (h𝒮 s hs).1).aestronglyMeasurable)
  rwa [integral_map (f := fun z ↦ φ z ^ 2) hO.aemeasurable
    (hAL.measurable.pow_const 2).aestronglyMeasurable] at h

end Population

end Efficiency
end CausalInference
