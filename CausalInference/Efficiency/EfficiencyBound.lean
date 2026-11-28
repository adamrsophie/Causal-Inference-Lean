/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.PathwiseDerivative
public import CausalInference.Efficiency.OracleNormality
public import CausalInference.Efficiency.ProductBias

/-!
# The semiparametric efficiency bound for an arm mean and the average effect

The arm mean `ψ_a = E[Y(a)]` is pathwise differentiable along the score submodels
`dμ_t = (1 + t s(O)) dμ` with gradient `φ_a = armEIF e m a ψ_a`
(`hasDerivAt_regressionFunctional_arm`). This file derives the efficiency bound from that fact.

* **Uniqueness of the gradient.** A centered integrable function `ϕ` of the observed data with
  `E[ϕ(O) s(O)] = E[φ(O) s(O)]` for every bounded measurable centered score `s` equals `φ`
  almost surely (`ae_eq_of_forall_integral_mul_eq`). The scores of the submodels are all bounded
  centered functions of the observed data, so the model is nonparametric and `φ_a` is the only
  gradient: it is the efficient influence function.
* **The bound of each submodel.** The Cramér-Rao bound `ψ'(0)² / E[s(O)²]` of a submodel is at
  most `V_a = E[φ_a(O)²]` (`sq_deriv_div_le_integral_armEIF_sq`).
* **The bound is the supremum.** `V_a` is the least upper bound of these submodel bounds
  (`isLUB_submodelBounds_arm`); the scores approaching it are the centered truncations of `φ_a`.
* **Regular estimators.** If the influence function of an asymptotically linear estimator is a
  gradient along the submodels (`IsPathwiseGradient`), it is `φ_a` and the asymptotic variance is
  `V_a = E[v(a, W) / π_a(W)] + Var(E[Y(a) | W])` (`IsAsymptoticallyLinear.integral_sq_eq_arm`).
  That the influence function of a *regular* asymptotically linear estimator is a gradient is
  the consequence of Le Cam's third lemma; it is the hypothesis `IsPathwiseGradient` here.

For the average effect `E[Y(1)] - E[Y(0)]` this file proves pathwise differentiability with
gradient `ateEIF` and the least upper bound statement.

## Main definitions

* `IsPathwiseGradient`: `ϕ` is a gradient of the arm mean along the score submodels.
* `submodelBounds`: the set of Cramér-Rao bounds of the submodels.

## Main results

* `ae_eq_of_forall_integral_mul_eq`: uniqueness of a gradient in the nonparametric model.
* `ae_eq_armEIF_of_isPathwiseGradient`, `integral_sq_eq_of_isPathwiseGradient`.
* `sq_integral_mul_le_mul`: the Cauchy-Schwarz form of the Cramér-Rao inequality.
* `isLUB_submodelBounds`: the second moment of a centered square integrable `φ` is the supremum
  of the bounds `E[φ s]² / E[s²]` over bounded centered scores.
* `hasDerivAt_regressionFunctional_ate`: the gradient of the average effect.
* `isLUB_submodelBounds_arm`, `isLUB_submodelBounds_ate`: the efficiency bounds.
* `IsAsymptoticallyLinear.integral_sq_eq_arm`: the asymptotic variance of an asymptotically
  linear estimator whose influence function is a gradient.

## References

* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66 (1998).
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
* P. J. Bickel, C. A. J. Klaassen, Y. Ritov and J. A. Wellner, *Efficient and Adaptive
  Estimation for Semiparametric Models*, Johns Hopkins University Press (1993).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Topology MissingData PointTreatment

section Abstract

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {O : Ω → 𝒪}

/-- A bounded score of the observed data: measurable, bounded and centered. -/
def IsBoundedScore (μ : Measure Ω) (O : Ω → 𝒪) (s : 𝒪 → ℝ) : Prop :=
  Measurable s ∧ (∃ C, ∀ z, |s z| ≤ C) ∧ ∫ ω, s (O ω) ∂μ = 0

theorem IsBoundedScore.memLp (hO : Measurable O) {s : 𝒪 → ℝ} (hs : IsBoundedScore μ O s)
    (p : ENNReal) : MemLp (fun ω => s (O ω)) p μ := by
  obtain ⟨hsm, ⟨C, hC⟩, -⟩ := hs
  exact MemLp.of_bound (hsm.comp hO).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC _)

theorem integral_mul_indicator_eq_zero (hO : Measurable O) {D : 𝒪 → ℝ}
    (hDI : Integrable (fun ω => D (O ω)) μ) (hD0 : ∫ ω, D (O ω) ∂μ = 0)
    (hD : ∀ s, IsBoundedScore μ O s → ∫ ω, D (O ω) * s (O ω) ∂μ = 0) {B : Set 𝒪}
    (hB : MeasurableSet B) :
    ∫ ω, D (O ω) * B.indicator 1 (O ω) ∂μ = 0 := by
  set c := ∫ ω, B.indicator (1 : 𝒪 → ℝ) (O ω) ∂μ with hc
  have hgm : Measurable (B.indicator (1 : 𝒪 → ℝ)) := measurable_one.indicator hB
  have hg1 : ∀ z, |B.indicator (1 : 𝒪 → ℝ) z| ≤ 1 := fun z => by
    by_cases h : z ∈ B <;> simp [Set.indicator, h]
  have hgI : Integrable (fun ω => B.indicator (1 : 𝒪 → ℝ) (O ω)) μ :=
    Integrable.of_bound (hgm.comp hO).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hg1 _)
  have hs : IsBoundedScore μ O fun z => B.indicator 1 z - c := by
    refine ⟨hgm.sub_const c, ⟨1 + |c|, fun z => ?_⟩, ?_⟩
    · exact (abs_sub _ _).trans (by linarith [hg1 z])
    · rw [integral_sub hgI (integrable_const c), integral_const]; simp [hc]
  have h := hD _ hs
  have hDg : Integrable (fun ω => D (O ω) * B.indicator 1 (O ω)) μ :=
    hDI.mul_bdd (hgm.comp hO).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hg1 _)
  have e1 : (fun ω => D (O ω) * (B.indicator 1 (O ω) - c)) =
      fun ω => D (O ω) * B.indicator 1 (O ω) - c * D (O ω) := by funext ω; ring
  rw [e1, integral_sub hDg (hDI.const_mul c), integral_const_mul, hD0, mul_zero,
    sub_zero] at h
  exact h

/-- **Uniqueness of a gradient in the nonparametric model.** If `φ(O)` and `ϕ(O)` are integrable
and centered and `E[φ(O) s(O)] = E[ϕ(O) s(O)]` for every bounded measurable centered score `s`
of `O`, then `φ(O) = ϕ(O)` almost surely. -/
theorem ae_eq_of_forall_integral_mul_eq (hO : Measurable O) {φ ϕ : 𝒪 → ℝ} (hφ : Measurable φ)
    (hϕ : Measurable ϕ) (hφI : Integrable (fun ω => φ (O ω)) μ)
    (hϕI : Integrable (fun ω => ϕ (O ω)) μ) (hφ0 : ∫ ω, φ (O ω) ∂μ = 0)
    (hϕ0 : ∫ ω, ϕ (O ω) ∂μ = 0)
    (h : ∀ s, IsBoundedScore μ O s →
      ∫ ω, φ (O ω) * s (O ω) ∂μ = ∫ ω, ϕ (O ω) * s (O ω) ∂μ) :
    (fun ω => φ (O ω)) =ᵐ[μ] fun ω => ϕ (O ω) := by
  set D : 𝒪 → ℝ := fun z => ϕ z - φ z with hDdef
  have hDm : Measurable D := hϕ.sub hφ
  have hDI : Integrable (fun ω => D (O ω)) μ := hϕI.sub hφI
  have hD0 : ∫ ω, D (O ω) ∂μ = 0 := by
    simp only [hDdef]; rw [integral_sub hϕI hφI, hφ0, hϕ0, sub_zero]
  have hD : ∀ s, IsBoundedScore μ O s → ∫ ω, D (O ω) * s (O ω) ∂μ = 0 := by
    intro s hs
    have hsb : ∀ᵐ ω ∂μ, ‖s (O ω)‖ ≤ hs.2.1.choose := Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hs.2.1.choose_spec _
    have I1 := hϕI.mul_bdd (hs.1.comp hO).aestronglyMeasurable hsb
    have I2 := hφI.mul_bdd (hs.1.comp hO).aestronglyMeasurable hsb
    have e1 : (fun ω => D (O ω) * s (O ω)) =
        fun ω => ϕ (O ω) * s (O ω) - φ (O ω) * s (O ω) := by funext ω; simp only [hDdef]; ring
    rw [e1, integral_sub (f := fun ω => ϕ (O ω) * s (O ω)) (g := fun ω => φ (O ω) * s (O ω)) I1 I2,
      h s hs, sub_self]
  -- the positive and the negative parts vanish
  have hmul : ∀ {B : Set 𝒪}, MeasurableSet B →
      Integrable (fun ω => D (O ω) * B.indicator 1 (O ω)) μ :=
    fun {B} hB => hDI.mul_bdd ((measurable_one.indicator hB).comp hO).aestronglyMeasurable
      (c := 1) (Eventually.of_forall fun ω => by
        by_cases h : O ω ∈ B <;> simp [Set.indicator, h])
  have hpos : MeasurableSet {z | 0 < D z} := measurableSet_lt measurable_const hDm
  have hneg : MeasurableSet {z | D z < 0} := measurableSet_lt hDm measurable_const
  have h1 := integral_mul_indicator_eq_zero hO hDI hD0 hD hpos
  have h2 := integral_mul_indicator_eq_zero hO hDI hD0 hD hneg
  have n1 : 0 ≤ fun ω => D (O ω) * {z | 0 < D z}.indicator 1 (O ω) := fun ω => by
    by_cases h : 0 < D (O ω)
    · simp [Set.indicator, h, h.le]
    · simp [Set.indicator, h]
  have n2 : 0 ≤ fun ω => -(D (O ω) * {z | D z < 0}.indicator 1 (O ω)) := fun ω => by
    by_cases h : D (O ω) < 0
    · simp [Set.indicator, h, h.le]
    · simp [Set.indicator, h]
  have z1 := (integral_eq_zero_iff_of_nonneg n1 (hmul hpos)).1 h1
  have z2 := (integral_eq_zero_iff_of_nonneg n2 (hmul hneg).neg).1
    (by rw [integral_neg, h2, neg_zero])
  filter_upwards [z1, z2] with ω h1 h2
  simp only [Pi.zero_apply] at h1 h2
  have hle : D (O ω) ≤ 0 := by
    by_contra hc
    have hc : 0 < D (O ω) := lt_of_not_ge hc
    simp [Set.indicator, hc, hc.ne'] at h1
  have hge : 0 ≤ D (O ω) := by
    by_contra hc
    have hc : D (O ω) < 0 := lt_of_not_ge hc
    simp [Set.indicator, hc, hc.ne] at h2
  have : D (O ω) = 0 := le_antisymm hle hge
  simp only [hDdef] at this
  linarith

omit [IsProbabilityMeasure μ] in
/-- **The Cramér-Rao inequality of a submodel**, in its Cauchy-Schwarz form:
`E[f g]² ≤ E[f²] E[g²]` for square integrable `f` and `g`. -/
theorem sq_integral_mul_le_mul {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
  have hcs := integral_mul_le_sqrt_mul_sqrt (μ := μ) (fun ω => abs_nonneg (f ω))
    (fun ω => abs_nonneg (g ω)) hf.abs hg.abs
  simp only [sq_abs] at hcs
  have habs : |∫ ω, f ω * g ω ∂μ| ≤ ∫ ω, |f ω| * |g ω| ∂μ := by
    refine (abs_integral_le_integral_abs).trans_eq ?_
    simp only [abs_mul]
  have hf2 : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hg2 : 0 ≤ ∫ ω, g ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  calc (∫ ω, f ω * g ω ∂μ) ^ 2 = |∫ ω, f ω * g ω ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (√(∫ ω, f ω ^ 2 ∂μ) * √(∫ ω, g ω ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (habs.trans hcs) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hf2, Real.sq_sqrt hg2]

/-- The set of Cramér-Rao bounds `E[φ(O) s(O)]² / E[s(O)²]` of the score submodels, over all
bounded measurable centered scores `s` with positive information `E[s(O)²] > 0`. -/
def submodelBounds (μ : Measure Ω) (O : Ω → 𝒪) (φ : 𝒪 → ℝ) : Set ℝ :=
  {r | ∃ s, IsBoundedScore μ O s ∧ 0 < ∫ ω, s (O ω) ^ 2 ∂μ ∧
    r = (∫ ω, φ (O ω) * s (O ω) ∂μ) ^ 2 / ∫ ω, s (O ω) ^ 2 ∂μ}

/-- The truncation `max (-N) (min x N)` of `x` to `[-N, N]`. -/
def truncate (N x : ℝ) : ℝ := max (-N) (min x N)

theorem abs_truncate_le_abs {N x : ℝ} (hN : 0 ≤ N) : |truncate N x| ≤ |x| := by
  unfold truncate
  rw [abs_le]
  exact ⟨le_max_of_le_right (le_min (neg_abs_le x) (by linarith [abs_nonneg x])),
    max_le (by linarith [abs_nonneg x]) ((min_le_left _ _).trans (le_abs_self x))⟩

theorem abs_truncate_le' {N x : ℝ} (hN : 0 ≤ N) : |truncate N x| ≤ N := by
  unfold truncate
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem truncate_eq_of_abs_le {N x : ℝ} (h : |x| ≤ N) : truncate N x = x := by
  unfold truncate
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem tendsto_truncate (x : ℝ) : Tendsto (fun n : ℕ => truncate n x) atTop (𝓝 x) :=
  tendsto_const_nhds.congr' (eventually_atTop.2 ⟨⌈|x|⌉₊, fun n hn =>
    (truncate_eq_of_abs_le ((Nat.le_ceil _).trans (by exact_mod_cast hn))).symm⟩)

theorem measurable_truncate (N : ℝ) : Measurable (truncate N) :=
  measurable_const.max (measurable_id.min measurable_const)

/-- **The second moment of a centered square integrable function is the supremum of the
submodel bounds.** If `φ(O)` is square integrable and centered with `E[φ(O)²] > 0`, then
`E[φ(O)²]` is the least upper bound of `E[φ(O) s(O)]² / E[s(O)²]` over bounded measurable
centered scores with positive information. The scores approaching it are the centered
truncations of `φ`. -/
theorem isLUB_submodelBounds (hO : Measurable O) {φ : 𝒪 → ℝ} (hφ : Measurable φ)
    (hφ2 : MemLp (fun ω => φ (O ω)) 2 μ) (hφ0 : ∫ ω, φ (O ω) ∂μ = 0)
    (hV : 0 < ∫ ω, φ (O ω) ^ 2 ∂μ) :
    IsLUB (submodelBounds μ O φ) (∫ ω, φ (O ω) ^ 2 ∂μ) := by
  set V := ∫ ω, φ (O ω) ^ 2 ∂μ with hVdef
  have hφI := hφ2.integrable one_le_two
  have hφsq : Integrable (fun ω => φ (O ω) ^ 2) μ := hφ2.integrable_sq
  refine ⟨?_, fun b hb => ?_⟩
  · rintro r ⟨s, hs, hI, rfl⟩
    rw [div_le_iff₀ hI]
    exact sq_integral_mul_le_mul hφ2 (hs.memLp hO 2)
  -- the truncated scores
  set g : ℕ → Ω → ℝ := fun n ω => truncate n (φ (O ω)) with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n => (measurable_truncate _).comp (hφ.comp hO)
  have hgb : ∀ n ω, |g n ω| ≤ n := fun n ω => abs_truncate_le' (Nat.cast_nonneg n)
  have hgφ : ∀ n ω, |g n ω| ≤ |φ (O ω)| := fun n ω => abs_truncate_le_abs (Nat.cast_nonneg n)
  have hgI : ∀ n, Integrable (g n) μ := fun n =>
    Integrable.of_bound (hgm n).aestronglyMeasurable n
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb n ω)
  have hg2 : ∀ n, MemLp (g n) 2 μ := fun n =>
    MemLp.of_bound (hgm n).aestronglyMeasurable n
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb n ω)
  have hlim : ∀ ω, Tendsto (fun n => g n ω) atTop (𝓝 (φ (O ω))) := fun ω =>
    tendsto_truncate _
  -- three dominated limits
  have L1 : Tendsto (fun n => ∫ ω, g n ω ∂μ) atTop (𝓝 0) := by
    rw [← hφ0]
    refine tendsto_integral_of_dominated_convergence (fun ω => |φ (O ω)|)
      (fun n => (hgm n).aestronglyMeasurable) hφI.abs
      (fun n => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgφ n ω)
      (Eventually.of_forall hlim)
  have L2 : Tendsto (fun n => ∫ ω, φ (O ω) * g n ω ∂μ) atTop (𝓝 V) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => φ (O ω) ^ 2)
      (fun n => ((hφ.comp hO).mul (hgm n)).aestronglyMeasurable) hφsq
      (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => by
        simpa [sq] using (tendsto_const_nhds (x := φ (O ω))).mul (hlim ω))
    rw [Real.norm_eq_abs, abs_mul, sq, ← abs_mul_abs_self]
    exact mul_le_mul_of_nonneg_left (hgφ n ω) (abs_nonneg _)
  have L3 : Tendsto (fun n => ∫ ω, g n ω ^ 2 ∂μ) atTop (𝓝 V) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => φ (O ω) ^ 2)
      (fun n => ((hgm n).pow_const 2).aestronglyMeasurable) hφsq
      (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => (hlim ω).pow 2)
    rw [Real.norm_eq_abs, abs_pow, ← sq_abs (φ (O ω))]
    exact pow_le_pow_left₀ (abs_nonneg _) (hgφ n ω) 2
  -- the centered truncations
  set c : ℕ → ℝ := fun n => ∫ ω, g n ω ∂μ with hcdef
  set s : ℕ → 𝒪 → ℝ := fun n z => truncate n (φ z) - c n with hsdef
  have hsO : ∀ n ω, s n (O ω) = g n ω - c n := fun _ _ => rfl
  have hs : ∀ n, IsBoundedScore μ O (s n) := fun n => by
    refine ⟨((measurable_truncate _).comp hφ).sub_const _, ⟨n + |c n|, fun z => ?_⟩, ?_⟩
    · exact (abs_sub _ _).trans (by linarith [abs_truncate_le' (x := φ z) (Nat.cast_nonneg n)])
    · simp only [hsO]; rw [integral_sub (hgI n) (integrable_const _), integral_const]; simp [hcdef]
  have hnum : ∀ n, ∫ ω, φ (O ω) * s n (O ω) ∂μ = ∫ ω, φ (O ω) * g n ω ∂μ := fun n => by
    simp only [hsO, mul_sub]
    rw [integral_sub (((hg2 n).integrable_mul hφ2).congr (Eventually.of_forall fun ω => by
      simp only [Pi.mul_apply, mul_comm])) (hφI.mul_const _), integral_mul_const, hφ0, zero_mul,
      sub_zero]
  have hden : ∀ n, ∫ ω, s n (O ω) ^ 2 ∂μ = ∫ ω, g n ω ^ 2 ∂μ - c n ^ 2 := fun n => by
    have e1 : (fun ω => s n (O ω) ^ 2) = fun ω => g n ω ^ 2 - 2 * c n * g n ω + c n ^ 2 := by
      funext ω; rw [hsO]; ring
    rw [e1, integral_add (f := fun ω => g n ω ^ 2 - 2 * c n * g n ω) (g := fun _ => c n ^ 2)
        ((hg2 n).integrable_sq.sub ((hgI n).const_mul _)) (integrable_const _),
      integral_sub (f := fun ω => g n ω ^ 2) (g := fun ω => 2 * c n * g n ω)
        (hg2 n).integrable_sq ((hgI n).const_mul _), integral_const_mul,
      integral_const]
    simp only [hcdef, probReal_univ, one_smul]
    ring
  have Lnum : Tendsto (fun n => (∫ ω, φ (O ω) * s n (O ω) ∂μ) ^ 2) atTop (𝓝 (V ^ 2)) := by
    simp only [hnum]; exact L2.pow 2
  have Lden : Tendsto (fun n => ∫ ω, s n (O ω) ^ 2 ∂μ) atTop (𝓝 V) := by
    simp only [hden]
    have := L3.sub (L1.pow 2)
    simpa using this
  have Lr : Tendsto (fun n => (∫ ω, φ (O ω) * s n (O ω) ∂μ) ^ 2 / ∫ ω, s n (O ω) ^ 2 ∂μ) atTop
      (𝓝 V) := by
    have := Lnum.div Lden hV.ne'
    rwa [sq, mul_div_assoc, div_self hV.ne', mul_one] at this
  have hevpos : ∀ᶠ n in atTop, 0 < ∫ ω, s n (O ω) ^ 2 ∂μ := Lden.eventually (lt_mem_nhds hV)
  refine le_of_tendsto Lr (hevpos.mono fun n hn => hb ⟨s n, hs n, hn, rfl⟩)

end Abstract

section Arm

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **`ϕ` is a gradient of the arm mean along the score submodels**: for every bounded
measurable centered score `s` of the observed data, the observed data functional along
`dμ_t = (1 + t s(O)) dμ` has derivative `E[ϕ(O) s(O)]` at `t = 0`. For the influence function
of a regular asymptotically linear estimator this is the consequence of Le Cam's third lemma. -/
def IsPathwiseGradient (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (a : Bool) (ϕ : 𝒲 × Bool × ℝ → ℝ) : Prop :=
  ∀ s, IsBoundedScore μ (obsData A Y W) s →
    HasDerivAt (fun t ↦ regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
      (arm A a) W (obsOutcome A Y)) (∫ ω, ϕ (obsData A Y W ω) * s (obsData A Y W ω) ∂μ) 0

/-- **The efficient influence function is a gradient** of the arm mean along the score
submodels, under mean ignorability of the arm, a correct score and regression, integrable
potential outcomes and `π_a(W) ≥ ε > 0`. -/
theorem isPathwiseGradient_armEIF (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) :
    IsPathwiseGradient μ A Y W a (armEIF e m a (armMean μ Y a)) := fun _ hs =>
  hasDerivAt_regressionFunctional_arm hW hA hY hYi hps hreg a hmi hε hpos hs.1
    hs.2.1.choose_spec hs.2.2

/-- **The gradient of the arm mean is unique**: an integrable centered gradient `ϕ` of the arm
mean along the score submodels equals the efficient influence function `φ_a` almost surely. -/
theorem ae_eq_armEIF_of_isPathwiseGradient (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) {ϕ : 𝒲 × Bool × ℝ → ℝ} (hϕ : Measurable ϕ)
    (hϕI : Integrable (fun ω => ϕ (obsData A Y W ω)) μ)
    (hϕ0 : ∫ ω, ϕ (obsData A Y W ω) ∂μ = 0) (hgrad : IsPathwiseGradient μ A Y W a ϕ) :
    (fun ω => ϕ (obsData A Y W ω)) =ᵐ[μ]
      fun ω => armEIF e m a (armMean μ Y a) (obsData A Y W ω) := by
  have hg := isPathwiseGradient_armEIF hW hA hY hYi hps hreg a hmi hε hpos
  exact ae_eq_of_forall_integral_mul_eq (measurable_obsData hW hA hY) hϕ
    (measurable_armEIF hps.1 (hreg.1 a) _) hϕI
    (integrable_armEIF hW hA hYi hps hreg a hmi hε hpos _) hϕ0
    (integral_armEIF_eq_zero hW hA hYi hps hreg a hmi hε hpos)
    fun s hs => (hgrad s hs).unique (hg s hs)

/-- **Every centered integrable gradient has the efficient variance**
`E[ϕ(O)²] = E[v(a, W) / π_a(W)] + Var(E[Y(a) | W])`. -/
theorem integral_sq_eq_of_isPathwiseGradient (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) {ϕ : 𝒲 × Bool × ℝ → ℝ} (hϕ : Measurable ϕ)
    (hϕI : Integrable (fun ω => ϕ (obsData A Y W ω)) μ)
    (hϕ0 : ∫ ω, ϕ (obsData A Y W ω) ∂μ = 0) (hgrad : IsPathwiseGradient μ A Y W a ϕ) :
    ∫ ω, ϕ (obsData A Y W ω) ^ 2 ∂μ = ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
      Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] := by
  have hu := ae_eq_armEIF_of_isPathwiseGradient hW hA hY
    (fun a => (hY2 a).integrable one_le_two) hps hreg a hmi hε hpos hϕ hϕI hϕ0 hgrad
  rw [← integral_armEIF_sq hW hA hY hY2 hps hreg hv a hmi hε hpos]
  exact integral_congr_ae (hu.mono fun ω h => by simp only [h])

/-- **The Cramér-Rao bound of each submodel is at most the efficient variance.** For a bounded
measurable centered score `s` with `E[s(O)²] > 0`, if `t ↦ ψ(μ_t)` has derivative `d` at `0`,
then `d² / E[s(O)²] ≤ E[φ_a(O)²]`. -/
theorem sq_deriv_div_le_integral_armEIF_sq (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) {s : 𝒲 × Bool × ℝ → ℝ}
    (hs : IsBoundedScore μ (obsData A Y W) s) (hI : 0 < ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ)
    {d : ℝ} (hd : HasDerivAt (fun t ↦ regressionFunctional
      (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t) (arm A a) W (obsOutcome A Y)) d 0) :
    d ^ 2 / ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ ≤
      ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  rw [hd.unique (isPathwiseGradient_armEIF hW hA hY hYi hps hreg a hmi hε hpos s hs),
    div_le_iff₀ hI]
  exact sq_integral_mul_le_mul (memLp_armEIF hW hA hY hY2 hps hreg a hmi hε hpos _)
    (hs.memLp (measurable_obsData hW hA hY) 2)

/-- **The efficiency bound of an arm mean is the supremum of the submodel bounds.** Under mean
ignorability of the arm, a correct score and regression, square integrable potential outcomes,
`π_a(W) ≥ ε > 0` and `V_a = E[φ_a(O)²] > 0`, `V_a` is the least upper bound of the Cramér-Rao
bounds `d² / E[s(O)²]` of the score submodels, `d` the derivative of `t ↦ ψ(μ_t)` at `0`. -/
theorem isLUB_submodelBounds_arm (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω))
    (hV : 0 < ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ) :
    IsLUB {r | ∃ s, IsBoundedScore μ (obsData A Y W) s ∧
        0 < ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ ∧ ∃ d, HasDerivAt (fun t ↦ regressionFunctional
          (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t) (arm A a) W (obsOutcome A Y)) d 0 ∧
        r = d ^ 2 / ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ}
      (∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ) := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hg := isPathwiseGradient_armEIF hW hA hY hYi hps hreg a hmi hε hpos
  have hset : {r | ∃ s, IsBoundedScore μ (obsData A Y W) s ∧
        0 < ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ ∧ ∃ d, HasDerivAt (fun t ↦ regressionFunctional
          (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t) (arm A a) W (obsOutcome A Y)) d 0 ∧
        r = d ^ 2 / ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ} =
      submodelBounds μ (obsData A Y W) (armEIF e m a (armMean μ Y a)) := by
    ext r
    constructor
    · rintro ⟨s, hs, hI, d, hd, rfl⟩
      exact ⟨s, hs, hI, by rw [hd.unique (hg s hs)]⟩
    · rintro ⟨s, hs, hI, rfl⟩
      exact ⟨s, hs, hI, _, hg s hs, rfl⟩
  rw [hset]
  exact isLUB_submodelBounds (measurable_obsData hW hA hY)
    (measurable_armEIF hps.1 (hreg.1 a) _) (memLp_armEIF hW hA hY hY2 hps hreg a hmi hε hpos _)
    (integral_armEIF_eq_zero hW hA hYi hps hreg a hmi hε hpos) hV

/-- **The asymptotic variance of an asymptotically linear estimator whose influence function is
a gradient.** Let `O_i` be a sample whose first observation has the law of the observed data,
and let `θ̂` be asymptotically linear at `E[Y(a)]` with influence function `ϕ`. If `ϕ` is a
gradient of the arm mean along the score submodels (`IsPathwiseGradient`, the consequence of
regularity given by Le Cam's third lemma, assumed here), then `ϕ = φ_a` almost surely under the
law of the observed data and the asymptotic variance `E[ϕ(O_0)²]` is the efficiency bound
`E[v(a, W) / π_a(W)] + Var(E[Y(a) | W])`. -/
theorem _root_.CausalInference.IsAsymptoticallyLinear.integral_sq_eq_arm
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} [IsProbabilityMeasure P]
    {O : ℕ → Ω' → 𝒲 × Bool × ℝ} {θhat : ℕ → Ω' → ℝ} {ϕ : 𝒲 × Bool × ℝ → ℝ}
    (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω))
    (hAL : IsAsymptoticallyLinear θhat (armMean μ Y a) ϕ O P)
    (hO : AEMeasurable (O 0) P) (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    (hgrad : IsPathwiseGradient μ A Y W a ϕ) :
    ∫ ω, ϕ (O 0 ω) ^ 2 ∂P = ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
      Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] := by
  have hϕ := hAL.measurable
  have hϕ2 : MemLp (fun ω => ϕ (obsData A Y W ω)) 2 μ := by
    have h := (memLp_map_measure_iff hϕ.aestronglyMeasurable hO).2 hAL.memLp
    rw [hlaw] at h
    exact (memLp_map_measure_iff hϕ.aestronglyMeasurable
      (measurable_obsData hW hA hY).aemeasurable).1 h
  have hϕ0 : ∫ ω, ϕ (obsData A Y W ω) ∂μ = 0 := by
    rw [← integral_comp_obs hW hA hY hO hlaw hϕ]; exact hAL.integral_eq_zero
  rw [integral_comp_obs hW hA hY hO hlaw (hϕ.pow_const 2)]
  exact integral_sq_eq_of_isPathwiseGradient hW hA hY hY2 hps hreg hv a hmi hε hpos hϕ
    (hϕ2.integrable one_le_two) hϕ0 hgrad

/-- **Pathwise differentiability of the average effect with gradient `ateEIF`**: under mean
ignorability of both arms, a correct score and regression, integrable potential outcomes and
strict overlap, `t ↦ ψ_1(μ_t) - ψ_0(μ_t)` has derivative `E[φ(O) s(O)]` at `0` along every
bounded score submodel, `φ = ateEIF e m (E[Y(1)] - E[Y(0)])`. -/
theorem hasDerivAt_regressionFunctional_ate (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    {s : 𝒲 × Bool × ℝ → ℝ} (hs : IsBoundedScore μ (obsData A Y W) s) :
    HasDerivAt (fun t ↦
        regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
          (arm A true) W (obsOutcome A Y) -
        regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
          (arm A false) W (obsOutcome A Y))
      (∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) * s (obsData A Y W ω) ∂μ) 0 := by
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  have hd := fun a => hasDerivAt_regressionFunctional_arm hW hA hY hYi hps hreg a (hmi a)
    hov.1 (hpos a) hs.1 hs.2.1.choose_spec hs.2.2
  have hsb : ∀ᵐ ω ∂μ, ‖s (obsData A Y W ω)‖ ≤ hs.2.1.choose := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hs.2.1.choose_spec _
  have hI := fun a => (integrable_armEIF hW hA hYi hps hreg a (hmi a) hov.1 (hpos a)
    (armMean μ Y a)).mul_bdd (hs.1.comp (measurable_obsData hW hA hY)).aestronglyMeasurable hsb
  convert (hd true).sub (hd false) using 1
  rw [← integral_sub (f := fun ω => armEIF e m true (armMean μ Y true) (obsData A Y W ω) *
      s (obsData A Y W ω)) (g := fun ω => armEIF e m false (armMean μ Y false) (obsData A Y W ω) *
      s (obsData A Y W ω)) (hI true) (hI false), ate_eq_armMean_sub (hYi true) (hYi false)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [ateEIF_eq_sub, sub_mul]

/-- **The efficiency bound of the average effect is the supremum of the submodel bounds**:
under the hypotheses of `hasDerivAt_regressionFunctional_ate`, square integrable potential
outcomes and `V = E[φ(O)²] > 0`, `V` is the least upper bound of the Cramér-Rao bounds of the
score submodels for `E[Y(1)] - E[Y(0)]`. -/
theorem isLUB_submodelBounds_ate (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hV : 0 < ∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ^ 2 ∂μ) :
    IsLUB {r | ∃ s, IsBoundedScore μ (obsData A Y W) s ∧
        0 < ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ ∧ ∃ d, HasDerivAt (fun t ↦
          regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
            (arm A true) W (obsOutcome A Y) -
          regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
            (arm A false) W (obsOutcome A Y)) d 0 ∧
        r = d ^ 2 / ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ}
      (∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ^ 2 ∂μ) := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  have hg := fun s (hs : IsBoundedScore μ (obsData A Y W) s) =>
    hasDerivAt_regressionFunctional_ate hW hA hY hYi hps hreg hmi hov hs
  have h2 : MemLp (fun ω => ateEIF e m (ate μ Y) (obsData A Y W ω)) 2 μ := by
    refine ((memLp_armEIF hW hA hY hY2 hps hreg true (hmi true) hov.1 (hpos true)
      (armMean μ Y true)).sub (memLp_armEIF hW hA hY hY2 hps hreg false (hmi false) hov.1
        (hpos false) (armMean μ Y false))).ae_eq (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, ate_eq_armMean_sub (hYi true) (hYi false), ateEIF_eq_sub]
  have hset : {r | ∃ s, IsBoundedScore μ (obsData A Y W) s ∧
        0 < ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ ∧ ∃ d, HasDerivAt (fun t ↦
          regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
            (arm A true) W (obsOutcome A Y) -
          regressionFunctional (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t)
            (arm A false) W (obsOutcome A Y)) d 0 ∧
        r = d ^ 2 / ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ} =
      submodelBounds μ (obsData A Y W) (ateEIF e m (ate μ Y)) := by
    ext r
    constructor
    · rintro ⟨s, hs, hI, d, hd, rfl⟩
      exact ⟨s, hs, hI, by rw [hd.unique (hg s hs)]⟩
    · rintro ⟨s, hs, hI, rfl⟩
      exact ⟨s, hs, hI, _, hg s hs, rfl⟩
  rw [hset]
  exact isLUB_submodelBounds (measurable_obsData hW hA hY) (measurable_ateEIF hps.1 hreg.1 _)
    h2 (integral_ateEIF_eq_zero hW hA hYi hps hreg hmi hov) hV

end Arm

end Efficiency
end CausalInference
