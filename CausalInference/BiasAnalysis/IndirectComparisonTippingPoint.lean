/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.AnchoredBias
public import CausalInference.PopulationAdjustment.OutcomeModelLinear
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Tipping points for an indirect comparison

A **tipping point** of a sensitivity analysis is the value of a bias parameter at which the
conclusion changes: the bias-adjusted estimate (or one of its confidence limits) reaches a
threshold `c`, usually the null. This file proves when tipping points exist, when they are
unique, and computes them for the bias of the anchored comparison caused by an imbalanced effect
modifier.

* **General curves.** For a continuous adjusted estimate `Δ(t)` with `Δ(0) > c` that reaches `c`
  somewhere on `[0, ∞)`, there is a least magnitude `t†` at which the conclusion `Δ > c` fails,
  and `Δ(t†) = c` (`exists_isLeast_tipping`). For a continuous strictly monotone curve on an
  interval the tipping point is unique when `c` lies between the endpoint values, and otherwise
  the conclusion holds or fails on the whole interval (`existsUnique_tipping`).
* **The anchored comparison on the linear predictor scale.** If the link of every arm mean is
  linear in the covariates, the bias of the anchored comparison is the sum over covariates of
  the mean differences between each trial and the target times the interaction coefficients
  (`anchored_bias_linear`, derived from `anchoredEstimand_sub_linkConditional`). When the
  adjusted covariates are balanced and one omitted covariate modifies the two active treatments
  equally, the target effect is the anchored comparison minus `D κ`, with `D` the difference of
  the omitted covariate's means between the two trials and `κ` its interaction coefficient
  (`linkConditional_eq_sub_omitted`).
* **The closed form.** For an estimate `θ > c` (a point estimate or the confidence limit nearest
  the null) and a bias `D κ`, the least imbalance `|D|` that moves `θ - D κ` to `c` is
  `(θ - c) / |κ|` (`isLeast_tipping_linear`); the tipping point `D† = (θ - c) / κ` is unique and
  the conclusion holds exactly on one side of it (`tipping_linear_iff`).
* **A simulated omitted covariate.** When the omitted covariate is simulated as `U(m) = Q m T`
  from a common uniform `T` (the normal to anything construction, `T = Φ(Z)`), with `Q m` the
  quantile function of the assumed law with parameter `m`, the adjusted marginal effect
  `simulatedEffect` is continuous and strictly monotone in `m`, with the direction of the
  outcome coefficient of `U`, whatever the direction of the link
  (`strictMonoOn_simulatedEffect`, `continuousOn_simulatedEffect`), so its tipping point is
  unique (`existsUnique_tipping_simulatedEffect`).

## Main definitions

* `simulatedEffect`: the marginal effect, on the scale `g`, of the predicted response with the
  simulated covariate, against a comparator mean.

-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace IndirectComparisonBias

open MeasureTheory Set Filter Topology EffectMeasure IndirectComparison PopulationAdjustment

/-! ### Tipping points of general curves -/

/-- **The least magnitude at which the conclusion fails.** Let the adjusted estimate `Δ` be
continuous on `[0, ∞)`, with the conclusion `Δ(0) > c` at no bias, and failing (`Δ(t) ≤ c`) for
some bias `t ≥ 0`. Then the set of magnitudes at which it fails has a least element `t†`; at
`t†` the adjusted estimate equals `c`, and the conclusion holds on `[0, t†)`. No monotonicity is
needed. -/
theorem exists_isLeast_tipping {Δ : ℝ → ℝ} {c : ℝ} (hΔ : ContinuousOn Δ (Ici 0))
    (h0 : c < Δ 0) (hfail : ∃ t, 0 ≤ t ∧ Δ t ≤ c) :
    ∃ t₀, IsLeast {t | 0 ≤ t ∧ Δ t ≤ c} t₀ ∧ Δ t₀ = c ∧ ∀ t, 0 ≤ t → t < t₀ → c < Δ t := by
  set S := {t | 0 ≤ t ∧ Δ t ≤ c} with hS
  have hSc : IsClosed S := by
    have := hΔ.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_Iic (a := c))
    convert this using 1
    ext t
    simp [hS]
  have hne : S.Nonempty := hfail
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set t₀ := sInf S with ht₀
  have hmem : t₀ ∈ S := hSc.csInf_mem hne hbdd
  have hleast : IsLeast S t₀ := ⟨hmem, fun t ht => csInf_le hbdd ht⟩
  have hbelow : ∀ t, 0 ≤ t → t < t₀ → c < Δ t := fun t ht htt =>
    not_le.1 fun h => absurd (hleast.2 ⟨ht, h⟩) (not_le.2 htt)
  refine ⟨t₀, hleast, le_antisymm hmem.2 ?_, hbelow⟩
  obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc' hmem.1
    (hΔ.mono fun x hx => (hx.1 : 0 ≤ x)) ⟨hmem.2, h0.le⟩
  have : t₀ ≤ s := hleast.2 ⟨hs.1, hsc.le⟩
  rw [← le_antisymm hs.2 this, hsc]

/-- **Existence and uniqueness of the tipping point for a monotone curve.** If `Δ` is continuous
and strictly monotone (in either direction) on `[lo, hi]`, then: when `c` lies between `Δ(lo)`
and `Δ(hi)` there is exactly one `t ∈ [lo, hi]` with `Δ(t) = c`; otherwise `Δ - c` has one
strict sign on the whole interval, and the conclusion does not change there. -/
theorem existsUnique_tipping {Δ : ℝ → ℝ} {lo hi c : ℝ} (hlh : lo ≤ hi)
    (hc : ContinuousOn Δ (Icc lo hi))
    (hm : StrictMonoOn Δ (Icc lo hi) ∨ StrictAntiOn Δ (Icc lo hi)) :
    (c ∈ uIcc (Δ lo) (Δ hi) → ∃! t, t ∈ Icc lo hi ∧ Δ t = c) ∧
      (c ∉ uIcc (Δ lo) (Δ hi) → (∀ t ∈ Icc lo hi, Δ t < c) ∨ (∀ t ∈ Icc lo hi, c < Δ t)) := by
  have hlo : lo ∈ Icc lo hi := ⟨le_rfl, hlh⟩
  have hhi : hi ∈ Icc lo hi := ⟨hlh, le_rfl⟩
  have hinj : InjOn Δ (Icc lo hi) := hm.elim StrictMonoOn.injOn StrictAntiOn.injOn
  have hbetween : ∀ t ∈ Icc lo hi, Δ t ∈ uIcc (Δ lo) (Δ hi) := fun t ht => by
    rcases hm with hm | hm
    · exact mem_uIcc.2 (Or.inl ⟨hm.monotoneOn hlo ht ht.1, hm.monotoneOn ht hhi ht.2⟩)
    · exact mem_uIcc.2 (Or.inr ⟨hm.antitoneOn ht hhi ht.2, hm.antitoneOn hlo ht ht.1⟩)
  refine ⟨fun hcm => ?_, fun hcm => ?_⟩
  · rw [← uIcc_of_le hlh] at hc
    obtain ⟨t, ht, htc⟩ := intermediate_value_uIcc hc hcm
    rw [uIcc_of_le hlh] at ht
    exact ⟨t, ⟨ht, htc⟩, fun t' ht' => hinj ht'.1 ht (ht'.2.trans htc.symm)⟩
  · rw [uIcc, mem_Icc, not_and_or, not_le, not_le] at hcm
    rcases hcm with hcm | hcm
    · exact Or.inr fun t ht => hcm.trans_le (hbetween t ht).1
    · exact Or.inl fun t ht => (hbetween t ht).2.trans_lt hcm

/-! ### The anchored comparison on the linear predictor scale -/

section Linear

variable {p : ℕ} {g : ℝ → ℝ} {ma mb mc : (Fin p → ℝ) → ℝ}

/-- On the linear predictor scale the conditional effect of `c` relative to `a` is linear:
if `g(m_a(x)) = α_a + ∑ⱼ xⱼ β_{a,j}` and `g(m_c(x)) = α_c + ∑ⱼ xⱼ β_{c,j}`, then
`τ_ac(x) = (α_c - α_a) + ∑ⱼ xⱼ (β_{c,j} - β_{a,j})`. -/
theorem linkContrast_linear {αa αc : ℝ} {βa βc : Fin p → ℝ}
    (hma : ∀ x, g (ma x) = αa + ∑ j, x j * βa j) (hmc : ∀ x, g (mc x) = αc + ∑ j, x j * βc j)
    (x : Fin p → ℝ) :
    linkContrast g ma mc x = (αc - αa) + ∑ j, x j * (βc j - βa j) := by
  simp only [linkContrast, hma, hmc, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Under a probability covariate law with integrable coordinates, a linear conditional effect is
integrable and averages to its value at the mean covariates. -/
theorem integral_linkContrast_linear {ν : Measure (Fin p → ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) ν) {αa αc : ℝ} {βa βc : Fin p → ℝ}
    (hma : ∀ x, g (ma x) = αa + ∑ j, x j * βa j) (hmc : ∀ x, g (mc x) = αc + ∑ j, x j * βc j) :
    Integrable (linkContrast g ma mc) ν ∧
      ∫ x, linkContrast g ma mc x ∂ν = (αc - αa) + ∑ j, covMean ν j * (βc j - βa j) := by
  have hf : linkContrast g ma mc = fun x => (αc - αa) + ∑ j, x j * (βc j - βa j) :=
    funext (linkContrast_linear hma hmc)
  rw [hf]
  refine ⟨(integrable_const _).add (integrable_sum_mul hν _), ?_⟩
  rw [integral_add (integrable_const _) (integrable_sum_mul hν _), integral_const,
    integral_sum_mul hν]
  simp

/-- **The bias of the anchored comparison on the linear predictor scale.** Let the link of each
arm mean be linear in the covariates, `g(m_t(x)) = α_t + ∑ⱼ xⱼ β_{t,j}` for `t = a, b, c`, and
let the covariate laws `P_ac`, `P_bc` of the two trials and `P_*` of the target be probability
laws with integrable coordinates. Then the anchored comparison `∫ τ_ac dP_ac - ∫ τ_bc dP_bc`
minus the target average conditional effect of `b` relative to `a` is
`∑ⱼ (x̄_ac,j - x̄_*,j)(β_{c,j} - β_{a,j}) - ∑ⱼ (x̄_bc,j - x̄_*,j)(β_{c,j} - β_{b,j})`: mean
imbalances against the target times interaction coefficients. -/
theorem anchored_bias_linear {Pac Pbc Pt : Measure (Fin p → ℝ)} [IsProbabilityMeasure Pac]
    [IsProbabilityMeasure Pbc] [IsProbabilityMeasure Pt]
    (hac : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Pac)
    (hbc : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Pbc)
    (ht : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Pt) {αa αb αc : ℝ} {βa βb βc : Fin p → ℝ}
    (hma : ∀ x, g (ma x) = αa + ∑ j, x j * βa j) (hmb : ∀ x, g (mb x) = αb + ∑ j, x j * βb j)
    (hmc : ∀ x, g (mc x) = αc + ∑ j, x j * βc j) :
    (∫ x, linkContrast g ma mc x ∂Pac - ∫ x, linkContrast g mb mc x ∂Pbc) -
        linkConditional g Pt ma mb =
      ∑ j, (covMean Pac j - covMean Pt j) * (βc j - βa j) -
        ∑ j, (covMean Pbc j - covMean Pt j) * (βc j - βb j) := by
  obtain ⟨iac, eac⟩ := integral_linkContrast_linear hac hma hmc
  obtain ⟨ibc, ebc⟩ := integral_linkContrast_linear hbc hmb hmc
  obtain ⟨iact, eact⟩ := integral_linkContrast_linear ht hma hmc
  obtain ⟨ibct, ebct⟩ := integral_linkContrast_linear ht hmb hmc
  rw [anchoredEstimand_sub_linkConditional iac ibc iact ibct, eac, ebc, eact, ebct]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- **One omitted effect modifier.** In the setting of `anchored_bias_linear`, suppose every
covariate other than `j₀` has the same mean in both trials as in the target (the adjusted
covariates are balanced), and the covariate `j₀`, omitted from the adjustment, modifies the two
active treatments equally relative to `c` (`β_{a,j₀} = β_{b,j₀}`). Then the target effect is the
anchored comparison minus `D κ`, where `D = x̄_ac,j₀ - x̄_bc,j₀` is the difference of the means of
the omitted covariate between the two trials and `κ = β_{c,j₀} - β_{a,j₀}` its interaction
coefficient; the target mean of `j₀` does not enter. -/
theorem linkConditional_eq_sub_omitted {Pac Pbc Pt : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure Pac] [IsProbabilityMeasure Pbc] [IsProbabilityMeasure Pt]
    (hac : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Pac)
    (hbc : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Pbc)
    (ht : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Pt) {αa αb αc : ℝ} {βa βb βc : Fin p → ℝ}
    (hma : ∀ x, g (ma x) = αa + ∑ j, x j * βa j) (hmb : ∀ x, g (mb x) = αb + ∑ j, x j * βb j)
    (hmc : ∀ x, g (mc x) = αc + ∑ j, x j * βc j) {j₀ : Fin p}
    (hbal : ∀ j, j ≠ j₀ → covMean Pac j = covMean Pt j ∧ covMean Pbc j = covMean Pt j)
    (hshared : βa j₀ = βb j₀) :
    linkConditional g Pt ma mb =
      (∫ x, linkContrast g ma mc x ∂Pac - ∫ x, linkContrast g mb mc x ∂Pbc) -
        (covMean Pac j₀ - covMean Pbc j₀) * (βc j₀ - βa j₀) := by
  have h := anchored_bias_linear hac hbc ht hma hmb hmc
  have e₁ : ∑ j, (covMean Pac j - covMean Pt j) * (βc j - βa j) =
      (covMean Pac j₀ - covMean Pt j₀) * (βc j₀ - βa j₀) :=
    Finset.sum_eq_single j₀ (fun j _ hj => by rw [(hbal j hj).1, sub_self, zero_mul])
      (by simp)
  have e₂ : ∑ j, (covMean Pbc j - covMean Pt j) * (βc j - βb j) =
      (covMean Pbc j₀ - covMean Pt j₀) * (βc j₀ - βa j₀) := by
    rw [hshared]
    exact Finset.sum_eq_single j₀ (fun j _ hj => by rw [(hbal j hj).2, sub_self, zero_mul])
      (by simp)
  rw [e₁, e₂] at h
  linarith

end Linear

/-! ### The closed form for a linear bias -/

/-- **The least imbalance that changes the conclusion.** For an estimate `θ > c` (the point
estimate, or the confidence limit nearest the null when the conclusion is that this limit lies
beyond `c`) and a bias `D κ` with interaction coefficient `κ ≠ 0`, the least `|D|` for which
the adjusted value `θ - D κ` is at most `c` is `(θ - c) / |κ|`. -/
theorem isLeast_tipping_linear {θ c κ : ℝ} (hθ : c < θ) (hκ : κ ≠ 0) :
    IsLeast {s | 0 ≤ s ∧ ∃ D, |D| = s ∧ θ - D * κ ≤ c} ((θ - c) / |κ|) := by
  have hk : 0 < |κ| := abs_pos.2 hκ
  refine ⟨⟨div_nonneg (by linarith) hk.le, (θ - c) / κ, ?_, ?_⟩, ?_⟩
  · rw [abs_div, abs_of_pos (by linarith : 0 < θ - c)]
  · rw [div_mul_cancel₀ _ hκ]; linarith
  · rintro s ⟨hs, D, rfl, hD⟩
    rw [div_le_iff₀ hk]
    have : D * κ ≤ |D| * |κ| := by rw [← abs_mul]; exact le_abs_self _
    linarith

/-- **The tipping point of a linear bias is unique and separates the two conclusions.** For
`κ > 0` the adjusted value `θ - D κ` is strictly decreasing in `D`, equals `c` exactly at
`D† = (θ - c) / κ`, and exceeds `c` exactly when `D < D†`. -/
theorem tipping_linear {θ c κ : ℝ} (hκ : 0 < κ) :
    StrictAnti (fun D => θ - D * κ) ∧ (∀ D, θ - D * κ = c ↔ D = (θ - c) / κ) ∧
      (∀ D, c < θ - D * κ ↔ D < (θ - c) / κ) := by
  refine ⟨fun D D' h => by nlinarith, fun D => ?_, fun D => ?_⟩
  · rw [eq_div_iff hκ.ne']; constructor <;> intro h <;> linarith
  · rw [lt_div_iff₀ hκ]; constructor <;> intro h <;> linarith


/-! ### A simulated omitted covariate -/

section Simulated

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The **adjusted marginal effect with a simulated omitted covariate.** On a probability space
`(Ω, P)`, `η ω` is the measured part of the linear predictor of the outcome model, `T` a uniform
draw on `(0, 1)` (for instance `Φ(Z)` with `Z` standard normal), `Q m t` the quantile function at
`t` of the assumed law of the omitted covariate with parameter `m`, so `U(m) = Q m T`, and
`β_U` its coefficient. The predicted response is `ginv(η + β_U U(m))` with inverse link `ginv`,
and the effect is its marginal effect on the scale `g` against a comparator mean `μ₀`:
`g(∫ ginv(η + β_U U(m)) dP) - g(μ₀)`, written with `linkMarginal`. -/
noncomputable def simulatedEffect (P : Measure Ω) (g ginv : ℝ → ℝ) (η : Ω → ℝ) (βU : ℝ)
    (Q : ℝ → ℝ → ℝ) (T : Ω → ℝ) (μ₀ m : ℝ) : ℝ :=
  linkMarginal g P (fun _ => μ₀) (fun ω => ginv (η ω + βU * Q m (T ω)))

/-- For a probability space the comparator term of `simulatedEffect` is `g(μ₀)`. -/
theorem simulatedEffect_eq [IsProbabilityMeasure P] (g ginv : ℝ → ℝ) (η : Ω → ℝ) (βU : ℝ)
    (Q : ℝ → ℝ → ℝ) (T : Ω → ℝ) (μ₀ m : ℝ) :
    simulatedEffect P g ginv η βU Q T μ₀ m =
      g (∫ ω, ginv (η ω + βU * Q m (T ω)) ∂P) - g μ₀ := by
  simp [simulatedEffect, linkMarginal]

/-- Under the common quantile coupling, the mean of a function of `U(m)` that is almost surely
strictly increasing along the coupled values is strictly increasing in `m`: `U(m) ≤ U(m')`
pointwise for `m ≤ m'`, with strict inequality on a set of positive probability. -/
theorem strictMonoOn_integral_coupling {φ : Ω → ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {T : Ω → ℝ}
    {J : Set ℝ}
    (hφ : ∀ m ∈ J, ∀ m' ∈ J, ∀ᵐ ω ∂P,
      Q m (T ω) < Q m' (T ω) → φ ω (Q m (T ω)) < φ ω (Q m' (T ω)))
    (hint : ∀ m ∈ J, Integrable (fun ω => φ ω (Q m (T ω))) P)
    (hT : ∀ᵐ ω ∂P, T ω ∈ Ioo (0 : ℝ) 1) (hQ : ∀ t ∈ Ioo (0 : ℝ) 1, Monotone fun m => Q m t)
    (hstrict : ∀ m ∈ J, ∀ m' ∈ J, m < m' → P {ω | Q m (T ω) < Q m' (T ω)} ≠ 0) :
    StrictMonoOn (fun m => ∫ ω, φ ω (Q m (T ω)) ∂P) J := by
  intro m hm m' hm' hmm
  have hle : ∀ᵐ ω ∂P, 0 ≤ φ ω (Q m' (T ω)) - φ ω (Q m (T ω)) := by
    filter_upwards [hT, hφ m hm m' hm'] with ω hω hφω
    rcases (hQ _ hω hmm.le).lt_or_eq with h | h
    · exact sub_nonneg.2 (hφω h).le
    · change Q m (T ω) = Q m' (T ω) at h
      rw [h, sub_self]
  have hpos : 0 < ∫ ω, (φ ω (Q m' (T ω)) - φ ω (Q m (T ω))) ∂P := by
    rw [integral_pos_iff_support_of_nonneg_ae hle ((hint m' hm').sub (hint m hm))]
    refine pos_iff_ne_zero.2 fun h0 => hstrict m hm m' hm' hmm
      (measure_mono_null ?_ (measure_union_null h0 (ae_iff.1 (hφ m hm m' hm'))))
    intro ω (hω : Q m (T ω) < Q m' (T ω))
    by_cases hc : φ ω (Q m (T ω)) < φ ω (Q m' (T ω))
    · exact Or.inl (Function.mem_support.2 (sub_pos.2 hc).ne')
    · exact Or.inr fun h => hc (h hω)
  rw [integral_sub (hint m' hm') (hint m hm)] at hpos
  exact sub_pos.1 hpos

/-- **Monotonicity of the simulated effect.** Assume the common quantile coupling (`T ∈ (0, 1)`
almost surely, `Q m t` nondecreasing in `m`, and `P{U(m) < U(m')} > 0` for `m < m'` in the
parameter set `J`), an integrable envelope `G` of the predicted responses on `J`, an inverse link
`ginv` strictly monotone on a set `D` containing the predictors almost surely, and a link `g`
strictly monotone in the same direction on a set `I` containing every marginal mean. Then the
simulated effect is strictly increasing on `J` if `β_U > 0` and strictly decreasing if
`β_U < 0`, whatever the direction of the link. -/
theorem strictMonoOn_simulatedEffect {g ginv : ℝ → ℝ} {η : Ω → ℝ} {βU μ₀ : ℝ}
    {Q : ℝ → ℝ → ℝ} {T : Ω → ℝ} {J I D : Set ℝ} {G : Ω → ℝ}
    (hT : ∀ᵐ ω ∂P, T ω ∈ Ioo (0 : ℝ) 1) (hQ : ∀ t ∈ Ioo (0 : ℝ) 1, Monotone fun m => Q m t)
    (hstrict : ∀ m ∈ J, ∀ m' ∈ J, m < m' → P {ω | Q m (T ω) < Q m' (T ω)} ≠ 0)
    (hdir : (StrictMonoOn ginv D ∧ StrictMonoOn g I) ∨ (StrictAntiOn ginv D ∧ StrictAntiOn g I))
    (hD : ∀ m ∈ J, ∀ᵐ ω ∂P, η ω + βU * Q m (T ω) ∈ D)
    (hmeas : ∀ m ∈ J, AEStronglyMeasurable (fun ω => ginv (η ω + βU * Q m (T ω))) P)
    (hG : Integrable G P) (hbound : ∀ m ∈ J, ∀ᵐ ω ∂P, ‖ginv (η ω + βU * Q m (T ω))‖ ≤ G ω)
    (hI : ∀ m ∈ J, ∫ ω, ginv (η ω + βU * Q m (T ω)) ∂P ∈ I) :
    (0 < βU → StrictMonoOn (simulatedEffect P g ginv η βU Q T μ₀) J) ∧
      (βU < 0 → StrictAntiOn (simulatedEffect P g ginv η βU Q T μ₀) J) := by
  set φ : Ω → ℝ → ℝ := fun ω u => ginv (η ω + βU * u)
  set M : ℝ → ℝ := fun m => ∫ ω, φ ω (Q m (T ω)) ∂P with hM
  have hint : ∀ m ∈ J, Integrable (fun ω => φ ω (Q m (T ω))) P := fun m hm =>
    hG.mono' (hmeas m hm) (hbound m hm)
  have hMmono : (∀ m ∈ J, ∀ m' ∈ J, ∀ᵐ ω ∂P,
      Q m (T ω) < Q m' (T ω) → φ ω (Q m (T ω)) < φ ω (Q m' (T ω))) → StrictMonoOn M J :=
    fun h => strictMonoOn_integral_coupling h hint hT hQ hstrict
  have hManti : (∀ m ∈ J, ∀ m' ∈ J, ∀ᵐ ω ∂P,
      Q m (T ω) < Q m' (T ω) → φ ω (Q m' (T ω)) < φ ω (Q m (T ω))) → StrictAntiOn M J := by
    intro h
    have h' := strictMonoOn_integral_coupling (φ := fun ω u => -φ ω u)
      (fun m hm m' hm' => (h m hm m' hm').mono fun ω hω huv => neg_lt_neg (hω huv))
      (fun m hm => (hint m hm).neg) hT hQ hstrict
    intro a ha b hb hab
    have := h' ha hb hab
    simp only [integral_neg, neg_lt_neg_iff] at this
    exact this
  have hlt : ∀ (c u v : ℝ), u < v → 0 < βU → c + βU * u < c + βU * v := fun c u v huv hb => by
    nlinarith
  have hgt : ∀ (c u v : ℝ), u < v → βU < 0 → c + βU * v < c + βU * u := fun c u v huv hb => by
    nlinarith
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · intro a ha b hb' hab
    change g (M a) - g (∫ _, μ₀ ∂P) < g (M b) - g (∫ _, μ₀ ∂P)
    rcases hdir with ⟨hgi, hg⟩ | ⟨hgi, hg⟩
    · have := hMmono (fun m hm m' hm' => by
        filter_upwards [hD m hm, hD m' hm'] with ω h1 h2 huv
        exact hgi h1 h2 (hlt _ _ _ huv hb)) ha hb' hab
      linarith [hg (hI a ha) (hI b hb') this]
    · have := hManti (fun m hm m' hm' => by
        filter_upwards [hD m hm, hD m' hm'] with ω h1 h2 huv
        exact hgi h1 h2 (hlt _ _ _ huv hb)) ha hb' hab
      linarith [hg (hI b hb') (hI a ha) this]
  · intro a ha b hb' hab
    change g (M b) - g (∫ _, μ₀ ∂P) < g (M a) - g (∫ _, μ₀ ∂P)
    rcases hdir with ⟨hgi, hg⟩ | ⟨hgi, hg⟩
    · have := hManti (fun m hm m' hm' => by
        filter_upwards [hD m hm, hD m' hm'] with ω h1 h2 huv
        exact hgi h2 h1 (hgt _ _ _ huv hb)) ha hb' hab
      linarith [hg (hI b hb') (hI a ha) this]
    · have := hMmono (fun m hm m' hm' => by
        filter_upwards [hD m hm, hD m' hm'] with ω h1 h2 huv
        exact hgi h2 h1 (hgt _ _ _ huv hb)) ha hb' hab
      linarith [hg (hI a ha) (hI b hb') this]

/-- **Continuity of the simulated effect.** If `U(mₙ) → U(m)` almost surely along every sequence
`mₙ → m` in `J`, the inverse link is continuous on a set `D` containing the predictors almost
surely, the predicted responses have an integrable envelope, and `g` is continuous on a set `I`
containing the marginal means, then the simulated effect is continuous on `J` (dominated
convergence). -/
theorem continuousOn_simulatedEffect {g ginv : ℝ → ℝ} {η : Ω → ℝ} {βU μ₀ : ℝ}
    {Q : ℝ → ℝ → ℝ} {T : Ω → ℝ} {J I D : Set ℝ} {G : Ω → ℝ}
    (hginv : ContinuousOn ginv D) (hg : ContinuousOn g I)
    (hD : ∀ m ∈ J, ∀ᵐ ω ∂P, η ω + βU * Q m (T ω) ∈ D)
    (hconv : ∀ m ∈ J, ∀ x : ℕ → ℝ, Tendsto x atTop (𝓝[J] m) →
      ∀ᵐ ω ∂P, Tendsto (fun n => Q (x n) (T ω)) atTop (𝓝 (Q m (T ω))))
    (hmeas : ∀ m ∈ J, AEStronglyMeasurable (fun ω => ginv (η ω + βU * Q m (T ω))) P)
    (hG : Integrable G P) (hbound : ∀ m ∈ J, ∀ᵐ ω ∂P, ‖ginv (η ω + βU * Q m (T ω))‖ ≤ G ω)
    (hI : ∀ m ∈ J, ∫ ω, ginv (η ω + βU * Q m (T ω)) ∂P ∈ I) :
    ContinuousOn (simulatedEffect P g ginv η βU Q T μ₀) J := by
  set M : ℝ → ℝ := fun m => ∫ ω, ginv (η ω + βU * Q m (T ω)) ∂P
  have hMc : ContinuousOn M J := fun m hm => by
    refine tendsto_iff_seq_tendsto.2 fun x hx => ?_
    obtain ⟨-, hxJ⟩ := tendsto_nhdsWithin_iff.1 hx
    have hall : ∀ᵐ ω ∂P, ∀ n, x n ∈ J → η ω + βU * Q (x n) (T ω) ∈ D := by
      refine ae_all_iff.2 fun n => ?_
      by_cases hn : x n ∈ J
      · filter_upwards [hD _ hn] with ω h _ using h
      · exact ae_of_all _ fun ω h => absurd h hn
    refine tendsto_integral_filter_of_dominated_convergence G
      (hxJ.mono fun n hn => hmeas (x n) hn) (hxJ.mono fun n hn => hbound (x n) hn) hG ?_
    filter_upwards [hconv m hm x hx, hD m hm, hall] with ω hω hDm hDn
    refine (hginv _ hDm).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.add (tendsto_const_nhds.mul hω), hxJ.mono fun n hn => hDn n hn⟩)
  exact (hg.comp hMc hI).sub continuousOn_const

/-- **The tipping point of the simulated effect.** Under the hypotheses of
`strictMonoOn_simulatedEffect` and `continuousOn_simulatedEffect` on `J = [lo, hi]` with
`β_U ≠ 0`: if `c` lies between the simulated effects at `lo` and `hi`, exactly one parameter
`m ∈ [lo, hi]` gives the effect `c`; otherwise the effect minus `c` keeps one strict sign on
`[lo, hi]`, and the conclusion is the same over the whole assumed range. -/
theorem existsUnique_tipping_simulatedEffect {g ginv : ℝ → ℝ} {η : Ω → ℝ} {βU μ₀ c lo hi : ℝ}
    {Q : ℝ → ℝ → ℝ} {T : Ω → ℝ} {I D : Set ℝ} {G : Ω → ℝ} (hlh : lo ≤ hi) (hβ : βU ≠ 0)
    (hT : ∀ᵐ ω ∂P, T ω ∈ Ioo (0 : ℝ) 1) (hQ : ∀ t ∈ Ioo (0 : ℝ) 1, Monotone fun m => Q m t)
    (hstrict : ∀ m ∈ Icc lo hi, ∀ m' ∈ Icc lo hi, m < m' →
      P {ω | Q m (T ω) < Q m' (T ω)} ≠ 0)
    (hdir : (StrictMonoOn ginv D ∧ StrictMonoOn g I) ∨ (StrictAntiOn ginv D ∧ StrictAntiOn g I))
    (hginv : ContinuousOn ginv D) (hg : ContinuousOn g I)
    (hD : ∀ m ∈ Icc lo hi, ∀ᵐ ω ∂P, η ω + βU * Q m (T ω) ∈ D)
    (hconv : ∀ m ∈ Icc lo hi, ∀ x : ℕ → ℝ, Tendsto x atTop (𝓝[Icc lo hi] m) →
      ∀ᵐ ω ∂P, Tendsto (fun n => Q (x n) (T ω)) atTop (𝓝 (Q m (T ω))))
    (hmeas : ∀ m ∈ Icc lo hi,
      AEStronglyMeasurable (fun ω => ginv (η ω + βU * Q m (T ω))) P)
    (hG : Integrable G P)
    (hbound : ∀ m ∈ Icc lo hi, ∀ᵐ ω ∂P, ‖ginv (η ω + βU * Q m (T ω))‖ ≤ G ω)
    (hI : ∀ m ∈ Icc lo hi, ∫ ω, ginv (η ω + βU * Q m (T ω)) ∂P ∈ I) :
    let Δ := simulatedEffect P g ginv η βU Q T μ₀
    (c ∈ uIcc (Δ lo) (Δ hi) → ∃! m, m ∈ Icc lo hi ∧ Δ m = c) ∧
      (c ∉ uIcc (Δ lo) (Δ hi) → (∀ m ∈ Icc lo hi, Δ m < c) ∨ (∀ m ∈ Icc lo hi, c < Δ m)) := by
  intro Δ
  have hmono := strictMonoOn_simulatedEffect (μ₀ := μ₀) hT hQ hstrict hdir hD hmeas hG hbound hI
  have hcont := continuousOn_simulatedEffect (μ₀ := μ₀) hginv hg hD hconv hmeas hG hbound hI
  refine existsUnique_tipping hlh hcont ?_
  rcases hβ.lt_or_gt with h | h
  · exact Or.inr (hmono.2 h)
  · exact Or.inl (hmono.1 h)

end Simulated

end IndirectComparisonBias

end BiasAnalysis

end CausalInference
