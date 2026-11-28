/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MaximumLikelihood
public import CausalInference.Estimation.BernoulliPair

/-!
# Invariance of the maximum likelihood estimator and the profile likelihood

If the family `f(·; θ)`, `θ ∈ K`, is reparametrized as `η ↦ f(·; g η)`, `η ∈ H`, by a map `g`
from `H` onto `K` with a right inverse `h` on `K` (`g (h θ) = θ`), then `h` of a maximum
likelihood estimator of `θ` is a maximum likelihood estimator of `η`: maximum likelihood
estimation commutes with reparametrization. Conversely, `g` of a maximum likelihood estimator
of `η` is one of `θ`.

For a parameter of interest `τ(θ)`, the profile likelihood is
`L_p(ψ) = sup {L(θ) | θ ∈ K, τ θ = ψ}`; at a maximum likelihood estimator `θ̂`, `τ θ̂` maximizes
the profile likelihood over `τ '' K` and `L_p(τ θ̂) = L(θ̂)`. The supremum is taken only over
nonempty sets bounded above by `L(θ̂)`, so no default value of `sSup` enters.

## Main definitions

* `CausalInference.ParametricFamily.reparam`: the reparametrized family `η ↦ f(·; g η)`.
* `CausalInference.ParametricFamily.profileLikelihood`: the profile likelihood.

## Main results

* `CausalInference.ParametricFamily.IsMLE.reparam`: invariance of the maximum likelihood
  estimator.
* `CausalInference.ParametricFamily.IsMLE.of_reparam`: the converse.
* `CausalInference.ParametricFamily.IsMLE.profileLikelihood`: the profile likelihood is
  maximized at `τ θ̂` with maximum `L(θ̂)`.
* Instances: the maximum likelihood estimator of `√p` for a Bernoulli sample
  (`bernoulli_isMLE_sqrt`) and the profile likelihood of the first success probability of a pair
  (`bernoulliPair_profileLikelihood`).

References: P. W. Zehna (1966), *Invariance of maximum likelihood estimators*, Annals of
Mathematical Statistics; Y. Pawitan (2001), *In All Likelihood*, chapter 3.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace ParametricFamily

variable {P Q S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- The reparametrized family `η ↦ f(·; g η)` on the parameter set `H`, for `g` mapping `H`
into the parameter set of `F`. -/
noncomputable def reparam (F : ParametricFamily P S) (g : Q → P) (H : Set Q)
    (hg : Set.MapsTo g H F.Θ) : ParametricFamily Q S where
  ν := F.ν
  Θ := H
  density η := F.density (g η)
  measurable_density η := F.measurable_density (g η)
  density_nonneg η hη := F.density_nonneg (g η) (hg hη)
  integrable_density η hη := F.integrable_density (g η) (hg hη)
  integral_density η hη := F.integral_density (g η) (hg hη)

variable {F : ParametricFamily P S} {g : Q → P} {H : Set Q} {hg : Set.MapsTo g H F.Θ}

omit [MeasurableSpace Ω] in
/-- The likelihood of the reparametrized family at `η` is the likelihood at `g η`. -/
@[simp]
theorem likelihood_reparam (O : ℕ → Ω → S) (n : ℕ) (ω : Ω) (η : Q) :
    (F.reparam g H hg).likelihood O n ω η = F.likelihood O n ω (g η) := rfl

/-- **Invariance of the maximum likelihood estimator.** Let `g` map `H` into `K` and let `h`
be a right inverse of `g` on `K` with values in `H` (so `g` maps `H` onto `K`). If `θ̂` is a
maximum likelihood estimator over `K`, then `h θ̂` is a maximum likelihood estimator of the
reparametrized family over `H`. -/
theorem IsMLE.reparam {μ : Measure Ω} {K : Set P} {O : ℕ → Ω → S} {θh : ℕ → Ω → P}
    (hmle : F.IsMLE μ K O θh) (hgK : Set.MapsTo g H K) {h : P → Q}
    (hh : ∀ θ ∈ K, h θ ∈ H ∧ g (h θ) = θ) :
    (F.reparam g H hg).IsMLE μ H O (fun n ω ↦ h (θh n ω)) := by
  intro n
  filter_upwards [hmle n] with ω ⟨hK, hmax⟩
  refine ⟨(hh _ hK).1, fun η hη ↦ ?_⟩
  rw [likelihood_reparam, likelihood_reparam, (hh _ hK).2]
  exact hmax (g η) (hgK hη)

/-- **The converse.** If `g` maps `H` onto `K` and `η̂` is a maximum likelihood estimator of the
reparametrized family over `H`, then `g η̂` is a maximum likelihood estimator over `K`. -/
theorem IsMLE.of_reparam {μ : Measure Ω} {K : Set P} {O : ℕ → Ω → S} {ηh : ℕ → Ω → Q}
    (hmle : (F.reparam g H hg).IsMLE μ H O ηh) (hgK : Set.MapsTo g H K)
    (hsurj : Set.SurjOn g H K) :
    F.IsMLE μ K O (fun n ω ↦ g (ηh n ω)) := by
  intro n
  filter_upwards [hmle n] with ω ⟨hH, hmax⟩
  refine ⟨hgK hH, fun θ hθ ↦ ?_⟩
  obtain ⟨η, hη, rfl⟩ := hsurj hθ
  exact hmax η hη

/-- The profile likelihood `L_p(ψ) = sup {L(θ) | θ ∈ K, τ θ = ψ}` of a parameter of interest
`τ`. -/
noncomputable def profileLikelihood (F : ParametricFamily P S) (O : ℕ → Ω → S) (n : ℕ) (ω : Ω)
    (K : Set P) (τ : P → Q) (ψ : Q) : ℝ :=
  sSup (F.likelihood O n ω '' {θ | θ ∈ K ∧ τ θ = ψ})

/-- **The profile likelihood at a maximum likelihood estimator.** If `θ̂` is a maximum likelihood
estimator over `K`, then almost surely `L_p(τ θ̂) = L(θ̂)` and `τ θ̂` maximizes the profile
likelihood over `τ '' K`. -/
theorem IsMLE.profileLikelihood {μ : Measure Ω} {K : Set P} {O : ℕ → Ω → S}
    {θh : ℕ → Ω → P} (hmle : F.IsMLE μ K O θh) (τ : P → Q) (n : ℕ) :
    ∀ᵐ ω ∂μ, F.profileLikelihood O n ω K τ (τ (θh n ω)) = F.likelihood O n ω (θh n ω) ∧
      ∀ ψ ∈ τ '' K, F.profileLikelihood O n ω K τ ψ ≤
        F.profileLikelihood O n ω K τ (τ (θh n ω)) := by
  filter_upwards [hmle n] with ω ⟨hK, hmax⟩
  have hbdd : ∀ ψ, BddAbove (F.likelihood O n ω '' {θ | θ ∈ K ∧ τ θ = ψ}) := fun ψ ↦
    ⟨F.likelihood O n ω (θh n ω), by
      rintro _ ⟨θ, ⟨hθ, -⟩, rfl⟩
      exact hmax θ hθ⟩
  have hle : ∀ ψ ∈ τ '' K, F.profileLikelihood O n ω K τ ψ ≤ F.likelihood O n ω (θh n ω) := by
    rintro ψ ⟨θ₁, hθ₁, rfl⟩
    refine csSup_le ⟨_, θ₁, ⟨hθ₁, rfl⟩, rfl⟩ ?_
    rintro _ ⟨θ, ⟨hθ, -⟩, rfl⟩
    exact hmax θ hθ
  have heq : F.profileLikelihood O n ω K τ (τ (θh n ω)) = F.likelihood O n ω (θh n ω) :=
    le_antisymm (hle _ ⟨_, hK, rfl⟩) (le_csSup (hbdd _) ⟨θh n ω, ⟨hK, rfl⟩, rfl⟩)
  exact ⟨heq, fun ψ hψ ↦ heq ▸ hle ψ hψ⟩

/-! ### Instances -/

omit [MeasurableSpace S] [MeasurableSpace Ω] in
/-- Squaring maps `[√ε, √(1 - ε)]` into `[ε, 1 - ε]`. -/
theorem sq_mem_Icc_of_mem_Icc_sqrt {ε η : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hη : η ∈ Set.Icc √ε √(1 - ε)) : η ^ 2 ∈ Set.Icc ε (1 - ε) := by
  have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg ε) hη.1 2
  have h2 := pow_le_pow_left₀ ((Real.sqrt_nonneg ε).trans hη.1) hη.2 2
  rw [Real.sq_sqrt hε.le] at h1
  rw [Real.sq_sqrt (by linarith)] at h2
  exact ⟨h1, h2⟩

/-- The Bernoulli family reparametrized by `η = √p`, `p = η²`, on
`[√ε, √(1 - ε)]`. -/
noncomputable def bernoulliSqrt {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ParametricFamily ℝ Bool :=
  bernoulli.reparam (fun η ↦ η ^ 2) (Set.Icc √ε √(1 - ε)) fun _ hη ↦
    Icc_subset_bernoulli_Θ hε (sq_mem_Icc_of_mem_Icc_sqrt hε hε2 hη)

/-- **The maximum likelihood estimator of `√p`** for a Bernoulli sample is the square root of the
clipped sample mean, by invariance. -/
theorem bernoulli_isMLE_sqrt {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (μ : Measure Ω)
    (O : ℕ → Ω → Bool) :
    (bernoulliSqrt hε hε2).IsMLE μ (Set.Icc √ε √(1 - ε)) O
      (fun n ω ↦ √(max ε (min (1 - ε) (sampleMean successIndicator O n ω)))) := by
  exact (bernoulli_isMLE hε hε2 μ O).reparam (h := Real.sqrt)
    (fun _ hη ↦ sq_mem_Icc_of_mem_Icc_sqrt hε hε2 hη) fun θ hθ ↦
      ⟨⟨Real.sqrt_le_sqrt hθ.1, Real.sqrt_le_sqrt hθ.2⟩, Real.sq_sqrt (hε.le.trans hθ.1)⟩

omit [MeasurableSpace Ω] in
/-- The likelihood of the pair factors into the likelihoods of the two coordinates. -/
theorem bernoulliPair_likelihood (O : ℕ → Ω → Bool × Bool) (n : ℕ) (ω : Ω) (θ : Fin 2 → ℝ) :
    bernoulliPair.likelihood O n ω θ =
      bernoulli.likelihood (fun i ω ↦ (O i ω).1) n ω (θ 0) *
        bernoulli.likelihood (fun i ω ↦ (O i ω).2) n ω (θ 1) := by
  simp only [likelihood, bernoulliPair_density, Finset.prod_mul_distrib]

/-- The pair of clipped coordinate sample means is a maximum likelihood estimator of the pair
over `[ε, 1 - ε]²`. -/
theorem bernoulliPair_isMLE {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (μ : Measure Ω)
    (O : ℕ → Ω → Bool × Bool) :
    bernoulliPair.IsMLE μ {θ | θ 0 ∈ Set.Icc ε (1 - ε) ∧ θ 1 ∈ Set.Icc ε (1 - ε)} O
      (fun n ω ↦ ![max ε (min (1 - ε) (sampleMean successIndicator (fun i ω ↦ (O i ω).1) n ω)),
        max ε (min (1 - ε) (sampleMean successIndicator (fun i ω ↦ (O i ω).2) n ω))]) := by
  intro n
  filter_upwards [bernoulli_isMLE hε hε2 μ (fun i ω ↦ (O i ω).1) n,
    bernoulli_isMLE hε hε2 μ (fun i ω ↦ (O i ω).2) n] with ω ⟨h1, m1⟩ ⟨h2, m2⟩
  refine ⟨⟨h1, h2⟩, fun θ hθ ↦ ?_⟩
  have hL : ∀ (X : ℕ → Ω → Bool) (r : ℝ), r ∈ Set.Icc ε (1 - ε) →
      0 ≤ bernoulli.likelihood X n ω r := fun X r hr ↦
    Finset.prod_nonneg fun i _ ↦ bernoulli.density_nonneg r (Icc_subset_bernoulli_Θ hε hr) _
  rw [bernoulliPair_likelihood, bernoulliPair_likelihood]
  exact mul_le_mul (m1 _ hθ.1) (m2 _ hθ.2) (hL _ _ hθ.2) (hL _ _ h1)

/-- **The profile likelihood of the first success probability of a pair** is maximized at the
clipped first sample mean, where it equals the maximized likelihood. -/
theorem bernoulliPair_profileLikelihood {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (μ : Measure Ω)
    (O : ℕ → Ω → Bool × Bool) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ψ ∈ Set.Icc ε (1 - ε),
      bernoulliPair.profileLikelihood O n ω
          {θ | θ 0 ∈ Set.Icc ε (1 - ε) ∧ θ 1 ∈ Set.Icc ε (1 - ε)} (fun θ ↦ θ 0) ψ ≤
        bernoulliPair.profileLikelihood O n ω
          {θ | θ 0 ∈ Set.Icc ε (1 - ε) ∧ θ 1 ∈ Set.Icc ε (1 - ε)} (fun θ ↦ θ 0)
          (max ε (min (1 - ε) (sampleMean successIndicator (fun i ω ↦ (O i ω).1) n ω))) := by
  filter_upwards [(bernoulliPair_isMLE hε hε2 μ O).profileLikelihood (fun θ ↦ θ 0) n] with
    ω ⟨_, hmax⟩ ψ hψ
  have he : (![ψ, ε] : Fin 2 → ℝ) 1 = ε := rfl
  exact hmax ψ ⟨![ψ, ε], ⟨hψ, by rw [he]; exact ⟨le_rfl, by linarith⟩⟩, rfl⟩

end ParametricFamily

end CausalInference
