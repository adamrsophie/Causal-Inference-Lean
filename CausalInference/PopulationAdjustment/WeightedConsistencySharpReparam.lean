/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencySharpInstances

/-!
# Lower dimensional features: reparametrization of entropy balancing

When the features `φ(X) ∈ ℝ^q` lie in a proper affine subspace `E = c + range M` (for instance two
perfectly collinear features), the closed convex hull of their support has empty interior and the
full dimensional consistency theorems do not apply. Writing `φ = c + M ψ` with coordinates
`ψ(X) ∈ ℝ^p` on a basis of the direction of `E` (the columns of `M`, linearly independent, which
is the existence of a left inverse `N` with `N M = 1`), the entropy balancing weights do not see
the change of coordinates.

**Invariance.** For an injective linear map `M` the weights of the data `M Δᵢ` are those of the
data `Δᵢ` (`balancingWeights_mulVec`): `β ↦ Mᵀβ` maps the dual of `MΔ` onto the dual of `Δ`, so
the two log partition functions have minimizers together, with the same entropy weights, and
when there is none both weights are uniform. For an injective affine change `φ = c + M ψ` on the
support and targets `c + M s` the weights coincide (`balancingWeights_affine`,
`sampleBalancedArmMean_affine`).

**Consistency.** The full dimensional theorem applies to the coordinates `ψ`: under the interior
condition for the law of `ψ(X)` in `ℝ^p` (the relative interior condition for `φ(X)`), all
exponential moments, and reported targets in `E` converging to `c + M t`, the weighted arm mean
with the features `φ` is consistent (`sampleBalancedArmMean_isConsistent_trial_reparam`).
The instance `sharpInst_collinear_consistent` balances the two collinear features `(X, 2X)` of
the three point law.

## Main results

* `balancingWeights_mulVec`, `balancingWeights_affine`: invariance of the weights.
* `sampleBalancedArmMean_affine`: invariance of the weighted arm mean.
* `sampleBalancedArmMean_isConsistent_trial_reparam`: consistency for lower dimensional features.
* `sharpInst_collinear_consistent`: two perfectly collinear features.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press (1970).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-! ### Invariance of the weights -/

section Invariance

variable {n p q : ℕ}

/-- **The balancing weights are invariant under an injective linear map of the data.** If
`N M = 1`, the entropy balancing weights of `(M Δᵢ)ᵢ` are those of `(Δᵢ)ᵢ`. -/
theorem balancingWeights_mulVec {M : Matrix (Fin q) (Fin p) ℝ} {N : Matrix (Fin p) (Fin q) ℝ}
    (hNM : N * M = 1) (Δ : Fin n → Fin p → ℝ) :
    balancingWeights (fun i => M *ᵥ Δ i) = balancingWeights Δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext i; exact i.elim0
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hlp : ∀ β, logPartition (fun i => M *ᵥ Δ i) β = logPartition Δ (β ᵥ* M) := fun β => by
    simp only [logPartition, partitionFunction, dotProduct_mulVec]
  have hew : ∀ β, entropyWeights (fun i => M *ᵥ Δ i) β = entropyWeights Δ (β ᵥ* M) := fun β => by
    funext i
    simp only [entropyWeights, partitionFunction, dotProduct_mulVec]
  have hsurj : ∀ γ : Fin p → ℝ, (γ ᵥ* N) ᵥ* M = γ := fun γ => by
    rw [vecMul_vecMul, hNM, vecMul_one]
  by_cases h : ∃ β, IsMinOn (logPartition Δ) Set.univ β
  · obtain ⟨β', hβ'⟩ := h
    have hmin : IsMinOn (logPartition fun i => M *ᵥ Δ i) Set.univ (β' ᵥ* N) :=
      isMinOn_iff.2 fun γ _ => by
        rw [hlp, hlp, hsurj]; exact isMinOn_iff.1 hβ' _ (Set.mem_univ _)
    rw [← entropyWeights_eq_balancingWeights hmin, ← entropyWeights_eq_balancingWeights hβ',
      hew, hsurj]
  · have h' : ¬ ∃ β, IsMinOn (logPartition fun i => M *ᵥ Δ i) Set.univ β := by
      rintro ⟨β, hβ⟩
      refine h ⟨β ᵥ* M, isMinOn_iff.2 fun γ _ => ?_⟩
      have := isMinOn_iff.1 hβ (γ ᵥ* N) (Set.mem_univ _)
      rwa [hlp, hlp, hsurj] at this
    simp only [balancingWeights, dualMinimizer, h, h', ↓reduceDIte]
    rw [hew, zero_vecMul]

/-- **The balancing weights are invariant under an injective affine change of features.** If
`N M = 1`, the weights of `(c + M zᵢ) - (c + M s)` are those of `zᵢ - s`. -/
theorem balancingWeights_affine {M : Matrix (Fin q) (Fin p) ℝ} {N : Matrix (Fin p) (Fin q) ℝ}
    (hNM : N * M = 1) (c : Fin q → ℝ) (z : Fin n → Fin p → ℝ) (s : Fin p → ℝ) :
    balancingWeights (fun i => (c + M *ᵥ z i) - (c + M *ᵥ s)) =
      balancingWeights fun i => z i - s := by
  have e : (fun i => (c + M *ᵥ z i) - (c + M *ᵥ s)) = fun i => M *ᵥ (z i - s) :=
    funext fun i => by rw [mulVec_sub]; abel
  rw [e, balancingWeights_mulVec hNM]

variable {Ω 𝒳 : Type*}

/-- **The weighted arm mean is invariant under an injective affine change of features on the
sample.** If `φ(Xᵢ) = c + M ψ(Xᵢ)` for the records and `N M = 1`, the weighted arm mean with
the features `φ` at the target `c + M s` is the weighted arm mean with the features `ψ` at `s`. -/
theorem sampleBalancedArmMean_affine {M : Matrix (Fin q) (Fin p) ℝ}
    {N : Matrix (Fin p) (Fin q) ℝ} (hNM : N * M = 1) (c : Fin q → ℝ) {φ : 𝒳 → Fin q → ℝ}
    {ψ : 𝒳 → Fin p → ℝ} (O : ℕ → Ω → 𝒳 × Bool × ℝ) (s : Fin p → ℝ) (a : Bool) (n : ℕ) (ω : Ω)
    (h : ∀ i, φ (O i ω).1 = c + M *ᵥ ψ (O i ω).1) :
    sampleBalancedArmMean φ (c + M *ᵥ s) O a n ω = sampleBalancedArmMean ψ s O a n ω := by
  simp only [sampleBalancedArmMean]
  rw [show (fun i : Fin n => φ (O i ω).1 - (c + M *ᵥ s)) =
      fun i : Fin n => (c + M *ᵥ ψ (O i ω).1) - (c + M *ᵥ s) from funext fun i => by rw [h i],
    balancingWeights_affine hNM]

end Invariance

/-! ### Consistency for lower dimensional features -/

section Trial

variable {Ω₁ Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p q : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted arm mean for features in a proper affine subspace.** Let `T`
be a randomized trial as in `sampleBalancedArmMean_isConsistent_trial_general` and let the
measurable features `φ : 𝒳 → ℝ^q` satisfy `φ = c + M ψ` almost surely under the covariate law,
for coordinates `ψ : 𝒳 → ℝ^p` and a matrix `M` with a left inverse `N`. Assume the interior
condition at `t` for the law of `ψ(X)` and all its exponential moments, reported targets
`tₙ = Gₙ(W)` in `c + range M`, computed from data `W` independent of the sample, with
`tₙ → c + M t` in probability, and the arm `a` hypotheses with `m = a₀ + bᵀψ`. Then the weighted
arm mean with the features `φ` at `tₙ` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_trial_reparam (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin q → ℝ} (hφ : Measurable φ) {ψ : 𝒳 → Fin p → ℝ} (hψ : Measurable ψ)
    {M : Matrix (Fin q) (Fin p) ℝ} {N : Matrix (Fin p) (Fin q) ℝ} (hNM : N * M = 1)
    {c : Fin q → ℝ} (hrep : ∀ᵐ x ∂T.covLaw, φ x = c + M *ᵥ ψ x) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map ψ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖ψ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin q → ℝ} (hG : ∀ n, Measurable (G n))
    (hGE : ∀ n w, ∃ u, G n w = c + M *ᵥ u)
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => c + M *ᵥ t))
    (hq : 0 < T.μ.real (T.A ⁻¹' {a})) {m : 𝒳 → ℝ} (hm : T.IsCondMean a m)
    (hres2 : Integrable (fun ω => (T.Y a ω - m (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 | MeasurableSpace.comap T.X inferInstance]
      ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ ψ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  set G' : ℕ → 𝒲 → Fin p → ℝ := fun n w => N *ᵥ (G n w - c) with hG'
  have hGG : ∀ n w, G n w = c + M *ᵥ G' n w := fun n w => by
    obtain ⟨u, hu⟩ := hGE n w
    rw [hG']; simp only
    rw [hu, add_sub_cancel_left,
      show N *ᵥ (M *ᵥ u) = u by rw [mulVec_mulVec, hNM, one_mulVec]]
  have hcont : Continuous fun y : Fin q → ℝ => N *ᵥ (y - c) :=
    (Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const))
  have hG'm : ∀ n, Measurable (G' n) := fun n => hcont.measurable.comp (hG n)
  have htm' : TendstoInMeasure P (fun n ω => G' n (W ω)) atTop (fun _ => t) := by
    have h := htm.comp_continuousAt hcont.continuousAt
    rwa [add_sub_cancel_left, mulVec_mulVec, hNM, one_mulVec] at h
  have h := sampleBalancedArmMean_isConsistent_trial_general hX hA hYo a hYa hrand hO hOm hlaw
    hψ hint hexp hW hWO hG'm htm' hq hm hres2 hvar haff
  have hset : MeasurableSet {x | φ x = c + M *ᵥ ψ x} :=
    measurableSet_eq_fun hφ (measurable_const.add
      ((Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp hψ))
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have hrec : ∀ᵐ z ∂(P.map (O 0)), φ (z : 𝒳 × Bool × ℝ).1 = c + M *ᵥ ψ z.1 := by
    rw [hlaw, Trial.ipdLaw]
    refine (ae_map_iff (p := fun z : 𝒳 × Bool × ℝ => φ z.1 = c + M *ᵥ ψ z.1) hf.aemeasurable
      (hset.preimage measurable_fst)).2 ?_
    exact (ae_map_iff (p := fun x => φ x = c + M *ᵥ ψ x) hX.aemeasurable hset).1 hrep
  have hae := hO.ae_forall (p := fun z : 𝒳 × Bool × ℝ => φ z.1 = c + M *ᵥ ψ z.1) hrec
  refine TendstoInMeasure.congr' (Eventually.of_forall fun n => hae.mono fun ω hω => ?_)
    EventuallyEq.rfl h
  change sampleBalancedArmMean ψ (G' n (W ω)) O a n ω =
    sampleBalancedArmMean φ (G n (W ω)) O a n ω
  rw [hGG n (W ω), sampleBalancedArmMean_affine hNM c O _ a n ω hω]

end Trial

/-! ### Two perfectly collinear features -/

section Collinear

/-- The two perfectly collinear features `(x, 2x)` of a scalar covariate. -/
def collinearFeatures (x : Fin 1 → ℝ) : Fin 2 → ℝ := ![x 0, 2 * x 0]

/-- The direction `(1, 2)` of the collinear features. -/
def collinearDirection : Matrix (Fin 2) (Fin 1) ℝ := !![1; 2]

/-- A left inverse of `collinearDirection`. -/
def collinearLeftInverse : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]

theorem collinearLeftInverse_mul : collinearLeftInverse * collinearDirection = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [collinearLeftInverse, collinearDirection, Matrix.mul_apply, Fin.sum_univ_two]

theorem collinearFeatures_eq (x : Fin 1 → ℝ) :
    collinearFeatures x = 0 + collinearDirection *ᵥ x := by
  ext k
  fin_cases k <;> simp [collinearFeatures, collinearDirection, dotProduct]

/-- **Two perfectly collinear features.** The covariate follows the three point law, the
assignment is a fair coin, `Y(true) = 1 + 2X`, and the arm `true` is balanced on the two
collinear features `(X, 2X)` at the reported targets `(1 / (n + 1), 2 / (n + 1)) → (0, 0)`. The
features span a line, so the full dimensional interior condition fails; by the reparametrization
the weighted arm mean converges in probability to `1`. -/
theorem sharpInst_collinear_consistent :
    IsConsistent (fun n ω => sampleBalancedArmMean collinearFeatures
      ![1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1))]
      (sharpInstSample threePointLaw sharpInstOutcome) true n ω) 1
      (sharpInstLaw threePointLaw sharpInstOutcome) := by
  have key : ∀ (n : ℕ) ω, sampleBalancedArmMean collinearFeatures
      ![1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1))]
      (sharpInstSample threePointLaw sharpInstOutcome) true n ω =
      sampleBalancedArmMean id (featureLineVec (1 / ((n : ℝ) + 1)))
        (sharpInstSample threePointLaw sharpInstOutcome) true n ω := fun n ω => by
    have ht : ![1 / ((n : ℝ) + 1), 2 * (1 / ((n : ℝ) + 1))] =
        0 + collinearDirection *ᵥ featureLineVec (1 / ((n : ℝ) + 1)) := by
      rw [← collinearFeatures_eq]; rfl
    rw [ht]
    exact sampleBalancedArmMean_affine collinearLeftInverse_mul 0 _ _ true n ω
      fun i => collinearFeatures_eq _
  simp only [key]
  exact sharpInst_threePoint_consistent

end Collinear

end PopulationAdjustment

end CausalInference
