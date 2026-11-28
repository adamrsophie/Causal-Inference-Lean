/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.SampleEstimators
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Independence.Basic

/-!
# Weighted averages of conditionally centered noise

Let `O 0, O 1, …` be an i.i.d. sample of records with law `ν`, `C` a feature map of a record
and `e` a noise with `E[e | C] = 0` and `E[e² | C] ≤ v(C)` under `ν`. For coefficients `cₙᵢ`
that are measurable functions of the features `(C(O 0), …, C(O (n - 1)))` of the whole sample,
with `|cₙᵢ| ≤ 1`, the weighted sum `∑ᵢ cₙᵢ e(O i)` has second moment at most
`E[∑ᵢ cₙᵢ² v(C(O i))]` (`integral_sq_weighted_noise_le`), and it tends to zero in probability
as soon as `∑ᵢ cₙᵢ² v(C(O i))` does (`tendstoInMeasure_weighted_noise`).

The coefficients depend on the features of all units, so the summands are not independent. The
cross terms still vanish: record `i` is independent of the other records, and conditioning it on
its own features and on the other records replaces `e(O i)` by `E[e | C](O i) = 0`. This step is
`integral_mul_eq_condExp_of_indepFun`, proved by factoring the joint law of a record and an
independent variable as a product measure and integrating the record first (Fubini).

This is the variance computation behind the consistency of the weighted (matching adjusted)
estimator: the coefficients are the normalized weights of the units, which depend on all the
covariates of the sample.

## Main definitions

* `recordsExcept`: the records of the first `n` units other than unit `i`.
* `spliceFeatures`: the features of the sample with those of unit `i` put back in place.

## Main results

* `integral_comp_mul_condExp`, `integral_mul_eq_condExp_of_indepFun`.
* `integral_cross_noise_eq_zero`, `integral_diag_noise_le`, `integral_sq_weighted_noise_le`.
* `tendstoInMeasure_weighted_noise`: the weighted law of large numbers.
* `allocation_noise_moments`, `residual_noise_moments`: for a record `(X, A, Y)` of a trial with
  randomized assignment, the allocation noise `(1{A = a} - P(A = a)) ψ(X)` and the residual
  `1{A = a}(Y - μ_A(X))` are conditionally centered with bounded conditional second moment.

## References

* D. Williams, *Probability with Martingales*, Cambridge University Press (1991).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

/-! ### Conditioning a record on its features and on independent data -/

section Conditioning

variable {Ω D 𝒞 𝒲 : Type*} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace 𝒞]
  [MeasurableSpace 𝒲] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure D}
  [IsProbabilityMeasure ν]

/-- A bounded function of the features comes out of the conditional expectation:
`∫ h(C(v)) f(v) dν = ∫ h(C(v)) E[f | C](v) dν`. -/
theorem integral_comp_mul_condExp {C : D → 𝒞} (hC : Measurable C) {h : 𝒞 → ℝ}
    (hh : Measurable h) {M : ℝ} (hM : ∀ c, |h c| ≤ M) {f : D → ℝ} (hf : Integrable f ν) :
    ∫ v, h (C v) * f v ∂ν =
      ∫ v, h (C v) * (ν[f | MeasurableSpace.comap C inferInstance]) v ∂ν := by
  have hm : MeasurableSpace.comap C inferInstance ≤ ‹MeasurableSpace D› := hC.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap C inferInstance] (fun v => h (C v)) :=
    (hh.comp (comap_measurable C)).stronglyMeasurable
  have hhf : Integrable (fun v => h (C v) * f v) ν :=
    hf.bdd_mul (hh.comp hC).aestronglyMeasurable (c := M)
      (ae_of_all _ fun v => by rw [Real.norm_eq_abs]; exact hM _)
  rw [← integral_condExp hm]
  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hsm hhf hf)

/-- **Conditioning a record on its own features and on independent data.** Let `V` have law `ν`
and be independent of `W`. For a measurable `g` of the features `C(V)` and of `W` with
`|g| ≤ 1`, an integrable factor `k(W)` and an integrable `f`,
`E[g(C(V), W) k(W) f(V)] = E[g(C(V), W) k(W) E_ν[f | C](V)]`. The joint law of `(V, W)` is the
product of the two laws; integrate `V` first. -/
theorem integral_mul_eq_condExp_of_indepFun {V : Ω → D} {W : Ω → 𝒲} (hV : Measurable V)
    (hW : Measurable W) (hVν : P.map V = ν) (hind : IndepFun V W P) {C : D → 𝒞}
    (hC : Measurable C) {g : 𝒞 × 𝒲 → ℝ} (hg : Measurable g) (hg1 : ∀ c, |g c| ≤ 1)
    {k : 𝒲 → ℝ} (hk : Measurable k) (hki : Integrable (fun ω => k (W ω)) P)
    {f : D → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    ∫ ω, g (C (V ω), W ω) * k (W ω) * f (V ω) ∂P =
      ∫ ω, g (C (V ω), W ω) * k (W ω) *
        (ν[f | MeasurableSpace.comap C inferInstance]) (V ω) ∂P := by
  set u := ν[f | MeasurableSpace.comap C inferInstance] with hu
  have hm : MeasurableSpace.comap C inferInstance ≤ ‹MeasurableSpace D› := hC.comap_le
  have hum : Measurable u := (stronglyMeasurable_condExp.mono hm).measurable
  have hui : Integrable u ν := integrable_condExp
  set lam := P.map W with hlam
  have hjoint : P.map (fun ω => (V ω, W ω)) = ν.prod lam := by
    rw [← hVν]
    exact (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hW.aemeasurable).1 hind
  have hkl : Integrable k lam := (integrable_map_measure hk.aestronglyMeasurable
    hW.aemeasurable).2 hki
  -- both sides are integrals of a function of `(V, W)` under the product law
  have hF : ∀ r : D → ℝ, Measurable r → Integrable r ν →
      Integrable (fun z : D × 𝒲 => g (C z.1, z.2) * k z.2 * r z.1) (ν.prod lam) ∧
      ∫ ω, g (C (V ω), W ω) * k (W ω) * r (V ω) ∂P =
        ∫ w, ∫ v, g (C v, w) * k w * r v ∂ν ∂lam := by
    intro r hr hri
    have hmeas : Measurable fun z : D × 𝒲 => g (C z.1, z.2) * k z.2 * r z.1 :=
      (hg.comp ((hC.comp measurable_fst).prodMk measurable_snd)).mul (hk.comp measurable_snd)
        |>.mul (hr.comp measurable_fst)
    have hint : Integrable (fun z : D × 𝒲 => g (C z.1, z.2) * k z.2 * r z.1) (ν.prod lam) := by
      refine (hri.norm.mul_prod hkl.norm).mono' hmeas.aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      simp only [Real.norm_eq_abs, abs_mul]
      have := hg1 (C z.1, z.2)
      calc |g (C z.1, z.2)| * |k z.2| * |r z.1| ≤ 1 * |k z.2| * |r z.1| := by gcongr
        _ = |r z.1| * |k z.2| := by ring
    refine ⟨hint, ?_⟩
    have h1 : ∫ ω, g (C (V ω), W ω) * k (W ω) * r (V ω) ∂P =
        ∫ z, g (C z.1, z.2) * k z.2 * r z.1 ∂(ν.prod lam) := by
      rw [← hjoint, integral_map (hV.prodMk hW).aemeasurable hmeas.aestronglyMeasurable]
    rw [h1, integral_prod_symm _ hint]
  rw [(hF f hf hfi).2, (hF u hum hui).2]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only
  have hgw : Measurable fun c => g (c, w) := hg.comp (measurable_id.prodMk measurable_const)
  have h := integral_comp_mul_condExp hC hgw (fun c => hg1 (c, w)) hfi (ν := ν)
  calc ∫ v, g (C v, w) * k w * f v ∂ν = k w * ∫ v, g (C v, w) * f v ∂ν := by
        rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun v => by ring)
    _ = k w * ∫ v, g (C v, w) * u v ∂ν := by rw [h]
    _ = ∫ v, g (C v, w) * k w * u v ∂ν := by
        rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun v => by ring)

end Conditioning

/-! ### The other records of a sample -/

section Sample

variable {Ω D 𝒞 : Type*} [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace 𝒞]
  {P : Measure Ω} {O : ℕ → Ω → D}

/-- The records `O k` with `k < n` and `k ≠ i`, as one random vector. -/
def recordsExcept (O : ℕ → Ω → D) (n i : ℕ) (ω : Ω) : ((Finset.range n).erase i) → D :=
  fun k => O k ω

/-- The feature vector `(C(O k))_{k < n}` rebuilt from the features of unit `i` and the other
records. -/
def spliceFeatures (C : D → 𝒞) {n : ℕ} (i : Fin n)
    (q : 𝒞 × (((Finset.range n).erase (i : ℕ)) → D)) : Fin n → 𝒞 :=
  fun k => if h : k = i then q.1 else
    C (q.2 ⟨k, Finset.mem_erase.2 ⟨fun h' => h (Fin.ext h'), Finset.mem_range.2 k.2⟩⟩)

omit [MeasurableSpace Ω] in
theorem measurable_spliceFeatures {C : D → 𝒞} (hC : Measurable C) {n : ℕ} (i : Fin n) :
    Measurable (spliceFeatures C i) := by
  refine measurable_pi_iff.2 fun k => ?_
  by_cases h : k = i
  · simp only [spliceFeatures, h, dite_true]; exact measurable_fst
  · simp only [spliceFeatures, h, dite_false]
    exact hC.comp ((measurable_pi_apply _).comp measurable_snd)

omit [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace 𝒞] in
/-- Splicing unit `i` back among the other records gives the feature vector of the sample. -/
theorem spliceFeatures_eq (C : D → 𝒞) (O : ℕ → Ω → D) {n : ℕ} (i : Fin n) (ω : Ω) :
    spliceFeatures C i (C (O i ω), recordsExcept O n i ω) = fun k : Fin n => C (O k ω) := by
  funext k
  by_cases h : k = i
  · subst h; simp [spliceFeatures]
  · simp [spliceFeatures, h, recordsExcept]

theorem measurable_recordsExcept (hOm : ∀ i, Measurable (O i)) (n i : ℕ) :
    Measurable (recordsExcept O n i) :=
  measurable_pi_iff.2 fun k => hOm k

/-- In an independent sample, record `i` is independent of the other records. -/
theorem indepFun_recordsExcept (hO : iIndepFun O P) (hOm : ∀ i, Measurable (O i)) (n i : ℕ) :
    IndepFun (O i) (recordsExcept O n i) P := by
  have h := hO.indepFun_finset {i} ((Finset.range n).erase i)
    (Finset.disjoint_singleton_left.2 (Finset.notMem_erase i _)) hOm
  exact h.comp (_mγ := ‹MeasurableSpace D›) (φ := fun x => x ⟨i, Finset.mem_singleton_self i⟩)
    (ψ := id)
    (measurable_pi_apply _) measurable_id

/-- A function integrable under the law of the first record is integrable at every record of an
i.i.d. sample. -/
theorem integrable_comp_of_isIIDSample (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {f : D → ℝ} (hf : Integrable f (P.map (O 0))) (i : ℕ) :
    Integrable (fun ω => f (O i ω)) P := by
  rw [← (hO.ident i).map_eq] at hf
  exact hf.comp_measurable (hOm i)

variable [IsProbabilityMeasure P] {C : D → 𝒞} {e : D → ℝ} {v : 𝒞 → ℝ}

omit [IsProbabilityMeasure P] in
/-- The product of two noises and a coefficient bounded by one is integrable:
`|F e(O i) e(O j)| ≤ (e(O i)² + e(O j)²) / 2`. -/
theorem integrable_mul_noise (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (he : Measurable e) (he2 : Integrable (fun z => e z ^ 2) (P.map (O 0))) {F : Ω → ℝ}
    (hF : AEStronglyMeasurable F P) (hF1 : ∀ ω, |F ω| ≤ 1) (i j : ℕ) :
    Integrable (fun ω => F ω * e (O j ω) * e (O i ω)) P := by
  refine Integrable.mono' (((integrable_comp_of_isIIDSample hO hOm he2 j).add
    (integrable_comp_of_isIIDSample hO hOm he2 i)).div_const 2)
    ((hF.mul (he.comp (hOm j)).aestronglyMeasurable).mul (he.comp (hOm i)).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 := hF1 ω
  have h2 : |e (O j ω)| * |e (O i ω)| ≤ (e (O j ω) ^ 2 + e (O i ω) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|e (O j ω)| - |e (O i ω)|), sq_abs (e (O j ω)), sq_abs (e (O i ω))]
  calc |F ω| * |e (O j ω)| * |e (O i ω)| ≤ 1 * |e (O j ω)| * |e (O i ω)| := by gcongr
    _ ≤ _ := by rw [one_mul]; exact h2

/-- **Cross terms vanish.** For units `i ≠ j` of an i.i.d. sample and a measurable `F` of the
feature vector with `|F| ≤ 1`, `E[F(C(O)) e(O j) e(O i)] = 0` when `E[e | C] = 0`. -/
theorem integral_cross_noise_eq_zero (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hC : Measurable C) (he : Measurable e) (he2 : Integrable (fun z => e z ^ 2) (P.map (O 0)))
    (hmean : (P.map (O 0))[e | MeasurableSpace.comap C inferInstance] =ᵐ[P.map (O 0)] 0)
    {n : ℕ} {F : (Fin n → 𝒞) → ℝ} (hF : Measurable F) (hF1 : ∀ c, |F c| ≤ 1) {i j : Fin n}
    (hij : i ≠ j) :
    ∫ ω, F (fun k => C (O k ω)) * e (O j ω) * e (O i ω) ∂P = 0 := by
  have hjT : (j : ℕ) ∈ (Finset.range n).erase i :=
    Finset.mem_erase.2 ⟨fun h => hij (Fin.ext h).symm, Finset.mem_range.2 j.2⟩
  have heI : Integrable e (P.map (O 0)) :=
    ((memLp_two_iff_integrable_sq he.aestronglyMeasurable).2 he2).integrable one_le_two
  have hrepr : ∀ ω, F (fun k => C (O k ω)) * e (O j ω) * e (O i ω) =
      F (spliceFeatures C i (C (O i ω), recordsExcept O n i ω)) *
        e (recordsExcept O n i ω ⟨j, hjT⟩) * e (O i ω) := fun ω => by
    rw [spliceFeatures_eq]; rfl
  simp_rw [hrepr]
  have hkm : Measurable fun w : ((Finset.range n).erase (i : ℕ)) → D => e (w ⟨j, hjT⟩) :=
    he.comp (measurable_pi_apply _)
  rw [integral_mul_eq_condExp_of_indepFun (g := fun q => F (spliceFeatures C i q))
    (k := fun w => e (w ⟨j, hjT⟩)) (hOm i) (measurable_recordsExcept hOm n i)
    ((hO.ident i).map_eq) (indepFun_recordsExcept hO.indep hOm n i) hC
    (hF.comp (measurable_spliceFeatures hC i)) (fun q => hF1 _) hkm
    (integrable_comp_of_isIIDSample hO hOm heI j) he heI]
  refine (integral_congr_ae ?_).trans (integral_zero Ω ℝ)
  filter_upwards [(hO.ae_forall hmean)] with ω hω
  simp [hω i]

/-- **Diagonal terms are bounded by the conditional variance.** For a measurable `G` of the
feature vector with `0 ≤ G ≤ 1`, `E[G(C(O)) e(O i)²] ≤ E[G(C(O)) v(C(O i))]` when
`E[e² | C] ≤ v(C)`. -/
theorem integral_diag_noise_le (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hC : Measurable C) (he : Measurable e) (he2 : Integrable (fun z => e z ^ 2) (P.map (O 0)))
    (hvi : Integrable (fun z => v (C z)) (P.map (O 0)))
    (hvar : (P.map (O 0))[fun z => e z ^ 2 | MeasurableSpace.comap C inferInstance]
      ≤ᵐ[P.map (O 0)] fun z => v (C z))
    {n : ℕ} {G : (Fin n → 𝒞) → ℝ} (hG : Measurable G) (hG0 : ∀ c, 0 ≤ G c)
    (hG1 : ∀ c, G c ≤ 1) (i : Fin n) :
    ∫ ω, G (fun k => C (O k ω)) * e (O i ω) ^ 2 ∂P ≤
      ∫ ω, G (fun k => C (O k ω)) * v (C (O i ω)) ∂P := by
  have hrepr : ∀ ω, G (fun k => C (O k ω)) =
      G (spliceFeatures C i (C (O i ω), recordsExcept O n i ω)) := fun ω => by
    rw [spliceFeatures_eq]
  have hGm : Measurable fun ω => G (fun k => C (O k ω)) :=
    hG.comp (measurable_pi_iff.2 fun k => hC.comp (hOm k))
  have hbound : ∀ {f : Ω → ℝ}, Integrable f P →
      Integrable (fun ω => G (fun k => C (O k ω)) * f ω) P := fun hf =>
    hf.bdd_mul hGm.aestronglyMeasurable (c := 1) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _)]; exact hG1 _)
  have h1 : ∫ ω, G (fun k => C (O k ω)) * e (O i ω) ^ 2 ∂P =
      ∫ ω, G (spliceFeatures C i (C (O i ω), recordsExcept O n i ω)) * (fun _ => (1 : ℝ))
        (recordsExcept O n i ω) * (fun z => e z ^ 2) (O i ω) ∂P := by
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [mul_one]; rw [hrepr]
  rw [h1, integral_mul_eq_condExp_of_indepFun (g := fun q => G (spliceFeatures C i q))
    (k := fun _ => (1 : ℝ)) (f := fun z => e z ^ 2) (hOm i) (measurable_recordsExcept hOm n i)
    ((hO.ident i).map_eq) (indepFun_recordsExcept hO.indep hOm n i) hC
    (hG.comp (measurable_spliceFeatures hC i))
    (fun q => by rw [abs_of_nonneg (hG0 _)]; exact hG1 _) measurable_const
    (integrable_const _) (he.pow_const 2) he2]
  simp only [mul_one, ← hrepr]
  have hu : Integrable (fun ω => ((P.map (O 0))[fun z => e z ^ 2 |
      MeasurableSpace.comap C inferInstance]) (O i ω)) P :=
    integrable_comp_of_isIIDSample hO hOm integrable_condExp i
  have hvP : Integrable (fun ω => v (C (O i ω))) P := integrable_comp_of_isIIDSample hO hOm hvi i
  refine integral_mono_ae (hbound hu) (hbound hvP) ?_
  filter_upwards [hO.ae_forall hvar] with ω hω
  exact mul_le_mul_of_nonneg_left (hω i) (hG0 _)

/-- **Second moment of a weighted noise sum.** For coefficients `bᵢ` that are measurable
functions of the feature vector with `|bᵢ| ≤ 1`, `E[(∑ᵢ bᵢ e(O i))²] ≤ E[∑ᵢ bᵢ² v(C(O i))]`. The
square expands into a double sum; the cross terms vanish (`integral_cross_noise_eq_zero`) and the
diagonal terms are bounded by the conditional variance (`integral_diag_noise_le`). -/
theorem integral_sq_weighted_noise_le (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hC : Measurable C) (he : Measurable e) (he2 : Integrable (fun z => e z ^ 2) (P.map (O 0)))
    (hmean : (P.map (O 0))[e | MeasurableSpace.comap C inferInstance] =ᵐ[P.map (O 0)] 0)
    (hvi : Integrable (fun z => v (C z)) (P.map (O 0)))
    (hvar : (P.map (O 0))[fun z => e z ^ 2 | MeasurableSpace.comap C inferInstance]
      ≤ᵐ[P.map (O 0)] fun z => v (C z))
    {n : ℕ} (b : Fin n → (Fin n → 𝒞) → ℝ) (hb : ∀ i, Measurable (b i))
    (hb1 : ∀ i c, |b i c| ≤ 1) :
    ∫ ω, (∑ i, b i (fun k => C (O k ω)) * e (O i ω)) ^ 2 ∂P ≤
      ∫ ω, ∑ i, b i (fun k => C (O k ω)) ^ 2 * v (C (O i ω)) ∂P := by
  set c : Ω → Fin n → 𝒞 := fun ω k => C (O k ω) with hc
  have hcm : Measurable c := measurable_pi_iff.2 fun k => hC.comp (hOm k)
  have hbb : ∀ i j x, |b i x * b j x| ≤ 1 := fun i j x => by
    rw [abs_mul]
    exact (mul_le_mul (hb1 i _) (hb1 j _) (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hterm : ∀ i j : Fin n, Integrable
      (fun ω => b i (c ω) * e (O i ω) * (b j (c ω) * e (O j ω))) P := by
    intro i j
    have := integrable_mul_noise hO hOm he he2 (F := fun ω => b i (c ω) * b j (c ω))
      (((hb i).comp hcm).mul ((hb j).comp hcm)).aestronglyMeasurable (fun ω => hbb i j _) i j
    refine this.congr (Eventually.of_forall fun ω => ?_)
    ring
  have hexp : ∀ ω, (∑ i, b i (c ω) * e (O i ω)) ^ 2 =
      ∑ i, ∑ j, b i (c ω) * e (O i ω) * (b j (c ω) * e (O j ω)) := fun ω => by
    rw [sq, Finset.sum_mul_sum]
  rw [show (fun ω => (∑ i, b i (fun k => C (O k ω)) * e (O i ω)) ^ 2) =
      fun ω => ∑ i, ∑ j, b i (c ω) * e (O i ω) * (b j (c ω) * e (O j ω)) from funext hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j]
  have hdiag : ∀ i : Fin n, ∫ ω, ∑ j, b i (c ω) * e (O i ω) * (b j (c ω) * e (O j ω)) ∂P =
      ∫ ω, b i (c ω) ^ 2 * e (O i ω) ^ 2 ∂P := by
    intro i
    rw [integral_finsetSum _ fun j _ => hterm i j, Finset.sum_eq_single i]
    · exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    · intro j _ hji
      have := integral_cross_noise_eq_zero hO hOm hC he he2 hmean
        (F := fun x => b i x * b j x) ((hb i).mul (hb j)) (hbb i j) (Ne.symm hji)
      rw [← this]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    · simp
  simp_rw [hdiag]
  have hvP : ∀ i : Fin n, Integrable (fun ω => b i (c ω) ^ 2 * v (C (O i ω))) P := fun i =>
    (integrable_comp_of_isIIDSample hO hOm hvi i).bdd_mul
      (((hb i).comp hcm).pow_const 2).aestronglyMeasurable (c := 1)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow, sq_abs]
        exact (sq_le_one_iff_abs_le_one _).2 (hb1 i _))
  rw [integral_finsetSum _ fun i _ => hvP i]
  refine Finset.sum_le_sum fun i _ => ?_
  exact integral_diag_noise_le hO hOm hC he he2 hvi hvar (G := fun x => b i x ^ 2)
    ((hb i).pow_const 2) (fun _ => sq_nonneg _)
    (fun x => (sq_le_one_iff_abs_le_one _).2 (hb1 i x)) i

omit [IsProbabilityMeasure P] in
/-- The square of a weighted noise sum with coefficients bounded by one is integrable. -/
theorem integrable_sq_weighted_noise (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hC : Measurable C) (he : Measurable e) (he2 : Integrable (fun z => e z ^ 2) (P.map (O 0)))
    {n : ℕ} (b : Fin n → (Fin n → 𝒞) → ℝ) (hb : ∀ i, Measurable (b i))
    (hb1 : ∀ i c, |b i c| ≤ 1) :
    Integrable (fun ω => (∑ i, b i (fun k => C (O k ω)) * e (O i ω)) ^ 2) P := by
  have hcm : Measurable fun ω (k : Fin n) => C (O k ω) :=
    measurable_pi_iff.2 fun k => hC.comp (hOm k)
  have hexp : ∀ ω, (∑ i, b i (fun k => C (O k ω)) * e (O i ω)) ^ 2 =
      ∑ i, ∑ j, (b i (fun k => C (O k ω)) * b j (fun k => C (O k ω))) * e (O j ω) * e (O i ω) :=
    fun ω => by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_).congr
    (Eventually.of_forall fun ω => (hexp ω).symm)
  exact integrable_mul_noise hO hOm he he2
    (F := fun ω => b i (fun k => C (O k ω)) * b j (fun k => C (O k ω)))
    (((hb i).comp hcm).mul ((hb j).comp hcm)).aestronglyMeasurable
    (fun ω => by
      rw [abs_mul]
      exact (mul_le_mul (hb1 i _) (hb1 j _) (abs_nonneg _) zero_le_one).trans (by norm_num)) i j

/-- **A weighted law of large numbers for conditionally centered noise.** Let `O` be an i.i.d.
sample, `C` a feature map and `e` a noise with `E[e | C] = 0` and `E[e² | C] ≤ v(C)` under the
law of a record. Let the coefficients `aₙᵢ` be measurable functions of the feature vector
`(C(O k))_{k < n}` with `|aₙᵢ| ≤ 1`. If `∑ᵢ aₙᵢ² v(C(O i)) → 0` in probability, then
`∑ᵢ aₙᵢ e(O i) → 0` in probability. On the event `{∑ᵢ aₙᵢ² v(C(O i)) < η}` the truncated sum has
second moment at most `η` (`integral_sq_weighted_noise_le`), and Chebyshev's inequality bounds
the rest. -/
theorem tendstoInMeasure_weighted_noise (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hC : Measurable C) (he : Measurable e) (he2 : Integrable (fun z => e z ^ 2) (P.map (O 0)))
    (hmean : (P.map (O 0))[e | MeasurableSpace.comap C inferInstance] =ᵐ[P.map (O 0)] 0)
    (hv : Measurable v) (hv0 : ∀ c, 0 ≤ v c) (hvi : Integrable (fun z => v (C z)) (P.map (O 0)))
    (hvar : (P.map (O 0))[fun z => e z ^ 2 | MeasurableSpace.comap C inferInstance]
      ≤ᵐ[P.map (O 0)] fun z => v (C z))
    (a : (n : ℕ) → Fin n → (Fin n → 𝒞) → ℝ) (ha : ∀ n i, Measurable (a n i))
    (ha1 : ∀ n i c, |a n i c| ≤ 1)
    (hD : TendstoInMeasure P
      (fun n ω => ∑ i : Fin n, a n i (fun k => C (O k ω)) ^ 2 * v (C (O i ω))) atTop
        (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => ∑ i : Fin n, a n i (fun k => C (O k ω)) * e (O i ω)) atTop
      (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hD ⊢
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun _ => htop ▸ le_top
  set r := (ε / 2).toReal with hr
  have hε2 : ε / 2 ≠ ⊤ := ENNReal.div_ne_top htop (by norm_num)
  have hr0 : 0 < r := ENNReal.toReal_pos (ENNReal.half_pos hε.ne').ne' hε2
  have hrε : ENNReal.ofReal r = ε / 2 := ENNReal.ofReal_toReal hε2
  set η := r * δ ^ 2 with hη
  have hη0 : 0 < η := by positivity
  have hD' := ENNReal.tendsto_nhds_zero.1 (hD η hη0) (ε / 2) (ENNReal.half_pos hε.ne')
  filter_upwards [hD'] with n hn
  set Dn : (Fin n → 𝒞) → ℝ := fun c => ∑ j, a n j c ^ 2 * v (c j) with hDn
  have hDm : Measurable Dn :=
    Finset.measurable_sum _ fun j _ => ((ha n j).pow_const 2).mul (hv.comp (measurable_pi_apply j))
  have hD0 : ∀ c, 0 ≤ Dn c := fun c =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hv0 _)
  set b : Fin n → (Fin n → 𝒞) → ℝ := fun i c => if Dn c < η then a n i c else 0 with hbdef
  have hb : ∀ i, Measurable (b i) := fun i =>
    Measurable.ite (measurableSet_lt hDm measurable_const) (ha n i) measurable_const
  have hb1 : ∀ i c, |b i c| ≤ 1 := fun i c => by
    simp only [hbdef]; split_ifs
    · exact ha1 n i c
    · simp
  set c : Ω → Fin n → 𝒞 := fun ω k => C (O k ω) with hc
  set S' : Ω → ℝ := fun ω => (∑ i, b i (c ω) * e (O i ω)) ^ 2 with hS'
  have hsub : {ω | δ ≤ dist (∑ i : Fin n, a n i (c ω) * e (O i ω)) 0} ⊆
      {ω | η ≤ dist (∑ i : Fin n, a n i (c ω) ^ 2 * v (C (O i ω))) 0} ∪
        {ω | δ ^ 2 ≤ S' ω} := by
    intro ω hω
    change δ ≤ dist (∑ i : Fin n, a n i (c ω) * e (O i ω)) 0 at hω
    rw [Real.dist_eq, sub_zero] at hω
    by_cases hlt : Dn (c ω) < η
    · right
      have : ∑ i, b i (c ω) * e (O i ω) = ∑ i, a n i (c ω) * e (O i ω) :=
        Finset.sum_congr rfl fun i _ => by simp only [hbdef, hlt, ite_true]
      change δ ^ 2 ≤ (∑ i, b i (c ω) * e (O i ω)) ^ 2
      rw [this]
      exact (pow_le_pow_left₀ hδ.le hω 2).trans (sq_abs _).le
    · left
      change η ≤ dist (Dn (c ω)) 0
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hD0 _)]
      exact not_lt.1 hlt
  have hint := integrable_sq_weighted_noise hO hOm hC he he2 b hb hb1
  have hmom := integral_sq_weighted_noise_le hO hOm hC he he2 hmean hvi hvar b hb hb1
  have hbound : ∫ ω, ∑ i, b i (c ω) ^ 2 * v (C (O i ω)) ∂P ≤ η := by
    have hle : ∀ ω, ∑ i, b i (c ω) ^ 2 * v (C (O i ω)) ≤ η := fun ω => by
      by_cases hlt : Dn (c ω) < η
      · simp only [hbdef, hlt, ite_true]; exact hlt.le
      · simp only [hbdef, hlt, ite_false]; simp [hη0.le]
    calc ∫ ω, ∑ i, b i (c ω) ^ 2 * v (C (O i ω)) ∂P ≤ ∫ _, η ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => Finset.sum_nonneg fun i _ =>
            mul_nonneg (sq_nonneg _) (hv0 _)) (integrable_const η) (Eventually.of_forall hle)
      _ = η := by simp
  have hcheb := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
    hint (δ ^ 2)
  have hreal : P.real {ω | δ ^ 2 ≤ S' ω} ≤ r := by
    have h2 : δ ^ 2 * P.real {ω | δ ^ 2 ≤ S' ω} ≤ r * δ ^ 2 := hcheb.trans (hmom.trans hbound)
    have hδ2 : 0 < δ ^ 2 := by positivity
    nlinarith
  calc P {ω | δ ≤ dist (∑ i : Fin n, a n i (c ω) * e (O i ω)) 0}
      ≤ P ({ω | η ≤ dist (∑ i : Fin n, a n i (c ω) ^ 2 * v (C (O i ω))) 0} ∪
          {ω | δ ^ 2 ≤ S' ω}) := measure_mono hsub
    _ ≤ P {ω | η ≤ dist (∑ i : Fin n, a n i (c ω) ^ 2 * v (C (O i ω))) 0} +
          P {ω | δ ^ 2 ≤ S' ω} := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add hn ?_
        rw [← ofReal_measureReal, ← hrε]; exact ENNReal.ofReal_le_ofReal hreal
    _ = ε := ENNReal.add_halves ε

end Sample

/-! ### The index trial record: allocation noise and residual noise -/

section TrialNoise

open PointTreatment

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)} [IsProbabilityMeasure ν]

omit [MeasurableSpace 𝒳] in
theorem armIndObs_eq_zero_or_one (a : Bool) (z : 𝒳 × Bool × ℝ) :
    armIndObs a z = 0 ∨ armIndObs a z = 1 := by
  unfold armIndObs; split_ifs <;> simp

theorem abs_armIndObs_sub_le_one (a : Bool) (z : 𝒳 × Bool × ℝ) :
    |armIndObs a z - ν.real {z | z.2.1 = a}| ≤ 1 := by
  have h0 : 0 ≤ ν.real {z : 𝒳 × Bool × ℝ | z.2.1 = a} := measureReal_nonneg
  have h1 : ν.real {z : 𝒳 × Bool × ℝ | z.2.1 = a} ≤ 1 := measureReal_le_one
  rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h, abs_le] <;> constructor <;> linarith

/-- **Randomized allocation noise.** If the arm `A` is independent of the covariate `X` under
the record law and `q = P(A = a)`, then for a feature `ψ` with `E[ψ(X)²] < ∞` the allocation
noise `(1{A = a} - q) ψ(X)` has `E[· | X] = 0` and `E[(·)² | X] ≤ ψ(X)²`. -/
theorem allocation_noise_moments (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1)
    (fun z => z.2.1) ν) (a : Bool) {ψ : 𝒳 → ℝ} (hψ : Measurable ψ)
    (hψ2 : Integrable (fun z : 𝒳 × Bool × ℝ => ψ z.1 ^ 2) ν) :
    ν[fun z => (armIndObs a z - ν.real {z | z.2.1 = a}) * ψ z.1 |
        MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1) inferInstance] =ᵐ[ν] 0 ∧
      ν[fun z => ((armIndObs a z - ν.real {z | z.2.1 = a}) * ψ z.1) ^ 2 |
        MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1) inferInstance] ≤ᵐ[ν]
        fun z => ψ z.1 ^ 2 := by
  set q := ν.real {z : 𝒳 × Bool × ℝ | z.2.1 = a} with hq
  have hm : MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1) inferInstance ≤
      (inferInstance : MeasurableSpace (𝒳 × Bool × ℝ)) :=
    (measurable_fst : Measurable fun z : 𝒳 × Bool × ℝ => z.1).comap_le
  have hA : Measurable (armIndObs (𝒲 := 𝒳) a) := measurable_armIndObs a
  have hAsm : StronglyMeasurable[MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.2.1)
      inferInstance] (armIndObs (𝒲 := 𝒳) a) := by
    have : armIndObs (𝒲 := 𝒳) a = (fun b : Bool => if b = a then (1 : ℝ) else 0) ∘
        fun z : 𝒳 × Bool × ℝ => z.2.1 := rfl
    rw [this]
    exact (Measurable.of_discrete.comp (comap_measurable _)).stronglyMeasurable
  have hT : ν[armIndObs a | MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1)
      inferInstance] =ᵐ[ν] fun _ => q := by
    refine (condExp_indep_eq measurable_snd.fst.comap_le hm hAsm hind.symm).trans
      (Eventually.of_forall fun _ => ?_)
    have : armIndObs (𝒲 := 𝒳) a = ((fun z : 𝒳 × Bool × ℝ => z.2.1) ⁻¹' {a}).indicator 1 := by
      funext z; simp [armIndObs, Set.indicator]
    change ∫ z, armIndObs a z ∂ν = q
    rw [this, integral_indicator_one (measurable_snd.fst (measurableSet_singleton a))]
    rfl
  have hψm : Measurable fun z : 𝒳 × Bool × ℝ => ψ z.1 := hψ.comp measurable_fst
  have hψI : Integrable (fun z : 𝒳 × Bool × ℝ => ψ z.1) ν :=
    ((memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).2 hψ2).integrable one_le_two
  have hAq : ∀ z : 𝒳 × Bool × ℝ, |armIndObs a z - q| ≤ 1 := abs_armIndObs_sub_le_one a
  have hAqI : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z - q) ν :=
    (integrable_const 1).mono' (hA.sub_const q).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hAq z)
  have hprodI : Integrable (fun z : 𝒳 × Bool × ℝ => ψ z.1 * (armIndObs a z - q)) ν :=
    hψI.norm.mono' (hψm.mul (hA.sub_const q)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hAq z))
  have hψsm : StronglyMeasurable[MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1)
      inferInstance] (fun z : 𝒳 × Bool × ℝ => ψ z.1) :=
    (hψ.comp (comap_measurable _)).stronglyMeasurable
  have hAI : Integrable (armIndObs (𝒲 := 𝒳) a) ν :=
    (integrable_const 1).mono' hA.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> simp)
  have hsq : ∀ z : 𝒳 × Bool × ℝ, ((armIndObs a z - q) * ψ z.1) ^ 2 ≤ ψ z.1 ^ 2 := fun z => by
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) ((sq_le_one_iff_abs_le_one _).2 (hAq z))
  constructor
  · have h1 := condExp_mul_of_stronglyMeasurable_left hψsm hprodI hAqI
    have h2 := condExp_sub
      (m := MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1) inferInstance) hAI
      (integrable_const q)
    rw [condExp_const hm q] at h2
    have hfun : (fun z : 𝒳 × Bool × ℝ => (armIndObs a z - q) * ψ z.1) =
        (fun z => ψ z.1) * fun z => armIndObs a z - q := by
      funext z; simp [mul_comm]
    rw [hfun]
    filter_upwards [h1, h2, hT] with z h1 h2 hT
    rw [h1]
    simp only [Pi.mul_apply, Pi.zero_apply]
    change ψ z.1 * (ν[armIndObs a - fun _ => q |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1) inferInstance]) z = 0
    rw [h2]
    simp [hT]
  · have he2I : Integrable (fun z : 𝒳 × Bool × ℝ => ((armIndObs a z - q) * ψ z.1) ^ 2) ν :=
      hψ2.mono' (((hA.sub_const q).mul hψm).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsq z)
    have h1 := condExp_mono
      (m := MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1) inferInstance) he2I hψ2
      (Eventually.of_forall hsq)
    have h2 : ν[fun z : 𝒳 × Bool × ℝ => ψ z.1 ^ 2 |
        MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => z.1) inferInstance] =
        fun z => ψ z.1 ^ 2 :=
      condExp_of_stronglyMeasurable hm
        (by exact ((hψ.pow_const 2).comp (comap_measurable _)).stronglyMeasurable) hψ2
    rwa [h2] at h1

/-- **Residual noise.** If `E[Y | X, A] = μ_A(X)` and `E[(Y - μ_A(X))² | X, A] ≤ σ²` under the
record law, the residual of arm `a`, `1{A = a}(Y - μ_A(X))`, has `E[· | X, A] = 0` and
`E[(·)² | X, A] ≤ max σ² 0`. -/
theorem residual_noise_moments (a : Bool) {mu : Bool → 𝒳 → ℝ} (hmu : ∀ t, Measurable (mu t))
    (hY : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν)
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) ν)
    (hreg : ν[fun z => z.2.2 | MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
      inferInstance] =ᵐ[ν] fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : ν[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[ν]
        fun _ => σ2) :
    ν[fun z => armIndObs a z * (z.2.2 - mu z.2.1 z.1) |
        MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] 0 ∧
      ν[fun z => (armIndObs a z * (z.2.2 - mu z.2.1 z.1)) ^ 2 |
        MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[ν]
        fun _ => max σ2 0 := by
  have hpair : Measurable fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have hm : MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance ≤
      (inferInstance : MeasurableSpace (𝒳 × Bool × ℝ)) := hpair.comap_le
  have hsurf : Measurable fun q : 𝒳 × Bool => mu q.2 q.1 :=
    measurable_from_prod_countable_left (f := fun q : 𝒳 × Bool => mu q.2 q.1) hmu
  have hS : Measurable fun z : 𝒳 × Bool × ℝ => mu z.2.1 z.1 := hsurf.comp hpair
  have hRm : Measurable fun z : 𝒳 × Bool × ℝ => z.2.2 - mu z.2.1 z.1 :=
    measurable_snd.snd.sub hS
  have hRI : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2 - mu z.2.1 z.1) ν :=
    ((memLp_two_iff_integrable_sq hRm.aestronglyMeasurable).2 hres2).integrable one_le_two
  have hSI : Integrable (fun z : 𝒳 × Bool × ℝ => mu z.2.1 z.1) ν :=
    (hY.sub hRI).congr (Eventually.of_forall fun z => by simp)
  have hSsm : StronglyMeasurable[MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
      inferInstance] (fun z : 𝒳 × Bool × ℝ => mu z.2.1 z.1) :=
    (hsurf.comp (comap_measurable _)).stronglyMeasurable
  have hAsm : StronglyMeasurable[MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1))
      inferInstance] (armIndObs (𝒲 := 𝒳) a) := by
    have : armIndObs (𝒲 := 𝒳) a = (fun q : 𝒳 × Bool => if q.2 = a then (1 : ℝ) else 0) ∘
        fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1) := rfl
    rw [this]
    exact (((Measurable.of_discrete (f := fun b : Bool => if b = a then (1 : ℝ) else 0)).comp
      measurable_snd).comp (comap_measurable _)).stronglyMeasurable
  have hA : Measurable (armIndObs (𝒲 := 𝒳) a) := measurable_armIndObs a
  have hAb : ∀ z : 𝒳 × Bool × ℝ, |armIndObs a z| ≤ 1 := fun z => by
    rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> simp
  have hR0 : ν[fun z => z.2.2 - mu z.2.1 z.1 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[ν] 0 := by
    have h1 := condExp_sub
      (m := MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance) hY hSI
    rw [condExp_of_stronglyMeasurable hm hSsm hSI] at h1
    filter_upwards [h1, hreg] with z h1 h2
    change (ν[(fun z : 𝒳 × Bool × ℝ => z.2.2) - fun z => mu z.2.1 z.1 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]) z = 0
    rw [h1]
    simp [h2]
  have hprod : ∀ {f : 𝒳 × Bool × ℝ → ℝ}, Integrable f ν →
      Integrable (fun z => armIndObs a z * f z) ν := fun hf =>
    hf.bdd_mul hA.aestronglyMeasurable (c := 1) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hAb z)
  constructor
  · have h1 := condExp_mul_of_stronglyMeasurable_left hAsm (hprod hRI) hRI
    filter_upwards [h1, hR0] with z h1 h2
    refine h1.trans ?_
    simp only [Pi.mul_apply, Pi.zero_apply] at h2 ⊢
    rw [h2, mul_zero]
  · have hsq : (fun z : 𝒳 × Bool × ℝ => (armIndObs a z * (z.2.2 - mu z.2.1 z.1)) ^ 2) =
        armIndObs a * fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 := by
      funext z
      simp only [Pi.mul_apply, mul_pow]
      rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h] <;> simp
    rw [hsq]
    have h1 := condExp_mul_of_stronglyMeasurable_left hAsm (hprod hres2) hres2
    filter_upwards [h1, hvar] with z h1 h2
    rw [h1]
    simp only [Pi.mul_apply]
    rcases armIndObs_eq_zero_or_one a z with h | h <;> rw [h]
    · simp
    · rw [one_mul]; exact h2.trans (le_max_left _ _)

end TrialNoise

end PopulationAdjustment

end CausalInference
