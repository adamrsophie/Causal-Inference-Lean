/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountMixedPoisson

/-!
# Aggregate Poisson counts with exposure times

Patient `i` of an arm is followed for an exposure time `eᵢ ≥ 0`, has covariates `xᵢ` drawn
independently from `F`, and has a `Po(eᵢ r(xᵢ))` count of events. The arm reports the total
count `S = ∑ Yᵢ` and the total exposure `E = ∑ eᵢ`.

* **Mean and variance** (`integral_count_exposure`, `variance_count_exposure`):
  `E S = E ∫ r dF` and `Var S = E ∫ r dF + (∑ eᵢ²) Var r`.
* **Overdispersion and its equality case** (`integral_le_variance_count_exposure`,
  `variance_count_exposure_eq_iff`): `Var S ≥ E S`, with equality exactly when the rate is
  almost surely constant (for positive exposures).
* **The aggregate count with total exposure** (`map_count_exposure_of_ae_eq`): for an almost
  surely constant rate `c` the count is `Po(c E)`.
* **The multilevel model with a log exposure offset** (`MultilevelModel.integral_count_offset`,
  `MultilevelModel.variance_count_offset`): with rate `exp(η_k(x) + log eᵢ)` the count has
  mean `E θ` and variance `E θ + (∑ eᵢ²) Var exp(η_k)`, with `θ` the aggregate arm mean.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalInference

namespace NetworkMetaRegression

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {F : Measure 𝒳} [IsProbabilityMeasure F]
  {r : 𝒳 → ℝ} {n : ℕ}

/-- The joint law of an arm of `n` patients with exposure times `e` and event rate `r`:
patient `i` has covariates from `F` and a `Po(eᵢ r(x))` count. -/
noncomputable def exposureArm (F : Measure 𝒳) (r : 𝒳 → ℝ) (hr : Measurable r) (e : Fin n → ℝ) :
    Measure (Fin n → 𝒳 × ℕ) :=
  Measure.pi fun i => F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))

variable {hr : Measurable r} {e : Fin n → ℝ}

instance : IsProbabilityMeasure (exposureArm F r hr e) := by
  unfold exposureArm; infer_instance

private lemma integral_coord_exposureArm (i : Fin n) (g : ℕ → ℝ) :
    ∫ w, g (w i).2 ∂exposureArm F r hr e =
      ∫ k, g k ∂(F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))).snd := by
  rw [Measure.snd, integral_map measurable_snd.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable, exposureArm,
    ← (measurePreserving_eval (μ := fun i => F ⊗ₘ
      poissonKernel (fun x => e i * r x) (hr.const_mul (e i))) i).map_eq,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

/-- **The mean of the aggregate count with exposures**: `E S = (∑ eᵢ) ∫ r dF`. -/
theorem integral_count_exposure (h0 : ∀ x, 0 ≤ r x) (he : ∀ i, 0 ≤ e i) (hri : Integrable r F) :
    ∫ w, ((∑ i, (w i).2 : ℕ) : ℝ) ∂exposureArm F r hr e = (∑ i, e i) * ∫ x, r x ∂F := by
  have hi : ∀ i, Integrable (fun k : ℕ => (k : ℝ))
      (F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))).snd ∧
      ∫ k, (k : ℝ) ∂(F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))).snd =
        ∫ x, e i * r x ∂F := fun i =>
    integral_snd_compProd_poissonKernel (fun x => mul_nonneg (he i) (h0 x)) (hri.const_mul _)
  simp only [Nat.cast_sum]
  rw [integral_finsetSum _ fun i _ => ?_]
  · simp_rw [integral_coord_exposureArm (hr := hr) _ (fun k : ℕ => (k : ℝ)), fun i => (hi i).2,
      integral_const_mul, Finset.sum_mul]
  · have := (hi i).1
    rw [Measure.snd, integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
      measurable_snd.aemeasurable] at this
    exact (measurePreserving_eval (μ := fun i => F ⊗ₘ
      poissonKernel (fun x => e i * r x) (hr.const_mul (e i))) i).integrable_comp_of_integrable
        (g := fun p : 𝒳 × ℕ => (p.2 : ℝ)) this

/-- **The variance of the aggregate count with exposures**:
`Var S = (∑ eᵢ) ∫ r dF + (∑ eᵢ²) Var r`. -/
theorem variance_count_exposure (h0 : ∀ x, 0 ≤ r x) (he : ∀ i, 0 ≤ e i) (hr2 : MemLp r 2 F) :
    variance (fun w => ((∑ i, (w i).2 : ℕ) : ℝ)) (exposureArm F r hr e) =
      (∑ i, e i) * ∫ x, r x ∂F + (∑ i, e i ^ 2) * variance r F := by
  have hv : ∀ i, MemLp (fun k : ℕ => (k : ℝ)) 2
      (F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))).snd ∧
      variance (fun k : ℕ => (k : ℝ))
        (F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))).snd =
        ∫ x, e i * r x ∂F + variance (fun x => e i * r x) F := fun i =>
    variance_snd_compProd_poissonKernel (fun x => mul_nonneg (he i) (h0 x)) (hr2.const_mul _)
  have hm : ∀ i, MemLp (fun p : 𝒳 × ℕ => (p.2 : ℝ)) 2
      (F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))) := fun i => by
    have := (hv i).1
    rw [Measure.snd, memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable
      measurable_snd.aemeasurable] at this
    exact this
  have h := variance_sum_pi (X := fun _ (p : 𝒳 × ℕ) => (p.2 : ℝ)) hm
  have e1 : (∑ i : Fin n, fun w : Fin n → 𝒳 × ℕ => ((w i).2 : ℝ)) =
      fun w => ((∑ i, (w i).2 : ℕ) : ℝ) := by
    funext w; simp
  rw [e1] at h
  rw [exposureArm, h]
  have hvi : ∀ i, variance (fun p : 𝒳 × ℕ => (p.2 : ℝ))
      (F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))) =
        e i * ∫ x, r x ∂F + e i ^ 2 * variance r F := fun i => by
    rw [show (fun p : 𝒳 × ℕ => (p.2 : ℝ)) = (fun k : ℕ => (k : ℝ)) ∘ Prod.snd from rfl,
      ← variance_map Measurable.of_discrete.aemeasurable measurable_snd.aemeasurable]
    change variance _ (F ⊗ₘ _).snd = _
    rw [(hv i).2, integral_const_mul]
    rw [show (fun x => e i * r x) = e i • r from rfl, variance_smul]
  simp_rw [hvi, Finset.sum_add_distrib, Finset.sum_mul]

/-- **Overdispersion with exposures**: the variance of the aggregate count is at least its
mean. -/
theorem integral_le_variance_count_exposure (h0 : ∀ x, 0 ≤ r x) (he : ∀ i, 0 ≤ e i)
    (hr2 : MemLp r 2 F) :
    ∫ w, ((∑ i, (w i).2 : ℕ) : ℝ) ∂exposureArm F r hr e ≤
      variance (fun w => ((∑ i, (w i).2 : ℕ) : ℝ)) (exposureArm F r hr e) := by
  rw [integral_count_exposure h0 he (hr2.integrable one_le_two), variance_count_exposure h0 he hr2]
  exact le_add_of_nonneg_right (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (variance_nonneg _ _))

/-- **Equidispersion with exposures only for a constant rate**: for `n ≥ 1` positive exposures,
the variance of the aggregate count equals its mean exactly when the rate is almost surely
constant. -/
theorem variance_count_exposure_eq_iff (h0 : ∀ x, 0 ≤ r x) (he : ∀ i, 0 < e i)
    (hr2 : MemLp r 2 F) (hn : 0 < n) :
    variance (fun w => ((∑ i, (w i).2 : ℕ) : ℝ)) (exposureArm F r hr e) =
        ∫ w, ((∑ i, (w i).2 : ℕ) : ℝ) ∂exposureArm F r hr e ↔
      ∃ c : ℝ, r =ᵐ[F] fun _ => c := by
  have h1 := variance_count_poisson_eq_integral_iff (hr := hr) h0 hr2 one_pos
  rw [variance_count_poisson h0 hr2, integral_count_poisson h0 (hr2.integrable one_le_two)]
    at h1
  rw [← h1, integral_count_exposure (fun x => h0 x) (fun i => (he i).le)
    (hr2.integrable one_le_two), variance_count_exposure h0 (fun i => (he i).le) hr2]
  have hs : 0 < ∑ i, e i ^ 2 :=
    Finset.sum_pos (fun i _ => pow_pos (he i) 2) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  constructor
  · intro h
    have : (∑ i, e i ^ 2) * variance r F = 0 := by linarith
    rw [mul_eq_zero, or_iff_right hs.ne'] at this
    simp [this]
  · intro h
    have : variance r F = 0 := by simpa using h
    simp [this]

/-- **The aggregate count with total exposure**: for an almost surely constant rate `c ≥ 0`, the
count of the arm is `Po(c E)`, `E = ∑ eᵢ`. -/
theorem map_count_exposure_of_ae_eq (he : ∀ i, 0 ≤ e i) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : r =ᵐ[F] fun _ => c) (h0 : ∀ x, 0 ≤ r x) :
    (exposureArm F r hr e).map (fun w => ∑ i, (w i).2) =
      poissonMeasure (c * ∑ i, e i).toNNReal := by
  refine eq_of_generatingFunction_eqOn fun z hz => ?_
  have hz' : |z| ≤ 1 := (abs_lt.mpr hz).le
  have hind : iIndepFun (fun (i : Fin n) (w : Fin n → 𝒳 × ℕ) => (w i).2) (exposureArm F r hr e) :=
    iIndepFun_pi (X := fun _ (p : 𝒳 × ℕ) => p.2) fun _ => measurable_snd.aemeasurable
  rw [(generatingFunction_map_sum (Y := fun (i : Fin n) (w : Fin n → 𝒳 × ℕ) => (w i).2)
    (fun i => by fun_prop) hind hz').2, generatingFunction_poissonMeasure _ hz',
    Real.coe_toNNReal _ (mul_nonneg hc0 (Finset.sum_nonneg fun i _ => he i))]
  have hmap : ∀ i : Fin n, (exposureArm F r hr e).map (fun w => (w i).2) =
      (F ⊗ₘ poissonKernel (fun x => e i * r x) (hr.const_mul (e i))).snd := fun i => by
    rw [show (fun w : Fin n → 𝒳 × ℕ => (w i).2) = Prod.snd ∘ fun w => w i from rfl,
      ← Measure.map_map measurable_snd (measurable_pi_apply i), exposureArm,
      (measurePreserving_eval (μ := fun i => F ⊗ₘ
        poissonKernel (fun x => e i * r x) (hr.const_mul (e i))) i).map_eq]
    rfl
  simp_rw [hmap]
  rw [Finset.prod_congr rfl fun i _ => generatingFunction_snd_poissonKernel F
    (hr.const_mul (e i)) (fun x => mul_nonneg (he i) (h0 x)) hz']
  have hci : ∀ i, ∫ x, Real.exp (e i * r x * (z - 1)) ∂F = Real.exp (e i * c * (z - 1)) :=
    fun i => by
      rw [integral_congr_ae (hc.mono fun x hx => by rw [hx]), integral_const]
      simp
  simp_rw [hci, ← Real.exp_sum, Finset.mul_sum]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The multilevel model with a log exposure offset -/

namespace MultilevelModel

variable {J K : Type*} {p : ℕ} (M : MultilevelModel J K p) (α : ℝ) (k : K)
  {G : Measure (Fin p → ℝ)} [IsProbabilityMeasure G]

/-- The log link with an offset `log e` is the rate `e exp(η_k(x))` for `e > 0`. -/
theorem exp_eta_add_log {e : ℝ} (he : 0 < e) (x : Fin p → ℝ) :
    Real.exp (M.eta α k x + Real.log e) = e * M.surface Real.exp α k x := by
  rw [Real.exp_add, Real.exp_log he, mul_comm]
  rfl

/-- The joint law of an arm with exposure times `e` under the log link with offset `log eᵢ`. -/
noncomputable def offsetArm (G : Measure (Fin p → ℝ)) (e : Fin n → ℝ) :
    Measure (Fin n → (Fin p → ℝ) × ℕ) :=
  Measure.pi fun i => G ⊗ₘ poissonKernel (fun x => Real.exp (M.eta α k x + Real.log (e i)))
    (Real.measurable_exp.comp ((M.measurable_surface measurable_id α k).add_const _))

omit [IsProbabilityMeasure G] in
theorem offsetArm_eq_exposureArm (he : ∀ i, 0 < e i) :
    M.offsetArm α k G e =
      exposureArm G (M.surface Real.exp α k) (M.measurable_surface Real.measurable_exp α k) e := by
  unfold offsetArm exposureArm
  congr 1
  funext i
  congr 2
  exact funext fun x => M.exp_eta_add_log α k (he i) x

/-- **The mean of the multilevel count with a log exposure offset**: `(∑ eᵢ) θ`, with `θ` the
aggregate arm mean of `exp(η_k)`. -/
theorem integral_count_offset (he : ∀ i, 0 < e i)
    (hG : Integrable (M.surface Real.exp α k) G) :
    ∫ w, ((∑ i, (w i).2 : ℕ) : ℝ) ∂M.offsetArm α k G e = (∑ i, e i) * M.armMean Real.exp α G k := by
  rw [offsetArm_eq_exposureArm M α k he]
  exact integral_count_exposure (fun x => (Real.exp_pos _).le) (fun i => (he i).le) hG

/-- **The variance of the multilevel count with a log exposure offset**:
`(∑ eᵢ) θ + (∑ eᵢ²) Var exp(η_k)`. -/
theorem variance_count_offset (he : ∀ i, 0 < e i) (hG : MemLp (M.surface Real.exp α k) 2 G) :
    variance (fun w => ((∑ i, (w i).2 : ℕ) : ℝ)) (M.offsetArm α k G e) =
      (∑ i, e i) * M.armMean Real.exp α G k +
        (∑ i, e i ^ 2) * variance (M.surface Real.exp α k) G := by
  rw [offsetArm_eq_exposureArm M α k he]
  exact variance_count_exposure (fun x => (Real.exp_pos _).le) (fun i => (he i).le) hG

end MultilevelModel

end NetworkMetaRegression

end CausalInference
