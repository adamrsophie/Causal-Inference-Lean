/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ExchangeableBinaryUnique
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Exchangeable binary sequences as hierarchical models

The Bernoulli sampling kernel `θ ↦ Bernoulli(θ)` on `Bool` (`bernoulliClampKernel`, Mathlib's
`bernoulliMeasure` at `θ` clamped to `[0, 1]`) and its `n` fold product
`θ ↦ Bernoulli(θ)^{⊗n}` (`bernoulliPiKernel`) turn de Finetti's theorem into a statement about
the mixture laws of the library:

* **The law of the sequence is a mixture of i.i.d. Bernoulli laws**
  (`InfExchangeable.exists_map_eq_bind_bernoulli`): for an infinitely exchangeable binary sequence
  there is a probability measure `Π` on `[0, 1]` with
  `law(X₀, …, X_{n-1}) = ∫ Bernoulli(θ)^{⊗n} dΠ(θ)` for every `n`, the object of
  `exchangeable_of_hasLaw_bind_pi`; with that easy direction this characterizes infinite
  exchangeability (`infExchangeable_iff_hasLaw_bind_bernoulli`).
* **The hierarchical form** (`InfExchangeable.exists_map_eq_hierarchicalLaw`): the same law is
  the law of the data of the hierarchical model `hierarchicalLaw n Π dirac bernoulliClampKernel`, in
  which the hyperparameter `φ ~ Π` is shared by all units (`θᵢ = φ`) and the data are Bernoulli
  draws given it. This is the sense in which exchangeability of binary study outcomes justifies a
  hierarchical model with a common mixing law.

## Main definitions

* `bernoulliClampKernel`, `bernoulliPiKernel`.

## Main results

* `bernoulliClampKernel_singleton`, `bernoulliPiKernel_singleton`,
  `InfExchangeable.exists_map_eq_bind_bernoulli`, `infExchangeable_iff_hasLaw_bind_bernoulli`,
  `dirac_compProd_eq_map`, `pi_dirac_compProd_eq_map`, `map_snd_hierarchicalLaw_dirac`,
  `InfExchangeable.exists_map_eq_hierarchicalLaw`.

## References

* B. de Finetti, *La prévision : ses lois logiques, ses sources subjectives*, Annales de
  l'Institut Henri Poincaré 7 (1937).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal NNReal

/-- The **Bernoulli sampling kernel**: `θ ↦ Bernoulli(θ)` on `Bool`, with `θ` clamped to
`[0, 1]` (Mathlib's `bernoulliMeasure true false`). -/
noncomputable def bernoulliClampKernel : Kernel ℝ Bool where
  toFun θ := bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one θ)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
    simp only [bernoulliMeasure_def, add_apply, smul_apply]
    have h1 : Measurable fun θ : ℝ =>
        ((toNNReal (Set.projIcc 0 1 zero_le_one θ) : ℝ≥0) : ℝ≥0∞) :=
      (ENNReal.continuous_coe.comp (toNNReal_continuous.comp continuous_projIcc)).measurable
    have h2 : Measurable fun θ : ℝ =>
        ((toNNReal (σ (Set.projIcc 0 1 zero_le_one θ)) : ℝ≥0) : ℝ≥0∞) :=
      (ENNReal.continuous_coe.comp (toNNReal_continuous.comp
        (continuous_symm.comp continuous_projIcc))).measurable
    exact (h1.mul_const _).add (h2.mul_const _)

instance : IsMarkovKernel bernoulliClampKernel :=
  ⟨fun θ => by
    change IsProbabilityMeasure (bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one θ))
    infer_instance⟩

/-- On `[0, 1]` the Bernoulli kernel gives `true` the probability `θ` and `false` the
probability `1 - θ`. -/
theorem bernoulliClampKernel_singleton {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (b : Bool) :
    bernoulliClampKernel θ {b} = ENNReal.ofReal (if b then θ else 1 - θ) := by
  change bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one θ) {b} = _
  rw [Set.projIcc_of_mem _ hθ, bernoulliMeasure_apply _ (measurableSet_singleton b)]
  have h1 : (((toNNReal ⟨θ, hθ⟩ : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal θ := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hθ.1]
    rfl
  have h2 : (((toNNReal (σ ⟨θ, hθ⟩) : ℝ≥0)) : ℝ≥0∞) = ENNReal.ofReal (1 - θ) := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (by linarith [hθ.2])]
    rfl
  cases b <;> simp [h1, h2]

/-- The **product Bernoulli kernel** `θ ↦ Bernoulli(θ)^{⊗n}` on `Fin n → Bool`. -/
noncomputable def bernoulliPiKernel (n : ℕ) : Kernel ℝ (Fin n → Bool) where
  toFun θ := Measure.pi fun _ : Fin n => bernoulliClampKernel θ
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
    have hs : ∀ θ, (Measure.pi fun _ : Fin n => bernoulliClampKernel θ) s =
        ∑ x ∈ s.toFinset, ∏ i, bernoulliClampKernel θ {x i} := by
      intro θ
      conv_lhs => rw [← Set.coe_toFinset s, ← MeasureTheory.sum_measure_singleton]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Set.univ_pi_singleton, Measure.pi_pi]
    simp_rw [hs]
    exact Finset.measurable_sum _ fun x _ => Finset.measurable_prod _ fun i _ =>
      Kernel.measurable_coe _ (measurableSet_singleton _)

instance (n : ℕ) : IsMarkovKernel (bernoulliPiKernel n) :=
  ⟨fun θ => by
    change IsProbabilityMeasure (Measure.pi fun _ : Fin n => bernoulliClampKernel θ)
    infer_instance⟩

theorem bernoulliPiKernel_apply (n : ℕ) (θ : ℝ) :
    bernoulliPiKernel n θ = Measure.pi fun _ : Fin n => bernoulliClampKernel θ := rfl

/-- `∏ᵢ (θ if xᵢ else 1 - θ) = θ^s (1 - θ)^{n - s}`, `s` the number of successes of `x`. -/
theorem prod_ite_eq_pow_mul_pow {n : ℕ} (x : Fin n → Bool) (θ : ℝ) :
    ∏ i, (if x i then θ else 1 - θ) = θ ^ boolCount x * (1 - θ) ^ (n - boolCount x) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, boolCount_eq_card_filter]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun j => x j = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [show (Finset.univ.filter fun j => ¬ x j = true).card =
    n - (Finset.univ.filter fun j => x j = true).card by omega]

/-- On `[0, 1]` the product Bernoulli kernel gives the pattern `x` with `s` successes the
probability `θ^s (1 - θ)^{n - s}`. -/
theorem bernoulliPiKernel_singleton {n : ℕ} {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (x : Fin n → Bool) :
    bernoulliPiKernel n θ {x} = ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) := by
  rw [bernoulliPiKernel_apply, ← Set.univ_pi_singleton, Measure.pi_pi]
  simp_rw [bernoulliClampKernel_singleton hθ]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => by
    split_ifs <;> linarith [hθ.1, hθ.2], prod_ite_eq_pow_mul_pow]

/-- For a mixing law concentrated on `[0, 1]`, the mixture `∫ Bernoulli(θ)^{⊗n} dΠ(θ)` gives the
pattern `x` with `s` successes the probability `∫ θ^s (1 - θ)^{n - s} dΠ(θ)`. -/
theorem bind_bernoulli_singleton {μ : Measure ℝ} (hμ : μ (Icc (0 : ℝ) 1)ᶜ = 0) {n : ℕ}
    (x : Fin n → Bool) :
    (μ.bind fun θ => Measure.pi fun _ : Fin n => bernoulliClampKernel θ) {x} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ := by
  have hm : AEMeasurable (fun θ => Measure.pi fun _ : Fin n => bernoulliClampKernel θ) μ :=
    (bernoulliPiKernel n).aemeasurable
  rw [Measure.bind_apply (measurableSet_singleton x) hm]
  exact lintegral_congr_ae (Filter.Eventually.mono (mem_ae_iff.2 hμ) fun θ hθ =>
    bernoulliPiKernel_singleton hθ x)

/-- **The law of an infinitely exchangeable binary sequence is a mixture of i.i.d. Bernoulli
laws** (de Finetti 1937): there is a probability measure `Π` on `ℝ` with `Π([0, 1]ᶜ) = 0` such
that for every `n` the law of `(X₀, …, X_{n-1})` is `∫ Bernoulli(θ)^{⊗n} dΠ(θ)`. -/
theorem InfExchangeable.exists_map_eq_bind_bernoulli {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ n : ℕ, P.map (fun ω (i : Fin n) => X i ω) =
        μ.bind fun θ => Measure.pi fun _ : Fin n => bernoulliClampKernel θ := by
  obtain ⟨μ, hμp, hμs, hμr⟩ := hE.exists_binaryMixture hX
  refine ⟨μ, hμp, hμs, fun n => Measure.ext_iff_singleton.2 fun x => ?_⟩
  have hv : Measurable fun ω (i : Fin n) => X i ω := measurable_pi_iff.2 fun i => hX i
  rw [Measure.map_apply hv (measurableSet_singleton x), bind_bernoulli_singleton hμs, ← hμr n x]
  congr 1
  ext ω
  simp [funext_iff]

/-- **de Finetti's characterization in the mixture form**: a sequence of measurable `Bool`
valued variables on a probability space is infinitely exchangeable if and only if there is a
probability measure `Π` on `[0, 1]` such that for every `n` the vector `(X₀, …, X_{n-1})` has the
law `∫ Bernoulli(θ)^{⊗n} dΠ(θ)`. The converse direction is `exchangeable_of_hasLaw_bind_pi`. -/
theorem infExchangeable_iff_hasLaw_bind_bernoulli {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P] :
    InfExchangeable X P ↔ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ n : ℕ, HasLaw (fun ω (i : Fin n) => X i ω)
        (μ.bind fun θ => Measure.pi fun _ : Fin n => bernoulliClampKernel θ) P := by
  constructor
  · intro hE
    obtain ⟨μ, hμp, hμs, h⟩ := hE.exists_map_eq_bind_bernoulli hX
    exact ⟨μ, hμp, hμs, fun n =>
      ⟨(measurable_pi_iff.2 fun (i : Fin n) => hX i).aemeasurable, h n⟩⟩
  · rintro ⟨μ, _, _, h⟩ n
    exact exchangeable_of_hasLaw_bind_pi (bernoulliPiKernel n).aemeasurable (h n)

/-! ### The hierarchical model with a shared parameter -/

/-- The joint law of a point mass and a kernel is the kernel's law pushed along `y ↦ (a, y)`. -/
theorem dirac_compProd_eq_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) :
    Measure.dirac a ⊗ₘ κ = (κ a).map (Prod.mk a) := by
  ext s hs
  rw [Measure.dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]

/-- With the point mass at `φ` as population law, the units `(θᵢ, yᵢ)` of the hierarchical model
are `(φ, yᵢ)` with `y₁, …, yₙ` i.i.d. from the sampling law at `φ`. -/
theorem pi_dirac_compProd_eq_map {β : Type*} [MeasurableSpace β] (κ : Kernel ℝ β)
    [IsMarkovKernel κ] (n : ℕ) (φ : ℝ) :
    (Measure.pi fun _ : Fin n => Measure.dirac φ ⊗ₘ κ) =
      (Measure.pi fun _ : Fin n => κ φ).map (fun y i => (φ, y i)) := by
  simp_rw [dirac_compProd_eq_map]
  rw [Measure.pi_map_pi (fun _ => measurable_prodMk_left.aemeasurable)]

/-- The map `φ ↦ (Measure.dirac φ ⊗ₘ κ)^{⊗n}` is measurable: it is the kernel
`φ ↦ (δ_φ × κ^{⊗n}(φ))` pushed along `(φ, y) ↦ ((φ, y₁), …, (φ, yₙ))`. -/
theorem measurable_pi_dirac_compProd {β : Type*} [MeasurableSpace β] (κ : Kernel ℝ β)
    [IsMarkovKernel κ] (n : ℕ) (K : Kernel ℝ (Fin n → β))
    (hK : ∀ φ, K φ = Measure.pi fun _ : Fin n => κ φ) :
    Measurable fun φ => Measure.pi fun _ : Fin n => Measure.dirac φ ⊗ₘ κ := by
  have : IsMarkovKernel K := ⟨fun φ => by rw [hK]; infer_instance⟩
  have hG : Measurable fun p : ℝ × (Fin n → β) => fun i => (p.1, p.2 i) := by fun_prop
  have h : (fun φ => Measure.pi fun _ : Fin n => Measure.dirac φ ⊗ₘ κ) =
      ⇑((Kernel.deterministic id measurable_id ×ₖ K).map fun p => fun i => (p.1, p.2 i)) := by
    funext φ
    rw [Kernel.map_apply _ hG, Kernel.prod_apply, Kernel.deterministic_apply, id,
      Measure.dirac_prod, Measure.map_map hG measurable_prodMk_left, pi_dirac_compProd_eq_map,
      hK]
    rfl
  rw [h]
  exact Kernel.measurable _

/-- **The data of the hierarchical model with a shared parameter**: in
`hierarchicalLaw n Π dirac κ` (hyperparameter `φ ~ Π`, every unit parameter equal to `φ`, data
from `κ`) the data `(y₁, …, yₙ)` have the mixture law `∫ κ(φ)^{⊗n} dΠ(φ)`. -/
theorem map_snd_hierarchicalLaw_dirac {β : Type*} [MeasurableSpace β] (κ : Kernel ℝ β)
    [IsMarkovKernel κ] (n : ℕ) (K : Kernel ℝ (Fin n → β))
    (hK : ∀ φ, K φ = Measure.pi fun _ : Fin n => κ φ) (μ : Measure ℝ) :
    (hierarchicalLaw n μ (fun φ => Measure.dirac φ) κ).map (fun u i => (u i).2) =
      μ.bind fun φ => Measure.pi fun _ : Fin n => κ φ := by
  have hm : Measurable fun (u : Fin n → ℝ × β) i => (u i).2 := by fun_prop
  rw [hierarchicalLaw, Measure.map_bind (measurable_pi_dirac_compProd κ n K hK).aemeasurable
    hm.aemeasurable]
  congr 1
  funext φ
  rw [pi_dirac_compProd_eq_map, Measure.map_map hm (by fun_prop)]
  exact Measure.map_id

/-- **An infinitely exchangeable binary sequence is the data of a hierarchical model** (de Finetti
1937): there is a probability measure `Π` on `[0, 1]` such that for every `n` the law of
`(X₀, …, X_{n-1})` is the law of the data of `hierarchicalLaw n Π dirac bernoulliClampKernel`: a
parameter `φ ~ Π` shared by the units, and given it i.i.d. Bernoulli(`φ`) outcomes. -/
theorem InfExchangeable.exists_map_eq_hierarchicalLaw {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ n : ℕ, P.map (fun ω (i : Fin n) => X i ω) =
        (hierarchicalLaw n μ (fun φ => Measure.dirac φ) bernoulliClampKernel).map
          (fun u i => (u i).2) := by
  obtain ⟨μ, hμp, hμs, h⟩ := hE.exists_map_eq_bind_bernoulli hX
  exact ⟨μ, hμp, hμs, fun n => by
    rw [h n, map_snd_hierarchicalLaw_dirac bernoulliClampKernel n (bernoulliPiKernel n)
      (bernoulliPiKernel_apply n)]⟩

end MetaAnalysis

end CausalInference
