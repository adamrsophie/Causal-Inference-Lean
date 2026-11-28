/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Exchangeability and mixtures of i.i.d. laws

Random variables `X₁, …, Xₙ` are **exchangeable** if the joint law of `(X_{σ 1}, …, X_{σ n})` is
that of `(X₁, …, Xₙ)` for every permutation `σ` (`Exchangeable`); a sequence is **infinitely
exchangeable** if every initial segment is exchangeable (`InfExchangeable`).

* `exchangeable_of_hasLaw_bind_pi`: a **mixture of i.i.d. laws** `∫ Q_θ^{⊗n} dΠ(θ)` is
  exchangeable (no densities are needed).
* `Exchangeable.comp`: exchangeability passes to coordinatewise images.
* `infExchangeable_of_binary_mixture`: a binary sequence whose finite dimensional laws are
  `P(X₁ = x₁, …, Xₙ = xₙ) = ∫ θ^s (1 - θ)^{n - s} dΠ(θ)`, `s = ∑ xᵢ`, is infinitely exchangeable.
  This is the easy direction of de Finetti's theorem for binary sequences (de Finetti 1937). The
  converse, that every infinitely exchangeable binary sequence has this form, is
  `InfExchangeable.exists_binaryMixture` in `ExchangeableBinaryMixing`.
* **Finite exchangeability does not give a mixture** (`urnLaw_exchangeable`,
  `urnLaw_not_iidMixture`): two draws without replacement from an urn with one ball of each
  color are exchangeable, but their law is no mixture of i.i.d. laws of any kind: the draws
  differ almost surely, while under every i.i.d. law `Q ⊗ Q` on `Bool²` two draws agree with
  probability `q² + (1 - q)² ≥ 1/2`. (Diaconis and Freedman 1980 quantify how far a finite
  exchangeable law can be from a mixture.)
* **The units of a hierarchical model are exchangeable** (`hierarchicalLaw`,
  `exchangeable_of_hasLaw_hierarchicalLaw`): if `φ ~ π`, the unit parameters `θᵢ` are i.i.d.
  from `pop φ` given `φ`, and `yᵢ` is drawn from a common sampling kernel `samp θᵢ` given the
  `θ`'s, then the pairs `(θᵢ, yᵢ)` are exchangeable, and so are the `θᵢ` and the `yᵢ` alone. A
  common sampling kernel is needed: with study specific sampling laws (for example known but
  unequal within study variances `vᵢ`) the `yᵢ` are not exchangeable in general.

## Main definitions

* `Exchangeable`, `InfExchangeable`, `boolCount`, `urnLaw`, `hierarchicalLaw`.

## Main results

* `measure_pi_map_perm`, `exchangeable_of_hasLaw_bind_pi`, `Exchangeable.comp`,
  `infExchangeable_of_binary_mixture`, `urnLaw_exchangeable`, `urnLaw_not_iidMixture`,
  `exchangeable_of_hasLaw_hierarchicalLaw`.

## References

* B. de Finetti, *La prévision : ses lois logiques, ses sources subjectives*, Annales de
  l'Institut Henri Poincaré 7 (1937).
* P. Diaconis and D. Freedman, *Finite exchangeable sequences*, Annals of Probability 8 (1980).
* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- **Exchangeability**: `X₁, …, Xₙ` are exchangeable under `P` if for every permutation `σ` the
vector `(X_{σ 1}, …, X_{σ n})` has the law of `(X₁, …, Xₙ)`. -/
def Exchangeable {n : ℕ} (X : Fin n → Ω → S) (P : Measure Ω) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), P.map (fun ω i => X (σ i) ω) = P.map (fun ω i => X i ω)

/-- **Infinite exchangeability**: every initial segment `X₀, …, X_{n-1}` is exchangeable. -/
def InfExchangeable (X : ℕ → Ω → S) (P : Measure Ω) : Prop :=
  ∀ n : ℕ, Exchangeable (fun i : Fin n => X i) P

/-- An i.i.d. product law is invariant under permutations of the coordinates. -/
theorem measure_pi_map_perm {n : ℕ} (Q : Measure S) [SigmaFinite Q] (σ : Equiv.Perm (Fin n)) :
    (Measure.pi fun _ : Fin n => Q).map (fun x i => x (σ i)) = Measure.pi fun _ : Fin n => Q := by
  have hm : Measurable fun (x : Fin n → S) i => x (σ i) := by fun_prop
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun (x : Fin n → S) i => x (σ i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun j => s (σ.symm j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact ⟨fun h j => by simpa using h (σ.symm j), fun h i => by simpa using h (σ i)⟩
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp σ.symm fun i => Q (s i)

/-- **Mixtures of i.i.d. laws are exchangeable**: if the joint law of `(X₁, …, Xₙ)` is
`∫ Q_θ^{⊗n} dΠ(θ)`, then `X₁, …, Xₙ` are exchangeable. Proof: permuting the coordinates commutes
with the mixture and leaves every i.i.d. product unchanged. -/
theorem exchangeable_of_hasLaw_bind_pi {T : Type*} [MeasurableSpace T] {n : ℕ}
    {X : Fin n → Ω → S} {P : Measure Ω} {Pr : Measure T} {Q : T → Measure S}
    [∀ θ, SigmaFinite (Q θ)] (hQ : AEMeasurable (fun θ => Measure.pi fun _ : Fin n => Q θ) Pr)
    (hX : HasLaw (fun ω i => X i ω) (Pr.bind fun θ => Measure.pi fun _ : Fin n => Q θ) P) :
    Exchangeable X P := by
  intro σ
  have hm : Measurable fun (x : Fin n → S) i => x (σ i) := by fun_prop
  have hcomp : (fun ω i => X (σ i) ω) = (fun (x : Fin n → S) i => x (σ i)) ∘
      fun ω i => X i ω := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hX.aemeasurable, hX.map_eq,
    Measure.map_bind hQ hm.aemeasurable]
  simp_rw [measure_pi_map_perm]

/-- **Exchangeability passes to coordinatewise images**: if `X₁, …, Xₙ` are exchangeable and
almost everywhere measurable, then so are `f(X₁), …, f(Xₙ)` for measurable `f`. -/
theorem Exchangeable.comp {S' : Type*} [MeasurableSpace S'] {n : ℕ} {X : Fin n → Ω → S}
    {P : Measure Ω} (h : Exchangeable X P) (hX : ∀ i, AEMeasurable (X i) P) {f : S → S'}
    (hf : Measurable f) : Exchangeable (fun i ω => f (X i ω)) P := by
  intro σ
  have hF : Measurable fun (x : Fin n → S) i => f (x i) := by fun_prop
  have hv : AEMeasurable (fun ω i => X i ω) P := AEMeasurable.of_eval hX
  have hvσ : AEMeasurable (fun ω i => X (σ i) ω) P := AEMeasurable.of_eval fun i => hX _
  have e1 : (fun ω i => f (X (σ i) ω)) = (fun (x : Fin n → S) i => f (x i)) ∘
      fun ω i => X (σ i) ω := rfl
  have e2 : (fun ω i => f (X i ω)) = (fun (x : Fin n → S) i => f (x i)) ∘
      fun ω i => X i ω := rfl
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hvσ,
    ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hv, h σ]

/-- The number of successes `∑ᵢ xᵢ` of a binary vector. -/
def boolCount {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, (x i).toNat

theorem boolCount_perm {n : ℕ} (x : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    boolCount (fun i => x (σ i)) = boolCount x :=
  Equiv.sum_comp σ fun i => (x i).toNat

/-- **Binary mixtures are infinitely exchangeable** (the easy direction of de Finetti's theorem,
de Finetti 1937). If a sequence of measurable `Bool` valued variables has, for every `n` and every
pattern `x` with `s = ∑ xᵢ` successes, `P(X₀ = x₀, …, X_{n-1} = x_{n-1}) =
∫ θ^s (1 - θ)^{n - s} dΠ(θ)`, then it is infinitely exchangeable. The converse direction is
`InfExchangeable.exists_binaryMixture`. Proof: on `Bool^n` a law is determined by its atoms,
and permuting a pattern does not change its number of successes. -/
theorem infExchangeable_of_binary_mixture {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} {Pr : Measure ℝ}
    (h : ∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂Pr) :
    InfExchangeable X P := by
  intro n σ
  have hv : Measurable fun ω (i : Fin n) => X i ω := Measurable.of_eval fun i => hX i
  have hvσ : Measurable fun ω (i : Fin n) => X (σ i) ω := Measurable.of_eval fun i => hX _
  refine Measure.ext_iff_singleton.2 fun x => ?_
  rw [Measure.map_apply hvσ (measurableSet_singleton x),
    Measure.map_apply hv (measurableSet_singleton x)]
  have h1 : (fun ω (i : Fin n) => X (σ i) ω) ⁻¹' {x} =
      {ω | ∀ j : Fin n, X j ω = x (σ.symm j)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_ofPred_eq]
    exact ⟨fun h j => by simpa using h (σ.symm j), fun h i => by simpa using h (σ i)⟩
  have h2 : (fun ω (i : Fin n) => X i ω) ⁻¹' {x} = {ω | ∀ j : Fin n, X j ω = x j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_ofPred_eq]
  rw [h1, h2, h n, h n, boolCount_perm x σ.symm]

/-! ### The urn: finite exchangeability without a mixture -/

/-- The law of two draws without replacement from an urn with one ball of each color: the
outcomes `(true, false)` and `(false, true)`, each with probability `1/2`. -/
noncomputable def urnLaw : Measure (Fin 2 → Bool) :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac ![true, false] + Measure.dirac ![false, true])

instance : IsProbabilityMeasure urnLaw :=
  ⟨by
    simp only [urnLaw, smul_apply, add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

/-- **The two draws are exchangeable.** -/
theorem urnLaw_exchangeable : Exchangeable (fun i (ω : Fin 2 → Bool) => ω i) urnLaw := by
  intro σ
  have hm : Measurable fun (ω : Fin 2 → Bool) (i : Fin 2) => ω (σ i) := by fun_prop
  change urnLaw.map (fun ω i => ω (σ i)) = urnLaw.map (fun ω i => ω i)
  rw [urnLaw, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm,
    Measure.map_dirac' hm]
  swap
  · exact hm.aemeasurable
  have hid : (fun ω i => (ω : Fin 2 → Bool) i) = id := rfl
  rw [hid, Measure.map_id]
  congr 1
  rcases Fin.exists_fin_two.1 ⟨σ 0, rfl⟩ with h0 | h0
  · have h1 : σ 1 = 1 := by
      have := σ.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
      rw [h0] at this
      omega
    have e1 : (fun i => (![true, false] : Fin 2 → Bool) (σ i)) = ![true, false] := by
      funext i; fin_cases i <;> simp [h0, h1]
    have e2 : (fun i => (![false, true] : Fin 2 → Bool) (σ i)) = ![false, true] := by
      funext i; fin_cases i <;> simp [h0, h1]
    rw [e1, e2]
  · have h1 : σ 1 = 0 := by
      have := σ.injective.ne (show (0 : Fin 2) ≠ 1 by decide)
      rw [h0] at this
      omega
    have e1 : (fun i => (![true, false] : Fin 2 → Bool) (σ i)) = ![false, true] := by
      funext i; fin_cases i <;> simp [h0, h1]
    have e2 : (fun i => (![false, true] : Fin 2 → Bool) (σ i)) = ![true, false] := by
      funext i; fin_cases i <;> simp [h0, h1]
    rw [e1, e2, add_comm]

/-- **The urn law is no mixture of i.i.d. laws**: for no probability measure `Π` on any
parameter space and no family of probability laws `Q_θ` on `Bool` is the urn law equal to
`∫ Q_θ ⊗ Q_θ dΠ(θ)` (with the mixing map measurable, as the mixture requires). Proof: the event
`{x₀ = x₁}` has urn probability `0`, while
`(Q_θ ⊗ Q_θ){x₀ = x₁} = Q_θ{true}² + Q_θ{false}² ≥ 1/2` for every `θ`. -/
theorem urnLaw_not_iidMixture {T : Type*} [MeasurableSpace T] (Pr : Measure T)
    [IsProbabilityMeasure Pr] (Q : T → Measure Bool) [∀ θ, IsProbabilityMeasure (Q θ)]
    (hm : AEMeasurable (fun θ => Measure.pi fun _ : Fin 2 => Q θ) Pr) :
    urnLaw ≠ Pr.bind fun θ => Measure.pi fun _ : Fin 2 => Q θ := by
  intro h
  set E : Set (Fin 2 → Bool) := {x | x 0 = x 1}
  have hE : MeasurableSet E := (Set.toFinite E).measurableSet
  have hurn : urnLaw E = 0 := by
    simp [urnLaw, E, Measure.dirac_apply' _ hE, Set.indicator]
  have hpi : ∀ θ, (2 : ℝ≥0∞)⁻¹ ≤ (Measure.pi fun _ : Fin 2 => Q θ) E := by
    intro θ
    have hsplit : E = Set.univ.pi (fun _ => {true}) ∪ Set.univ.pi (fun _ => {false}) := by
      ext x
      simp only [E, Set.mem_ofPred_eq, Set.mem_union, Set.mem_univ_pi, Set.mem_singleton_iff,
        Fin.forall_fin_two]
      cases x 0 <;> cases x 1 <;> simp
    have hdisj : Disjoint (Set.univ.pi (fun _ : Fin 2 => ({true} : Set Bool)))
        (Set.univ.pi fun _ => {false}) := by
      rw [Set.disjoint_left]
      intro x h1 h2
      have a := h1 0 (Set.mem_univ _)
      have b := h2 0 (Set.mem_univ _)
      simp only [Set.mem_singleton_iff] at a b
      rw [a] at b
      exact Bool.noConfusion b
    rw [hsplit, measure_union hdisj (MeasurableSet.univ_pi fun _ => measurableSet_singleton _),
      Measure.pi_pi, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hsum : Q θ {true} + Q θ {false} = 1 := by
      rw [← measure_union (by simp) (measurableSet_singleton _)]
      have : ({true} ∪ {false} : Set Bool) = Set.univ := by
        ext b; cases b <;> simp
      rw [this, measure_univ]
    have ht : Q θ {true} ≠ ∞ := measure_ne_top _ _
    have hf : Q θ {false} ≠ ∞ := measure_ne_top _ _
    have hr : (Q θ {true}).toReal + (Q θ {false}).toReal = 1 := by
      rw [← ENNReal.toReal_add ht hf, hsum, ENNReal.toReal_one]
    rw [← ENNReal.ofReal_toReal ht, ← ENNReal.ofReal_toReal hf,
      ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
        rw [ENNReal.ofReal_div_of_pos two_pos]; simp]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg ((Q θ {true}).toReal -
      (Q θ {false}).toReal)])
  have hbind := Measure.bind_apply hE hm
  rw [← h, hurn] at hbind
  have hle : ∫⁻ _ : T, (2 : ℝ≥0∞)⁻¹ ∂Pr ≤ ∫⁻ θ, (Measure.pi fun _ : Fin 2 => Q θ) E ∂Pr :=
    lintegral_mono hpi
  rw [← hbind, lintegral_const, measure_univ, mul_one, nonpos_iff_eq_zero] at hle
  exact ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top hle

/-! ### The units of a hierarchical model -/

variable {Φ Θ Y : Type*} [MeasurableSpace Φ] [MeasurableSpace Θ] [MeasurableSpace Y]

/-- The **joint law of the units of a two level hierarchical model**: the hyperparameter
`φ ~ hyper`; given `φ` the unit parameters `θ₁, …, θₙ` are i.i.d. from `pop φ`; given the
parameters the data `yᵢ` are independent from the common sampling kernel `samp θᵢ`. The law of
the units `(θᵢ, yᵢ)` is `∫ (pop φ ⊗ samp)^{⊗n} d hyper(φ)`. -/
noncomputable def hierarchicalLaw (n : ℕ) (hyper : Measure Φ) (pop : Φ → Measure Θ)
    (samp : Kernel Θ Y) : Measure (Fin n → Θ × Y) :=
  hyper.bind fun φ => Measure.pi fun _ : Fin n => pop φ ⊗ₘ samp

/-- **The units of a hierarchical model are exchangeable**: if the units `(θᵢ, yᵢ)` have the law
`hierarchicalLaw n hyper pop samp` (probability laws `pop φ`, Markov sampling kernel), then the
pairs `(θᵢ, yᵢ)` are exchangeable, the unit parameters `θᵢ` are exchangeable, and the data `yᵢ`
are exchangeable. The measurability of the mixing map is a side condition. -/
theorem exchangeable_of_hasLaw_hierarchicalLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {θ : Fin n → Ω → Θ} {y : Fin n → Ω → Y} {hyper : Measure Φ} {pop : Φ → Measure Θ}
    [∀ φ, IsProbabilityMeasure (pop φ)] {samp : Kernel Θ Y} [IsMarkovKernel samp]
    (hm : AEMeasurable (fun φ => Measure.pi fun _ : Fin n => pop φ ⊗ₘ samp) hyper)
    (h : HasLaw (fun ω i => (θ i ω, y i ω)) (hierarchicalLaw n hyper pop samp) P) :
    Exchangeable (fun i ω => (θ i ω, y i ω)) P ∧ Exchangeable θ P ∧ Exchangeable y P := by
  have hpair : Exchangeable (fun i ω => (θ i ω, y i ω)) P :=
    exchangeable_of_hasLaw_bind_pi hm h
  have hae : ∀ i, AEMeasurable (fun ω => (θ i ω, y i ω)) P := fun i =>
    (measurable_pi_apply i).comp_aemeasurable h.aemeasurable
  exact ⟨hpair, hpair.comp hae measurable_fst, hpair.comp hae measurable_snd⟩

end MetaAnalysis

end CausalInference
