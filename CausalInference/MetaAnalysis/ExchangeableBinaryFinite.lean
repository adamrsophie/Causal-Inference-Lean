/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.Exchangeable
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Finset.Powerset

/-!
# Finite exchangeable binary vectors

For exchangeable random variables `X₁, …, X_N` the law of `(X_{τ 1}, …, X_{τ k})` is the same for
every injective choice of indices `τ` (`Exchangeable.map_comp_injective`); for an infinitely
exchangeable sequence it is the law of `(X₀, …, X_{k-1})` (`InfExchangeable.map_comp_injective`).

For binary variables this gives the **urn representation** of a finite exchangeable vector:

* the probability of a pattern `x` depends on `x` only through its number of successes
  `boolCount x` (`Exchangeable.measure_pattern_eq_of_boolCount_eq`), because every pattern is a
  rearrangement of the sorted pattern `(1, …, 1, 0, …, 0)` (`exists_perm_sortedPattern`);
* there are `C(n, k)` patterns with `k` successes (`card_boolCount_eq`), so
  `C(n, k) · P(X = x) = P(S_n = k)` for every pattern `x` with `k` successes
  (`Exchangeable.choose_mul_measure_pattern`): given `S_n = k` the vector is uniform over the
  arrangements of `k` successes, which is the law of `n` draws without replacement from an urn
  with `k` successes and `n - k` failures.

A finite exchangeable vector need not be a mixture of i.i.d. laws: the urn with one ball of each
kind is the library's `urnLaw` (`urnLaw_exchangeable`, `urnLaw_not_iidMixture`). In the binary
form, no measure `Π` on `ℝ` of total mass one, concentrated on `[0, 1]` or not, gives the urn
probabilities as `∫ θ^s (1 - θ)^{2 - s} dΠ(θ)` (`urnLaw_ne_binaryMixture`).

## Main definitions

* `sortedPattern`.

## Main results

* `Exchangeable.map_comp_injective`, `InfExchangeable.map_comp_injective`,
  `exists_perm_sortedPattern`, `Exchangeable.measure_pattern_eq_of_boolCount_eq`,
  `card_boolCount_eq`, `Exchangeable.choose_mul_measure_pattern`, `urnLaw_ne_binaryMixture`.

## References

* P. Diaconis and D. Freedman, *Finite exchangeable sequences*, Annals of Probability 8 (1980).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- An exchangeable vector restricted to the injective index map `τ` has the law of its first `k`
coordinates. -/
private theorem Exchangeable.map_comp_injective_castLE {N k : ℕ} {X : Fin N → Ω → S}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : Exchangeable X P) (τ : Fin k → Fin N)
    (hτ : Injective τ) (hk : k ≤ N) :
    P.map (fun ω j => X (τ j) ω) = P.map (fun ω j => X (Fin.castLE hk j) ω) := by
  classical
  let e : {x : Fin N // x.val < k} ≃ {x : Fin N // x ∈ Set.range τ} :=
    Equiv.ofBijective (fun x => ⟨τ ⟨x.1.val, x.2⟩, ⟨_, rfl⟩⟩) ⟨fun x y hxy => by
      have h := hτ (congrArg Subtype.val hxy)
      exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val h)), fun y => by
      obtain ⟨y, j, rfl⟩ := y
      exact ⟨⟨⟨j.val, lt_of_lt_of_le j.2 hk⟩, j.2⟩, rfl⟩⟩
  let σ : Equiv.Perm (Fin N) := e.extendSubtype
  have hσ : ∀ j : Fin k, σ (Fin.castLE hk j) = τ j := fun j => by
    simp only [σ]
    rw [Equiv.extendSubtype_apply_of_mem e _ j.2]
    rfl
  have hproj : Measurable fun (x : Fin N → S) (j : Fin k) => x (Fin.castLE hk j) := by fun_prop
  have hv : Measurable fun ω (i : Fin N) => X i ω := measurable_pi_iff.2 hX
  have hvσ : Measurable fun ω (i : Fin N) => X (σ i) ω := measurable_pi_iff.2 fun i => hX _
  have h := congrArg (Measure.map fun (x : Fin N → S) (j : Fin k) => x (Fin.castLE hk j)) (hE σ)
  rw [Measure.map_map hproj hvσ, Measure.map_map hproj hv] at h
  convert h using 2
  · funext ω j
    simp only [Function.comp_apply, hσ]
  · rfl

/-- **Exchangeability along injective index maps**: for exchangeable `X₁, …, X_N` and two
injective maps `τ, τ' : Fin k → Fin N`, the vectors `(X_{τ j})_j` and `(X_{τ' j})_j` have the same
law. Proof: each is the image of a permutation of the coordinates. -/
theorem Exchangeable.map_comp_injective {N k : ℕ} {X : Fin N → Ω → S}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : Exchangeable X P) {τ τ' : Fin k → Fin N}
    (hτ : Injective τ) (hτ' : Injective τ') :
    P.map (fun ω j => X (τ j) ω) = P.map (fun ω j => X (τ' j) ω) := by
  have hk : k ≤ N := by simpa using Fintype.card_le_of_injective τ hτ
  rw [hE.map_comp_injective_castLE hX τ hτ hk, hE.map_comp_injective_castLE hX τ' hτ' hk]

/-- **Infinite exchangeability along injective index maps**: for an infinitely exchangeable
sequence and an injective `τ : Fin k → Fin N`, the vector `(X_{τ 0}, …, X_{τ (k-1)})` has the law
of `(X₀, …, X_{k-1})`. -/
theorem InfExchangeable.map_comp_injective {X : ℕ → Ω → S} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} (hE : InfExchangeable X P) {k N : ℕ} {τ : Fin k → Fin N}
    (hτ : Injective τ) :
    P.map (fun ω (j : Fin k) => X (τ j) ω) = P.map (fun ω (j : Fin k) => X j ω) := by
  have hk : k ≤ N := by simpa using Fintype.card_le_of_injective τ hτ
  exact (hE N).map_comp_injective (X := fun i : Fin N => X i) (fun i => hX i) hτ
    (Fin.castLE_injective hk)

/-! ### Patterns and their number of successes -/

/-- The **sorted pattern** `(1, …, 1, 0, …, 0)` of length `n` with successes in the first `k`
places. -/
def sortedPattern (k n : ℕ) : Fin n → Bool := fun j => decide (j.val < k)

theorem boolCount_eq_card_filter {n : ℕ} (x : Fin n → Bool) :
    boolCount x = (Finset.univ.filter fun j => x j = true).card := by
  rw [boolCount, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases x j <;> rfl

/-- A pattern of length `n` has at most `n` successes. -/
theorem boolCount_le {n : ℕ} (x : Fin n → Bool) : boolCount x ≤ n := by
  rw [boolCount_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem boolCount_sortedPattern {k n : ℕ} (hk : k ≤ n) : boolCount (sortedPattern k n) = k := by
  rw [boolCount_eq_card_filter]
  simp only [sortedPattern, decide_eq_true_eq]
  rw [Fin.card_filter_val_lt, min_eq_right hk]

theorem card_false_eq_sub {n : ℕ} (x : Fin n → Bool) :
    Fintype.card {j // x j = false} = n - boolCount x := by
  rw [Fintype.card_subtype, boolCount_eq_card_filter]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := fun j => x j = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- **Sorting a binary pattern**: every pattern `x` is a rearrangement of the sorted pattern with
the same number of successes. Proof: the two patterns have fibers of equal sizes over `true` and
`false`, and bijections of the fibers glue to a permutation. -/
theorem exists_perm_sortedPattern {n : ℕ} (x : Fin n → Bool) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j, x (σ j) = sortedPattern (boolCount x) n j := by
  have hle := boolCount_le x
  have htrue : Fintype.card {j // sortedPattern (boolCount x) n j = true} =
      Fintype.card {j // x j = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, ← boolCount_eq_card_filter,
      ← boolCount_eq_card_filter, boolCount_sortedPattern hle]
  have hc : ∀ c, Fintype.card {j // sortedPattern (boolCount x) n j = c} =
      Fintype.card {j // x j = c} := by
    intro c
    cases c
    · rw [card_false_eq_sub, card_false_eq_sub, boolCount_sortedPattern hle]
    · exact htrue
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c), fun j =>
    Equiv.ofFiberEquiv_map _ j⟩

/-- The pattern event `{X = x}` is measurable. -/
theorem measurableSet_pattern {n : ℕ} {X : Fin n → Ω → Bool} (hX : ∀ i, Measurable (X i))
    (x : Fin n → Bool) : MeasurableSet {ω | ∀ j, X j ω = x j} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => (hX j) (measurableSet_singleton (x j))

/-- Pattern probabilities of an exchangeable vector are invariant under rearranging the
pattern. -/
theorem Exchangeable.measure_pattern_perm {n : ℕ} {X : Fin n → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : Exchangeable X P) (x : Fin n → Bool)
    (σ : Equiv.Perm (Fin n)) :
    P {ω | ∀ j, X j ω = x (σ j)} = P {ω | ∀ j, X j ω = x j} := by
  have hv : Measurable fun ω (i : Fin n) => X i ω := measurable_pi_iff.2 hX
  have hvσ : Measurable fun ω (i : Fin n) => X (σ i) ω := measurable_pi_iff.2 fun i => hX _
  have h := congrArg (fun μ : Measure (Fin n → Bool) => μ {fun j => x (σ j)}) (hE σ)
  rw [Measure.map_apply hvσ (measurableSet_singleton _),
    Measure.map_apply hv (measurableSet_singleton _)] at h
  have e1 : (fun ω (i : Fin n) => X (σ i) ω) ⁻¹' {fun j => x (σ j)} =
      {ω | ∀ j, X j ω = x j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_ofPred_eq]
    exact ⟨fun h j => by simpa using h (σ.symm j), fun h i => h (σ i)⟩
  have e2 : (fun ω (i : Fin n) => X i ω) ⁻¹' {fun j => x (σ j)} =
      {ω | ∀ j, X j ω = x (σ j)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_ofPred_eq]
  rw [e1, e2] at h
  exact h.symm

/-- The probability of a pattern is that of the sorted pattern with the same number of
successes. -/
theorem Exchangeable.measure_pattern_eq_sorted {n : ℕ} {X : Fin n → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : Exchangeable X P) (x : Fin n → Bool) :
    P {ω | ∀ j, X j ω = x j} = P {ω | ∀ j, X j ω = sortedPattern (boolCount x) n j} := by
  obtain ⟨σ, hσ⟩ := exists_perm_sortedPattern x
  rw [← hE.measure_pattern_perm hX x σ]
  simp_rw [hσ]

/-- **Pattern probabilities of an exchangeable binary vector depend only on the number of
successes**: if `x` and `y` have the same number of successes, `P(X = x) = P(X = y)`. -/
theorem Exchangeable.measure_pattern_eq_of_boolCount_eq {n : ℕ} {X : Fin n → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : Exchangeable X P) {x y : Fin n → Bool}
    (hxy : boolCount x = boolCount y) :
    P {ω | ∀ j, X j ω = x j} = P {ω | ∀ j, X j ω = y j} := by
  rw [hE.measure_pattern_eq_sorted hX x, hE.measure_pattern_eq_sorted hX y, hxy]

/-! ### The urn representation -/

/-- **There are `C(n, k)` binary patterns of length `n` with `k` successes.** Proof: a pattern is
determined by its set of successes, a subset of size `k`. -/
theorem card_boolCount_eq (n k : ℕ) :
    (Finset.univ.filter fun x : Fin n → Bool => boolCount x = k).card = n.choose k := by
  classical
  have hc : n.choose k = (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card := by
    rw [Finset.card_powersetCard, Finset.card_fin]
  rw [hc]
  refine Finset.card_nbij (fun x => Finset.univ.filter fun j => x j = true) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_powersetCard, ← boolCount_eq_card_filter, hx.2]
    exact ⟨Finset.subset_univ _, rfl⟩
  · intro x _ y _ hxy
    funext j
    have h := congrArg (fun s : Finset (Fin n) => j ∈ s) hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at h
    cases hx : x j <;> cases hy : y j <;> simp_all
  · intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    refine ⟨fun j => decide (j ∈ s), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter, boolCount_eq_card_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [decide_eq_true_eq, Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact hs.2
    · ext j
      simp

/-- **The urn representation of a finite exchangeable binary vector**: for every pattern `x` with
`k` successes, `C(n, k) · P(X = x) = P(S_n = k)`, `S_n = ∑ᵢ Xᵢ`. Given `S_n = k` the vector is
uniform over the `C(n, k)` arrangements of `k` successes: the law of `n` draws without replacement
from an urn with `k` successes and `n - k` failures. -/
theorem Exchangeable.choose_mul_measure_pattern {n : ℕ} {X : Fin n → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : Exchangeable X P) (x : Fin n → Bool) :
    (n.choose (boolCount x) : ℝ≥0∞) * P {ω | ∀ j, X j ω = x j} =
      P {ω | boolCount (fun j => X j ω) = boolCount x} := by
  classical
  set T := Finset.univ.filter fun y : Fin n → Bool => boolCount y = boolCount x
  have hset : {ω | boolCount (fun j => X j ω) = boolCount x} =
      ⋃ y ∈ T, {ω | ∀ j, X j ω = y j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, T, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop]
    exact ⟨fun h => ⟨_, h, fun _ => rfl⟩, fun ⟨y, hy, h⟩ => by
      rw [show (fun j => X j ω) = y from funext h]; exact hy⟩
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun y hy => hE.measure_pattern_eq_of_boolCount_eq hX
      (Finset.mem_filter.1 hy).2, Finset.sum_const, nsmul_eq_mul, card_boolCount_eq]
  · intro y _ z _ hyz
    refine Set.disjoint_left.2 fun ω h1 h2 => hyz (funext fun j => ?_)
    rw [← h1 j, ← h2 j]
  · exact fun y _ => measurableSet_pattern hX y

/-! ### The urn with one ball of each kind has no binary mixture representation -/

/-- **The two draws from the urn with one ball of each kind have no de Finetti representation**,
even allowing any mixing measure of total mass one on `ℝ`: there is a pattern `x` of length two
with `urnLaw {x} ≠ ∫ θ^s (1 - θ)^{2 - s} dΠ(θ)`, `s` the number of successes of `x`. Proof: the two
patterns with equal draws have urn probability `0`, while their mixture probabilities add up to
`∫ (θ² + (1 - θ)²) dΠ(θ) ≥ 1/2`. -/
theorem urnLaw_ne_binaryMixture (Pr : Measure ℝ) [IsProbabilityMeasure Pr] :
    ∃ x : Fin 2 → Bool, urnLaw {x} ≠
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (2 - boolCount x)) ∂Pr := by
  by_contra h
  push Not at h
  have h0 : ∀ x : Fin 2 → Bool, x 0 = x 1 → urnLaw {x} = 0 := by
    intro x hx
    simp only [urnLaw, smul_apply, add_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Measure.dirac_apply' _ (measurableSet_singleton _)]
    have h1 : (![true, false] : Fin 2 → Bool) ∉ ({x} : Set (Fin 2 → Bool)) := by
      intro hm
      rw [Set.mem_singleton_iff] at hm
      have := congrFun hm 0
      have := congrFun hm 1
      simp_all
    have h2 : (![false, true] : Fin 2 → Bool) ∉ ({x} : Set (Fin 2 → Bool)) := by
      intro hm
      rw [Set.mem_singleton_iff] at hm
      have := congrFun hm 0
      have := congrFun hm 1
      simp_all
    simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have ht := h ![true, true]
  have hf := h ![false, false]
  rw [h0 _ rfl] at ht hf
  have cT : boolCount (![true, true] : Fin 2 → Bool) = 2 := by decide
  have cF : boolCount (![false, false] : Fin 2 → Bool) = 0 := by decide
  rw [cT] at ht
  rw [cF] at hf
  simp only [pow_zero, mul_one, one_mul, Nat.sub_self, Nat.sub_zero] at ht hf
  have hsum : ∫⁻ θ, (ENNReal.ofReal (θ ^ 2) + ENNReal.ofReal ((1 - θ) ^ 2)) ∂Pr = 0 := by
    rw [lintegral_add_left (by fun_prop), ← ht, ← hf, add_zero]
  have hle : ∫⁻ _ : ℝ, ENNReal.ofReal (1 / 2) ∂Pr ≤
      ∫⁻ θ, (ENNReal.ofReal (θ ^ 2) + ENNReal.ofReal ((1 - θ) ^ 2)) ∂Pr := by
    refine lintegral_mono fun θ => ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (2 * θ - 1)])
  rw [hsum, lintegral_const, measure_univ, mul_one, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero] at hle
  norm_num at hle

end MetaAnalysis

end CausalInference
