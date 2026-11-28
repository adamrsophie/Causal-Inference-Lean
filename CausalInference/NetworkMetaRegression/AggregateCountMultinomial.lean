/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountBinomial
public import CausalInference.Measures.LinkScale
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Nat.Choose.Cast

/-!
# The multinomial law and the aggregate counts of a categorical outcome

An arm of `N` patients with a categorical outcome (ordered or not) on a finite set `K` of
categories reports the count vector `n_k` of patients in each category. A patient with
covariates `x` falls in category `k` with probability `π_k(x)`; for an ordered outcome these are
differences of a cumulative link model, for an unordered one a multinomial logit model. The
category law of a patient is the stratum law `stratumLaw π`.

* **The multinomial law** (`multinomialLaw`, `multinomialLaw_singleton`): the law of the count
  vector of `N` independent categorical trials; its mass function is
  `N! / (n₁! ⋯ n_K!) ∏ p_k ^ {n_k}` on count vectors summing to `N`.
* **Margins** (`map_multinomialLaw_eval`): each count is `Bin(N, p_k)`.
* **Moments** (`integral_multinomialLaw`, `covariance_multinomialLaw`,
  `variance_multinomialLaw`): `E n_k = N p_k`, `Cov(n_j, n_k) = N ([j = k] p_k - p_j p_k)`.
* **With covariates integrated out the count vector is multinomial**
  (`map_categoryCount_pi_compProd`): if the covariates of the patients are independent draws
  from `F`, the count vector of the arm is `Multinomial(N, θ)`, `θ_k = ∫ π_k dF`. The aggregate
  likelihood of the arm is therefore the multinomial mass function at the averaged category
  probabilities (`measureReal_categoryCount_pi_compProd`).

## Main definitions

* `categoryCount`, `multinomialLaw`, `categoricalKernel`.

## Main results

* `stratumLaw_singleton`, `sum_prod_categoryCount`, `multinomialLaw_singleton`,
  `isProbabilityMeasure_multinomialLaw`, `map_multinomialLaw_eval`.
* `integral_multinomialLaw`, `covariance_multinomialLaw`, `variance_multinomialLaw`.
* `snd_compProd_categoricalKernel`, `map_categoryCount_pi_compProd`,
  `measureReal_categoryCount_pi_compProd`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset CausalInference.EffectMeasure
open scoped ENNReal Nat

namespace CausalInference

namespace NetworkMetaRegression

variable {K : Type*} [Fintype K] [DecidableEq K] [MeasurableSpace K] [MeasurableSingletonClass K]

omit [DecidableEq K] in
theorem stratumLaw_singleton (p : K → ℝ) (k : K) :
    stratumLaw p {k} = ENNReal.ofReal (p k) := by
  simp only [stratumLaw, FunLike.coe_sum, Finset.sum_apply, smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton k), smul_eq_mul]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp

omit [DecidableEq K] [MeasurableSingletonClass K] in
instance isFiniteMeasure_stratumLaw (p : K → ℝ) : IsFiniteMeasure (stratumLaw p) := by
  refine ⟨?_⟩
  simp only [stratumLaw, FunLike.coe_sum, Finset.sum_apply, smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr fun k _ => ENNReal.ofReal_lt_top

/-- The **count vector** of the outcomes `ω` of `N` trials: `n_k` is the number of trials in
category `k`. -/
def categoryCount {N : ℕ} (ω : Fin N → K) (k : K) : ℕ := (univ.filter fun i => ω i = k).card

/-- The **multinomial law** `Multinomial(N, p)`: the law of the count vector of `N` independent
trials, each in category `k` with probability `p k`. -/
noncomputable def multinomialLaw (N : ℕ) (p : K → ℝ) : Measure (K → ℕ) :=
  (Measure.pi fun _ : Fin N => stratumLaw p).map categoryCount

omit [Fintype K] in
theorem measurable_categoryCount [Finite K] {N : ℕ} :
    Measurable (categoryCount : (Fin N → K) → K → ℕ) :=
  measurable_of_countable _

omit [MeasurableSpace K] [MeasurableSingletonClass K] in
/-- **The multinomial theorem, sorted by count vector**: the sum of `∏ᵢ a(ωᵢ)` over the outcome
sequences `ω` with count vector `n` is `N! / (n₁! ⋯ n_K!) ∏ₖ aₖ^{nₖ}` when `∑ nₖ = N`, and `0`
otherwise. -/
theorem sum_prod_categoryCount (N : ℕ) (a : K → ℝ) (n : K → ℕ) :
    ∑ ω ∈ univ.filter (fun ω : Fin N → K => categoryCount ω = n), ∏ i, a (ω i) =
      if ∑ k, n k = N then ((N ! : ℝ) / ∏ k, ((n k)! : ℝ)) * ∏ k, a k ^ n k else 0 := by
  obtain ⟨s, hs⟩ : ∃ s : K →₀ ℕ, s = Finsupp.equivFunOnFinite.symm n := ⟨_, rfl⟩
  have hsn : ∀ k, s k = n k := fun k => by rw [hs]; rfl
  have h1 := MvPolynomial.coeff_linearCombination_X_pow_of_fintype (R := ℝ) a s N
  have h2 : (∑ k, a k • MvPolynomial.X k : MvPolynomial K ℝ) ^ N =
      ∑ ω : Fin N → K, MvPolynomial.C (∏ i, a (ω i)) *
        MvPolynomial.monomial (∑ i, Finsupp.single (ω i) 1) 1 := by
    rw [← Fin.prod_const, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [MvPolynomial.monomial_sum_one, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul]
    rfl
  have hd : ∀ ω : Fin N → K, (∑ i, Finsupp.single (ω i) 1 = s) ↔ categoryCount ω = n := by
    intro ω
    rw [Finsupp.ext_iff, funext_iff]
    refine forall_congr' fun k => ?_
    rw [hsn, Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, Finset.sum_boole, Nat.cast_id, categoryCount]
  rw [h2, MvPolynomial.coeff_sum] at h1
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_ite, mul_one,
    mul_zero] at h1
  rw [← Finset.sum_filter] at h1
  have hfil : (univ.filter fun ω : Fin N → K => ∑ i, Finsupp.single (ω i) 1 = s) =
      univ.filter (fun ω : Fin N → K => categoryCount ω = n) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hd]
  rw [hfil] at h1
  rw [h1, Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  have hsf : (⇑s : K → ℕ) = n := funext hsn
  simp only [hsf]
  split_ifs with hN
  · congr 1
    have hspec := Nat.multinomial_spec Finset.univ n
    rw [hN] at hspec
    have hpos : (∏ k, ((n k)! : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [eq_div_iff hpos, mul_comm]
    exact_mod_cast hspec
  · rfl

omit [DecidableEq K] in
theorem pi_stratumLaw_finset {N : ℕ} {p : K → ℝ} (hp : ∀ k, 0 ≤ p k) (S : Finset (Fin N → K)) :
    Measure.pi (fun _ : Fin N => stratumLaw p) S = ENNReal.ofReal (∑ ω ∈ S, ∏ i, p (ω i)) := by
  rw [← sum_measure_singleton, ENNReal.ofReal_sum_of_nonneg
    fun ω _ => Finset.prod_nonneg fun i _ => hp _]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Measure.pi_singleton, ENNReal.ofReal_prod_of_nonneg fun i _ => hp _]
  exact Finset.prod_congr rfl fun i _ => stratumLaw_singleton p (ω i)

/-- **The multinomial mass function**: `Multinomial(N, p)` gives the count vector `n` the mass
`N! / (n₁! ⋯ n_K!) ∏ₖ pₖ^{nₖ}` when `∑ nₖ = N`, and `0` otherwise. -/
theorem multinomialLaw_singleton {N : ℕ} {p : K → ℝ} (hp : ∀ k, 0 ≤ p k) (n : K → ℕ) :
    multinomialLaw N p {n} = ENNReal.ofReal
      (if ∑ k, n k = N then ((N ! : ℝ) / ∏ k, ((n k)! : ℝ)) * ∏ k, p k ^ n k else 0) := by
  have hpre : categoryCount ⁻¹' {n} =
      ((univ.filter fun ω : Fin N → K => categoryCount ω = n : Finset _) : Set (Fin N → K)) := by
    ext ω
    simp
  rw [multinomialLaw, Measure.map_apply measurable_categoryCount (measurableSet_singleton n),
    hpre, pi_stratumLaw_finset hp, sum_prod_categoryCount]

omit [MeasurableSingletonClass K] in
theorem isProbabilityMeasure_multinomialLaw {N : ℕ} {p : K → ℝ} (hp : IsWeights p) :
    IsProbabilityMeasure (multinomialLaw N p) := by
  have := isProbabilityMeasure_stratumLaw hp
  unfold multinomialLaw
  infer_instance

omit [DecidableEq K] in
private lemma integral_pi_stratumLaw_eval {N : ℕ} {p : K → ℝ} (hp : IsWeights p) (a : Fin N)
    (g : K → ℝ) :
    ∫ ω, g (ω a) ∂Measure.pi (fun _ : Fin N => stratumLaw p) = ∑ k, p k * g k := by
  have := isProbabilityMeasure_stratumLaw hp
  have hm := (measurePreserving_eval (μ := fun _ : Fin N => stratumLaw p) a).map_eq
  rw [← integral_map (measurable_pi_apply a).aemeasurable
    (measurable_of_countable g).aestronglyMeasurable] at *
  rw [show (∫ x, g x ∂Measure.map (fun ω : Fin N → K => ω a)
      (Measure.pi fun _ : Fin N => stratumLaw p)) = ∫ x, g x ∂stratumLaw p from
    congrArg (fun ν => ∫ x, g x ∂ν) hm, integral_stratumLaw hp.1]
  rfl

omit [DecidableEq K] in
private lemma integral_pi_stratumLaw_pair {N : ℕ} {p : K → ℝ} (hp : IsWeights p) {a b : Fin N}
    (hab : a ≠ b) (g h : K → ℝ) :
    ∫ ω, g (ω a) * h (ω b) ∂Measure.pi (fun _ : Fin N => stratumLaw p) =
      (∑ k, p k * g k) * ∑ k, p k * h k := by
  have := isProbabilityMeasure_stratumLaw hp
  have hind := ((iIndepFun_pi (μ := fun _ : Fin N => stratumLaw p) (X := fun _ x => x)
    fun _ => aemeasurable_id).indepFun hab).comp (measurable_of_countable g)
      (measurable_of_countable h)
  rw [← integral_pi_stratumLaw_eval hp a g, ← integral_pi_stratumLaw_eval hp b h]
  exact hind.integral_fun_mul_eq_mul_integral (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

omit [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem categoryCount_eq_sum {N : ℕ} (ω : Fin N → K) (k : K) :
    (categoryCount ω k : ℝ) = ∑ a, if ω a = k then 1 else 0 := by
  rw [Finset.sum_boole]
  rfl

private lemma integral_categoryCount {N : ℕ} {p : K → ℝ} (hp : IsWeights p) (k : K) :
    ∫ ω, (categoryCount ω k : ℝ) ∂Measure.pi (fun _ : Fin N => stratumLaw p) = N * p k := by
  have := isProbabilityMeasure_stratumLaw hp
  simp_rw [categoryCount_eq_sum]
  rw [integral_finsetSum _ fun a _ => Integrable.of_finite]
  have hk : ∀ a : Fin N, ∫ ω, (if ω a = k then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin N => stratumLaw p) = p k := fun a => by
    rw [integral_pi_stratumLaw_eval hp a (fun x => if x = k then 1 else 0)]
    simp
  simp [hk]

private lemma integral_categoryCount_mul {N : ℕ} {p : K → ℝ} (hp : IsWeights p) (j k : K) :
    ∫ ω, (categoryCount ω j : ℝ) * categoryCount ω k
        ∂Measure.pi (fun _ : Fin N => stratumLaw p) =
      N * (N * (p j * p k) + ((if j = k then p k else 0) - p j * p k)) := by
  have := isProbabilityMeasure_stratumLaw hp
  simp_rw [categoryCount_eq_sum, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => Integrable.of_finite]
  have hab : ∀ a b : Fin N, ∫ ω, (if ω a = j then (1 : ℝ) else 0) * (if ω b = k then 1 else 0)
      ∂Measure.pi (fun _ : Fin N => stratumLaw p) =
        p j * p k + if a = b then (if j = k then p k else 0) - p j * p k else 0 := by
    intro a b
    by_cases h : a = b
    · subst h
      rw [integral_pi_stratumLaw_eval hp a
        (fun x => (if x = j then (1 : ℝ) else 0) * if x = k then 1 else 0)]
      by_cases hjk : j = k
      · subst hjk
        simp
      · simp [hjk, Ne.symm hjk]
    · rw [integral_pi_stratumLaw_pair hp h (fun x => if x = j then (1 : ℝ) else 0)
        (fun x => if x = k then 1 else 0)]
      simp [h]
  have hin : ∀ a : Fin N,
      ∫ ω, ∑ b, (if ω a = j then (1 : ℝ) else 0) * (if ω b = k then 1 else 0)
      ∂Measure.pi (fun _ : Fin N => stratumLaw p) =
        ∑ b, (p j * p k + if a = b then (if j = k then p k else 0) - p j * p k else 0) := by
    intro a
    rw [integral_finsetSum _ fun b _ => Integrable.of_finite]
    exact Finset.sum_congr rfl fun b _ => hab a b
  rw [Finset.sum_congr rfl fun a _ => hin a]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, sum_ite_eq,
    mem_univ, ↓reduceIte]
  ring

/-- **The covariance of two multinomial counts**: `Cov(n_j, n_k) = N ([j = k] p_k - p_j p_k)`. -/
theorem covariance_multinomialLaw {N : ℕ} {p : K → ℝ} (hp : IsWeights p) (j k : K) :
    cov[fun n : K → ℕ => (n j : ℝ), fun n => (n k : ℝ); multinomialLaw N p] =
      N * ((if j = k then p k else 0) - p j * p k) := by
  have := isProbabilityMeasure_stratumLaw hp
  rw [multinomialLaw, covariance_map (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable measurable_categoryCount.aemeasurable,
    covariance_eq_sub MemLp.of_discrete MemLp.of_discrete]
  simp only [Function.comp_def, Pi.mul_apply]
  rw [integral_categoryCount_mul hp, integral_categoryCount hp, integral_categoryCount hp]
  ring

/-- **The mean of a multinomial count**: `E n_k = N p_k`. -/
theorem integral_multinomialLaw {N : ℕ} {p : K → ℝ} (hp : IsWeights p) (k : K) :
    ∫ n, (n k : ℝ) ∂multinomialLaw N p = N * p k := by
  rw [multinomialLaw, integral_map measurable_categoryCount.aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  exact integral_categoryCount hp k

/-- **The variance of a multinomial count**: `Var n_k = N p_k (1 - p_k)`. -/
theorem variance_multinomialLaw {N : ℕ} {p : K → ℝ} (hp : IsWeights p) (k : K) :
    Var[fun n : K → ℕ => (n k : ℝ); multinomialLaw N p] = N * p k * (1 - p k) := by
  rw [← covariance_self (measurable_of_countable _).aemeasurable, covariance_multinomialLaw hp]
  simp only [↓reduceIte]
  ring

omit [MeasurableSpace K] [MeasurableSingletonClass K] in
theorem sum_categoryCount {N : ℕ} (ω : Fin N → K) : ∑ k, categoryCount ω k = N := by
  have h := Finset.card_eq_sum_card_fiberwise (f := ω) (s := univ) (t := univ)
    fun _ _ => Finset.mem_coe.2 (mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

omit [MeasurableSpace K] [MeasurableSingletonClass K] in
private lemma sum_filter_categoryCount_prod {N : ℕ} (p : K → ℝ) (k : K) (j : ℕ) :
    ∑ ω ∈ univ.filter (fun ω : Fin N → K => categoryCount ω k = j), ∏ i, p (ω i) =
      N.choose j * p k ^ j * (∑ x ∈ univ.filter (· ≠ k), p x) ^ (N - j) := by
  set q : Bool → ℝ := fun c => ∑ x ∈ univ.filter (fun x => decide (x = k) = c), p x with hq
  set g : (Fin N → K) → Fin N → Bool := fun ω i => decide (ω i = k) with hg
  have hgc : ∀ ω, categoryCount ω k = categoryCount (g ω) true := by
    intro ω
    simp [categoryCount, g]
  have hfib : ∀ b : Fin N → Bool,
      ∑ ω ∈ univ.filter (fun ω => g ω = b), ∏ i, p (ω i) = ∏ i, q (b i) := by
    intro b
    change _ = ∏ i, ∑ x ∈ univ.filter (fun x => decide (x = k) = b i), p x
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ω
    simp [g, Fintype.mem_piFinset, funext_iff]
  have h1 : ∑ ω ∈ univ.filter (fun ω : Fin N → K => categoryCount ω k = j), ∏ i, p (ω i) =
      ∑ b ∈ univ.filter (fun b : Fin N → Bool => categoryCount b true = j), ∏ i, q (b i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := g)
      (t := univ.filter (fun b : Fin N → Bool => categoryCount b true = j))
      (fun ω hω => by simpa [hgc] using hω)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← hfib b]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [hgc, h]
    simpa using hb
  have hqt : q true = p k := by simp [q, Finset.filter_eq']
  have hqf : q false = ∑ x ∈ univ.filter (· ≠ k), p x := by simp [q]
  rw [h1, ← hqt, ← hqf]
  by_cases hj : j ≤ N
  · set n : Bool → ℕ := fun c => if c then j else N - j with hn
    have hfil : univ.filter (fun b : Fin N → Bool => categoryCount b true = j) =
        univ.filter (fun b : Fin N → Bool => categoryCount b = n) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hs := sum_categoryCount b
      rw [Fintype.sum_bool] at hs
      refine ⟨fun h => funext fun c => ?_, fun h => by rw [h]; rfl⟩
      cases c
      · change categoryCount b false = N - j
        omega
      · exact h
    have hsum : ∑ c, n c = N := by
      rw [Fintype.sum_bool]
      simp only [n, Bool.false_eq_true, ↓reduceIte]
      omega
    rw [hfil, sum_prod_categoryCount]
    simp only [hsum, ↓reduceIte]
    rw [Fintype.prod_bool, Fintype.prod_bool, Nat.cast_choose ℝ hj]
    simp only [n, Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [Nat.choose_eq_zero_of_lt (not_le.mp hj), Nat.cast_zero, zero_mul, zero_mul]
    refine Finset.sum_eq_zero fun b hb => absurd ?_ hj
    rw [← (Finset.mem_filter.mp hb).2]
    calc categoryCount b true ≤ (univ : Finset (Fin N)).card := Finset.card_le_univ _
      _ = N := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The margins of the multinomial law are binomial**: under `Multinomial(N, p)` the count
`n_k` has the law `Bin(N, p_k)`. -/
theorem map_multinomialLaw_eval {N : ℕ} {p : K → ℝ} (hp : IsWeights p) (k : K)
    (q : unitInterval) (hq : (q : ℝ) = p k) :
    (multinomialLaw N p).map (fun n => n k) = binomial N q := by
  have hrest : ∑ x ∈ univ.filter (· ≠ k), p x = 1 - p k := by
    rw [← hp.2, ← Finset.sum_filter_add_sum_filter_not univ (fun x => x = k) p,
      Finset.filter_eq' univ k]
    simp
  refine Measure.ext_of_singleton fun j => ?_
  have hpre : categoryCount ⁻¹' ((fun n : K → ℕ => n k) ⁻¹' {j}) =
      ((univ.filter fun ω : Fin N → K => categoryCount ω k = j : Finset _) :
        Set (Fin N → K)) := by
    ext ω
    simp
  rw [Measure.map_apply (measurable_pi_apply k) (measurableSet_singleton j), multinomialLaw,
    Measure.map_apply measurable_categoryCount ((measurable_pi_apply k)
      (measurableSet_singleton j)),
    hpre, pi_stratumLaw_finset hp.1, sum_filter_categoryCount_prod, hrest, binomial_singleton, hq]

/-! ### The categorical outcome kernel and the aggregate count vector -/

section Kernel

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

omit [DecidableEq K] [MeasurableSingletonClass K] in
/-- The **categorical outcome kernel** of measurable category probabilities `π_k(x)` (weights
for every `x`): a patient with covariates `x` has the category law `stratumLaw (π · x)`. -/
noncomputable def categoricalKernel (π : K → 𝒳 → ℝ) (hπ : ∀ k, Measurable (π k))
    (_hw : ∀ x, IsWeights fun k => π k x) : Kernel 𝒳 K where
  toFun x := stratumLaw fun k => π k x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
    simp only [stratumLaw, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun k _ =>
      (ENNReal.measurable_ofReal.comp (hπ k)).mul_const _

omit [DecidableEq K] [MeasurableSingletonClass K] in
theorem categoricalKernel_apply (π : K → 𝒳 → ℝ) (hπ : ∀ k, Measurable (π k))
    (hw : ∀ x, IsWeights fun k => π k x) (x : 𝒳) :
    categoricalKernel π hπ hw x = stratumLaw fun k => π k x :=
  rfl

omit [DecidableEq K] [MeasurableSingletonClass K] in
instance (π : K → 𝒳 → ℝ) (hπ : ∀ k, Measurable (π k)) (hw : ∀ x, IsWeights fun k => π k x) :
    IsMarkovKernel (categoricalKernel π hπ hw) :=
  ⟨fun x => by rw [categoricalKernel_apply]; exact isProbabilityMeasure_stratumLaw (hw x)⟩

variable {F : Measure 𝒳} [IsProbabilityMeasure F] {π : K → 𝒳 → ℝ} {hπ : ∀ k, Measurable (π k)}
  {hw : ∀ x, IsWeights fun k => π k x}

omit [DecidableEq K] [MeasurableSpace K] [MeasurableSingletonClass K] [MeasurableSpace 𝒳] in
theorem le_one_of_isWeights (hw : ∀ x, IsWeights fun k => π k x) (k : K) (x : 𝒳) :
    π k x ≤ 1 := by
  have h := Finset.single_le_sum (f := fun j => π j x) (fun j _ => (hw x).1 j) (mem_univ k)
  rwa [(hw x).2] at h

omit [DecidableEq K] in
/-- **The category of a patient drawn from the covariate law**: under the joint law
`F ⊗ stratumLaw (π · x)`, the category has the law
`stratumLaw θ`, `θ_k = ∫ π_k dF`. -/
theorem snd_compProd_categoricalKernel :
    (F ⊗ₘ categoricalKernel π hπ hw).snd = stratumLaw fun k => ∫ x, π k x ∂F := by
  have hπ0 : ∀ k x, 0 ≤ π k x := fun k x => (hw x).1 k
  have hi : ∀ k, Integrable (π k) F := fun k => (integrable_const 1).mono'
    (hπ k).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hπ0 k x)]; exact le_one_of_isWeights hw k x)
  rw [Measure.snd_compProd]
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.bind_apply (measurableSet_singleton k) (Kernel.aemeasurable _),
    stratumLaw_singleton]
  simp_rw [categoricalKernel_apply, stratumLaw_singleton]
  exact (ofReal_integral_eq_lintegral_ofReal (hi k) (ae_of_all _ (hπ0 k))).symm

omit [DecidableEq K] in
/-- **With covariates integrated out the count vector is multinomial**: if the pairs of `N`
patients are independent with covariates from `F` and category law `stratumLaw (π · x)`, the
count vector of the arm has the law `Multinomial(N, θ)`, `θ_k = ∫ π_k dF`. -/
theorem map_categoryCount_pi_compProd [DecidableEq K] (N : ℕ) :
    (Measure.pi fun _ : Fin N => F ⊗ₘ categoricalKernel π hπ hw).map
        (fun z => categoryCount fun i => (z i).2) =
      multinomialLaw N fun k => ∫ x, π k x ∂F := by
  rw [show (fun z : Fin N → 𝒳 × K => categoryCount fun i => (z i).2) =
      categoryCount ∘ (fun z i => (z i).2) from rfl,
    ← Measure.map_map measurable_categoryCount (by fun_prop),
    Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable), multinomialLaw]
  congr 2
  exact funext fun _ => snd_compProd_categoricalKernel

omit [DecidableEq K] in
/-- **The aggregate likelihood of a categorical outcome**: the probability that the count vector
of the arm equals `n`, with `∑ n_k = N`, is the multinomial mass
`N! / (n₁! ⋯ n_K!) ∏ θ_k ^ {n_k}` at the averaged category probabilities `θ_k = ∫ π_k dF`. -/
theorem measureReal_categoryCount_pi_compProd [DecidableEq K] {N : ℕ} (n : K → ℕ)
    (hn : ∑ k, n k = N) :
    (Measure.pi fun _ : Fin N => F ⊗ₘ categoricalKernel π hπ hw).real
        {z | (categoryCount fun i => (z i).2) = n} =
      ((N ! : ℝ) / ∏ k, ((n k)! : ℝ)) * ∏ k, (∫ x, π k x ∂F) ^ n k := by
  have hπ0 : ∀ k x, 0 ≤ π k x := fun k x => (hw x).1 k
  have hm : Measurable fun z : Fin N → 𝒳 × K => categoryCount fun i => (z i).2 :=
    measurable_categoryCount.comp
      (measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i))
  rw [show {z : Fin N → 𝒳 × K | (categoryCount fun i => (z i).2) = n} =
      (fun z => categoryCount fun i => (z i).2) ⁻¹' {n} from rfl,
    ← map_measureReal_apply hm (measurableSet_singleton n), map_categoryCount_pi_compProd,
    measureReal_def, multinomialLaw_singleton (fun k => integral_nonneg (hπ0 k))]
  simp only [hn, ↓reduceIte]
  rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity)
      (Finset.prod_nonneg fun k _ => pow_nonneg (integral_nonneg (hπ0 k)) _))]

end Kernel

end NetworkMetaRegression

end CausalInference
