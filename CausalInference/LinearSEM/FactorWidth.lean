/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.CorrelatedErrors
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

/-!
# Factor width two and scaled diagonal dominance

A path diagram (`LinearSEM.PathDiagram`) represents the error covariance as `Ω = Λ Λᵀ + diag(D)`
with `D ≥ 0` and every latent factor loading on at most two variables: `Ω` has *factor width at
most two*. This file characterizes these matrices: a symmetric matrix has such a representation
if and only if it is *scaled diagonally dominant*, that is, there are positive weights `d` with
`∑ b ≠ a, d b |Ω a b| ≤ d a Ω a a` for every `a` (Boman, Chen, Parekh and Toledo 2005,
Theorem 9).

From scaled dominance to factors: the factor `(a, b)` loads `√((d b / d a) |Ω a b| / 2)` on `a`
and `sign (Ω a b) √((d a / d b) |Ω a b| / 2)` on `b`, generalizing the construction for diagonal
dominance (`PathDiagram.ofDiagDominant`, the case `d = 1`).

From factors to scaled dominance: the comparison matrix (`FactorWidth.comparison`), with the
diagonal of `Ω` and `-|Ω a b|` off the diagonal, is positive semidefinite, by the `2 × 2` fact
`2 |u v| ≤ u ^ 2 + v ^ 2` applied to each factor. A symmetric positive semidefinite matrix with
nonpositive off-diagonal entries has a positive vector `d` with `M d ≥ 0`
(`FactorWidth.exists_pos_of_quad_nonneg`). The proof needs no Perron and Frobenius theorem: a
minimizer `w` of `xᵀ M x` on the unit sphere of the vectors supported on a set `U` can be taken
nonnegative (replacing `w` by `|w|` does not increase the form), it satisfies `M w = μ w` on `U`
(a first variation argument), and on the vertices of `U` where `w` vanishes `M` decouples from
the support of `w`, so one recurses on that smaller set.

## Main definitions

* `CausalInference.HasFactorWidthTwo`: `Ω = Λ Λᵀ + diag(D)` with `D ≥ 0` and the factor indexed
  by `(a, b)` loading only on `a` and `b`.
* `CausalInference.IsScaledDiagDominant`: positive weights `d` with
  `∑ b ≠ a, d b |Ω a b| ≤ d a Ω a a`.
* `LinearSEM.PathDiagram.ofScaledDiagDominant`: the path diagram of a scaled diagonally dominant
  error covariance supported on the bidirected edges of a graph `H`.

## Main results

* `CausalInference.FactorWidth.isScaledDiagDominant_of_factorRep`: any representation
  `Λ Λᵀ + diag(D)`, with an arbitrary finite index set of factors each loading on at most two
  variables, gives scaled dominance.
* `CausalInference.hasFactorWidthTwo_iff`: factor width at most two if and only if symmetric and
  scaled diagonally dominant.
* `LinearSEM.PathDiagram.exists_iff`: `M` has a path diagram with bidirected part `H` if and
  only if every nonzero off-diagonal entry of `Ω` lies on an edge of `H` and `Ω` is scaled
  diagonally dominant; `LinearSEM.PathDiagram.nonempty_iff` is the version without `H`.
* `LinearSEM.PathDiagram.exists_of_diagDominant`: the diagonally dominant case as a corollary.
* `LinearSEM.NoFactorRep.not_isScaledDiagDominant`: the equicorrelation matrix with
  correlations `3 / 5` is scaled diagonally dominant for no positive weights, which explains
  `LinearSEM.NoFactorRep.isEmpty_pathDiagram`.

## References

* E. G. Boman, D. Chen, O. Parekh and S. Toledo (2005), *On factor width and symmetric
  H-matrices*, Linear Algebra and its Applications 405, 239 to 248.
-/

@[expose] public section

namespace CausalInference

open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Ω` has factor width at most two: `Ω = Λ Λᵀ + diag(D)` with `D ≥ 0`, where the factor indexed
by `(a, b)` loads only on `a` and `b`. -/
def HasFactorWidthTwo (Ω : Matrix V V ℝ) : Prop :=
  ∃ (Λ : Matrix V (V × V) ℝ) (D : V → ℝ), (∀ v p, Λ v p ≠ 0 → v = p.1 ∨ v = p.2) ∧
    (∀ v, 0 ≤ D v) ∧ Ω = Λ * Λᵀ + diagonal D

/-- `Ω` is scaled diagonally dominant: there are positive weights `d` with
`∑ b ≠ a, d b |Ω a b| ≤ d a Ω a a` for every `a`. Equivalently `diag(d) Ω diag(d)` is diagonally
dominant. -/
def IsScaledDiagDominant (Ω : Matrix V V ℝ) : Prop :=
  ∃ d : V → ℝ, (∀ a, 0 < d a) ∧ ∀ a, ∑ b ∈ univ.erase a, d b * |Ω a b| ≤ d a * Ω a a

namespace FactorWidth

/-- The quadratic form `xᵀ M x`. -/
def quad (M : Matrix V V ℝ) (x : V → ℝ) : ℝ := ∑ a, ∑ b, x a * M a b * x b

/-- The comparison matrix of `Ω`: the diagonal of `Ω`, and `-|Ω a b|` off the diagonal. -/
def comparison (Ω : Matrix V V ℝ) : Matrix V V ℝ := fun a b => if a = b then Ω a a else -|Ω a b|

/-! ### Positive vectors for positive semidefinite matrices with nonpositive off-diagonal -/

omit [DecidableEq V] in
/-- If the off-diagonal entries of `M` are nonpositive, replacing `x` by `|x|` does not increase
`xᵀ M x`. -/
theorem quad_abs_le {M : Matrix V V ℝ} (hoff : ∀ a b, a ≠ b → M a b ≤ 0) (x : V → ℝ) :
    quad M (fun a => |x a|) ≤ quad M x := by
  classical
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  by_cases hab : a = b
  · subst hab
    refine le_of_eq ?_
    rw [show |x a| * M a a * |x a| = M a a * (|x a| * |x a|) by ring, abs_mul_abs_self]
    ring
  · have h2 : x a * x b ≤ |x a| * |x b| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith [mul_le_mul_of_nonpos_left h2 (hoff a b hab)]

/-- A quadratic function `2 t g + t ^ 2 c` that is nonnegative for every `t` has `g = 0`. -/
theorem eq_zero_of_forall_quadratic_nonneg {g c : ℝ}
    (h : ∀ t : ℝ, 0 ≤ 2 * t * g + t ^ 2 * c) : g = 0 := by
  by_contra hg
  have hu0 : 0 < |c| + 1 := by positivity
  have key := h (-g / (|c| + 1))
  have e : (2 * (-g / (|c| + 1)) * g + (-g / (|c| + 1)) ^ 2 * c) * (|c| + 1) ^ 2 =
      g ^ 2 * (c - 2 * (|c| + 1)) := by
    field_simp
    ring
  have hg2 : 0 < g ^ 2 := by positivity
  have hc : c - 2 * (|c| + 1) < 0 := by
    have := le_abs_self c
    have := abs_nonneg c
    linarith
  have h1 : (2 * (-g / (|c| + 1)) * g + (-g / (|c| + 1)) ^ 2 * c) * (|c| + 1) ^ 2 < 0 := by
    rw [e]
    exact mul_neg_of_pos_of_neg hg2 hc
  have h2 := mul_nonneg key (le_of_lt (pow_pos hu0 2))
  linarith

theorem quad_add_single {M : Matrix V V ℝ} (hsymm : ∀ a b, M a b = M b a) (w : V → ℝ) (a : V)
    (t : ℝ) : quad M (fun b => w b + t * (if b = a then 1 else 0)) =
      quad M w + 2 * t * ∑ b, M a b * w b + t ^ 2 * M a a := by
  have e1 : ∀ b c, (w b + t * (if b = a then (1 : ℝ) else 0)) * M b c *
      (w c + t * (if c = a then 1 else 0)) =
        w b * M b c * w c + t * ((if b = a then 1 else 0) * (M b c * w c)) +
          t * ((if c = a then 1 else 0) * (w b * M b c)) +
            t ^ 2 * ((if b = a then 1 else 0) * ((if c = a then 1 else 0) * M b c)) := by
    intro b c
    ring
  simp only [quad, e1, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have : ∑ b, w b * M b a = ∑ b, M a b * w b :=
    Finset.sum_congr rfl fun b _ => by rw [hsymm b a]; ring
  rw [this]
  ring

theorem sum_sq_add_single (w : V → ℝ) (a : V) (t : ℝ) :
    ∑ b, (w b + t * (if b = a then 1 else 0)) ^ 2 = ∑ b, w b ^ 2 + 2 * t * w a + t ^ 2 := by
  have : ∀ b, (w b + t * (if b = a then (1 : ℝ) else 0)) ^ 2 =
      w b ^ 2 + (if b = a then 2 * t * w a + t ^ 2 else 0) := by
    intro b
    split_ifs with h
    · subst h
      ring
    · ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

omit [DecidableEq V] in
/-- **A nonnegative eigenvector on a block.** Let `M` be symmetric with nonpositive off-diagonal
entries and `xᵀ M x ≥ 0` for every `x`. For a nonempty set `U` there is a nonzero vector
`w ≥ 0` supported on `U` and `μ ≥ 0` with `(M w) a = μ w a` for every `a ∈ U`: a minimizer of
`xᵀ M x` over the unit vectors supported on `U`, replaced by its absolute value. -/
theorem exists_eigen_nonneg {M : Matrix V V ℝ} (hsymm : ∀ a b, M a b = M b a)
    (hoff : ∀ a b, a ≠ b → M a b ≤ 0) (hpsd : ∀ x, 0 ≤ quad M x) {U : Finset V}
    (hU : U.Nonempty) :
    ∃ (w : V → ℝ) (μ : ℝ), 0 ≤ μ ∧ (∀ a, 0 ≤ w a) ∧ (∀ a, a ∉ U → w a = 0) ∧
      (∃ a ∈ U, w a ≠ 0) ∧ ∀ a ∈ U, ∑ b, M a b * w b = μ * w a := by
  classical
  set K : Set (V → ℝ) := {x | (∀ a, a ∉ U → x a = 0) ∧ ∑ a, x a ^ 2 = 1} with hK
  have hclosed : IsClosed K := by
    have h1 : IsClosed {x : V → ℝ | ∀ a, a ∉ U → x a = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply a) continuous_const
    have h2 : IsClosed {x : V → ℝ | ∑ a, x a ^ 2 = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    exact h1.inter h2
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : V → ℝ)) (r := 1)).subset fun x hx => ?_
    rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
    intro a
    rw [Real.dist_eq, Pi.zero_apply, sub_zero, ← sq_le_one_iff_abs_le_one]
    calc x a ^ 2 ≤ ∑ b, x b ^ 2 :=
          Finset.single_le_sum (fun b _ => sq_nonneg (x b)) (Finset.mem_univ a)
      _ = 1 := hx.2
  have hcomp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨a₀, ha₀⟩ := hU
  have hne : K.Nonempty := by
    refine ⟨fun b => if b = a₀ then 1 else 0, fun a ha => ?_, ?_⟩
    · have : a ≠ a₀ := fun h => ha (h ▸ ha₀)
      simp [this]
    · simp
  have hcont : Continuous (quad M) := by
    unfold quad
    fun_prop
  obtain ⟨w₀, hw₀K, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
  have hhom : ∀ x : V → ℝ, (∀ a, a ∉ U → x a = 0) →
      quad M w₀ * ∑ a, x a ^ 2 ≤ quad M x := by
    intro x hx
    by_cases hs : ∑ a, x a ^ 2 = 0
    · have hx0 : ∀ a, x a = 0 := fun a => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (x b))).1 hs a
          (Finset.mem_univ a)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      simp [quad, hx0]
    · have hpos : 0 < ∑ a, x a ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun b _ => sq_nonneg _) (Ne.symm hs)
      set r := Real.sqrt (∑ a, x a ^ 2)
      have hr : 0 < r := Real.sqrt_pos.2 hpos
      have hr2 : r ^ 2 = ∑ a, x a ^ 2 := Real.sq_sqrt hpos.le
      have hmem : (fun a => x a / r) ∈ K := by
        refine ⟨fun a ha => by simp [hx a ha], ?_⟩
        simp only [div_pow]
        rw [← Finset.sum_div, ← hr2, div_self (by positivity)]
      have h1 := isMinOn_iff.1 hmin _ hmem
      have h2 : quad M (fun a => x a / r) = quad M x / r ^ 2 := by
        simp only [quad, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        field_simp
      rw [h2, le_div_iff₀ (by positivity), hr2] at h1
      exact h1
  set w : V → ℝ := fun a => |w₀ a| with hw
  have hwK : w ∈ K := ⟨fun a ha => by simp [w, hw₀K.1 a ha], by simp [w, sq_abs, hw₀K.2]⟩
  have hQw : quad M w = quad M w₀ :=
    le_antisymm (quad_abs_le hoff w₀) (isMinOn_iff.1 hmin _ hwK)
  refine ⟨w, quad M w₀, hpsd w₀, fun a => abs_nonneg _, hwK.1, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have h0 : ∑ a, w a ^ 2 = 0 := Finset.sum_eq_zero fun a _ => by
      by_cases ha : a ∈ U
      · simp [hcon a ha]
      · simp [hwK.1 a ha]
    rw [hwK.2] at h0
    exact one_ne_zero h0
  · intro a ha
    apply sub_eq_zero.1
    refine eq_zero_of_forall_quadratic_nonneg (c := M a a - quad M w₀) fun t => ?_
    have hx : ∀ b, b ∉ U → (w b + t * (if b = a then 1 else 0)) = 0 := fun b hb => by
      have : b ≠ a := fun h => hb (h ▸ ha)
      simp [hwK.1 b hb, this]
    have h1 := hhom _ hx
    rw [sum_sq_add_single, quad_add_single hsymm, hwK.2, hQw] at h1
    nlinarith [h1]

omit [DecidableEq V] in
/-- **A positive vector `d` with `M d ≥ 0`.** A symmetric matrix with nonpositive off-diagonal
entries whose quadratic form is nonnegative has a vector `d` with positive entries and
`M d ≥ 0`. The vector is assembled from the nonnegative eigenvectors of
`FactorWidth.exists_eigen_nonneg` on a decreasing sequence of blocks. -/
theorem exists_pos_of_quad_nonneg {M : Matrix V V ℝ} (hsymm : ∀ a b, M a b = M b a)
    (hoff : ∀ a b, a ≠ b → M a b ≤ 0) (hpsd : ∀ x, 0 ≤ quad M x) :
    ∃ d : V → ℝ, (∀ a, 0 < d a) ∧ ∀ a, 0 ≤ ∑ b, M a b * d b := by
  classical
  have key : ∀ n, ∀ U : Finset V, U.card = n → ∃ d : V → ℝ, (∀ a ∈ U, 0 < d a) ∧
      (∀ a, a ∉ U → d a = 0) ∧ ∀ a ∈ U, 0 ≤ ∑ b, M a b * d b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hUn
      rcases U.eq_empty_or_nonempty with rfl | hU
      · exact ⟨0, by simp, fun _ _ => rfl, by simp⟩
      obtain ⟨w, μ, hμ, hw0, hwU, ⟨a₁, ha₁U, ha₁⟩, heig⟩ :=
        exists_eigen_nonneg hsymm hoff hpsd hU
      set U' := U.filter (fun a => w a = 0) with hU'
      have hlt : U'.card < n := by
        rw [← hUn]
        exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a₁, ha₁U, ha₁⟩)
      obtain ⟨d', hd'pos, hd'0, hd'M⟩ := ih _ hlt U' rfl
      have hblock : ∀ a ∈ U', ∀ b, w b ≠ 0 → M a b = 0 := by
        intro a ha b hb
        obtain ⟨haU, hwa⟩ := Finset.mem_filter.1 ha
        have hsum : ∑ c, M a c * w c = 0 := by rw [heig a haU, hwa, mul_zero]
        have hterm : ∀ c ∈ (univ : Finset V), M a c * w c ≤ 0 := by
          intro c _
          by_cases hc : c = a
          · subst hc
            simp [hwa]
          · exact mul_nonpos_of_nonpos_of_nonneg (hoff a c (Ne.symm hc)) (hw0 c)
        have := (Finset.sum_eq_zero_iff_of_nonpos hterm).1 hsum b (Finset.mem_univ b)
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hb
      refine ⟨fun a => w a + d' a, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
      · change 0 < w a + d' a
        by_cases hwa : w a = 0
        · have : a ∈ U' := Finset.mem_filter.2 ⟨ha, hwa⟩
          simpa [hwa] using hd'pos a this
        · have : a ∉ U' := fun h => hwa (Finset.mem_filter.1 h).2
          rw [hd'0 a this, add_zero]
          exact lt_of_le_of_ne (hw0 a) (Ne.symm hwa)
      · have : a ∉ U' := fun h => ha (Finset.mem_filter.1 h).1
        simp [hwU a ha, hd'0 a this]
      · simp only [mul_add, Finset.sum_add_distrib]
        by_cases hwa : w a = 0
        · have : a ∈ U' := Finset.mem_filter.2 ⟨ha, hwa⟩
          rw [heig a ha, hwa, mul_zero, zero_add]
          exact hd'M a this
        · have h0 : ∑ b, M a b * d' b = 0 := Finset.sum_eq_zero fun b _ => by
            by_cases hb : b ∈ U'
            · rw [hsymm a b, hblock b hb a hwa, zero_mul]
            · rw [hd'0 b hb, mul_zero]
          rw [h0, add_zero, heig a ha]
          exact mul_nonneg hμ (hw0 a)
  obtain ⟨d, hd, -, hdM⟩ := key _ univ rfl
  exact ⟨d, fun a => hd a (Finset.mem_univ a), fun a => hdM a (Finset.mem_univ a)⟩

/-! ### From factors to scaled dominance -/

/-- The `2 × 2` inequality behind factor width two: for a vector `u` supported on at most two
coordinates, `∑ a, u a ^ 2 - ∑ a ≠ b, u a u b = 2 ∑ u ^ 2 - (∑ u) ^ 2 ≥ 0`. -/
theorem sum_pair_nonneg (u : V → ℝ) {i j : V} (hu : ∀ v, u v ≠ 0 → v = i ∨ v = j) :
    0 ≤ ∑ a, ∑ b, (if a = b then u a ^ 2 else -(u a * u b)) := by
  have e : ∑ a, ∑ b, (if a = b then u a ^ 2 else -(u a * u b)) =
      2 * ∑ a, u a ^ 2 - (∑ a, u a) ^ 2 := by
    have : ∀ a b, (if a = b then u a ^ 2 else -(u a * u b)) =
        (if a = b then 2 * u a ^ 2 else 0) - u a * u b := by
      intro a b
      split_ifs with h
      · subst h
        ring
      · ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      ← Finset.mul_sum]
    rw [sq (∑ a, u a), Finset.sum_mul, Finset.mul_sum]
  rw [e]
  have hsub : ∑ a, u a = ∑ a ∈ {i, j}, u a :=
    (Finset.sum_subset (Finset.subset_univ _) fun v _ hv => by
      by_contra h
      rcases hu v h with rfl | rfl <;> simp at hv).symm
  have hcard : (({i, j} : Finset V).card : ℝ) ≤ 2 := by
    have : ({i, j} : Finset V).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    exact_mod_cast this
  have h1 := sq_sum_le_card_mul_sum_sq (s := ({i, j} : Finset V)) (f := u)
  have h2 : ∑ a ∈ {i, j}, u a ^ 2 ≤ ∑ a, u a ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ a ∈ {i, j}, u a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [hsub]
  nlinarith

/-- **Factors on pairs make the comparison matrix positive semidefinite.** If
`Ω = Λ Λᵀ + diag(D)` with `D ≥ 0` and each factor `k` loading on at most two variables, then
`xᵀ M x ≥ 0` for the comparison matrix `M` of `Ω`. -/
theorem quad_comparison_nonneg {K : Type*} [Fintype K] {Ω : Matrix V V ℝ} {Λ : Matrix V K ℝ}
    {D : V → ℝ} (hΛ : ∀ k, ∃ i j, ∀ v, Λ v k ≠ 0 → v = i ∨ v = j) (hD : ∀ v, 0 ≤ D v)
    (hΩ : Ω = Λ * Λᵀ + diagonal D) (x : V → ℝ) : 0 ≤ quad (comparison Ω) x := by
  have hoff : ∀ a b, a ≠ b → comparison Ω a b ≤ 0 := fun a b h => by
    simp [comparison, h]
  refine le_trans ?_ (quad_abs_le hoff x)
  set y : V → ℝ := fun a => |x a| with hy_def
  have hy : ∀ a, 0 ≤ y a := fun a => abs_nonneg _
  set u : K → V → ℝ := fun k a => |Λ a k| * y a with hu_def
  have hentry : ∀ a b, (if a = b then D a * y a ^ 2 else 0) +
      ∑ k, (if a = b then u k a ^ 2 else -(u k a * u k b)) ≤
        y a * comparison Ω a b * y b := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have hd : Ω a a = ∑ k, Λ a k * Λ a k + D a := by
        rw [hΩ]
        simp [Matrix.mul_apply]
      simp only [comparison, ite_true, hd]
      refine le_of_eq ?_
      have : ∀ k, u k a ^ 2 = y a * (Λ a k * Λ a k) * y a := fun k => by
        simp only [hu_def]
        rw [mul_pow, sq_abs]
        ring
      simp only [this]
      rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      ring
    · have h1 : Ω a b = ∑ k, Λ a k * Λ b k := by
        rw [hΩ]
        simp [Matrix.mul_apply, hab]
      have h2 : |Ω a b| ≤ ∑ k, |Λ a k| * |Λ b k| := by
        rw [h1]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp [abs_mul]
      simp only [comparison, hab, ite_false, zero_add]
      have : ∑ k, -(u k a * u k b) = -(y a * y b * ∑ k, |Λ a k| * |Λ b k|) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp only [hu_def]; ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg (hy a) (hy b))]
  have hsum : ∑ a, ∑ b, ((if a = b then D a * y a ^ 2 else 0) +
      ∑ k, (if a = b then u k a ^ 2 else -(u k a * u k b))) ≤ quad (comparison Ω) y :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry a b
  refine le_trans ?_ hsum
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hswap : ∑ a, ∑ b, ∑ k, (if a = b then u k a ^ 2 else -(u k a * u k b)) =
      ∑ k, ∑ a, ∑ b, (if a = b then u k a ^ 2 else -(u k a * u k b)) := by
    calc ∑ a, ∑ b, ∑ k, (if a = b then u k a ^ 2 else -(u k a * u k b))
        = ∑ a, ∑ k, ∑ b, (if a = b then u k a ^ 2 else -(u k a * u k b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  refine add_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (hD a) (sq_nonneg _))
    (Finset.sum_nonneg fun k _ => ?_)
  obtain ⟨i, j, hij⟩ := hΛ k
  refine sum_pair_nonneg (u k) (i := i) (j := j) fun v hv => hij v fun h => hv ?_
  simp [hu_def, h]

/-- **Factor width two implies scaled diagonal dominance.** If `Ω = Λ Λᵀ + diag(D)` with
`D ≥ 0` and each factor (of an arbitrary finite family) loading on at most two variables, then
`Ω` is scaled diagonally dominant. -/
theorem isScaledDiagDominant_of_factorRep {K : Type*} [Fintype K] {Ω : Matrix V V ℝ}
    {Λ : Matrix V K ℝ} {D : V → ℝ} (hΛ : ∀ k, ∃ i j, ∀ v, Λ v k ≠ 0 → v = i ∨ v = j)
    (hD : ∀ v, 0 ≤ D v) (hΩ : Ω = Λ * Λᵀ + diagonal D) : IsScaledDiagDominant Ω := by
  have hsymm : ∀ a b, Ω a b = Ω b a := by
    intro a b
    rw [hΩ]
    by_cases hab : a = b
    · rw [hab]
    · simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply,
        diagonal_apply_ne _ hab, diagonal_apply_ne _ (Ne.symm hab), mul_comm]
  have hCsymm : ∀ a b, comparison Ω a b = comparison Ω b a := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · simp [comparison, hab, Ne.symm hab, hsymm a b]
  have hoff : ∀ a b, a ≠ b → comparison Ω a b ≤ 0 := fun a b h => by
    simp [comparison, h]
  obtain ⟨d, hd, hdM⟩ := exists_pos_of_quad_nonneg hCsymm hoff
    (quad_comparison_nonneg hΛ hD hΩ)
  refine ⟨d, hd, fun a => ?_⟩
  have h := hdM a
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
  have he : ∑ b ∈ univ.erase a, comparison Ω a b * d b = -∑ b ∈ univ.erase a, d b * |Ω a b| := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hba : a ≠ b := Ne.symm (Finset.ne_of_mem_erase hb)
    simp only [comparison, hba, ite_false]
    ring
  rw [he] at h
  simp only [comparison, ite_true] at h
  linarith

/-! ### From scaled dominance to factors -/

theorem sign_mul_sign_mul_half (r c : ℝ) :
    Real.sign r * Real.sign r * (c * (|r| / 2)) = c * (|r| / 2) := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h]
    ring
  · simp [h]
  · rw [Real.sign_of_pos h]
    ring

theorem sqrt_mul_sqrt_div {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (q / p * r) * Real.sqrt (p / q * r) = r := by
  rw [← Real.sqrt_mul (mul_nonneg (div_nonneg hq.le hp.le) hr)]
  rw [show q / p * r * (p / q * r) = r * r by field_simp]
  exact Real.sqrt_mul_self hr

/-- The loadings of the factor representation of a scaled diagonally dominant matrix `Ω` with
weights `d`, along the edges of `H`: the factor `(a, b)` loads `√((d b / d a) |Ω a b| / 2)` on
`a` and `sign (Ω a b) √((d a / d b) |Ω a b| / 2)` on `b`. With `d = 1` these are the loadings
`LinearSEM.PathDiagram.ddLoading`. -/
noncomputable def sddLoading (H : SimpleGraph V) [DecidableRel H.Adj] (Ω : Matrix V V ℝ)
    (d : V → ℝ) : Matrix V (V × V) ℝ :=
  fun v p => if H.Adj p.1 p.2 then
    (if v = p.1 then Real.sqrt (d p.2 / d p.1 * (|Ω p.1 p.2| / 2))
      else if v = p.2 then
        Real.sign (Ω p.1 p.2) * Real.sqrt (d p.1 / d p.2 * (|Ω p.1 p.2| / 2))
      else 0)
  else 0

variable {H : SimpleGraph V} [DecidableRel H.Adj] {Ω : Matrix V V ℝ} {d : V → ℝ}

omit [Fintype V] in
theorem sddLoading_support {v : V} {p : V × V} (h : sddLoading H Ω d v p ≠ 0) :
    H.Adj p.1 p.2 ∧ (v = p.1 ∨ v = p.2) := by
  simp only [sddLoading] at h
  split_ifs at h with h1 h2 h3
  · exact ⟨h1, Or.inl h2⟩
  · exact ⟨h1, Or.inr h3⟩
  · exact absurd rfl h
  · exact absurd rfl h

theorem sddLoading_mul_apply_ne (hsymm : ∀ a b, Ω a b = Ω b a)
    (hsupp : ∀ a b, a ≠ b → Ω a b ≠ 0 → H.Adj a b) (hd : ∀ a, 0 < d a) {i j : V}
    (hij : i ≠ j) : (sddLoading H Ω d * (sddLoading H Ω d)ᵀ) i j = Ω i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add (i, j) (j, i) (by simp [hij])]
  · have hji : H.Adj j i ↔ H.Adj i j := H.adj_comm j i
    by_cases hadj : H.Adj i j
    · have hs := sqrt_mul_sqrt_div (hd i) (hd j) (show (0 : ℝ) ≤ |Ω i j| / 2 by positivity)
      simp only [transpose_apply, sddLoading, hadj, hji, hij, Ne.symm hij, ↓reduceIte,
        hsymm j i]
      linear_combination (2 * Real.sign (Ω i j)) * hs +
        LinearSEM.PathDiagram.sign_mul_abs_self (Ω i j)
    · have h0 : Ω i j = 0 := not_not.1 fun h => hadj (hsupp i j hij h)
      simp [transpose_apply, sddLoading, hadj, hji, h0]
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    simp only [transpose_apply, sddLoading]
    split_ifs <;> simp_all

theorem sddLoading_mul_apply_self (hsymm : ∀ a b, Ω a b = Ω b a)
    (hsupp : ∀ a b, a ≠ b → Ω a b ≠ 0 → H.Adj a b) (hd : ∀ a, 0 < d a) (i : V) :
    (sddLoading H Ω d * (sddLoading H Ω d)ᵀ) i i =
      ∑ b ∈ univ.erase i, d b / d i * |Ω i b| := by
  have hterm : ∀ p : V × V, sddLoading H Ω d i p * sddLoading H Ω d i p =
      (if p.1 = i then (if H.Adj i p.2 then d p.2 / d i * (|Ω i p.2| / 2) else 0) else 0) +
      (if p.2 = i then (if H.Adj i p.1 then d p.1 / d i * (|Ω i p.1| / 2) else 0) else 0) := by
    rintro ⟨a, b⟩
    have hs := Real.mul_self_sqrt (mul_nonneg (div_nonneg (hd b).le (hd a).le)
      (show (0 : ℝ) ≤ |Ω a b| / 2 by positivity))
    have hs' := Real.mul_self_sqrt (mul_nonneg (div_nonneg (hd a).le (hd b).le)
      (show (0 : ℝ) ≤ |Ω a b| / 2 by positivity))
    simp only [sddLoading]
    by_cases hab : H.Adj a b
    · have hne : a ≠ b := hab.ne
      by_cases ha : a = i
      · subst ha
        simp only [hab, Ne.symm hne, ↓reduceIte, add_zero, hs]
      · by_cases hb : b = i
        · subst hb
          simp only [hab, Ne.symm ha, ha, ↓reduceIte, H.adj_comm b a, hsymm b a, zero_add]
          calc Real.sign (Ω a b) * Real.sqrt (d a / d b * (|Ω a b| / 2)) *
                (Real.sign (Ω a b) * Real.sqrt (d a / d b * (|Ω a b| / 2)))
              = Real.sign (Ω a b) * Real.sign (Ω a b) *
                  (Real.sqrt (d a / d b * (|Ω a b| / 2)) *
                    Real.sqrt (d a / d b * (|Ω a b| / 2))) := by ring
            _ = d a / d b * (|Ω a b| / 2) := by rw [hs', sign_mul_sign_mul_half]
        · simp [hab, Ne.symm ha, Ne.symm hb, ha, hb]
    · by_cases ha : a = i
      · subst ha
        by_cases hb : b = a
        · subst hb
          simp
        · simp [hab, hb]
      · by_cases hb : b = i
        · subst hb
          simp [hab, ha, H.adj_comm b a]
        · simp [hab, ha, hb]
  rw [Matrix.mul_apply]
  simp only [transpose_apply, hterm, Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, ← Finset.sum_erase univ (a := i) (by simp)]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbi : b ≠ i := Finset.ne_of_mem_erase hb
  by_cases hadj : H.Adj i b
  · simp only [hadj, ↓reduceIte]
    ring
  · have h0 : Ω i b = 0 := not_not.1 fun h => hadj (hsupp i b (Ne.symm hbi) h)
    simp [hadj, h0]

/-- The residual variances of the factor representation `FactorWidth.sddLoading`. -/
noncomputable def sddResidual (Ω : Matrix V V ℝ) (d : V → ℝ) (a : V) : ℝ :=
  Ω a a - ∑ b ∈ univ.erase a, d b / d a * |Ω a b|

theorem sddResidual_nonneg (hd : ∀ a, 0 < d a)
    (hdd : ∀ a, ∑ b ∈ univ.erase a, d b * |Ω a b| ≤ d a * Ω a a) (a : V) :
    0 ≤ sddResidual Ω d a := by
  rw [sddResidual, sub_nonneg]
  have : ∑ b ∈ univ.erase a, d b / d a * |Ω a b| = (∑ b ∈ univ.erase a, d b * |Ω a b|) / d a := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, div_le_iff₀ (hd a)]
  linarith [hdd a]

/-- The factor representation of a scaled diagonally dominant matrix supported on the edges
of `H`. -/
theorem eq_sddLoading (hsymm : ∀ a b, Ω a b = Ω b a)
    (hsupp : ∀ a b, a ≠ b → Ω a b ≠ 0 → H.Adj a b) (hd : ∀ a, 0 < d a) :
    Ω = sddLoading H Ω d * (sddLoading H Ω d)ᵀ + diagonal (sddResidual Ω d) := by
  ext i j
  rw [Matrix.add_apply]
  by_cases hij : i = j
  · subst hij
    rw [sddLoading_mul_apply_self hsymm hsupp hd, diagonal_apply_eq, sddResidual]
    ring
  · rw [sddLoading_mul_apply_ne hsymm hsupp hd hij, diagonal_apply_ne _ hij, add_zero]

end FactorWidth

open FactorWidth

/-- Diagonal dominance is scaled diagonal dominance with unit weights. -/
theorem isScaledDiagDominant_of_diagDominant {Ω : Matrix V V ℝ}
    (hdd : ∀ a, ∑ b ∈ univ.erase a, |Ω a b| ≤ Ω a a) : IsScaledDiagDominant Ω :=
  ⟨fun _ => 1, fun _ => one_pos, fun a => by simpa using hdd a⟩

/-- **Factor width two is scaled diagonal dominance** (Boman, Chen, Parekh and Toledo 2005,
Theorem 9): `Ω = Λ Λᵀ + diag(D)` with `D ≥ 0` and every factor loading on at most two variables
if and only if `Ω` is symmetric and scaled diagonally dominant. -/
theorem hasFactorWidthTwo_iff {Ω : Matrix V V ℝ} :
    HasFactorWidthTwo Ω ↔ (∀ a b, Ω a b = Ω b a) ∧ IsScaledDiagDominant Ω := by
  constructor
  · rintro ⟨Λ, D, hΛ, hD, hΩ⟩
    refine ⟨fun a b => ?_, isScaledDiagDominant_of_factorRep
      (fun p => ⟨p.1, p.2, fun v h => hΛ v p h⟩) hD hΩ⟩
    rw [hΩ]
    by_cases hab : a = b
    · rw [hab]
    · simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply,
        diagonal_apply_ne _ hab, diagonal_apply_ne _ (Ne.symm hab), mul_comm]
  · rintro ⟨hsymm, d, hd, hdd⟩
    refine ⟨sddLoading ⊤ Ω d, sddResidual Ω d, fun v p h => (sddLoading_support h).2,
      sddResidual_nonneg hd hdd, eq_sddLoading hsymm (fun a b hab _ => ?_) hd⟩
    exact (SimpleGraph.top_adj a b).2 hab

namespace LinearSEM

namespace PathDiagram

variable {M : LinearSEM V}

/-- **Scaled diagonal dominance gives a path diagram.** If every nonzero off-diagonal entry of
the error covariance lies on a bidirected edge of `H` and `Ω` is scaled diagonally dominant with
weights `d`, then `M` has a path diagram on the mixed graph `(M.G, H)` with the loadings
`FactorWidth.sddLoading` and the residual variances `FactorWidth.sddResidual`. -/
noncomputable def ofScaledDiagDominant (H : SimpleGraph V) [DecidableRel H.Adj]
    (hsupp : ∀ a b, a ≠ b → M.Ω a b ≠ 0 → H.Adj a b) (d : V → ℝ) (hd : ∀ a, 0 < d a)
    (hdd : ∀ a, ∑ b ∈ univ.erase a, d b * |M.Ω a b| ≤ d a * M.Ω a a) : M.PathDiagram where
  G := ⟨M.G, H⟩
  acyclic := M.acyclic
  B_support := M.B_support
  Λ := sddLoading H M.Ω d
  Λ_support _ _ h := sddLoading_support h
  D := sddResidual M.Ω d
  D_nonneg := sddResidual_nonneg hd hdd
  Ω_eq := eq_sddLoading (fun a b => by simpa using (M.Ω_posSemidef.isHermitian.apply a b).symm)
    hsupp hd

/-- **Existence of a path diagram.** The model `M` has a path diagram whose bidirected part is
`H` if and only if every nonzero off-diagonal entry of the error covariance lies on an edge of
`H` and the error covariance is scaled diagonally dominant. -/
theorem exists_iff (H : SimpleGraph V) :
    (∃ F : M.PathDiagram, F.G.bidirected = H) ↔
      (∀ a b, a ≠ b → M.Ω a b ≠ 0 → H.Adj a b) ∧ IsScaledDiagDominant M.Ω := by
  classical
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨fun a b hab h => (F.covers h).resolve_left hab,
      isScaledDiagDominant_of_factorRep (fun p => ⟨p.1, p.2, fun v h => (F.Λ_support v p h).2⟩)
        F.D_nonneg F.Ω_eq⟩
  · rintro ⟨hsupp, d, hd, hdd⟩
    exact ⟨ofScaledDiagDominant H hsupp d hd hdd, rfl⟩

/-- The model `M` has a path diagram if and only if its error covariance is scaled diagonally
dominant. -/
theorem nonempty_iff : Nonempty M.PathDiagram ↔ IsScaledDiagDominant M.Ω := by
  classical
  constructor
  · rintro ⟨F⟩
    exact ((exists_iff F.G.bidirected).1 ⟨F, rfl⟩).2
  · intro h
    obtain ⟨F, -⟩ := (exists_iff (M := M) ⊤).2
      ⟨fun a b hab _ => (SimpleGraph.top_adj a b).2 hab, h⟩
    exact ⟨F⟩

/-- **Diagonal dominance, as a corollary.** The statement of `PathDiagram.ofDiagDominant`:
under its hypotheses `M` has a path diagram with bidirected part `H`. -/
theorem exists_of_diagDominant (H : SimpleGraph V)
    (hsupp : ∀ a b, a ≠ b → M.Ω a b ≠ 0 → H.Adj a b)
    (hdd : ∀ a, ∑ b ∈ univ.erase a, |M.Ω a b| ≤ M.Ω a a) :
    ∃ F : M.PathDiagram, F.G.bidirected = H :=
  (exists_iff H).2 ⟨hsupp, isScaledDiagDominant_of_diagDominant hdd⟩

end PathDiagram

namespace NoFactorRep

/-- The equicorrelation matrix with correlations `3 / 5` is scaled diagonally dominant for no
positive weights: adding the three inequalities `d a ≥ (3 / 5) (d b + d c)` gives
`d 0 + d 1 + d 2 ≥ (6 / 5) (d 0 + d 1 + d 2)`. -/
theorem not_isScaledDiagDominant : ¬ IsScaledDiagDominant Ω := by
  rintro ⟨d, hd, hdd⟩
  have h0 := hdd 0
  have h1 := hdd 1
  have h2 := hdd 2
  simp [Finset.sum_erase_eq_sub, Fin.sum_univ_three, Ω, abs_of_pos] at h0 h1 h2
  norm_num [abs_of_pos] at h0 h1 h2
  linarith [hd 0, hd 1, hd 2]

/-- `NoFactorRep.Ω` does not have factor width two, by `hasFactorWidthTwo_iff`. -/
theorem not_hasFactorWidthTwo : ¬ HasFactorWidthTwo Ω := fun h =>
  not_isScaledDiagDominant (hasFactorWidthTwo_iff.1 h).2

end NoFactorRep

end LinearSEM

end CausalInference
