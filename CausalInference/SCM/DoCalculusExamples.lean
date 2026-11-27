/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.DoCalculus
public import CausalInference.Graphical.DSeparationExamples
public import CausalInference.Graphical.Closure

/-!
# Testing the rules of do-calculus

Corollaries of the rules of do-calculus (`CausalInference.SCM.DoCalculus`) and counterexamples
showing that each rule fails without its graphical condition.

## Main results

* `SCM.backdoor_adjustment`: the back-door adjustment
  `P(y | do(x)) = ∑_z P(y | x, z) P(z)` for a set `Z` of non-descendants of `X` that
  d-separates `X` from `Y` in `G.deleteOutgoing X`, derived from Rule 2 under the positivity
  `P(z) > 0 → P(x, z) > 0`. The two back-door conditions are stated as hypotheses.
* `SCM.FrontDoorExample.frontdoor_formula`: on the front-door graph with a latent confounder,
  `P(y | do(x)) = ∑_z P(z | x) ∑_x' P(y | x', z) P(x')` when the observed law of `(X, Z)` is
  strictly positive, derived with Rules 2 and 3 and the back-door adjustment as in Pearl
  (2009), section 3.4.3.
* `SCM.DoCalculusCounterexamples.rule1_fails`, `rule2_fails`, `rule3_fails`: for each rule, a
  small concrete model in which the d-separation condition fails and the division-free
  identity of the rule fails, with the numbers checked.

Source: Pearl (2009), *Causality*, 2nd edition, sections 3.3 and 3.4.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- Interventions on equal sets induce the same distribution. -/
theorem dist_intervene_of_eq {X X' : Finset V} (h : X = X') {x : ∀ u, α u} :
    (M.intervene X x).dist = (M.intervene X' x).dist := by
  subst h
  rfl

/-- **Back-door adjustment** (Pearl 2009, Theorem 3.3.2, equation (3.19)), derived from Rule 2.
Let `X`, `Y`, `Z` be pairwise disjoint, let no vertex of `Z` be a descendant of `X`, and let `X`
and `Y` be d-separated by `Z` in `G.deleteOutgoing X`. If every value `z` of positive
probability gives `x` positive probability together with it, then
`P(y | do(x)) = ∑_z P(y, x, z) / P(x, z) * P(z)`, that is `∑_z P(y | x, z) P(z)`. The sum runs
over the configurations that agree with `v` outside `Z`. Values `z` of probability zero
contribute zero on both sides. -/
theorem backdoor_adjustment {X Y Z : Finset V} (v : ∀ u, α u) (hXY : Disjoint X Y)
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) (hnd : ∀ u ∈ Z, u ∉ G.descendantsOf ↑X)
    (hsep : (G.deleteOutgoing ↑X).DSep ↑X ↑Y ↑Z)
    (hpos : ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) → 0 < M.dist.margAt Z c →
      0 < M.dist.margAt (X ∪ Z) c) :
    M.effect X v Y v = ∑ c ∈ FiniteDist.agreeOn Zᶜ v,
      M.dist.margAt (Y ∪ X ∪ Z) c / M.dist.margAt (X ∪ Z) c * M.dist.margAt Z c := by
  rw [effect, FiniteDist.margAt_eq_sum_margAt _ (subset_union_left (s₂ := Z)),
    union_sdiff_cancel_left hYZ]
  refine sum_congr rfl fun c hc => ?_
  have hcX : ∀ u ∈ X, v u = c u := fun u hu =>
    ((FiniteDist.mem_agreeOn.1 hc) u (mem_compl.2 (disjoint_left.1 hXZ hu))).symm
  rw [M.intervene_congr hcX]
  have hsep' : ((G.deleteIncoming ↑(∅ : Finset V)).deleteOutgoing ↑X).DSep ↑Y ↑X
      ↑((∅ : Finset V) ∪ Z) := by
    simpa using hsep.symm
  have h2 := M.rule2 c (disjoint_empty_left X) hXY.symm hXZ.symm hsep'
  rw [M.dist_intervene_of_eq (empty_union X)] at h2
  simp only [dist_intervene_empty] at h2
  have hZ : (M.intervene X c).dist.margAt Z c = M.dist.margAt Z c :=
    M.margAt_intervene_of_notMem_descendantsOf hnd c
  rw [hZ] at h2
  rcases (M.dist.margAt_nonneg Z c).eq_or_lt with h0 | hz
  · rw [← h0, mul_zero]
    refine le_antisymm ?_ (FiniteDist.margAt_nonneg _ _ _)
    rw [h0, ← hZ]
    exact FiniteDist.margAt_anti _ subset_union_right c
  · have hxz := hpos c (fun u hu => (hcX u hu).symm) hz
    field_simp
    linear_combination h2

end SCM

end CausalInference

namespace Digraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With no observed set `W`, the set `Z(W)` of Rule 3 is all of `Z`. -/
theorem rule3Set_empty_right (G : Digraph V) (X Z : Finset V) : G.rule3Set X Z ∅ = Z := by
  ext z
  simp [mem_rule3Set]

end Digraph

namespace CausalInference

open Finset

/-! ### The front-door formula derived with the rules -/

namespace SCM.FrontDoorExample

open DSeparationExamples

variable {α : Fin 4 → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  {ε : Fin 4 → Type*}
  [∀ v, Fintype (ε v)]

/-- **The front-door formula** (Pearl 2009, section 3.4.3, equation (3.42); Theorem 3.3.4),
derived with the rules of do-calculus on the front-door graph `DSeparationExamples.frontdoor`:
a latent confounder `U = 0` of the treatment `X = 1` and the outcome `Y = 3`, and a mediator
`Z = 2` with `X → Z → Y`. If the observed law of `(X, Z)` is strictly positive, then
`P(y | do(x)) = ∑_z P(z | x) ∑_x' P(y | x', z) P(x')`, with
`P(z | x) = P(z, x) / P(x)` and `P(y | x', z) = P(y, z, x') / P(z, x')`. The sums run over the
configurations that agree with `v` outside `Z` and then with `c` outside `X`. Only marginals on
subsets of the observed vertices `{1, 2, 3}` appear on the right.

The derivation follows Pearl: Task 1 is Rule 2, `P(z | do(x)) = P(z | x)`; then Rule 2 gives
`P(y | do(x), z) = P(y | do(x), do(z))`, Rule 3 deletes `do(x)`, and the back-door adjustment
(itself derived from Rule 2) evaluates `P(y | do(z))`. -/
theorem frontdoor_formula (M : SCM frontdoor α ε) (v : ∀ u, α u)
    (hpos : ∀ c : ∀ u, α u, 0 < M.dist.margAt {1, 2} c) :
    M.effect {1} v {3} v = ∑ c ∈ FiniteDist.agreeOn {2}ᶜ v,
      M.dist.margAt ({2} ∪ {1}) c / M.dist.margAt {1} c *
        ∑ d ∈ FiniteDist.agreeOn {1}ᶜ c,
          M.dist.margAt ({3} ∪ {2} ∪ {1}) d / M.dist.margAt ({2} ∪ {1}) d *
            M.dist.margAt {1} d := by
  rw [effect,
    FiniteDist.margAt_eq_sum_margAt _ (subset_union_left (s₂ := ({2} : Finset (Fin 4)))),
    show ({3} ∪ {2} : Finset (Fin 4)) \ {3} = {2} by decide]
  refine sum_congr rfl fun c hc => ?_
  have hc1 : ∀ u ∈ ({1} : Finset (Fin 4)), v u = c u := by
    intro u hu
    rw [mem_singleton] at hu
    subst hu
    exact ((FiniteDist.mem_agreeOn.1 hc) 1 (by decide)).symm
  rw [M.intervene_congr hc1]
  -- Task 1 (Rule 2): `P(z | do(x)) * P(x) = P(z, x)`
  have t1 := M.rule2 (X := ∅) (Y := {2}) (Z := {1}) (W := ∅) c (by decide) (by decide)
    (by decide) (by decide)
  rw [M.dist_intervene_of_eq (empty_union {1})] at t1
  simp only [dist_intervene_empty, union_empty, FiniteDist.margAt_empty, mul_one] at t1
  -- Rule 2: `P(y | do(x), do(z)) * P(z | do(x)) = P(y, z | do(x))`
  have t2 := M.rule2 (X := {1}) (Y := {3}) (Z := {2}) (W := ∅) c (by decide) (by decide)
    (by decide) (by decide)
  simp only [union_empty, FiniteDist.margAt_empty, mul_one] at t2
  -- Rule 3: `P(y | do(z), do(x)) = P(y | do(z))`
  have t3 := M.rule3 (X := {2}) (Y := {3}) (Z := {1}) (W := ∅) c (by decide) (by decide)
    (by rw [Digraph.rule3Set_empty_right]; decide)
  simp only [union_empty, FiniteDist.margAt_empty, mul_one] at t3
  rw [M.dist_intervene_of_eq (union_comm {2} {1})] at t3
  -- the back-door adjustment for `P(y | do(z))`, adjusting for `X`
  have bd := M.backdoor_adjustment (X := {2}) (Y := {3}) (Z := {1}) c (by decide) (by decide)
    (by decide) (by decide) (by decide) fun d _ _ => by
      rw [show ({2} ∪ {1} : Finset (Fin 4)) = {1, 2} by decide]
      exact hpos d
  rw [effect] at bd
  have hx : 0 < M.dist.margAt {1} c :=
    (hpos c).trans_le (M.dist.margAt_anti (by decide) c)
  rw [← bd, ← t3, ← t2, ← t1]
  field_simp

end SCM.FrontDoorExample

/-! ### Each rule fails without its graphical condition -/

namespace SCM.DoCalculusCounterexamples

open SCMExamples BowExample

/-- The all-`true` configuration on two vertices. -/
def allTrue : Fin 2 → Bool := fun _ => true

/-- In the copy model `X := U₀`, `Y := X`, every nonempty set of vertices takes the value `true`
with probability `1/2`. -/
theorem copyModel_margAt {S : Finset (Fin 2)} (hS : S.Nonempty) :
    copyModel.dist.margAt S allTrue = 1 / 2 := by
  obtain ⟨s, hs⟩ := hS
  rw [margAt_dist]
  simp only [copyModel_solve, allTrue]
  rw [FiniteDist.probOf_congr _ (Q := fun u : Fin 2 → Bool => u 0 = true)
    fun u => ⟨fun h => h s hs, fun h _ _ => h⟩]
  change (FiniteDist.pi fun _ => FiniteDist.uniform).probOf _ = _
  exact (FiniteDist.probOf_pi_eval (κ := fun _ : Fin 2 => Bool) (fun _ => FiniteDist.uniform) 0
    (fun b : Bool => b = true)).trans (by simp [FiniteDist.probOf, FiniteDist.prob]; rfl)

/-- **Rule 1 fails without its graphical condition.** In the copy model on `0 → 1`, with
`X = W = ∅`, `Y = {1}`, `Z = {0}` (pairwise disjoint), `Y` and `Z` are d-connected, and
`P(y, z) * P(∅) = 1/2` differs from `P(y) * P(z) = 1/4`. -/
theorem rule1_fails :
    ¬ (arrow.deleteIncoming ↑(∅ : Finset (Fin 2))).DSep ↑({1} : Finset (Fin 2))
        ↑({0} : Finset (Fin 2)) ↑((∅ : Finset (Fin 2)) ∪ ∅) ∧
      (copyModel.intervene ∅ allTrue).dist.margAt ({1} ∪ {0} ∪ ∅) allTrue *
          (copyModel.intervene ∅ allTrue).dist.margAt ∅ allTrue ≠
        (copyModel.intervene ∅ allTrue).dist.margAt ({1} ∪ ∅) allTrue *
          (copyModel.intervene ∅ allTrue).dist.margAt ({0} ∪ ∅) allTrue := by
  refine ⟨by decide, ?_⟩
  simp only [dist_intervene_empty, union_empty, FiniteDist.margAt_empty, mul_one]
  rw [copyModel_margAt (by decide), copyModel_margAt (by decide), copyModel_margAt (by decide)]
  norm_num

/-- Under `do(X := true)` in the copy model, the outcome is `true` with probability one. -/
theorem copyModel_intervene_margAt :
    (copyModel.intervene {0} allTrue).dist.margAt {1} allTrue = 1 := by
  have h : ∀ u, ∀ w ∈ ({1} : Finset (Fin 2)),
      (copyModel.intervene {0} allTrue).solve u w = allTrue w := by
    intro u w hw
    rw [mem_singleton] at hw
    subst hw
    rw [copyModel.solve_intervene_of_notMem u (by decide)]
    simp only [copyModel, dite_true, Finset.restrict]
    exact copyModel.solve_intervene_of_mem u (mem_singleton_self 0)
  rw [margAt_dist, FiniteDist.probOf]
  convert FiniteDist.prob_univ _
  ext u
  simp only [mem_filter, mem_univ, true_and, iff_true]
  exact h u

/-- **Rule 3 fails without its graphical condition.** In the copy model on `0 → 1`, with
`X = W = ∅`, `Y = {1}`, `Z = {0}` (pairwise disjoint, so `Z(W) = Z`), `Y` and `Z` are
d-connected in
`G.deleteIncoming Z`, and `P(y | do(z)) = 1` differs from `P(y) = 1/2`. -/
theorem rule3_fails :
    ¬ (arrow.deleteIncoming ↑((∅ : Finset (Fin 2)) ∪ arrow.rule3Set ∅ {0} ∅)).DSep
        ↑({1} : Finset (Fin 2)) ↑({0} : Finset (Fin 2)) ↑((∅ : Finset (Fin 2)) ∪ ∅) ∧
      (copyModel.intervene (∅ ∪ {0}) allTrue).dist.margAt ({1} ∪ ∅) allTrue *
          (copyModel.intervene ∅ allTrue).dist.margAt ∅ allTrue ≠
        (copyModel.intervene ∅ allTrue).dist.margAt ({1} ∪ ∅) allTrue *
          (copyModel.intervene (∅ ∪ {0}) allTrue).dist.margAt ∅ allTrue := by
  refine ⟨by rw [Digraph.rule3Set_empty_right]; decide, ?_⟩
  rw [copyModel.dist_intervene_of_eq (empty_union {0})]
  simp only [dist_intervene_empty, union_empty, FiniteDist.margAt_empty, mul_one]
  rw [copyModel_intervene_margAt, copyModel_margAt (by decide)]
  norm_num

/-- In the bow model A, `P(X = true) = 1/2`. -/
theorem modelA_margAt_one : modelA.dist.margAt {1} treat = 1 / 2 := by
  rw [margAt_dist]
  simp only [mem_singleton, forall_eq, modelA_solve]
  change (FiniteDist.pi bowNoise).probOf (fun u => u 0 = true) = _
  exact (FiniteDist.probOf_pi_eval (κ := fun _ : Fin 3 => Bool) bowNoise 0
    (fun b : Bool => b = true)).trans (by simp [bowNoise, FiniteDist.probOf, FiniteDist.prob]; rfl)

/-- In the bow model A, `P(Y = true, X = true) = 3/8`. -/
theorem modelA_margAt_two_one : modelA.dist.margAt ({2} ∪ {1}) treat = 3 / 8 := by
  rw [margAt_dist]
  simp only [mem_union, mem_singleton, forall_eq_or_imp, forall_eq, modelA_solve]
  change (FiniteDist.pi bowNoise).probOf (fun u => xor (u 0) (u 2) = true ∧ u 0 = true) = _
  rw [← FiniteDist.probOf_map (FiniteDist.pi bowNoise) (fun u => (u 0, u 2))
    (fun q => xor q.1 q.2 = true ∧ q.1 = true), FiniteDist.map_pi_eval_pair bowNoise (by decide)]
  simp [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type, bowNoise,
    quarterCoin]
  norm_num

/-- **Rule 2 fails without its graphical condition.** In the bow model A (a latent common cause
`U = 0` of `X = 1` and `Y = 2`), with `X = W = ∅` in the rule, `Y = {2}` and `Z = {1}`
(pairwise disjoint), the back-door path `X ← U → Y` d-connects `Y` and `Z` in
`G.deleteOutgoing Z`, and `P(y | do(x)) * P(x) = 1/2 * 1/2` differs from `P(y, x) = 3/8`; so
`P(y | do(x)) = 1/2` differs from `P(y | x) = 3/4`. -/
theorem rule2_fails :
    ¬ ((bow.deleteIncoming ↑(∅ : Finset (Fin 3))).deleteOutgoing
          ↑({1} : Finset (Fin 3))).DSep ↑({2} : Finset (Fin 3)) ↑({1} : Finset (Fin 3))
        ↑((∅ : Finset (Fin 3)) ∪ ∅) ∧
      (modelA.intervene (∅ ∪ {1}) treat).dist.margAt ({2} ∪ ∅) treat *
          (modelA.intervene ∅ treat).dist.margAt ({1} ∪ ∅) treat ≠
        (modelA.intervene ∅ treat).dist.margAt ({2} ∪ {1} ∪ ∅) treat *
          (modelA.intervene (∅ ∪ {1}) treat).dist.margAt ∅ treat := by
  refine ⟨by decide, ?_⟩
  rw [modelA.dist_intervene_of_eq (empty_union {1})]
  simp only [dist_intervene_empty, union_empty, FiniteDist.margAt_empty, mul_one]
  rw [show (modelA.intervene {1} treat).dist.margAt {2} treat = 1 / 2 from modelA_effect,
    modelA_margAt_one, modelA_margAt_two_one]
  norm_num

end SCM.DoCalculusCounterexamples

end CausalInference
