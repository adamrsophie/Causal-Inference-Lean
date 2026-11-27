/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.Tian

/-!
# Expressions in the observed law

A small syntax for the formulas returned by the identification algorithm, and its evaluation
into functionals of a finite joint law. An expression denotes a real function of
configurations `w : ∀ v, α v`, built from marginal masses, quotients, sums over the values of
a set of coordinates, and finite products.

## Main definitions

* `IdExpr V`: the expressions.
* `IdExpr.eval p e`: the value of `e` under the joint law `p`, as a function of `w`.
  `marg S` is the marginal mass `P(s)`, `div` a quotient, `sum S e` the sum of `e` over the
  values of the coordinates in `S` (the other coordinates held at those of `w`), `prodV S f`
  and `prodSets 𝒮 f` products over a finset of vertices or of sets of vertices.
* `IdExpr.MargWithin O e`: every marginal mass in `e` is on a subset of `O`.

## Main results

* `IdExpr.eval_eq_of_marginal_eq`: an expression whose marginals are all on subsets of `O`
  has the same value under two laws with the same marginal on `O`.
-/

@[expose] public section

namespace CausalInference

open Finset

/-- Expressions in the observed law: marginal masses, quotients, sums over the values of a
set of coordinates, and finite products over vertices or over sets of vertices. -/
inductive IdExpr (V : Type*) where
  /-- The marginal mass `P(s)` of the set `S`. -/
  | marg : Finset V → IdExpr V
  /-- A quotient. -/
  | div : IdExpr V → IdExpr V → IdExpr V
  /-- The sum over the values of the coordinates in a set. -/
  | sum : Finset V → IdExpr V → IdExpr V
  /-- A product over a finset of vertices. -/
  | prodV : Finset V → (V → IdExpr V) → IdExpr V
  /-- A product over a finset of sets of vertices. -/
  | prodSets : Finset (Finset V) → (Finset V → IdExpr V) → IdExpr V

namespace IdExpr

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- The value of an expression under the joint law `p`, as a function of the configuration
`w`: `marg S` is `p.margAt S w`; `sum S e` is the sum of `e` over the configurations that agree
with `w` outside `S`; `div`, `prodV` and `prodSets` are the real quotient and products. -/
noncomputable def eval (p : FiniteDist (∀ v, α v)) : IdExpr V → (∀ v, α v) → ℝ
  | marg S, w => p.margAt S w
  | div e₁ e₂, w => eval p e₁ w / eval p e₂ w
  | sum S e, w => ∑ c ∈ FiniteDist.agreeOn Sᶜ w, eval p e c
  | prodV S f, w => ∏ v ∈ S, eval p (f v) w
  | prodSets 𝒮 f, w => ∏ d ∈ 𝒮, eval p (f d) w

variable (p : FiniteDist (∀ v, α v))

/-- Evaluation of a marginal mass. -/
@[simp] theorem eval_marg (S : Finset V) (w : ∀ v, α v) : (marg S).eval p w = p.margAt S w :=
  rfl

/-- Evaluation of a quotient. -/
@[simp] theorem eval_div (e₁ e₂ : IdExpr V) (w : ∀ v, α v) :
    (div e₁ e₂).eval p w = e₁.eval p w / e₂.eval p w := rfl

/-- Evaluation of a sum over the values of a set of coordinates. -/
@[simp] theorem eval_sum (S : Finset V) (e : IdExpr V) (w : ∀ v, α v) :
    (sum S e).eval p w = ∑ c ∈ FiniteDist.agreeOn Sᶜ w, e.eval p c := rfl

/-- Evaluation of a product over vertices. -/
@[simp] theorem eval_prodV (S : Finset V) (f : V → IdExpr V) (w : ∀ v, α v) :
    (prodV S f).eval p w = ∏ v ∈ S, (f v).eval p w := rfl

/-- Evaluation of a product over sets of vertices. -/
@[simp] theorem eval_prodSets (𝒮 : Finset (Finset V)) (f : Finset V → IdExpr V)
    (w : ∀ v, α v) : (prodSets 𝒮 f).eval p w = ∏ d ∈ 𝒮, (f d).eval p w := rfl

omit [Fintype V] [DecidableEq V] in
/-- Every marginal mass in the expression is on a subset of `O`. -/
def MargWithin (O : Finset V) : IdExpr V → Prop
  | marg S => S ⊆ O
  | div e₁ e₂ => MargWithin O e₁ ∧ MargWithin O e₂
  | sum _ e => MargWithin O e
  | prodV S f => ∀ v ∈ S, MargWithin O (f v)
  | prodSets 𝒮 f => ∀ d ∈ 𝒮, MargWithin O (f d)

/-- **An expression in the observed law depends on the law only through the observed
marginal**: if every marginal mass of `e` is on a subset of `O`, two laws with the same
marginal on `O` give `e` the same value. -/
theorem eval_eq_of_marginal_eq {p q : FiniteDist (∀ v, α v)} {O : Finset V}
    (h : p.marginal O = q.marginal O) (e : IdExpr V) (he : e.MargWithin O) :
    e.eval p = e.eval q := by
  induction e with
  | marg S =>
    funext w
    exact FiniteDist.margAt_eq_of_marginal_eq h he w
  | div e₁ e₂ ih₁ ih₂ =>
    funext w
    simp only [eval_div, ih₁ he.1, ih₂ he.2]
  | sum S e ih =>
    funext w
    simp only [eval_sum, ih he]
  | prodV S f ih =>
    funext w
    simp only [eval_prodV]
    exact prod_congr rfl fun v hv => by rw [ih v (he v hv)]
  | prodSets 𝒮 f ih =>
    funext w
    simp only [eval_prodSets]
    exact prod_congr rfl fun d hd => by rw [ih d (he d hd)]

end IdExpr

end CausalInference
