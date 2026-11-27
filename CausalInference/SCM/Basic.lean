/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.TopologicalOrder
public import CausalInference.Basic.FiniteDistribution

/-!
# Finite Markovian structural causal models

A finite Markovian structural causal model on a directed acyclic graph `G : Digraph V`: each
endogenous vertex `v` takes values in a finite type `α v`, has its own exogenous noise in a
finite type `ε v`, and is determined by a structural equation `x v = f v (x restricted to the
parents of v) (u v)`. The noises are independent, with law `noise v` each.

## Main definitions

* `CausalInference.FiniteDist.pi p`: the product of a family of finite distributions, the joint
  law of independent coordinates.
* `CausalInference.SCM G α ε`: the structural equations, the noise laws, and the acyclicity of
  `G`.
* `SCM.IsSolution M u x`: the configuration `x` satisfies every structural equation at the noise
  value `u`.
* `SCM.solve M u`: the unique solution, defined by well-founded recursion along the edges.
* `SCM.noiseDist M`: the product law of the noises; `SCM.dist M`: the induced (observational)
  distribution, the pushforward of the noise law along `solve`.

## Main results

* `SCM.isSolution_iff`: `x` solves the equations at `u` if and only if `x = M.solve u`; hence
  `SCM.existsUnique_isSolution`, existence and uniqueness of the solution.
* `FiniteDist.prob_piFinset`: the product law of a rectangle is the product of the
  probabilities of its sides; `FiniteDist.map_pi_eval`: the coordinates of a product law have
  the given laws.
* `FiniteDist.probOf_map`: probabilities under a pushforward.

The models are the Markovian causal models of Pearl (2009), *Causality*, 2nd edition,
section 1.4.2 and Definition 7.1.1, restricted to finite recursive (acyclic) systems.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace FiniteDist

/-! ### Pushforward probabilities and product distributions -/

section Map

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']

/-- The probability of an event under a pushforward is the probability of its preimage. -/
theorem probOf_map (p : FiniteDist Ω) (f : Ω → Ω') (P : Ω' → Prop) [DecidablePred P] :
    (p.map f).probOf P = p.probOf (fun ω => P (f ω)) := by
  unfold probOf prob
  simp only [map_apply]
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun ω => P (f ω))
    (t := univ.filter P) (g := f) (fun ω hω => by simpa using hω)]
  refine sum_congr rfl fun b hb => sum_congr ?_ fun _ _ => rfl
  ext ω
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  exact ⟨fun h => ⟨h ▸ hb, h⟩, fun h => h.2⟩

end Map

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- The product of a family of finite distributions: the joint law of independent coordinates,
with mass `∏ i, p i (ω i)`. -/
def pi (p : ∀ i, FiniteDist (κ i)) : FiniteDist (∀ i, κ i) where
  mass ω := ∏ i, p i (ω i)
  nonneg ω := prod_nonneg fun i _ => (p i).nonneg _
  sum_eq_one := by
    rw [← Fintype.prod_sum]
    exact prod_eq_one fun i _ => (p i).sum_eq_one

@[simp] theorem pi_apply (p : ∀ i, FiniteDist (κ i)) (ω : ∀ i, κ i) :
    pi p ω = ∏ i, p i (ω i) := rfl

/-- The product law of a rectangle `∏ i, t i` is the product of the probabilities of its
sides. -/
theorem prob_piFinset (p : ∀ i, FiniteDist (κ i)) (t : ∀ i, Finset (κ i)) :
    (pi p).prob (Fintype.piFinset t) = ∏ i, (p i).prob (t i) := by
  simp only [prob, pi_apply]
  exact (prod_univ_sum t fun i e => p i e).symm

/-- The coordinate `i` of a product law has law `p i`. -/
theorem map_pi_eval [∀ i, DecidableEq (κ i)] (p : ∀ i, FiniteDist (κ i))
    (i : ι) : (pi p).map (fun ω => ω i) = p i := by
  ext a
  rw [map_apply_eq_prob]
  have h : (univ.filter fun ω : ∀ i, κ i => ω i = a) =
      Fintype.piFinset (Function.update (fun _ => univ) i {a}) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · intro h
      simpa using h i
  rw [h, prob_piFinset, Fintype.prod_eq_single i]
  · simp [prob]
  · intro j hj
    simp [Function.update_of_ne hj]

/-- The probability that the coordinate `i` of a product law satisfies `P` is the probability
of `P` under `p i`. -/
theorem probOf_pi_eval (p : ∀ i, FiniteDist (κ i)) (i : ι) (P : κ i → Prop)
    [DecidablePred P] : (pi p).probOf (fun ω => P (ω i)) = (p i).probOf P := by
  classical
  rw [← probOf_map, map_pi_eval]

end Pi

end FiniteDist

/-! ### Structural causal models -/

variable {V : Type*} [Fintype V]

/-- A finite Markovian structural causal model on the graph `G`. Each vertex `v` has a value
type `α v` and a noise type `ε v`; the structural equation of `v` computes its value from the
values of its parents and its own noise, `x v = f v (x restricted to the parents) (u v)`; the
noises are independent with laws `noise v`; and `G` is acyclic, so the system is recursive. -/
structure SCM (G : Digraph V) [DecidableRel G.Adj] (α : V → Type*) (ε : V → Type*)
    [∀ v, Fintype (ε v)] where
  /-- The causal graph is acyclic. -/
  acyclic : G.IsAcyclic
  /-- The structural function of `v`: from the values of the parents and the noise of `v` to
  the value of `v`. -/
  f : ∀ v, (∀ u : G.parentsFinset v, α u) → ε v → α v
  /-- The law of the noise of `v`. -/
  noise : ∀ v, FiniteDist (ε v)

namespace SCM

variable {G : Digraph V} [DecidableRel G.Adj] {α : V → Type*} {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- The configuration `x` solves the structural equations at the noise value `u`:
`x v = f v (x restricted to the parents of v) (u v)` for every vertex `v`. -/
def IsSolution (u : ∀ v, ε v) (x : ∀ v, α v) : Prop :=
  ∀ v, x v = M.f v ((G.parentsFinset v).restrict x) (u v)

/-- The solution of the structural equations at the noise value `u`, by well-founded recursion
along the edges of the acyclic graph: the value of `v` is computed from the values of its
parents. -/
noncomputable def solve (u : ∀ v, ε v) : ∀ v, α v :=
  M.acyclic.wellFounded_adj.fix (C := α)
    fun v rec => M.f v (fun p => rec p.1 (Digraph.mem_parentsFinset.1 p.2)) (u v)

/-- The unfolding equation of the solution. -/
theorem solve_eq (u : ∀ v, ε v) (v : V) :
    M.solve u v = M.f v ((G.parentsFinset v).restrict (M.solve u)) (u v) :=
  M.acyclic.wellFounded_adj.fix_eq _ v

/-- The solution solves the structural equations. -/
theorem isSolution_solve (u : ∀ v, ε v) : M.IsSolution u (M.solve u) := M.solve_eq u

/-- A solution of the structural equations is the solution: uniqueness, by well-founded
induction along the edges. -/
theorem eq_solve_of_isSolution {u : ∀ v, ε v} {x : ∀ v, α v} (h : M.IsSolution u x) :
    x = M.solve u := by
  funext v
  induction v using M.acyclic.wellFounded_adj.induction with
  | _ v ih =>
    rw [h v, M.solve_eq u v]
    congr 1
    funext p
    exact ih p.1 (Digraph.mem_parentsFinset.1 p.2)

/-- A configuration solves the structural equations at `u` if and only if it is the solution. -/
theorem isSolution_iff {u : ∀ v, ε v} {x : ∀ v, α v} : M.IsSolution u x ↔ x = M.solve u :=
  ⟨M.eq_solve_of_isSolution, fun h => h ▸ M.isSolution_solve u⟩

/-- **Existence and uniqueness of the solution** of a recursive structural causal model: at
every noise value there is exactly one configuration satisfying all structural equations. -/
theorem existsUnique_isSolution (u : ∀ v, ε v) : ∃! x, M.IsSolution u x :=
  ⟨M.solve u, M.isSolution_solve u, fun _ h => M.eq_solve_of_isSolution h⟩

variable [DecidableEq V]

/-- The product law of the noises: the noises of the vertices are independent. -/
def noiseDist : FiniteDist (∀ v, ε v) := FiniteDist.pi M.noise

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- The distribution induced by the model on the configurations: the pushforward of the noise
law along the solution map. -/
noncomputable def dist : FiniteDist (∀ v, α v) := M.noiseDist.map M.solve

theorem dist_apply (x : ∀ v, α v) :
    M.dist x = M.noiseDist.prob (univ.filter fun u => M.solve u = x) := rfl

/-- Probabilities of events under the induced distribution are noise probabilities. -/
theorem probOf_dist (P : (∀ v, α v) → Prop) [DecidablePred P] :
    M.dist.probOf P = M.noiseDist.probOf (fun u => P (M.solve u)) :=
  FiniteDist.probOf_map _ _ _

/-- The marginal mass of the induced distribution on a set `S` at `x` is the noise probability
that the solution agrees with `x` on `S`. -/
theorem margAt_dist (S : Finset V) (x : ∀ v, α v) :
    M.dist.margAt S x = M.noiseDist.probOf (fun u => ∀ v ∈ S, M.solve u v = x v) := by
  rw [FiniteDist.margAt_eq_probOf, probOf_dist]

end SCM

/-! ### A two-vertex example -/

namespace SCMExamples

/-- The graph `0 → 1` on two vertices. -/
def arrow : Digraph (Fin 2) where
  Adj i j := i = 0 ∧ j = 1

instance : DecidableRel arrow.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem arrow_isAcyclic : arrow.IsAcyclic := by decide

/-- The model `X := U₀`, `Y := X` on `0 → 1` with two fair noise bits: the outcome copies the
treatment. -/
noncomputable def copyModel : SCM arrow (fun _ => Bool) (fun _ => Bool) where
  acyclic := arrow_isAcyclic
  f v z e := if h : v = 1 then z ⟨0, by subst h; decide⟩ else e
  noise _ := FiniteDist.uniform

/-- In the copy model both variables equal the first noise bit. -/
theorem copyModel_solve (u : Fin 2 → Bool) : copyModel.solve u = fun _ => u 0 := by
  refine (copyModel.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [copyModel, Finset.restrict]

end SCMExamples

end CausalInference
