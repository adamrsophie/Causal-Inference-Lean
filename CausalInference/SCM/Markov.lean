/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Basic
public import CausalInference.Graphical.LocalMarkov

/-!
# The causal Markov condition

The distribution induced by a finite Markovian structural causal model factorizes according to
its graph, with the kernel of `v` given by the law of `f v z (u v)` for each parent
configuration `z`; hence it satisfies the local (parental) Markov property. Conversely, every
distribution that factorizes according to an acyclic graph is induced by a structural causal
model on that graph.

## Main definitions

* `SCM.kernel M v z`: the law of `M.f v z (u v)` when the noise `u v` has law `M.noise v`, that
  is, `P_ε(f v z ε = a)` at `a`.
* `SCM.kernels M`: these laws as Markov kernels of the graph.
* `Digraph.MarkovKernels.toSCM k hG`: the structural causal model with response-function noise
  realizing the kernels `k`. The noise of `v` is a function from parent configurations to values
  of `v`, its coordinates are independent with laws `k.kernel v z`, and `v` takes the value of
  that function at the configuration of its parents.

## Main results

* `SCM.dist_eq_prod`: `M.dist x = ∏ v, M.kernels.factor v x`.
* `SCM.factorizes`, `SCM.localMarkov`: the **causal Markov condition** (Pearl 2009,
  Theorem 1.4.1). The induced distribution factorizes according to `G`, and every vertex is
  conditionally independent of its nondescendants given its parents.
* `SCM.margAt_insert_parents`: the kernel of `v` is the conditional law of `v` given its parents
  under the induced distribution, in product form.
* `Digraph.MarkovKernels.dist_toSCM`, `Digraph.Factorizes.exists_scm`: every distribution that
  factorizes according to an acyclic graph `G` is the distribution induced by a structural causal
  model on `G`, with response-function noise (Pearl 2009, section 1.4.2, citing Druzdzel and
  Simon 1993).

Sources: Pearl (2009), *Causality*, 2nd edition, sections 1.4.1 and 1.4.2; Pearl and Verma
(1991).
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- The kernel of `v`: the law of the value `M.f v z e` of `v` when its parents take the values
`z` and its noise `e` has law `M.noise v`. -/
noncomputable def kernel (v : V) (z : ∀ u : G.parentsFinset v, α u) : FiniteDist (α v) :=
  (M.noise v).map (M.f v z)

/-- The kernel of `v` at `a` is the noise probability that the structural function of `v`
returns `a`. -/
theorem kernel_apply (v : V) (z : ∀ u : G.parentsFinset v, α u) (a : α v) :
    M.kernel v z a = (M.noise v).probOf (fun e => M.f v z e = a) := rfl

/-- The kernels of the model as Markov kernels of the graph. -/
noncomputable def kernels : G.MarkovKernels α where
  kernel v z a := M.kernel v z a
  nonneg v z a := (M.kernel v z).nonneg a
  sum_eq_one v z := (M.kernel v z).sum_eq_one

theorem kernels_kernel (v : V) (z : ∀ u : G.parentsFinset v, α u) (a : α v) :
    M.kernels.kernel v z a = M.kernel v z a := rfl

/-- The factor of `v` at a configuration `x` is the noise probability that the structural
equation of `v` holds at `x`. -/
theorem kernels_factor (v : V) (x : ∀ v, α v) :
    M.kernels.factor v x =
      (M.noise v).probOf (fun e => M.f v ((G.parentsFinset v).restrict x) e = x v) := rfl

variable [DecidableEq V]

omit [∀ v, Fintype (α v)] in
/-- The noise values at which the solution is `x` form a rectangle: at each vertex, the noise
values that make the structural equation of that vertex hold at `x`. -/
theorem filter_solve_eq (x : ∀ v, α v) :
    (univ.filter fun u => M.solve u = x) =
      Fintype.piFinset fun v => univ.filter fun e => M.f v ((G.parentsFinset v).restrict x) e =
        x v := by
  ext u
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  rw [eq_comm, ← M.isSolution_iff]
  exact forall_congr' fun v => eq_comm

/-- **Factorization of the induced distribution**: the mass of a configuration is the product of
the kernels of the vertices at that configuration. -/
theorem dist_eq_prod (x : ∀ v, α v) : M.dist x = ∏ v, M.kernels.factor v x := by
  rw [dist_apply, filter_solve_eq, noiseDist, FiniteDist.prob_piFinset]
  rfl

/-- **Causal Markov condition**, factorization form: the distribution induced by a Markovian
structural causal model factorizes according to its graph. -/
theorem factorizes : G.Factorizes M.dist := ⟨M.kernels, M.dist_eq_prod⟩

/-- **Causal Markov condition** (Pearl 2009, Theorem 1.4.1): the distribution induced by a
Markovian structural causal model satisfies the parental Markov condition relative to its
graph. Every vertex is conditionally independent of its nondescendants other than its parents,
given its parents. -/
theorem localMarkov : G.LocalMarkov M.dist := M.factorizes.localMarkov M.acyclic

/-- The kernel of `v` is the conditional law of `v` given its parents under the induced
distribution, in product form: `P(x_v, x_pa) = kernel v x_pa x_v * P(x_pa)`. -/
theorem margAt_insert_parents (v : V) (x : ∀ v, α v) :
    M.dist.margAt (insert v (G.parentsFinset v)) x =
      M.kernel v ((G.parentsFinset v).restrict x) (x v) * M.dist.margAt (G.parentsFinset v) x :=
  M.kernels.margAt_insert_parents M.acyclic M.dist_eq_prod v x

/-- On a set `A` closed under taking parents, the marginal of the induced distribution is the
product of the kernels of the vertices of `A`. -/
theorem margAt_of_ancestral {A : Finset V} (hA : ∀ v ∈ A, ∀ u, G.Adj u v → u ∈ A)
    (x : ∀ v, α v) : M.dist.margAt A x = ∏ v ∈ A, M.kernels.factor v x :=
  M.kernels.margAt_of_ancestral M.acyclic M.dist_eq_prod hA x

/-- Two models on the same graph with the same kernels induce the same distribution. -/
theorem dist_eq_of_kernel_eq {ε' : V → Type*} [∀ v, Fintype (ε' v)] {M' : SCM G α ε'}
    (h : ∀ v z a, M.kernel v z a = M'.kernel v z a) : M.dist = M'.dist := by
  ext x
  rw [dist_eq_prod, dist_eq_prod]
  exact prod_congr rfl fun v _ => h v _ _

end SCM

end CausalInference

/-! ### Every factorizing distribution is induced by a structural causal model -/

namespace Digraph.MarkovKernels

open CausalInference Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- The row of the kernel of `v` at the parent configuration `z`, as a finite distribution. -/
def row (k : G.MarkovKernels α) (v : V) (z : ∀ u : G.parentsFinset v, α u) :
    FiniteDist (α v) :=
  ⟨k.kernel v z, k.nonneg v z, k.sum_eq_one v z⟩

/-- The structural causal model with response-function noise realizing the kernels `k` of an
acyclic graph. The noise of `v` is a response function `r` from parent configurations to values
of `v`; its values `r z` at the different parent configurations are independent with laws
`k.kernel v z`; and the structural equation of `v` is `x v = r (x restricted to the parents)`.
-/
noncomputable def toSCM (k : G.MarkovKernels α) (hG : G.IsAcyclic) :
    SCM G α (fun v => (∀ u : G.parentsFinset v, α u) → α v) where
  acyclic := hG
  f _ z r := r z
  noise v := FiniteDist.pi (k.row v)

/-- The kernels of the response-function model are the given kernels. -/
theorem kernel_toSCM (k : G.MarkovKernels α) (hG : G.IsAcyclic) (v : V)
    (z : ∀ u : G.parentsFinset v, α u) (a : α v) :
    (k.toSCM hG).kernel v z a = k.kernel v z a := by
  change ((FiniteDist.pi (k.row v)).map fun r => r z) a = _
  rw [FiniteDist.map_pi_eval]
  rfl

/-- The response-function model induces the product of the kernels. -/
theorem dist_toSCM (k : G.MarkovKernels α) (hG : G.IsAcyclic) :
    (k.toSCM hG).dist = k.jointDist hG := by
  ext x
  rw [SCM.dist_eq_prod, jointDist_apply]
  refine prod_congr rfl fun v _ => ?_
  exact k.kernel_toSCM hG v _ _

end Digraph.MarkovKernels

namespace CausalInference

/-- **Every factorizing distribution has a functional model** (Pearl 2009, section 1.4.2): a
distribution that factorizes according to an acyclic graph `G` is the distribution induced by a
structural causal model on `G`. The noise types are the response-function types
`(∀ u : G.parentsFinset v, α u) → α v`. -/
theorem _root_.Digraph.Factorizes.exists_scm {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V}
    [DecidableRel G.Adj] {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (hG : G.IsAcyclic) {p : FiniteDist (∀ v, α v)} (h : G.Factorizes p) :
    ∃ M : SCM G α (fun v => (∀ u : G.parentsFinset v, α u) → α v), M.dist = p := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.toSCM hG, ?_⟩
  rw [k.dist_toSCM hG]
  ext x
  exact (hk x).symm

end CausalInference
