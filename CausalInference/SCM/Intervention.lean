/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Markov

/-!
# Interventions in finite structural causal models

The intervention `do(X := x)` on a finite Markovian structural causal model replaces the
structural equation of every vertex of `X` by the constant given by `x`. The resulting model
(the submodel `M_x`) lives on the mutilated graph `G.deleteIncoming X` and keeps the noise
space, so that potential responses at a fixed noise value can be compared across models.

The values of an intervention are given as a full configuration `x : ∀ v, α v`; only its
coordinates in `X` are used.

## Main definitions

* `SCM.intervene M X x`: the submodel `M_x` of `do(X := x)`, a model on `G.deleteIncoming X`.

## Main results

* `SCM.isSolution_intervene_iff`: the equations of the submodel.
* `SCM.dist_intervene`: the **truncated factorization** (Pearl 2009, equations (1.37), (3.10),
  (3.14); the g-formula; the manipulation theorem). The interventional mass of `y` is the product
  of the kernels of the vertices outside `X` when `y` agrees with `x` on `X`, and `0` otherwise.
* `SCM.solve_intervene_empty`, `SCM.dist_intervene_empty`: intervening on nothing changes
  nothing.
* `SCM.solve_intervene_intervene`, `SCM.dist_intervene_intervene`: composing `do(X := x)` with a
  later `do(W := w)` is the single intervention on `X ∪ W` in which `w` wins on `W`.
* `SCM.solve_intervene_of_notMem_descendantsOf`, `SCM.margAt_intervene_of_notMem_descendantsOf`:
  an intervention on `X` changes neither the value nor the marginal law of the vertices that are
  not descendants of `X` (Pearl 2009, section 1.3: only descendants respond).
* `SCM.factorizes_intervene`: the interventional distribution factorizes according to
  `G.deleteIncoming X` (condition (i) of Pearl 2009, Definition 1.3.1).
* `SCM.probOf_intervene_of_parents_subset`: under an intervention that fixes the parents of `v`
  but not `v`, the law of `v` is its kernel at the fixed parent values.
* `SCM.margAt_insert_parents_eq_probOf_intervene_mul` (**Property 1**, Pearl 2009, (1.38)):
  `P(v, pa v) = P_{do(pa v)}(v) * P(pa v)`, the product form of `P(v | pa v) = P_{pa v}(v)`;
  `SCM.div_margAt_parents_eq_probOf_intervene`: its ratio form when `P(pa v) > 0`.
* `SCM.probOf_intervene_union_eq` (**Property 2**, Pearl 2009, (1.39)): once the parents of `v`
  are fixed, further interventions on vertices other than `v` do not change the law of `v`.
* `SCM.margAt_insert_parents_intervene`, `SCM.margAt_insert_parents_intervene_mul_comm`
  (condition (iii) of Pearl 2009, Definition 1.3.1): for `v ∉ X`, the conditional law of `v`
  given its parents is the same under `do(X := x)` as without intervention, in product form.
* `SCM.replace`, `SCM.dist_replace`: general (soft or conditional) interventions that replace
  the mechanisms of `X` by other functions of the same parents and noise types, and the
  resulting product formula (Pearl 2009, section 3.2.3, mechanism replacement).

Sources: Pearl (2009), *Causality*, 2nd edition, sections 1.3.1, 1.4.3, 3.2.3, Definition 7.1.2;
Spirtes et al. (1993), the manipulation theorem; Robins (1986), the g-formula.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- A parent of `v ∉ X` in `G` is a parent of `v` in `G.deleteIncoming X`. -/
theorem mem_parentsFinset_deleteIncoming {X : Finset V} {v : V} (hv : v ∉ X)
    (p : G.parentsFinset v) : p.1 ∈ (G.deleteIncoming ↑X).parentsFinset v :=
  Digraph.mem_parentsFinset.2 ⟨Digraph.mem_parentsFinset.1 p.2, hv⟩

/-- The submodel of the intervention `do(X := x)`: the structural equation of every `v ∈ X` is
replaced by the constant `x v`; the other equations and all noise laws are unchanged. It is a
model on the graph `G.deleteIncoming X`, in which the vertices of `X` have no parents. -/
def intervene (X : Finset V) (x : ∀ v, α v) : SCM (G.deleteIncoming ↑X) α ε where
  acyclic := M.acyclic.deleteIncoming
  f v z e := if hv : v ∈ X then x v else
    M.f v (fun p => z ⟨p.1, mem_parentsFinset_deleteIncoming hv p⟩) e
  noise := M.noise

/-! ### General interventions: replacing mechanisms -/

/-- A general (soft or conditional) intervention on `X`: the structural function of every
`v ∈ X` is replaced by `g v`, a function of the same parents and of a noise of the same type,
whose law becomes `q v`; the other mechanisms are unchanged. The model stays on `G`. The
atomic intervention `intervene` is the special case of constant functions, on the smaller
graph `G.deleteIncoming X`. -/
def replace (X : Finset V) (g : ∀ v, (∀ u : G.parentsFinset v, α u) → ε v → α v)
    (q : ∀ v, FiniteDist (ε v)) : SCM G α ε where
  acyclic := M.acyclic
  f v := if v ∈ X then g v else M.f v
  noise v := if v ∈ X then q v else M.noise v

variable (X : Finset V) (x : ∀ v, α v)

@[simp] theorem noise_intervene : (M.intervene X x).noise = M.noise := rfl

@[simp] theorem noiseDist_intervene : (M.intervene X x).noiseDist = M.noiseDist := rfl

theorem intervene_f_of_mem {v : V} (hv : v ∈ X) (z) (e : ε v) :
    (M.intervene X x).f v z e = x v := by simp [intervene, hv]

theorem intervene_f_restrict_of_notMem {v : V} (hv : v ∉ X) (y : ∀ v, α v) (e : ε v) :
    (M.intervene X x).f v (((G.deleteIncoming ↑X).parentsFinset v).restrict y) e =
      M.f v ((G.parentsFinset v).restrict y) e := by
  simp only [intervene, hv, dite_false]
  rfl

variable {X x}

/-- The equations of the submodel of `do(X := x)`: `y` agrees with `x` on `X` and satisfies the
original structural equations outside `X`. -/
theorem isSolution_intervene_iff {u : ∀ v, ε v} {y : ∀ v, α v} :
    (M.intervene X x).IsSolution u y ↔
      (∀ v ∈ X, y v = x v) ∧ ∀ v ∉ X, y v = M.f v ((G.parentsFinset v).restrict y) (u v) := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [h v, intervene_f_of_mem M X x hv]
    · rw [h v, intervene_f_restrict_of_notMem M X x hv]
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ X
    · rw [intervene_f_of_mem M X x hv, h1 v hv]
    · rw [intervene_f_restrict_of_notMem M X x hv, ← h2 v hv]

/-- **Effectiveness**: under `do(X := x)` every vertex of `X` takes its assigned value. -/
theorem solve_intervene_of_mem (u : ∀ v, ε v) {v : V} (hv : v ∈ X) :
    (M.intervene X x).solve u v = x v :=
  ((M.isSolution_intervene_iff.1 ((M.intervene X x).isSolution_solve u)).1 v hv)

/-- Under `do(X := x)` a vertex outside `X` follows its original structural equation. -/
theorem solve_intervene_of_notMem (u : ∀ v, ε v) {v : V} (hv : v ∉ X) :
    (M.intervene X x).solve u v =
      M.f v ((G.parentsFinset v).restrict ((M.intervene X x).solve u)) (u v) :=
  ((M.isSolution_intervene_iff.1 ((M.intervene X x).isSolution_solve u)).2 v hv)

/-- **Intervening on nothing changes nothing**, at the level of the solutions. -/
theorem solve_intervene_empty (x : ∀ v, α v) : (M.intervene ∅ x).solve = M.solve := by
  funext u
  refine ((M.intervene ∅ x).eq_solve_of_isSolution ?_).symm
  exact M.isSolution_intervene_iff.2
    ⟨fun v hv => absurd hv (notMem_empty v), fun v _ => M.solve_eq u v⟩

/-- **Composition of interventions**: performing `do(X := x)` and then `do(W := w)` gives the
same solution as the single intervention on `X ∪ W` with the values of `w` on `W` and those of
`x` elsewhere. -/
theorem solve_intervene_intervene (X W : Finset V) (x w : ∀ v, α v) :
    ((M.intervene X x).intervene W w).solve =
      (M.intervene (X ∪ W) fun v => if v ∈ W then w v else x v).solve := by
  funext u
  have hy := M.isSolution_intervene_iff.1
    ((M.intervene (X ∪ W) fun v => if v ∈ W then w v else x v).isSolution_solve u)
  refine (((M.intervene X x).intervene W w).eq_solve_of_isSolution ?_).symm
  refine (M.intervene X x).isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hvW => ?_⟩
  · exact (hy.1 v (mem_union_right X hv)).trans (by simp [hv])
  · by_cases hvX : v ∈ X
    · rw [intervene_f_of_mem M X x hvX]
      exact (hy.1 v (mem_union_left W hvX)).trans (by simp [hvW])
    · rw [intervene_f_restrict_of_notMem M X x hvX]
      exact hy.2 v (by simp [hvX, hvW])

/-- **Only descendants respond**: under `do(X := x)` a vertex that is not a descendant of `X`
(in particular not in `X`) keeps the value it has without intervention, at every noise
value. -/
theorem solve_intervene_of_notMem_descendantsOf (u : ∀ v, ε v) {v : V}
    (hv : v ∉ G.descendantsOf ↑X) : (M.intervene X x).solve u v = M.solve u v := by
  induction v using M.acyclic.wellFounded_adj.induction with
  | _ v ih =>
    have hvX : v ∉ X := fun h => hv (Digraph.subset_descendantsOf _ (mem_coe.2 h))
    rw [M.solve_intervene_of_notMem u hvX, M.solve_eq u v]
    congr 1
    funext p
    have hp := Digraph.mem_parentsFinset.1 p.2
    exact ih p.1 hp fun h => hv (Digraph.mem_descendantsOf_of_adj hp h)

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- **Intervening on nothing changes nothing**: `do(∅)` induces the observational
distribution. -/
theorem dist_intervene_empty (x : ∀ v, α v) : (M.intervene ∅ x).dist = M.dist := by
  rw [dist, solve_intervene_empty]
  rfl

/-- **Composition of interventions**, for the induced distributions. -/
theorem dist_intervene_intervene (X W : Finset V) (x w : ∀ v, α v) :
    ((M.intervene X x).intervene W w).dist =
      (M.intervene (X ∪ W) fun v => if v ∈ W then w v else x v).dist := by
  rw [dist, solve_intervene_intervene]
  rfl

/-- An intervention on `X` does not change the marginal law of any set `S` of vertices that are
not descendants of `X`. -/
theorem margAt_intervene_of_notMem_descendantsOf {S : Finset V}
    (hS : ∀ v ∈ S, v ∉ G.descendantsOf ↑X) (y : ∀ v, α v) :
    (M.intervene X x).dist.margAt S y = M.dist.margAt S y := by
  rw [margAt_dist, margAt_dist, noiseDist_intervene]
  refine FiniteDist.probOf_congr _ fun u => forall₂_congr fun v hv => ?_
  rw [M.solve_intervene_of_notMem_descendantsOf u (hS v hv)]

/-- The factor of a vertex of `X` in the submodel of `do(X := x)` is the indicator that the
configuration gives it the value `x v`. -/
theorem factor_intervene_of_mem {v : V} (hv : v ∈ X) (y : ∀ v, α v) :
    (M.intervene X x).kernels.factor v y = if y v = x v then 1 else 0 := by
  rw [kernels_factor]
  simp_rw [intervene_f_of_mem M X x hv]
  split_ifs with h
  · rw [FiniteDist.probOf_congr _ fun e => iff_true_intro h.symm]
    simp [FiniteDist.probOf]
  · exact FiniteDist.probOf_eq_zero _ fun _ h' => h h'.symm

/-- The factor of a vertex outside `X` in the submodel of `do(X := x)` is its original
factor. -/
theorem factor_intervene_of_notMem {v : V} (hv : v ∉ X) (y : ∀ v, α v) :
    (M.intervene X x).kernels.factor v y = M.kernels.factor v y := by
  rw [kernels_factor, kernels_factor]
  simp_rw [intervene_f_restrict_of_notMem M X x hv]
  rfl

/-- The kernel of a vertex outside `X` in the submodel of `do(X := x)`, evaluated at the
parent values of a configuration, is its original kernel there. -/
theorem kernel_intervene_of_notMem {v : V} (hv : v ∉ X) (y : ∀ v, α v) (a : α v) :
    (M.intervene X x).kernel v (((G.deleteIncoming ↑X).parentsFinset v).restrict y) a =
      M.kernel v ((G.parentsFinset v).restrict y) a := by
  rw [kernel_apply, kernel_apply]
  simp_rw [intervene_f_restrict_of_notMem M X x hv]
  rfl

/-- **Truncated factorization** (Pearl 2009, equations (1.37), (3.10), (3.14); the g-formula;
the manipulation theorem of Spirtes et al. 1993). The distribution induced by
`do(X := x)` gives a configuration `y` that agrees with `x` on `X` the product of the kernels of
the vertices outside `X`, and every other configuration mass `0`. -/
theorem dist_intervene (y : ∀ v, α v) :
    (M.intervene X x).dist y =
      if ∀ v ∈ X, y v = x v then ∏ v ∈ Xᶜ, M.kernels.factor v y else 0 := by
  rw [dist_eq_prod, ← prod_mul_prod_compl X]
  rw [prod_congr rfl fun v hv => M.factor_intervene_of_mem hv y,
    prod_congr rfl fun v hv => M.factor_intervene_of_notMem (mem_compl.1 hv) y]
  split_ifs with h
  · rw [prod_eq_one fun v hv => by simp [h v hv], one_mul]
  · push Not at h
    obtain ⟨v, hv, hne⟩ := h
    rw [prod_eq_zero hv (by simp [hne]), zero_mul]

/-- The interventional distribution factorizes according to the mutilated graph
`G.deleteIncoming X` (condition (i) of Pearl 2009, Definition 1.3.1). -/
theorem factorizes_intervene : (G.deleteIncoming ↑X).Factorizes (M.intervene X x).dist :=
  (M.intervene X x).factorizes

/-- The interventional distribution gives probability one to the event that the vertices of
`X` take their assigned values (condition (ii) of Pearl 2009, Definition 1.3.1). -/
theorem probOf_intervene_agree :
    (M.intervene X x).dist.probOf (fun y => ∀ v ∈ X, y v = x v) = 1 := by
  rw [probOf_dist, noiseDist_intervene]
  rw [FiniteDist.probOf_congr _ fun u => iff_true_intro fun v hv =>
    M.solve_intervene_of_mem u hv]
  simp [FiniteDist.probOf]

/-- Under an intervention that fixes all parents of `v` but not `v` itself, the law of `v` is
its kernel at the fixed parent values. -/
theorem probOf_intervene_of_parents_subset {v : V} (hpa : G.parentsFinset v ⊆ X) (hv : v ∉ X)
    (a : α v) :
    (M.intervene X x).dist.probOf (fun y => y v = a) =
      M.kernel v ((G.parentsFinset v).restrict x) a := by
  rw [probOf_dist, noiseDist_intervene]
  have h : ∀ u, (M.intervene X x).solve u v = M.f v ((G.parentsFinset v).restrict x) (u v) :=
    fun u => by
      rw [M.solve_intervene_of_notMem u hv]
      congr 1
      funext p
      exact M.solve_intervene_of_mem u (hpa p.2)
  simp_rw [h]
  exact FiniteDist.probOf_pi_eval M.noise v
    (fun e => M.f v ((G.parentsFinset v).restrict x) e = a)

/-- **Property 1** of causal Bayesian networks (Pearl 2009, equation (1.38)), in product form:
`P(x_v, x_pa) = P_{do(pa := x_pa)}(x_v) * P(x_pa)`. The conditional law of `v` given its parents
is the law of `v` when its parents are set by intervention. -/
theorem margAt_insert_parents_eq_probOf_intervene_mul (v : V) (y : ∀ v, α v) :
    M.dist.margAt (insert v (G.parentsFinset v)) y =
      (M.intervene (G.parentsFinset v) y).dist.probOf (fun z => z v = y v) *
        M.dist.margAt (G.parentsFinset v) y := by
  rw [M.margAt_insert_parents, M.probOf_intervene_of_parents_subset subset_rfl
    fun h => M.acyclic.irrefl v (Digraph.mem_parentsFinset.1 h)]

/-- **Property 1** of causal Bayesian networks (Pearl 2009, equation (1.38)), in ratio form:
when the parent values `y_pa` have positive probability,
`P(y_v | y_pa) = P_{do(pa := y_pa)}(y_v)`. -/
theorem div_margAt_parents_eq_probOf_intervene (v : V) (y : ∀ v, α v)
    (hpos : 0 < M.dist.margAt (G.parentsFinset v) y) :
    M.dist.margAt (insert v (G.parentsFinset v)) y / M.dist.margAt (G.parentsFinset v) y =
      (M.intervene (G.parentsFinset v) y).dist.probOf (fun z => z v = y v) := by
  rw [M.margAt_insert_parents_eq_probOf_intervene_mul, mul_div_assoc, div_self hpos.ne',
    mul_one]

/-- **Property 2** of causal Bayesian networks (Pearl 2009, equation (1.39)): once the parents
of `v` are set by intervention, a further intervention on a set `S` of vertices not containing
`v` does not change the law of `v`. (If `S` meets the parents of `v`, the values of `x` win
there, as in Pearl's statement for `S` disjoint from the parents.) -/
theorem probOf_intervene_union_eq {v : V} {S : Finset V} (hvS : v ∉ S) (a : α v) :
    (M.intervene (G.parentsFinset v ∪ S) x).dist.probOf (fun y => y v = a) =
      (M.intervene (G.parentsFinset v) x).dist.probOf (fun y => y v = a) := by
  have hvpa : v ∉ G.parentsFinset v := fun h => M.acyclic.irrefl v (Digraph.mem_parentsFinset.1 h)
  rw [M.probOf_intervene_of_parents_subset subset_union_left
      (by simp [hvpa, hvS]),
    M.probOf_intervene_of_parents_subset subset_rfl hvpa]

/-- **Invariance of the conditional law given the parents** (condition (iii) of Pearl 2009,
Definition 1.3.1), product form with the original kernel: for `v ∉ X`,
`P_{do(X := x)}(y_v, y_pa) = kernel v y_pa y_v * P_{do(X := x)}(y_pa)`. -/
theorem margAt_insert_parents_intervene {v : V} (hv : v ∉ X) (y : ∀ v, α v) :
    (M.intervene X x).dist.margAt (insert v (G.parentsFinset v)) y =
      M.kernel v ((G.parentsFinset v).restrict y) (y v) *
        (M.intervene X x).dist.margAt (G.parentsFinset v) y := by
  have key := (M.intervene X x).margAt_insert_parents v y
  rw [M.kernel_intervene_of_notMem hv] at key
  have hpa : (G.deleteIncoming ↑X).parentsFinset v = G.parentsFinset v := by
    ext u
    simp [hv]
  rwa [hpa] at key

/-- **Invariance of the conditional law given the parents** (condition (iii) of Pearl 2009,
Definition 1.3.1), division-free form of `P_{do(X := x)}(y_v | y_pa) = P(y_v | y_pa)` for
`v ∉ X`:
`P_{do(X := x)}(y_v, y_pa) * P(y_pa) = P(y_v, y_pa) * P_{do(X := x)}(y_pa)`. -/
theorem margAt_insert_parents_intervene_mul_comm {v : V} (hv : v ∉ X) (y : ∀ v, α v) :
    (M.intervene X x).dist.margAt (insert v (G.parentsFinset v)) y *
        M.dist.margAt (G.parentsFinset v) y =
      M.dist.margAt (insert v (G.parentsFinset v)) y *
        (M.intervene X x).dist.margAt (G.parentsFinset v) y := by
  rw [M.margAt_insert_parents_intervene hv, M.margAt_insert_parents]
  ring

/-- **Mechanism replacement** (Pearl 2009, section 3.2.3), product form: the
distribution after replacing the mechanisms of `X` is the product of the new kernels
`(q v).map (g v pa)` of the vertices of `X` and of the original kernels of the other vertices. -/
theorem dist_replace (X : Finset V) (g : ∀ v, (∀ u : G.parentsFinset v, α u) → ε v → α v)
    (q : ∀ v, FiniteDist (ε v)) (y : ∀ v, α v) :
    (M.replace X g q).dist y =
      (∏ v ∈ X, (q v).map (g v ((G.parentsFinset v).restrict y)) (y v)) *
        ∏ v ∈ Xᶜ, M.kernels.factor v y := by
  rw [dist_eq_prod, ← prod_mul_prod_compl X]
  congr 1
  · refine prod_congr rfl fun v hv => ?_
    change ((if v ∈ X then q v else M.noise v).map
      ((if v ∈ X then g v else M.f v) ((G.parentsFinset v).restrict y))) (y v) = _
    simp only [hv, ite_true]
  · refine prod_congr rfl fun v hv => ?_
    change ((if v ∈ X then q v else M.noise v).map
      ((if v ∈ X then g v else M.f v) ((G.parentsFinset v).restrict y))) (y v) = _
    simp only [mem_compl.1 hv, ite_false]
    rfl

end SCM

end CausalInference
