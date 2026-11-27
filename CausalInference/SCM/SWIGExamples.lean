/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.SWIG

/-!
# Single world intervention graphs: examples

## Sequential exchangeability for two time points

`SWIGExamples.longitudinal` is a graph with a baseline covariate `L0`, treatments `A0` and
`A1`, a time-varying confounder `L1` affected by `A0`, an unmeasured common cause `U1` of `L1`
and the outcome `Y`, in the spirit of What If, section 19.5 and Figure 19.5 (with a baseline
covariate added). The back-door criterion for the joint treatment `{A0, A1}` fails for the
measured sets `{L0}` and `{L0, L1}` (`L1` is a descendant of `A0`). The SWIG of `do(A0, A1)`
nevertheless shows the two statements of static sequential exchangeability (What If, section
19.5): `Y_{a0,a1} ⫫ A0 | L0` (`SCM.SWIGExamples.seqExch_first`) and
`Y_{a0,a1} ⫫ A1 | A0 = a0, L0, L1` (`SCM.SWIGExamples.seqExch_second`), the second one in the
stratum `A0 = a0` only, where by consistency the world values `A1_{a0}` and `L1_{a0}` are the
factual `A1` and `L1`. Without the convention that the fixed nodes are conditioned on, the
path `A1_{a0} ← a0 → L1_{a0} ← U1 → Y` would be open (`SWIGExamples.longitudinal_open_path`),
as What If discusses after Figure 19.7.

The statements for dynamic strategies (What If, Technical Point 19.3) are not treated here.

## A failure of conditional exchangeability

On the M-bias graph of What If, Figure 7.4 (`BackDoorExamples.mBias`), the SWIG d-connects
`A` and `Y_a` given `L` through `Y_a ← U1 → L ← U2 → A`. The model
`SCM.SWIGExamples.MBiasModel.model` realizes the d-connection: there `Y_a ⫫ A | L` fails
(`SCM.SWIGExamples.MBiasModel.not_condIndepFun`), while `Y_a ⫫ A` holds in every model on the
graph (`SCM.SWIGExamples.mBias_condIndepFun_empty`).
-/

@[expose] public section

namespace CausalInference

open Finset Criteria

namespace SWIGExamples

/-! ### The longitudinal graph -/

/-- A graph with two treatment times: `L0 = 0` (baseline covariate), `A0 = 1`, `U1 = 2`
(unmeasured), `L1 = 3` (time-varying confounder), `A1 = 4` and `Y = 5`. The edges are
`L0 → A0`, `L0 → L1`, `L0 → A1`, `L0 → Y`, `A0 → L1`, `A0 → A1`, `A0 → Y`, `U1 → L1`,
`U1 → Y`, `L1 → A1` and `A1 → Y`. -/
abbrev longitudinal : Digraph (Fin 6) :=
  ofEdges [(0, 1), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4), (4, 5)]

theorem longitudinal_isAcyclic : longitudinal.IsAcyclic := by decide +kernel

/-- `Y_{a0,a1}` and the random half of `A0` are d-separated by `L0` in the SWIG of
`do(A0, A1)`. -/
theorem longitudinal_swigSep_first : longitudinal.SWIGSep {1, 4} {1} {5} {0} := by
  decide +kernel

/-- `Y_{a0,a1}` and the random half `A1_{a0}` are d-separated by `A0`, `L0` and `L1_{a0}` in
the SWIG of `do(A0, A1)`. -/
theorem longitudinal_swigSep_second : longitudinal.SWIGSep {1, 4} {4} {5} {0, 1, 3} := by
  decide +kernel

/-- Without conditioning on the fixed nodes, the path `A1_{a0} ← a0 → L1_{a0} ← U1 → Y` of the
SWIG is open given `A0`, `L0` and `L1_{a0}`: the fixed node `a0` passes the trail as a fork. -/
theorem longitudinal_open_path :
    ¬ (longitudinal.swigGraph {1, 4}).DSep
      ↑(({4} : Finset (Fin 6)).image (Sum.inl : Fin 6 → Fin 6 ⊕ ({1, 4} : Finset (Fin 6))))
      ↑(({5} : Finset (Fin 6)).image (Sum.inl : Fin 6 → Fin 6 ⊕ ({1, 4} : Finset (Fin 6))))
      ↑(({0, 1, 3} : Finset (Fin 6)).image
        (Sum.inl : Fin 6 → Fin 6 ⊕ ({1, 4} : Finset (Fin 6)))) := by
  decide +kernel

/-- The back-door criterion for the joint treatment `{A0, A1}` fails for the baseline
covariate `L0` alone, because of the path `A1 ← L1 ← U1 → Y`, and for `{L0, L1}`, because `L1`
is a descendant of `A0`. -/
theorem longitudinal_not_backDoor :
    ¬ longitudinal.BackDoor {1, 4} {5} {0} ∧ ¬ longitudinal.BackDoor {1, 4} {5} {0, 3} := by
  constructor <;> decide +kernel

end SWIGExamples

namespace SCM.SWIGExamples

open CausalInference.SWIGExamples

/-! ### Sequential exchangeability in every model on the longitudinal graph -/

section Longitudinal

variable {α ε : Fin 6 → Type*} [∀ v, Fintype (ε v)] [∀ v, Finite (α v)]
  [∀ v, DecidableEq (α v)] (M : SCM longitudinal α ε) (a : ∀ v, α v)

omit [∀ v, Finite (α v)] [∀ v, DecidableEq (α v)] in
/-- The random half of `A0`, the baseline covariate `L0`, and, on the event `A0 = a0`, the
random half `A1_{a0}` and the covariate `L1_{a0}` carry their factual values (consistency). -/
theorem world_longitudinal (u : ∀ v, ε v) :
    M.world {1, 4} a u 0 = M.solve u 0 ∧ M.world {1, 4} a u 1 = M.solve u 1 ∧
      (M.solve u 1 = a 1 → M.world {1, 4} a u 3 = M.solve u 3 ∧
        M.world {1, 4} a u 4 = M.solve u 4) := by
  refine ⟨M.world_of_notMem_descendantsOf a u (by decide +kernel),
    M.world_of_notMem_descendantsOf a u (by decide +kernel), fun h1 => ⟨?_, ?_⟩⟩
  · have h : (M.intervene {1} a).solve u = M.solve u :=
      M.solve_intervene_of_agree fun v hv => by rw [mem_singleton.1 hv, h1]
    rw [M.world_of_notMem a u (by decide), ← M.solve_intervene_erase_of_not_reflTransGen a u
      (w := 4) (by decide +kernel), show ({1, 4} : Finset (Fin 6)).erase 4 = {1} by decide, h]
  · have h : (M.intervene {1} a).solve u = M.solve u :=
      M.solve_intervene_of_agree fun v hv => by rw [mem_singleton.1 hv, h1]
    rw [world_apply, show ({1, 4} : Finset (Fin 6)).erase 4 = {1} by decide, h]

/-- **Sequential exchangeability, first time point** (What If, section 19.5): in every model on
the longitudinal graph, `Y_{a0,a1} ⫫ A0 | L0` under the noise law, with `A0` and `L0`
factual. Read off the SWIG of `do(A0, A1)`. -/
theorem seqExch_first :
    M.noiseDist.CondIndepFun (fun u => M.solve u 1) (fun u => (M.intervene {1, 4} a).solve u 5)
      (fun u => ({0} : Finset (Fin 6)).restrict (M.solve u)) := by
  have hw := M.condIndepFun_world_of_swigSep {1, 4} a longitudinal_swigSep_first
  have eC : (fun u => ({0} : Finset (Fin 6)).restrict (M.world {1, 4} a u)) =
      fun u => ({0} : Finset (Fin 6)).restrict (M.solve u) := by
    funext u v
    obtain ⟨v, hv⟩ := v
    rw [mem_singleton] at hv
    subst hv
    exact (world_longitudinal M a u).1
  rw [eC] at hw
  exact (hw.of_left (fun s => s ⟨1, by decide⟩) fun u =>
    (world_longitudinal M a u).2.1.symm).of_right (fun s => s ⟨5, by decide⟩) fun u =>
      (M.world_of_notMem a u (by decide)).symm

/-- **Sequential exchangeability, second time point** (What If, section 19.5):
`Y_{a0,a1} ⫫ A1 | A0 = a0, L0, L1` in every model on the longitudinal graph. The statement is
the product form of conditional independence in each stratum where the factual `A0` equals
`a0`, with all values read off a configuration `c` (`c 1 = a0`): `A1`, `L0`, `L1` and `A0`
factual. It is read off the SWIG statement `Y_{a0,a1} ⫫ A1_{a0} | A0, L0, L1_{a0}`, using
consistency (`A1_{a0} = A1` and `L1_{a0} = L1` where `A0 = a0`). In the strata `A0 ≠ a0` the
SWIG says nothing about the factual `A1`. -/
theorem seqExch_second (c : ∀ v, α v) (hc : c 1 = a 1) :
    M.noiseDist.probOf (fun u => M.solve u 4 = c 4 ∧ (M.intervene {1, 4} a).solve u 5 = c 5 ∧
        ∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.solve u v = c v) *
      M.noiseDist.probOf (fun u => ∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.solve u v = c v) =
    M.noiseDist.probOf (fun u => M.solve u 4 = c 4 ∧
        ∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.solve u v = c v) *
      M.noiseDist.probOf (fun u => (M.intervene {1, 4} a).solve u 5 = c 5 ∧
        ∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.solve u v = c v) := by
  have hw := M.condIndepFun_world_of_swigSep {1, 4} a longitudinal_swigSep_second
    (({4} : Finset (Fin 6)).restrict c) (({5} : Finset (Fin 6)).restrict c)
    (({0, 1, 3} : Finset (Fin 6)).restrict c)
  simp only [FiniteDist.restrict_eq_restrict_iff, mem_singleton, forall_eq] at hw
  have h5 : ∀ u, M.world {1, 4} a u 5 = (M.intervene {1, 4} a).solve u 5 := fun u =>
    M.world_of_notMem a u (by decide)
  have hs1 : ∀ u, ((∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.world {1, 4} a u v = c v) ∨
      ∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.solve u v = c v) → M.solve u 1 = a 1 := by
    rintro u (h | h)
    · rw [← (world_longitudinal M a u).2.1, h 1 (by decide), hc]
    · rw [h 1 (by decide), hc]
  have hcond : ∀ u, (∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.world {1, 4} a u v = c v) ↔
      ∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.solve u v = c v := by
    intro u
    have hw' : ∀ (h : M.solve u 1 = a 1), ∀ v ∈ ({0, 1, 3} : Finset (Fin 6)),
        M.world {1, 4} a u v = M.solve u v := by
      intro h v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact (world_longitudinal M a u).1
      · exact (world_longitudinal M a u).2.1
      · exact ((world_longitudinal M a u).2.2 h).1
    constructor
    · intro h v hv
      rw [← hw' (hs1 u (Or.inl h)) v hv]
      exact h v hv
    · intro h v hv
      rw [hw' (hs1 u (Or.inr h)) v hv]
      exact h v hv
  have h4 : ∀ u, (∀ v ∈ ({0, 1, 3} : Finset (Fin 6)), M.solve u v = c v) →
      M.world {1, 4} a u 4 = M.solve u 4 := fun u h =>
    ((world_longitudinal M a u).2.2 (hs1 u (Or.inr h))).2
  simp only [h5, hcond] at hw
  convert hw using 3
  all_goals
    funext u
    apply propext
    have key := h4 u
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩ <;>
      first
      | rw [key (by first | exact h2.2 | exact h2)]; exact h1
      | rw [← key (by first | exact h2.2 | exact h2)]; exact h1

end Longitudinal

/-! ### Conditional exchangeability on the M-bias graph -/

section MBias

open CausalInference.BackDoorExamples

/-- On the M-bias graph (What If, Figure 7.4; `A = 0`, `Y = 1`, `L = 2`, `U1 = 3`, `U2 = 4`),
the SWIG of `do(A)` separates the random half of `A` from `Y_a` without conditioning, and
d-connects them given `L`, through `Y_a ← U1 → L ← U2 → A`. -/
theorem mBias_swigSep : mBias.SWIGSep {0} {0} {1} ∅ ∧ ¬ mBias.SWIGSep {0} {0} {1} {2} := by
  constructor <;> decide +kernel

/-- **Marginal exchangeability on the M-bias graph** (What If, section 7.5): in every model on
the graph, `Y_a ⫫ A` under the noise law, read off the SWIG. -/
theorem mBias_condIndepFun_empty {α ε : Fin 5 → Type*} [∀ v, Fintype (ε v)]
    [∀ v, Finite (α v)] [∀ v, DecidableEq (α v)] (M : SCM mBias α ε) (a : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u 0)
      (fun u => ({1} : Finset (Fin 5)).restrict ((M.intervene {0} a).solve u))
      (fun u => (∅ : Finset (Fin 5)).restrict (M.solve u)) :=
  M.condIndepFun_of_swigSep_singleton (fun _ h => absurd h (notMem_empty _))
    mBias_swigSep.1 a

namespace MBiasModel

theorem mem_parentsFinset {p v : Fin 5} (h : mBias.Adj p v) : p ∈ mBias.parentsFinset v :=
  Digraph.mem_parentsFinset.2 h

/-- A model on the M-bias graph with fair noise bits: `U1` and `U2` copy their noise,
`L := U1 xor U2`, `A := U2`, and `Y := U1`, so that the treatment has no effect. -/
noncomputable def model : SCM mBias (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide +kernel
  f v z e :=
    if h0 : v = 0 then z ⟨4, mem_parentsFinset (by subst h0; decide)⟩
    else if h1 : v = 1 then z ⟨3, mem_parentsFinset (by subst h1; decide)⟩
    else if h2 : v = 2 then xor (z ⟨3, mem_parentsFinset (by subst h2; decide)⟩)
      (z ⟨4, mem_parentsFinset (by subst h2; decide)⟩)
    else e
  noise _ := FiniteDist.uniform

theorem model_solve (u : Fin 5 → Bool) :
    model.solve u = ![u 4, u 3, xor (u 3) (u 4), u 3, u 4] := by
  refine (model.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [model, Finset.restrict]

/-- The treatment value `A = false`, as a configuration. -/
def aFalse : Fin 5 → Bool := fun _ => false

theorem model_solve_intervene (u : Fin 5 → Bool) :
    (model.intervene {0} aFalse).solve u = ![false, u 3, xor (u 3) (u 4), u 3, u 4] := by
  refine ((model.intervene {0} aFalse).eq_solve_of_isSolution ?_).symm
  refine model.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [model, Finset.restrict]

/-- Probabilities of events depending on the noise bits of `U1` and `U2`. -/
theorem probOf_noise_pair (P : Bool × Bool → Prop) [DecidablePred P] :
    model.noiseDist.probOf (fun u => P (u 3, u 4)) =
      (if P (false, false) then 1 / 4 else 0) + (if P (false, true) then 1 / 4 else 0) +
        (if P (true, false) then 1 / 4 else 0) + (if P (true, true) then 1 / 4 else 0) := by
  rw [← FiniteDist.probOf_map model.noiseDist (fun u => (u 3, u 4)) P]
  change ((FiniteDist.pi fun _ => FiniteDist.uniform).map
    fun u : Fin 5 → Bool => (u 3, u 4)).probOf P = _
  rw [FiniteDist.map_pi_eval_pair _ (by decide)]
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, FiniteDist.prod_apply, FiniteDist.uniform_apply, Fintype.card_bool]
  split_ifs <;> norm_num

/-- **Conditional exchangeability fails on the M-bias graph**: in `model`, the potential outcome
`Y_{A = false}` is not conditionally independent of the factual `A` given the factual `L`. The
SWIG path `Y_a ← U1 → L ← U2 → A`, opened by conditioning on the collider `L`, is realized as a
dependence: at `A = Y_a = L = false` the product form reads `1/4 * 1/2 = 1/8` on the left and
`1/4 * 1/4 = 1/16` on the right. -/
theorem not_condIndepFun :
    ¬ model.noiseDist.CondIndepFun (fun u => model.solve u 0)
      (fun u => (model.intervene {0} aFalse).solve u 1) (fun u => model.solve u 2) := by
  intro h
  have key := h false false false
  simp only [model_solve, model_solve_intervene, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at key
  rw [probOf_noise_pair (fun q => q.2 = false ∧ q.1 = false ∧ xor q.1 q.2 = false),
    probOf_noise_pair (fun q => xor q.1 q.2 = false),
    probOf_noise_pair (fun q => q.2 = false ∧ xor q.1 q.2 = false),
    probOf_noise_pair (fun q => q.1 = false ∧ xor q.1 q.2 = false)] at key
  norm_num at key

end MBiasModel

end MBias

end SCM.SWIGExamples

end CausalInference
