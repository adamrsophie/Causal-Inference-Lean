/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.DoCalculusExamples
public import CausalInference.Graphical.Criteria.SequentialBackDoor

/-!
# The identification of plans

The effect of a plan `do(x_1), …, do(x_n)` on an outcome `Y` in a finite structural causal model,
identified by the sequential back-door criterion (`Digraph.Admissible`).

## Main definitions

* `Plan.ctrlBefore x k`, `Plan.ctrlFrom x k`: the controls `x j` with `j < k`, and with `j ≥ k`.
* `Plan.covBefore Zs k`: the covariates of the sets `Zs j` with `j < k`.

## Main results

* `SCM.effect_plan_eq_gFormula` (**Theorem 4.4.1** of Pearl 2009, equation (4.6), the
  sequential back-door criterion of Pearl and Robins 1995): if the covariate sets `Zs` form an
  admissible sequence for the controls `x` and the outcome `y`, then
  `P(y | do(x_1), …, do(x_n)) = ∑_z P(y | z, x) ∏_k P(z_k | z_1, …, z_{k-1}, x_1, …, x_{k-1})`,
  for any number `n` of controls, under positivity. The covariate sets may overlap.
  `SCM.effect_plan_eq_gFormula_of_admissiblePlan` takes Pearl's admissible sequences
  (`Digraph.AdmissiblePlan`), and `SCM.effect_plan_eq_gFormula_of_wSet` the sets `W_k` of
  Theorem 4.4.6 (`Digraph.wSet`).
* `SCM.planStage_mul`: the division-free step of the proof,
  `P^k(y, H_k) P(H_k, x_k) = P^{k+1}(y, H_k, x_k) P(H_k)`, where `H_k` are the observations
  before control `x_k` and `P^k` is the law under `do(x_k, …, x_n)`.
* `SCM.effect_plan_pearlFig44`: equation (4.7) for Figure 4.4,
  `P(y | do(x_1), do(x_2)) = ∑_z P(y | z, x_1, x_2) P(z | x_1)`.
* `SCM.PlanExamples.fig44Model_plan`: a concrete model on Figure 4.4 with full support on the
  observed `(X₁, Z, X₂)`, in which the plan effect and the g-formula (4.7) are both `1/4` while
  the unadjusted conditional probability is `1/10`.

All values are read off configurations, as in `CausalInference.SCM.DoCalculus`.

Sources: Pearl (2009), *Causality*, 2nd edition, section 4.4, Theorem 4.4.1 and Figure 4.4;
Pearl and Robins (1995), *Probabilistic evaluation of sequential plans from causal models with
hidden variables*.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace FiniteDist

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- Regrouping sums over cylinders: for disjoint `S` and `T`, summing over the configurations
that agree with `v` outside `S`, and then over those that agree with the result outside `T`, is
summing over the configurations that agree with `v` outside `S ∪ T`. -/
theorem sum_agreeOn_compl_agreeOn_compl {M : Type*} [AddCommMonoid M] {S T : Finset V}
    (hST : Disjoint S T) (v : ∀ u, α u) (F : (∀ u, α u) → M) :
    ∑ c ∈ agreeOn Sᶜ v, ∑ d ∈ agreeOn Tᶜ c, F d = ∑ d ∈ agreeOn (S ∪ T)ᶜ v, F d := by
  symm
  rw [← sum_fiberwise_of_maps_to (s := agreeOn (S ∪ T)ᶜ v) (t := agreeOn Sᶜ v)
    (g := fun d u => if u ∈ S then d u else v u) ?_]
  · refine sum_congr rfl fun c hc => sum_congr ?_ fun _ _ => rfl
    simp only [mem_agreeOn, mem_compl] at hc
    ext d
    simp only [mem_filter, mem_agreeOn, mem_compl, mem_union, not_or]
    constructor
    · rintro ⟨hd, hg⟩ u hu
      by_cases huS : u ∈ S
      · rw [← hg]
        simp [huS]
      · rw [hd u ⟨huS, hu⟩, hc u huS]
    · intro hd
      refine ⟨fun u hu => (hd u hu.2).trans (hc u hu.1), funext fun u => ?_⟩
      by_cases huS : u ∈ S
      · simp only [huS, ite_true]
        exact hd u (disjoint_left.1 hST huS)
      · simp only [huS, ite_false]
        exact (hc u huS).symm
  · intro d _
    simp only [mem_agreeOn, mem_compl]
    intro u hu
    simp [hu]

/-- The configurations that agree with `v` on every coordinate: only `v` itself. -/
theorem agreeOn_compl_empty_eq (v : ∀ u, α u) : agreeOn (∅ : Finset V)ᶜ v = {v} := by
  ext c
  simp [funext_iff]

end FiniteDist

namespace Plan

variable {V : Type*} [DecidableEq V] {n : ℕ}

/-- The controls `x j` with `j < k`. -/
def ctrlBefore (x : Fin n → V) (k : ℕ) : Finset V :=
  (univ.filter fun j : Fin n => (j : ℕ) < k).image x

/-- The controls `x j` with `j ≥ k`. -/
def ctrlFrom (x : Fin n → V) (k : ℕ) : Finset V :=
  (univ.filter fun j : Fin n => k ≤ (j : ℕ)).image x

/-- The covariates of the sets `Zs j` with `j < k`. -/
def covBefore (Zs : Fin n → Finset V) (k : ℕ) : Finset V :=
  (univ.filter fun j : Fin n => (j : ℕ) < k).biUnion Zs

variable {x : Fin n → V} {Zs : Fin n → Finset V} {k : ℕ} {u : V}

@[simp] theorem mem_ctrlBefore : u ∈ ctrlBefore x k ↔ ∃ j : Fin n, (j : ℕ) < k ∧ x j = u := by
  simp [ctrlBefore]

@[simp] theorem mem_ctrlFrom : u ∈ ctrlFrom x k ↔ ∃ j : Fin n, k ≤ (j : ℕ) ∧ x j = u := by
  simp [ctrlFrom]

@[simp] theorem mem_covBefore : u ∈ covBefore Zs k ↔ ∃ j : Fin n, (j : ℕ) < k ∧ u ∈ Zs j := by
  simp [covBefore]

theorem ctrlBefore_succ (k : Fin n) : ctrlBefore x (k + 1) = ctrlBefore x k ∪ {x k} := by
  ext u
  simp only [mem_ctrlBefore, mem_union, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr (by rw [Fin.ext hj])
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
    · exact ⟨k, Nat.lt_succ_self _, rfl⟩

theorem covBefore_succ (k : Fin n) : covBefore Zs (k + 1) = covBefore Zs k ∪ Zs k := by
  ext u
  simp only [mem_covBefore, mem_union]
  constructor
  · rintro ⟨j, hj, hu⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact Or.inl ⟨j, hj, hu⟩
    · exact Or.inr (by rwa [Fin.ext hj] at hu)
  · rintro (⟨j, hj, hu⟩ | hu)
    · exact ⟨j, Nat.lt_succ_of_lt hj, hu⟩
    · exact ⟨k, Nat.lt_succ_self _, hu⟩

theorem ctrlFrom_eq_succ (k : Fin n) : ctrlFrom x k = ctrlFrom x (k + 1) ∪ {x k} := by
  ext u
  simp only [mem_ctrlFrom, mem_union, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_or_eq_of_le hj with hj | hj
    · exact Or.inl ⟨j, hj, rfl⟩
    · exact Or.inr (by rw [Fin.ext hj.symm])
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j, Nat.le_of_succ_le hj, rfl⟩
    · exact ⟨k, le_rfl, rfl⟩

@[simp] theorem ctrlBefore_zero : ctrlBefore x 0 = ∅ := by
  ext u
  simp

@[simp] theorem covBefore_zero : covBefore Zs 0 = ∅ := by
  ext u
  simp

theorem ctrlFrom_zero : ctrlFrom x 0 = univ.image x := by
  ext u
  simp

theorem ctrlFrom_self : ctrlFrom x n = ∅ := by
  ext u
  simp only [mem_ctrlFrom, notMem_empty, iff_false, not_exists, not_and]
  exact fun j hj => absurd j.2 (not_lt.2 hj)

theorem ctrlBefore_self : ctrlBefore x n = univ.image x := by
  ext u
  simp

theorem covBefore_self : covBefore Zs n = univ.biUnion Zs := by
  ext u
  simp

theorem coe_ctrlFrom (k : Fin n) : (ctrlFrom x k : Set V) = Digraph.controlsFrom x k := by
  ext u
  simp only [mem_coe, mem_ctrlFrom]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨j, Fin.le_def.2 hj, h⟩, fun ⟨j, hj, h⟩ => ⟨j, Fin.le_def.1 hj, h⟩⟩

theorem coe_ctrlFrom_succ (k : Fin n) :
    (ctrlFrom x (k + 1) : Set V) = Digraph.controlsAfter x k := by
  ext u
  simp only [mem_coe, mem_ctrlFrom]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨j, Fin.lt_def.2 (by omega), h⟩,
    fun ⟨j, hj, h⟩ => ⟨j, by have := Fin.lt_def.1 hj; omega, h⟩⟩

theorem coe_stepCond (k : Fin n) :
    ((Zs k ∪ covBefore Zs k ∪ ctrlBefore x k : Finset V) : Set V) = Digraph.stepCond x Zs k := by
  ext u
  simp only [coe_union, Set.mem_union, mem_coe, mem_covBefore, mem_ctrlBefore,
    Digraph.stepCond, Set.mem_ofPred_eq, Fin.lt_def, Fin.le_def]
  constructor
  · rintro ((hu | ⟨j, hj, hu⟩) | ⟨j, hj, hu⟩)
    · exact Or.inr ⟨k, le_rfl, hu⟩
    · exact Or.inr ⟨j, hj.le, hu⟩
    · exact Or.inl ⟨j, hj, hu⟩
  · rintro (⟨j, hj, hu⟩ | ⟨j, hj, hu⟩)
    · exact Or.inr ⟨j, hj, hu⟩
    · rcases Nat.lt_or_eq_of_le hj with hj | hj
      · exact Or.inl (Or.inr ⟨j, hj, hu⟩)
      · exact Or.inl (Or.inl (by rwa [Fin.ext hj] at hu))

omit [DecidableEq V] in
/-- Under `Digraph.ControlsOrdered`, distinct positions hold distinct controls. -/
theorem ne_of_controlsOrdered {G : Digraph V} (hord : G.ControlsOrdered x) {i j : Fin n}
    (hij : i < j) : x i ≠ x j :=
  fun h => hord i j hij (by rw [h]; exact Digraph.subset_descendantsOf _ (Set.mem_singleton _))

/-- A covariate of `Zs j` with `j ≤ m` is not a descendant of the controls `x i`, `i ≥ m`
(condition (4.4) of an admissible sequence). -/
theorem notMem_descendantsOf_of_mem_Zs {G : Digraph V} {C : Finset V} {y : V}
    (hadm : G.Admissible C x y Zs) {j : Fin n} {m : ℕ} (hj : (j : ℕ) ≤ m) (hu : u ∈ Zs j) :
    u ∉ G.descendantsOf ↑(ctrlFrom x m) := by
  refine fun h => ((hadm j).1 u hu).2 (Digraph.descendantsOf_mono ?_ h)
  intro w hw
  obtain ⟨i, hi, rfl⟩ := mem_ctrlFrom.1 (mem_coe.1 hw)
  exact ⟨i, Fin.le_def.2 (by omega), rfl⟩

/-- Under `Digraph.ControlsOrdered`, a control `x i` with `i < m` is not a descendant of the
controls `x j`, `j ≥ m`. -/
theorem notMem_descendantsOf_ctrl {G : Digraph V} (hord : G.ControlsOrdered x) {i : Fin n}
    {m : ℕ} (hi : (i : ℕ) < m) : x i ∉ G.descendantsOf ↑(ctrlFrom x m) := by
  rintro ⟨s, hs, hsu⟩
  obtain ⟨j, hj, rfl⟩ := mem_ctrlFrom.1 (mem_coe.1 hs)
  exact hord i j (Fin.lt_def.2 (by omega)) ⟨x j, Set.mem_singleton _, hsu⟩

/-- The control `x k` is none of the observations of step `k`. -/
theorem ctrl_notMem_stepCond {G : Digraph V} (hord : G.ControlsOrdered x)
    (hZx : ∀ i j, x j ∉ Zs i) (k : Fin n) :
    x k ∉ Zs k ∪ covBefore Zs k ∪ ctrlBefore x k := by
  simp only [mem_union, mem_covBefore, mem_ctrlBefore, not_or, not_exists, not_and]
  exact ⟨⟨hZx k k, fun j _ => hZx j k⟩,
    fun j hj h => ne_of_controlsOrdered hord (Fin.lt_def.2 hj) h⟩

/-- The covariates of the steps before `k` are disjoint from those of step `k`. -/
theorem disjoint_covBefore (hZdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) (k : Fin n) :
    Disjoint (covBefore Zs k) (Zs k) := by
  rw [disjoint_left]
  intro u hu hu'
  obtain ⟨j, hj, hj'⟩ := mem_covBefore.1 hu
  exact disjoint_left.1 (hZdisj j k fun h => by rw [h] at hj; exact lt_irrefl _ hj) hj' hu'

/-- Removing from each covariate set the covariates of the earlier steps does not change the
cumulative covariate sets. -/
theorem covBefore_sdiff (Zs : Fin n → Finset V) (k : ℕ) :
    covBefore (fun j => Zs j \ covBefore Zs j) k = covBefore Zs k := by
  ext u
  simp only [mem_covBefore, mem_sdiff]
  constructor
  · rintro ⟨j, hj, hu, _⟩
    exact ⟨j, hj, hu⟩
  · rintro ⟨j, hj, hu⟩
    have hne : (univ.filter fun i : Fin n => u ∈ Zs i).Nonempty := ⟨j, by simpa using hu⟩
    set j₀ := (univ.filter fun i : Fin n => u ∈ Zs i).min' hne
    have hj₀ : u ∈ Zs j₀ := by simpa using min'_mem _ hne
    have hle : j₀ ≤ j := min'_le _ _ (by simpa using hu)
    refine ⟨j₀, lt_of_le_of_lt (Fin.le_def.1 hle) hj, hj₀, ?_⟩
    rintro ⟨i, hi, hui⟩
    have := min'_le (univ.filter fun i : Fin n => u ∈ Zs i) i (mem_filter.2 ⟨mem_univ _, hui⟩)
    exact absurd (Fin.le_def.1 this) (by omega)

/-- Removing from each covariate set the covariates of the earlier steps does not change the
union of the covariate sets. -/
theorem biUnion_sdiff_covBefore (Zs : Fin n → Finset V) :
    univ.biUnion (fun j => Zs j \ covBefore Zs j) = univ.biUnion Zs := by
  rw [← covBefore_self, ← covBefore_self, covBefore_sdiff]

/-- The covariate sets with the covariates of the earlier steps removed are pairwise
disjoint. -/
theorem disjoint_sdiff_covBefore (Zs : Fin n → Finset V) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Zs i \ covBefore Zs i) (Zs j \ covBefore Zs j) := by
  have key : ∀ {a b : Fin n}, a < b →
      Disjoint (Zs a \ covBefore Zs a) (Zs b \ covBefore Zs b) := fun {a b} hab =>
    disjoint_left.2 fun u hua hub =>
      (mem_sdiff.1 hub).2 (mem_covBefore.2 ⟨a, Fin.lt_def.1 hab, (mem_sdiff.1 hua).1⟩)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h
  · exact (key h).symm

/-- An admissible sequence stays admissible when the covariates of the earlier steps are removed
from each covariate set: condition (4.4) passes to subsets, and the conditioning set of every
step test (4.5) is unchanged. -/
theorem admissible_sdiff_covBefore {G : Digraph V} {C : Finset V} {y : V}
    (h : G.Admissible C x y Zs) : G.Admissible C x y (fun j => Zs j \ covBefore Zs j) := by
  intro k
  refine ⟨fun v hv => (h k).1 v (mem_sdiff.1 hv).1, ?_⟩
  have hstep := (h k).2
  unfold Digraph.SeqBackDoorStep at hstep ⊢
  rw [← coe_stepCond] at hstep ⊢
  rwa [covBefore_sdiff, sdiff_union_self_eq_union]

end Plan

namespace SCM

open Plan

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

variable {n : ℕ}

/-- The quantity of stage `k` in the proof of Theorem 4.4.1:
`P(y | z_1, …, z_k, x_1, …, x_k, do(x_{k+1}), …, do(x_n))` (with Pearl's indexing from one),
the interventional mass of `y` and the observations before stage `k` under the intervention on
the remaining controls, divided by the observational mass of those observations. -/
noncomputable def planStage (x : Fin n → V) (y : V) (Zs : Fin n → Finset V) (k : ℕ)
    (c : ∀ u, α u) : ℝ :=
  (M.intervene (ctrlFrom x k) c).dist.margAt ({y} ∪ (covBefore Zs k ∪ ctrlBefore x k)) c /
    M.dist.margAt (covBefore Zs k ∪ ctrlBefore x k) c

/-- The product of the first `k` factors of the g-formula (4.6),
`∏_{j < k} P(z_j | z_1, …, z_{j-1}, x_1, …, x_{j-1})`. -/
noncomputable def planWeight (x : Fin n → V) (Zs : Fin n → Finset V) (k : ℕ)
    (c : ∀ u, α u) : ℝ :=
  ∏ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k),
    M.dist.margAt (covBefore Zs (j + 1) ∪ ctrlBefore x j) c /
      M.dist.margAt (covBefore Zs j ∪ ctrlBefore x j) c


section Step

variable {x : Fin n → V} {y : V} {Zs : Fin n → Finset V} {C : Finset V}

/-- The factors of the g-formula accumulate: the weight of stage `k + 1` is the weight of stage
`k` times `P(z_k | z_1, …, z_{k-1}, x_1, …, x_{k-1})`. -/
theorem planWeight_succ (k : Fin n) (c : ∀ u, α u) :
    M.planWeight x Zs (k + 1) c = M.planWeight x Zs k c *
      (M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) c /
        M.dist.margAt (covBefore Zs k ∪ ctrlBefore x k) c) := by
  unfold planWeight
  rw [show univ.filter (fun j : Fin n => (j : ℕ) < k + 1) =
      insert k (univ.filter fun j : Fin n => (j : ℕ) < k) by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega, prod_insert (by simp), mul_comm]

/-- **The division-free step of the proof of Theorem 4.4.1** (Pearl 2009, p. 123). With
`H_k = (z_1, …, z_k, x_1, …, x_{k-1})` (the observations before control `x_k`, Pearl's indexing
from one) and `P^k` the law under `do(x_k, …, x_n)`, the step test (4.5) and the nondescendant
condition (4.4) give `P^k(y, H_k) * P(H_k, x_k) = P^{k+1}(y, H_k, x_k) * P(H_k)`, all values
read off `d`. No positivity and no disjointness of the covariate sets is needed. -/
theorem planStage_mul (hadm : G.Admissible C x y Zs) (hord : G.ControlsOrdered x)
    (hZx : ∀ i j, x j ∉ Zs i) (k : Fin n) (d : ∀ u, α u) :
    (M.intervene (ctrlFrom x k) d).dist.margAt ({y} ∪ (covBefore Zs (k + 1) ∪ ctrlBefore x k)) d *
        M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1)) d =
      (M.intervene (ctrlFrom x (k + 1)) d).dist.margAt
          ({y} ∪ (covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1))) d *
        M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) d := by
  have hxnot := ctrl_notMem_stepCond hord hZx k
  have hstep := (hadm k).2
  unfold Digraph.SeqBackDoorStep Digraph.stepGraph at hstep
  rw [← coe_ctrlFrom_succ, ← coe_stepCond] at hstep
  have hyx : y ≠ x k := by
    rintro rfl
    exact hxnot (hstep.inter_subset ⟨Set.mem_singleton _, Set.mem_singleton _⟩)
  have hND1 : ∀ u ∈ covBefore Zs (k + 1) ∪ ctrlBefore x k,
      u ∉ G.descendantsOf ↑(ctrlFrom x k) := by
    intro u hu
    rcases mem_union.1 hu with hu | hu
    · obtain ⟨j, hj, hu⟩ := mem_covBefore.1 hu
      exact notMem_descendantsOf_of_mem_Zs hadm (by omega) hu
    · obtain ⟨i, hi, rfl⟩ := mem_ctrlBefore.1 hu
      exact notMem_descendantsOf_ctrl hord hi
  have hND2 : ∀ u ∈ covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1),
      u ∉ G.descendantsOf ↑(ctrlFrom x (k + 1)) := by
    intro u hu
    rcases mem_union.1 hu with hu | hu
    · obtain ⟨j, hj, hu⟩ := mem_covBefore.1 hu
      exact notMem_descendantsOf_of_mem_Zs hadm (by omega) hu
    · obtain ⟨i, hi, rfl⟩ := mem_ctrlBefore.1 hu
      exact notMem_descendantsOf_ctrl hord hi
  -- Rule 2 in the submodel of the later controls
  have r := (M.intervene (ctrlFrom x (k + 1)) d).rule2 (X := ∅) (Y := {y}) (Z := {x k})
    (W := Zs k ∪ covBefore Zs k ∪ ctrlBefore x k) d (disjoint_empty_left _)
    (disjoint_singleton.2 hyx) (disjoint_singleton_right.2 hxnot)
    (by rw [coe_empty, Digraph.deleteIncoming_empty, Digraph.deleteIncoming_deleteOutgoing,
          coe_singleton, coe_singleton, empty_union]
        exact hstep)
  have hA : ((M.intervene (ctrlFrom x (k + 1)) d).intervene (∅ ∪ {x k}) d).dist =
      (M.intervene (ctrlFrom x k) d).dist := by
    rw [M.dist_intervene_intervene]
    simp only [ite_self]
    exact M.dist_intervene_of_eq (by rw [empty_union]; exact (ctrlFrom_eq_succ k).symm)
  have e2 : {x k} ∪ (Zs k ∪ covBefore Zs k ∪ ctrlBefore x k) =
      covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1) := by
    rw [covBefore_succ, ctrlBefore_succ]
    ext u
    simp only [mem_union, mem_singleton]
    tauto
  have e3 : {y} ∪ {x k} ∪ (Zs k ∪ covBefore Zs k ∪ ctrlBefore x k) =
      {y} ∪ (covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1)) := by
    rw [union_assoc, e2]
  have e4 : Zs k ∪ covBefore Zs k ∪ ctrlBefore x k = covBefore Zs (k + 1) ∪ ctrlBefore x k := by
    rw [covBefore_succ, union_comm (covBefore Zs k)]
  rw [hA, dist_intervene_empty, e2, e3, e4,
    M.margAt_intervene_of_notMem_descendantsOf hND1 d,
    M.margAt_intervene_of_notMem_descendantsOf hND2 d] at r
  exact r

/-- **One step of the proof of Theorem 4.4.1** (Pearl 2009, p. 123). The quantity of stage `k`
is the sum over `z_k` of the quantity of stage `k + 1` times `P(z_k | z_1, …, x_{k-1})`. Step 1
of Pearl's proof (deleting the later actions from `P(z_k | …)`) holds because the observations
before stage `k + 1` are nondescendants of the remaining controls; Step 2 (exchanging `do(x_k)`
for the observation `x_k`) is Rule 2, licensed by the step test (4.5), applied in the submodel
of the later controls; its division-free form is `SCM.planStage_mul`. -/
theorem planStage_eq_sum (hadm : G.Admissible C x y Zs) (hord : G.ControlsOrdered x)
    (hZdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) (hZx : ∀ i j, x j ∉ Zs i)
    (hZy : ∀ i, y ∉ Zs i) (k : Fin n) (c : ∀ u, α u)
    (hpos : ∀ d ∈ FiniteDist.agreeOn (Zs k)ᶜ c,
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) d →
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1)) d) :
    M.planStage x y Zs k c = ∑ d ∈ FiniteDist.agreeOn (Zs k)ᶜ c,
      M.planStage x y Zs (k + 1) d *
        (M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) d /
          M.dist.margAt (covBefore Zs k ∪ ctrlBefore x k) d) := by
  have hcovk := disjoint_covBefore hZdisj k
  have hctrlk : Disjoint (ctrlBefore x k) (Zs k) := by
    rw [disjoint_left]
    intro u hu hu'
    obtain ⟨j, _, rfl⟩ := mem_ctrlBefore.1 hu
    exact hZx k j hu'
  have hOk : Disjoint (covBefore Zs k ∪ ctrlBefore x k) (Zs k) :=
    disjoint_union_left.2 ⟨hcovk, hctrlk⟩
  have hO : Disjoint ({y} ∪ (covBefore Zs k ∪ ctrlBefore x k)) (Zs k) :=
    disjoint_union_left.2 ⟨disjoint_singleton_left.2 (hZy k), hOk⟩
  -- nondescendants of the remaining controls
  have hND1 : ∀ u ∈ covBefore Zs (k + 1) ∪ ctrlBefore x k,
      u ∉ G.descendantsOf ↑(ctrlFrom x k) := by
    intro u hu
    rcases mem_union.1 hu with hu | hu
    · obtain ⟨j, hj, hu⟩ := mem_covBefore.1 hu
      exact notMem_descendantsOf_of_mem_Zs hadm (by omega) hu
    · obtain ⟨i, hi, rfl⟩ := mem_ctrlBefore.1 hu
      exact notMem_descendantsOf_ctrl hord hi
  -- marginalize the numerator over `z_k`
  rw [planStage, FiniteDist.margAt_eq_sum_margAt _ (subset_union_left (s₂ := Zs k)),
    union_sdiff_cancel_left hO, sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hdc : ∀ u ∉ Zs k, d u = c u := fun u hu => FiniteDist.mem_agreeOn.1 hd u (mem_compl.2 hu)
  have hAk : ∀ u ∈ ctrlFrom x k, c u = d u := fun u hu => by
    obtain ⟨j, _, rfl⟩ := mem_ctrlFrom.1 hu
    exact (hdc _ (hZx k j)).symm
  rw [M.intervene_congr hAk, M.dist.margAt_congr (covBefore Zs k ∪ ctrlBefore x k)
    (fun u hu => (hdc u (disjoint_left.1 hOk hu)).symm)]
  have r := M.planStage_mul hadm hord hZx k d
  have e4 : Zs k ∪ covBefore Zs k ∪ ctrlBefore x k = covBefore Zs (k + 1) ∪ ctrlBefore x k := by
    rw [covBefore_succ, union_comm (covBefore Zs k)]
  have e1 : {y} ∪ (covBefore Zs k ∪ ctrlBefore x k) ∪ Zs k =
      {y} ∪ (covBefore Zs (k + 1) ∪ ctrlBefore x k) := by
    rw [← e4]
    ext u
    simp only [mem_union]
    tauto
  rw [e1, planStage]
  rcases (M.dist.margAt_nonneg (covBefore Zs (k + 1) ∪ ctrlBefore x k) d).eq_or_lt with h0 | hp
  · -- a stratum of probability zero contributes nothing on either side
    have hle := (M.intervene (ctrlFrom x k) d).dist.margAt_anti
      (S := covBefore Zs (k + 1) ∪ ctrlBefore x k)
      (T := {y} ∪ (covBefore Zs (k + 1) ∪ ctrlBefore x k)) subset_union_right d
    rw [M.margAt_intervene_of_notMem_descendantsOf hND1 d, ← h0] at hle
    rw [le_antisymm hle (FiniteDist.margAt_nonneg _ _ _), ← h0]
    simp
  · have hp' := hpos d hd hp
    have hOd : 0 < M.dist.margAt (covBefore Zs k ∪ ctrlBefore x k) d :=
      hp.trans_le (M.dist.margAt_anti (union_subset_union (by
        rw [covBefore_succ]; exact subset_union_left) subset_rfl) d)
    field_simp
    linear_combination r

/-- Theorem 4.4.1 of Pearl (2009) for covariate sets `Zs k` that are pairwise disjoint (the
form proved by induction on the stages); `SCM.effect_plan_eq_gFormula` drops the disjointness.
Under the hypotheses of `SCM.effect_plan_eq_gFormula` and the pairwise disjointness of the sets
`Zs k`, the same g-formula (4.6) holds.

The proof is Pearl's: by induction on the stages, Step 1 (deleting later actions from the
covariate factors) by the nondescendant condition (4.4), Step 2 (exchanging an action for an
observation) by Rule 2 and the test (4.5) (`SCM.planStage_eq_sum`). -/
theorem effect_plan_eq_gFormula_of_disjoint (x : Fin n → V) (y : V) (C : Finset V)
    (Zs : Fin n → Finset V) (v : ∀ u, α u) (hadm : G.Admissible C x y Zs)
    (hord : G.ControlsOrdered x) (hZdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hZx : ∀ i j, x j ∉ Zs i) (hZy : ∀ i, y ∉ Zs i)
    (hpos : ∀ (k : Fin n) (c : ∀ u, α u), (∀ j, c (x j) = v (x j)) →
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) c →
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1)) c) :
    M.effect (univ.image x) v {y} v = ∑ c ∈ FiniteDist.agreeOn (univ.biUnion Zs)ᶜ v,
      M.dist.margAt ({y} ∪ (univ.biUnion Zs ∪ univ.image x)) c /
          M.dist.margAt (univ.biUnion Zs ∪ univ.image x) c *
        ∏ k : Fin n, M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) c /
          M.dist.margAt (covBefore Zs k ∪ ctrlBefore x k) c := by
  have hctrl : ∀ (k : ℕ) (c : ∀ u, α u), c ∈ FiniteDist.agreeOn (covBefore Zs k)ᶜ v →
      ∀ j, c (x j) = v (x j) := fun k c hc j =>
    FiniteDist.mem_agreeOn.1 hc _ (mem_compl.2 fun h => by
      obtain ⟨i, _, hi⟩ := mem_covBefore.1 h
      exact hZx i j hi)
  have claim : ∀ k ≤ n, M.effect (univ.image x) v {y} v =
      ∑ c ∈ FiniteDist.agreeOn (covBefore Zs k)ᶜ v,
        M.planStage x y Zs k c * M.planWeight x Zs k c := by
    intro k hk
    induction k with
    | zero =>
      rw [covBefore_zero, FiniteDist.agreeOn_compl_empty_eq, sum_singleton, planStage, planWeight]
      simp only [effect, covBefore_zero, ctrlBefore_zero, union_empty, FiniteDist.margAt_empty,
        div_one, not_lt_zero, filter_false, prod_empty, mul_one]
      rw [ctrlFrom_zero]
    | succ k ih =>
      have hkn : k < n := hk
      let kk : Fin n := ⟨k, hkn⟩
      rw [ih hkn.le, show k = (kk : ℕ) from rfl, covBefore_succ kk,
        ← FiniteDist.sum_agreeOn_compl_agreeOn_compl (disjoint_covBefore hZdisj kk)]
      refine sum_congr rfl fun c hc => ?_
      have hpos' : ∀ d ∈ FiniteDist.agreeOn (Zs kk)ᶜ c,
          0 < M.dist.margAt (covBefore Zs (kk + 1) ∪ ctrlBefore x kk) d →
          0 < M.dist.margAt (covBefore Zs (kk + 1) ∪ ctrlBefore x (kk + 1)) d := by
        intro d hd
        refine hpos kk d fun j => ?_
        rw [FiniteDist.mem_agreeOn.1 hd _ (mem_compl.2 (hZx kk j))]
        exact hctrl kk c hc j
      rw [M.planStage_eq_sum hadm hord hZdisj hZx hZy kk c hpos', sum_mul]
      refine sum_congr rfl fun d hd => ?_
      have hdc : ∀ u ∉ Zs kk, d u = c u := fun u hu =>
        FiniteDist.mem_agreeOn.1 hd u (mem_compl.2 hu)
      have hoff : ∀ j : Fin n, (j : ℕ) < kk →
          ∀ u ∈ covBefore Zs (j + 1) ∪ ctrlBefore x j, d u = c u := by
        intro j hj u hu
        refine hdc u ?_
        rcases mem_union.1 hu with hu | hu
        · obtain ⟨i, hi, hu⟩ := mem_covBefore.1 hu
          exact disjoint_left.1 (hZdisj i kk fun h => by
            rw [h] at hi; omega) hu
        · obtain ⟨i, _, rfl⟩ := mem_ctrlBefore.1 hu
          exact hZx kk i
      have hw : M.planWeight x Zs kk d = M.planWeight x Zs kk c := by
        unfold planWeight
        refine prod_congr rfl fun j hj => ?_
        have hj' : (j : ℕ) < kk := (mem_filter.1 hj).2
        rw [M.dist.margAt_congr _ (hoff j hj'), M.dist.margAt_congr _ fun u hu =>
          hoff j hj' u (mem_of_subset (union_subset_union (by
            rw [covBefore_succ]; exact subset_union_left) subset_rfl) hu)]
      rw [planWeight_succ, hw]
      ring
  rw [claim n le_rfl, covBefore_self]
  refine sum_congr rfl fun c _ => ?_
  rw [planStage, planWeight, ctrlFrom_self, covBefore_self, ctrlBefore_self, dist_intervene_empty,
    filter_true_of_mem fun j _ => j.2]

/-- **The effect of a plan** (Pearl 2009, Theorem 4.4.1 and equation (4.6); Pearl and Robins
1995, the sequential back-door criterion). Let the controls `x 0, …, x (n - 1)` be listed in an
order compatible with `G` (`Digraph.ControlsOrdered`) and let the covariate sets `Zs` form an
admissible sequence for the outcome `y` (`Digraph.Admissible`, conditions (4.4) and (4.5)).
Assume, as in Pearl's partition of the vertices by role into controls, covariates, latent
variables and the outcome, that the sets `Zs k` contain neither a control nor `y`; the sets
`Zs k` may overlap (a covariate may be listed at several stages). Assume the positivity
`P(z_1, …, z_k, x_1, …, x_{k-1}) > 0 → P(z_1, …, z_k, x_1, …, x_k) > 0` at every stage, at the
planned values of the controls. Then
`P(y | do(x_1), …, do(x_n)) = ∑_z P(y | z, x) ∏_k P(z_k | z_1, …, z_{k-1}, x_1, …, x_{k-1})`,
written with ratios of marginals: `P(y | z, x) = P(y, z, x) / P(z, x)` and
`P(z_k | z_{<k}, x_{<k}) = P(z_{≤k}, x_{<k}) / P(z_{<k}, x_{<k})`, where `z_{≤k}` is the value of
the union `Z_1 ∪ … ∪ Z_k`. The sum runs over the configurations that agree with `v` outside the
covariates; only marginals on covariates, controls and `y` appear on the right, so every other
vertex may be latent. Strata of probability zero contribute zero, so the convention `x / 0 = 0`
carries nothing.

Proof: replacing `Z_k` by `Z_k \ (Z_1 ∪ … ∪ Z_{k-1})` keeps the sequence admissible
(`Plan.admissible_sdiff_covBefore`) and leaves every cumulative union, and so both sides and the
positivity hypothesis, unchanged (`Plan.covBefore_sdiff`); the new sets are pairwise disjoint,
and `SCM.effect_plan_eq_gFormula_of_disjoint` applies. -/
theorem effect_plan_eq_gFormula (x : Fin n → V) (y : V) (C : Finset V) (Zs : Fin n → Finset V)
    (v : ∀ u, α u) (hadm : G.Admissible C x y Zs) (hord : G.ControlsOrdered x)
    (hZx : ∀ i j, x j ∉ Zs i) (hZy : ∀ i, y ∉ Zs i)
    (hpos : ∀ (k : Fin n) (c : ∀ u, α u), (∀ j, c (x j) = v (x j)) →
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) c →
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1)) c) :
    M.effect (univ.image x) v {y} v = ∑ c ∈ FiniteDist.agreeOn (univ.biUnion Zs)ᶜ v,
      M.dist.margAt ({y} ∪ (univ.biUnion Zs ∪ univ.image x)) c /
          M.dist.margAt (univ.biUnion Zs ∪ univ.image x) c *
        ∏ k : Fin n, M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) c /
          M.dist.margAt (covBefore Zs k ∪ ctrlBefore x k) c := by
  have h := M.effect_plan_eq_gFormula_of_disjoint x y C (fun j => Zs j \ covBefore Zs j) v
    (admissible_sdiff_covBefore hadm) hord (fun _ _ hij => disjoint_sdiff_covBefore Zs hij)
    (fun i j hj => hZx i j (mem_sdiff.1 hj).1) (fun i hi => hZy i (mem_sdiff.1 hi).1)
    (by simpa only [covBefore_sdiff] using hpos)
  simpa only [biUnion_sdiff_covBefore, covBefore_sdiff] using h

/-- **The effect of a plan for Pearl's admissible sequences** (Pearl 2009, Theorem 4.4.1 with
Definition 4.4.2): `SCM.effect_plan_eq_gFormula` for a sequence `Zs` satisfying
`Digraph.AdmissiblePlan` (the step tests together with the standing assumptions
`Digraph.PlanRoles`), which supply the order of the controls and keep the controls and the
outcome out of the covariates. -/
theorem effect_plan_eq_gFormula_of_admissiblePlan (x : Fin n → V) (y : V) (C : Finset V)
    (Zs : Fin n → Finset V) (v : ∀ u, α u) (h : G.AdmissiblePlan C x y Zs)
    (hpos : ∀ (k : Fin n) (c : ∀ u, α u), (∀ j, c (x j) = v (x j)) →
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) c →
      0 < M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x (k + 1)) c) :
    M.effect (univ.image x) v {y} v = ∑ c ∈ FiniteDist.agreeOn (univ.biUnion Zs)ᶜ v,
      M.dist.margAt ({y} ∪ (univ.biUnion Zs ∪ univ.image x)) c /
          M.dist.margAt (univ.biUnion Zs ∪ univ.image x) c *
        ∏ k : Fin n, M.dist.margAt (covBefore Zs (k + 1) ∪ ctrlBefore x k) c /
          M.dist.margAt (covBefore Zs k ∪ ctrlBefore x k) c :=
  M.effect_plan_eq_gFormula x y C Zs v h.2 h.1.1
    (fun i j hj => h.1.2.2.1 j ((h.2 i).1 _ hj).1)
    (fun i hi => h.1.2.2.2.1 ((h.2 i).1 _ hi).1) hpos

/-- **The effect of a plan with the covariate sets of Theorem 4.4.6** (Pearl 2009): under the
standing assumptions `Digraph.PlanRoles`, if the explicit sets `W_k = Digraph.wSet G C x y k`
pass the tests (4.5), they form an admissible sequence (`Digraph.admissible_wSet`) and the
g-formula (4.6) holds with `Z_k = W_k`, under the stagewise positivity. -/
theorem effect_plan_eq_gFormula_of_wSet (x : Fin n → V) (y : V) (C : Finset V) (v : ∀ u, α u)
    (hroles : G.PlanRoles C x y) (hstep : ∀ k, G.SeqBackDoorStep x y (G.wSet C x y) k)
    (hpos : ∀ (k : Fin n) (c : ∀ u, α u), (∀ j, c (x j) = v (x j)) →
      0 < M.dist.margAt (covBefore (G.wSet C x y) (k + 1) ∪ ctrlBefore x k) c →
      0 < M.dist.margAt (covBefore (G.wSet C x y) (k + 1) ∪ ctrlBefore x (k + 1)) c) :
    M.effect (univ.image x) v {y} v = ∑ c ∈ FiniteDist.agreeOn (univ.biUnion (G.wSet C x y))ᶜ v,
      M.dist.margAt ({y} ∪ (univ.biUnion (G.wSet C x y) ∪ univ.image x)) c /
          M.dist.margAt (univ.biUnion (G.wSet C x y) ∪ univ.image x) c *
        ∏ k : Fin n, M.dist.margAt (covBefore (G.wSet C x y) (k + 1) ∪ ctrlBefore x k) c /
          M.dist.margAt (covBefore (G.wSet C x y) k ∪ ctrlBefore x k) c :=
  M.effect_plan_eq_gFormula_of_admissiblePlan x y C _ v ⟨hroles, Digraph.admissible_wSet hstep⟩
    hpos

end Step

end SCM

/-! ### Figure 4.4 -/

namespace SCM.PlanExamples

open SequentialBackDoorExamples Plan

variable {α : Fin 6 → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : Fin 6 → Type*}
  [∀ v, Fintype (ε v)]

/-- **Equation (4.7) of Pearl (2009)**, for the graph of Figure 4.4
(`SequentialBackDoorExamples.pearlFig44`: `U₁ = 0`, `U₂ = 1`, `X₁ = 2`, `Z = 3`, `X₂ = 4`,
`Y = 5`, with `U₁`, `U₂` latent). For every model on this graph whose observed law of
`(X₁, Z, X₂)` is strictly positive, the plan `do(x₁), do(x₂)` has the effect
`P(y | do(x₁), do(x₂)) = ∑_z P(y | z, x₁, x₂) P(z | x₁)`. It is the instance of
`SCM.effect_plan_eq_gFormula` with the admissible sequence `Z₁ = ∅`, `Z₂ = {Z}`. -/
theorem effect_plan_pearlFig44 (M : SCM pearlFig44 α ε) (v : ∀ u, α u)
    (hpos : ∀ c : ∀ u, α u, 0 < M.dist.margAt {2, 3, 4} c) :
    M.effect {2, 4} v {5} v = ∑ c ∈ FiniteDist.agreeOn {3}ᶜ v,
      M.dist.margAt {2, 3, 4, 5} c / M.dist.margAt {2, 3, 4} c *
        (M.dist.margAt {2, 3} c / M.dist.margAt {2} c) := by
  have h := M.effect_plan_eq_gFormula ![2, 4] 5 {3} ![∅, {3}] v (by decide +kernel)
    (by decide +kernel) (by decide) (by decide) fun k c _ _ =>
      (hpos c).trans_le (M.dist.margAt_anti (by fin_cases k <;> decide) c)
  simp only [Fin.prod_univ_two] at h
  have e1 : (univ.image ![(2 : Fin 6), 4]) = {2, 4} := by decide
  have e2 : (univ.biUnion ![(∅ : Finset (Fin 6)), {3}]) = {3} := by decide
  have e3 : ({5} ∪ ({3} ∪ {2, 4}) : Finset (Fin 6)) = {2, 3, 4, 5} := by decide
  have e4 : ({3} ∪ {2, 4} : Finset (Fin 6)) = {2, 3, 4} := by decide
  have e5 : (covBefore ![(∅ : Finset (Fin 6)), {3}] ((0 : Fin 2) + 1) ∪
      ctrlBefore ![(2 : Fin 6), 4] ((0 : Fin 2) : ℕ)) = ∅ := by decide
  have e6 : (covBefore ![(∅ : Finset (Fin 6)), {3}] ((0 : Fin 2) : ℕ) ∪
      ctrlBefore ![(2 : Fin 6), 4] ((0 : Fin 2) : ℕ)) = ∅ := by decide
  have e7 : (covBefore ![(∅ : Finset (Fin 6)), {3}] ((1 : Fin 2) + 1) ∪
      ctrlBefore ![(2 : Fin 6), 4] ((1 : Fin 2) : ℕ)) = {2, 3} := by decide
  have e8 : (covBefore ![(∅ : Finset (Fin 6)), {3}] ((1 : Fin 2) : ℕ) ∪
      ctrlBefore ![(2 : Fin 6), 4] ((1 : Fin 2) : ℕ)) = {2} := by decide
  rw [e1, e2, e3, e4, e5, e6, e7, e8] at h
  simpa using h

/-! ### A numerical model on Figure 4.4 -/

/-- The noise laws of `fig44Model`: biased coins with `P(true) = 1/4` at `U₂ = 1` and
`X₂ = 4`, fair bits elsewhere. -/
noncomputable def fig44Noise (v : Fin 6) : FiniteDist Bool :=
  if v = 1 ∨ v = 4 then BowExample.quarterCoin else FiniteDist.uniform

/-- A model on the graph of Figure 4.4 with full support on `(X₁, Z, X₂)`: `U₁ := false`,
`X₁ := ε₂` (a fair bit), `U₂ := X₁ xor ε₁`, `Z := U₂`, `X₂ := Z xor ε₄`, `Y := X₂ xor U₂`, with
`ε₁`, `ε₄` biased coins of `P(true) = 1/4`. -/
noncomputable def fig44Model : SCM pearlFig44 (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide +kernel
  f v z e :=
    if h1 : v = 1 then xor (z ⟨2, by subst h1; decide⟩) e else
    if v = 2 then e else
    if h3 : v = 3 then z ⟨1, by subst h3; decide⟩ else
    if h4 : v = 4 then xor (z ⟨3, by subst h4; decide⟩) e else
    if h5 : v = 5 then xor (z ⟨4, by subst h5; decide⟩) (z ⟨1, by subst h5; decide⟩) else false
  noise := fig44Noise

/-- The observational solution of `fig44Model`. -/
theorem fig44Model_solve (u : Fin 6 → Bool) :
    fig44Model.solve u = ![false, xor (u 2) (u 1), u 2, xor (u 2) (u 1),
      xor (xor (u 2) (u 1)) (u 4), xor (xor (xor (u 2) (u 1)) (u 4)) (xor (u 2) (u 1))] := by
  refine (fig44Model.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [fig44Model, Finset.restrict]

/-- Each noise law has total mass one on the two values. -/
theorem fig44Noise_add (i : Fin 6) : fig44Noise i true + fig44Noise i false = 1 := by
  simpa [Fintype.sum_bool] using (fig44Noise i).sum_eq_one

/-- The noise coordinates `ε₂`, `ε₁`, `ε₄` of `fig44Model` are independent with laws
`fig44Noise 2`, `fig44Noise 1`, `fig44Noise 4`. -/
theorem fig44_map_triple : (FiniteDist.pi fig44Noise).map (fun u => (u 2, u 1, u 4)) =
    (fig44Noise 2).prod ((fig44Noise 1).prod (fig44Noise 4)) := by
  ext ⟨a, b, c⟩
  rw [FiniteDist.map_apply_eq_prob]
  have h : (univ.filter fun u : Fin 6 → Bool => (u 2, u 1, u 4) = (a, b, c)) =
      Fintype.piFinset ![univ, {b}, {a}, univ, {c}, univ] := by
    ext u
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩ i
      fin_cases i <;> simp
    · intro h
      exact ⟨by simpa using h 2, by simpa using h 1, by simpa using h 4⟩
  rw [h, FiniteDist.prob_piFinset, Fin.prod_univ_six]
  simp only [FiniteDist.prob, Matrix.cons_val, sum_singleton, Fintype.sum_bool, fig44Noise_add,
    FiniteDist.prod_apply]
  ring

/-- A noise event that depends only on `ε₁`, `ε₂`, `ε₄` has probability given by the sum over
those three bits. -/
theorem fig44_probOf (P : (Fin 6 → Bool) → Prop) {_ : DecidablePred P}
    (hP : ∀ u u' : Fin 6 → Bool, u 1 = u' 1 → u 2 = u' 2 → u 4 = u' 4 → (P u ↔ P u')) :
    fig44Model.noiseDist.probOf P = ∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      if P ![false, b, a, false, d, false] then
        fig44Noise 2 a * (fig44Noise 1 b * fig44Noise 4 d) else 0 := by
  change (FiniteDist.pi fig44Noise).probOf P = _
  rw [show (FiniteDist.pi fig44Noise).probOf P =
      (FiniteDist.pi fig44Noise).probOf (fun u => P ![false, u 1, u 2, false, u 4, false]) from
    FiniteDist.probOf_congr _ fun u => hP _ _ rfl rfl rfl,
    show (FiniteDist.pi fig44Noise).probOf (fun u => P ![false, u 1, u 2, false, u 4, false]) =
      ((FiniteDist.pi fig44Noise).map (fun u => (u 2, u 1, u 4))).probOf
        (fun t => P ![false, t.2.1, t.1, false, t.2.2, false]) from
    (FiniteDist.probOf_map (FiniteDist.pi fig44Noise) (fun u => (u 2, u 1, u 4))
      (fun t => P ![false, t.2.1, t.1, false, t.2.2, false])).symm, fig44_map_triple]
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    FiniteDist.prod_apply]

/-- The all-`true` configuration: the plan `do(X₁ = true), do(X₂ = true)` and the outcome
`Y = true`. -/
def fig44Ones : Fin 6 → Bool := fun _ => true

/-- The solution of `fig44Model` under the plan `do(X₁ = true), do(X₂ = true)`. -/
theorem fig44Model_intervene_solve (u : Fin 6 → Bool) :
    (fig44Model.intervene {2, 4} fig44Ones).solve u =
      ![false, xor true (u 1), true, xor true (u 1), true, xor true (xor true (u 1))] := by
  refine ((fig44Model.intervene {2, 4} fig44Ones).eq_solve_of_isSolution ?_).symm
  refine fig44Model.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · fin_cases v <;> simp_all [fig44Ones]
  · fin_cases v <;> simp_all [fig44Model, Finset.restrict]

/-- The events `{V = c on S}` of `fig44Model` depend only on the noise bits `ε₁`, `ε₂`, `ε₄`. -/
theorem fig44Model_hP (S : Finset (Fin 6)) (c : Fin 6 → Bool) (u u' : Fin 6 → Bool)
    (h1 : u 1 = u' 1) (h2 : u 2 = u' 2) (h4 : u 4 = u' 4) :
    (∀ v ∈ S, fig44Model.solve u v = c v) ↔ ∀ v ∈ S, fig44Model.solve u' v = c v := by
  rw [fig44Model_solve, fig44Model_solve, h1, h2, h4]

/-- The events `{V = c on S}` of `fig44Model` under the plan depend only on the noise bit
`ε₁`. -/
theorem fig44Model_intervene_hP (S : Finset (Fin 6)) (c : Fin 6 → Bool) (u u' : Fin 6 → Bool)
    (h1 : u 1 = u' 1) (_ : u 2 = u' 2) (_ : u 4 = u' 4) :
    (∀ v ∈ S, (fig44Model.intervene {2, 4} fig44Ones).solve u v = c v) ↔
      ∀ v ∈ S, (fig44Model.intervene {2, 4} fig44Ones).solve u' v = c v := by
  rw [fig44Model_intervene_solve, fig44Model_intervene_solve, h1]

/-- The observational marginals of `fig44Model` as sums over the noise bits `ε₂`, `ε₁`, `ε₄`. -/
theorem fig44Model_margAt (S : Finset (Fin 6)) (c : Fin 6 → Bool) :
    fig44Model.dist.margAt S c = ∑ a : Bool, ∑ b : Bool, ∑ d : Bool,
      if (∀ v ∈ S, fig44Model.solve ![false, b, a, false, d, false] v = c v) then
        fig44Noise 2 a * (fig44Noise 1 b * fig44Noise 4 d) else 0 := by
  rw [margAt_dist, fig44_probOf _ (fig44Model_hP S c)]
  congr!

/-- The two configurations that agree with `fig44Ones` outside `Z = 3`. -/
theorem fig44_agreeOn : FiniteDist.agreeOn ({3} : Finset (Fin 6))ᶜ fig44Ones =
    {fig44Ones, Function.update fig44Ones 3 false} := by
  ext c
  simp only [FiniteDist.mem_agreeOn, mem_compl, mem_singleton, mem_insert]
  constructor
  · intro h
    cases h3 : c 3
    · right
      funext i
      by_cases hi : i = 3
      · subst hi; simpa using h3
      · rw [Function.update_of_ne hi]; exact h i hi
    · left
      funext i
      by_cases hi : i = 3
      · subst hi; simpa [fig44Ones] using h3
      · exact h i hi
  · rintro (rfl | rfl) i hi
    · rfl
    · exact Function.update_of_ne hi _ _

/-- **A numerical instance of equation (4.7)** (Pearl 2009, Figure 4.4). In `fig44Model` the
observed law of `(X₁, Z, X₂)` has full support; the plan `do(X₁ = true), do(X₂ = true)` gives
`P(Y = true | do(x₁), do(x₂)) = 1/4`; the g-formula (4.7),
`∑_z P(y | z, x₁, x₂) P(z | x₁)`, evaluated on the observational law, is also `1/4`; and the
unadjusted conditional probability `P(Y = true | X₁ = true, X₂ = true)` is `1/10`, which differs
from the effect. -/
theorem fig44Model_plan :
    (∀ c, 0 < fig44Model.dist.margAt {2, 3, 4} c) ∧
      fig44Model.effect {2, 4} fig44Ones {5} fig44Ones = 1 / 4 ∧
      (∑ c ∈ FiniteDist.agreeOn ({3} : Finset (Fin 6))ᶜ fig44Ones,
        fig44Model.dist.margAt {2, 3, 4, 5} c / fig44Model.dist.margAt {2, 3, 4} c *
          (fig44Model.dist.margAt {2, 3} c / fig44Model.dist.margAt {2} c)) = 1 / 4 ∧
      fig44Model.dist.margAt {2, 4, 5} fig44Ones / fig44Model.dist.margAt {2, 4} fig44Ones =
        1 / 10 := by
  have hnn : ∀ a b d, 0 ≤ fig44Noise 2 a * (fig44Noise 1 b * fig44Noise 4 d) := fun a b d =>
    mul_nonneg ((fig44Noise 2).nonneg _) (mul_nonneg ((fig44Noise 1).nonneg _)
      ((fig44Noise 4).nonneg _))
  refine ⟨fun c => ?_, ?_, ?_, ?_⟩
  · have h : ∀ i b, 0 < fig44Noise i b := fun i b => by
      unfold fig44Noise
      split_ifs <;> cases b <;> norm_num [BowExample.quarterCoin]
    rw [fig44Model_margAt]
    refine sum_pos' (fun a _ => sum_nonneg fun b _ => sum_nonneg fun d _ =>
      ite_nonneg (hnn a b d) le_rfl) ⟨c 2, mem_univ _, sum_pos' (fun b _ => sum_nonneg
      fun d _ => ite_nonneg (hnn _ b d) le_rfl) ⟨xor (c 2) (c 3), mem_univ _, sum_pos'
      (fun d _ => ite_nonneg (hnn _ _ d) le_rfl) ⟨xor (c 3) (c 4), mem_univ _, ?_⟩⟩⟩
    have hc : ∀ v ∈ ({2, 3, 4} : Finset (Fin 6)), fig44Model.solve
        ![false, xor (c 2) (c 3), c 2, false, xor (c 3) (c 4), false] v = c v := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> simp [fig44Model_solve]
    split_ifs
    exact mul_pos (h 2 _) (mul_pos (h 1 _) (h 4 _))
  · rw [effect, margAt_dist, noiseDist_intervene,
      fig44_probOf _ (fig44Model_intervene_hP {5} fig44Ones)]
    simp [fig44Model_intervene_solve, fig44Noise, BowExample.quarterCoin, fig44Ones]
    norm_num
  · rw [fig44_agreeOn, sum_pair (fun h => by simpa [fig44Ones] using congrFun h 3)]
    simp only [fig44Model_margAt]
    simp [fig44Model_solve, fig44Noise, BowExample.quarterCoin, fig44Ones]
    norm_num
  · simp only [fig44Model_margAt]
    simp [fig44Model_solve, fig44Noise, BowExample.quarterCoin, fig44Ones]
    norm_num

end SCM.PlanExamples

end CausalInference
