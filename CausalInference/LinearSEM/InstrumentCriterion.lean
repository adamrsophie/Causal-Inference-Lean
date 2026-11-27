/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.DSeparation
public import CausalInference.LinearSEM.InstrumentalVariable
public import CausalInference.Graphical.Criteria.Instrument

/-!
# The graphical instrument criterion in a linear SEM

For a linear structural equation model with uncorrelated errors, the graphical instrument
criterion of Pearl (2009), Definition 7.4.1, for a pretreatment instrument implies the moment
condition of the instrumental variable estimand, with the total effect as the slope.

## Main results

* `Digraph.dSep_deleteOutgoing_of_dSep_deleteIncoming`: if no member of `S` is a descendant of
  `x`, then a d-separation of `z` and `y` (both different from `x`) by `S` in the graph with the
  edges into `x` removed implies the same d-separation in the graph with the edges out of `x`
  removed. In the latter graph `x` cannot be an inner vertex of a trail that is active given `S`.
* `LinearSEM.cov_eq_T_mul_cov_of_dSep`, `LinearSEM.cov_eq_T_mul_cov_of_isPretreatmentInstrument`:
  with diagonal `Ω`, if `z` is not a descendant of `x`, `y ≠ x`, and `z` and `y` are
  d-separated in the graph with the edges into `x` removed, then `Σ z y = T y x Σ z x`, where
  `T y x` is the total effect of `x` on `y`. Hence the instrumental ratio `Σ z y / Σ z x` is
  `T y x` whenever `Σ z x ≠ 0` (`LinearSEM.cov_div_cov_eq_T_of_isPretreatmentInstrument`).
* `LinearSEM.partialCov_eq_T_mul_partialCov_of_dSep`: the conditional version with a set `S`
  of covariates that are not descendants of `x` and an invertible covariance block of `S`: the
  partial covariances given `S` satisfy the same identity.
* `LinearSEM.T_eq_B_of_forall`: the total effect is the path coefficient `B y x` when no other
  parent of `y` is a descendant of `x`.
* `LinearSEM.ErrorRealization.linearIV_of_isPretreatmentInstrument`: for a realization of the
  errors, the linear IV model with slope `T y x` satisfies exogeneity, relevance follows from a
  nonzero first stage, and the covariance ratio is `T y x`.
* `LinearSEM.DescendantInstrumentModel.counterexample`: on the graph `U → X → Z`, `U → Y`
  (`CausalInference.InstrumentExamples.descendantInstrument`), a model with unit errors in which
  every hypothesis holds except that `Z` is a descendant of `X`, and `Σ z y = 1` while
  `T y x Σ z x = 0`.

## Notes

The slope identified by the criterion is the total effect `T y x`, not the coefficient of the
edge `x → y`: the criterion removes only the edges into `x`, so every directed path from `x` to
`y` contributes. The relevance `Σ z x ≠ 0` is a hypothesis: d-connection of `z` and `x` does not
imply it for particular coefficients. Correlated errors are not covered.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 7.4.5,
  Definition 7.4.1, and section 5.3.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*} {G : Digraph V} {S : Set V} {x : V}

/-- A directed path ending outside the descendants of `x` avoids `x`, so it survives the
removal of the edges into `x`. -/
theorem reflTransGen_deleteIncoming_of_notMem {u s : V} (hs : s ∉ G.descendantsOf {x})
    (h : ReflTransGen G.Adj u s) : ReflTransGen (G.deleteIncoming {x}).Adj u s := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b hab hbs ih => exact .head ⟨hab, fun hb => hs ⟨b, hb, hbs⟩⟩ ih

/-- A trail of `G.deleteOutgoing {x}` that is active given `S`, with no member of `S` a
descendant of `x` and both ends different from `x`, is a trail of `G.deleteIncoming {x}` that is
active given `S`: the vertex `x` can be neither a collider (it is not an ancestor of `S`) nor a
non-collider (it has no outgoing edge). -/
theorem ActiveTrail.deleteIncoming_of_deleteOutgoing (hS : ∀ s ∈ S, s ∉ G.descendantsOf {x})
    {a : Bool} {u w : V} {l : List V} (p : (G.deleteOutgoing {x}).ActiveTrail S a u w l)
    (hux : u ≠ x) (hwx : w ≠ x) : (G.deleteIncoming {x}).ActiveTrail S a u w l := by
  have hanc : ∀ {t : V}, t ∈ (G.deleteOutgoing {x}).ancestorsOf S →
      t ∈ (G.deleteIncoming {x}).ancestorsOf S := by
    rintro t ⟨s, hs, hts⟩
    exact ⟨s, hs, reflTransGen_deleteIncoming_of_notMem (hS s hs)
      (reflTransGen_mono deleteOutgoing_le hts)⟩
  induction p with
  | nil hv => exact .nil hv
  | @fwd _ _ v _ _ h hu q ih =>
    have hvx : v ≠ x := by
      rintro rfl
      cases q with
      | nil _ => exact hwx rfl
      | fwd h' _ _ => exact h'.2 rfl
      | collider _ hc _ =>
        obtain ⟨s, hs, hvs⟩ := hc
        exact hS s hs ⟨v, rfl, reflTransGen_mono deleteOutgoing_le hvs⟩
    exact .fwd ⟨h.1, hvx⟩ hu (ih hvx hwx)
  | bwd h hu _ ih => exact .bwd ⟨h.1, hux⟩ hu (ih (fun e => h.2 e) hwx)
  | collider h hc _ ih => exact .collider ⟨h.1, hux⟩ (hanc hc) (ih (fun e => h.2 e) hwx)

/-- If no member of `S` is a descendant of `x`, a d-separation of `z` and `y` (both different
from `x`) by `S` in the graph with the edges into `x` removed gives the same d-separation in
the graph with the edges out of `x` removed. -/
theorem dSep_deleteOutgoing_of_dSep_deleteIncoming {z y : V}
    (hS : ∀ s ∈ S, s ∉ G.descendantsOf {x}) (hz : z ≠ x) (hy : y ≠ x)
    (h : (G.deleteIncoming {x}).DSep {z} {y} S) : (G.deleteOutgoing {x}).DSep {z} {y} S := by
  intro hc
  obtain ⟨z', hz', y', hy', l, hl⟩ := dConn_iff_dConnTrail.1 hc
  rw [Set.mem_singleton_iff] at hz' hy'
  subst hz' hy'
  exact h (dConn_iff_dConnTrail.2
    ⟨_, rfl, _, rfl, l, hl.deleteIncoming_of_deleteOutgoing hS hz hy⟩)

end Digraph

namespace CausalInference

namespace LinearSEM

open Matrix Finset Relation

variable {V : Type*} [Fintype V] [DecidableEq V] (M : LinearSEM V)

omit [Fintype V] in
/-- The covariance block of the empty set is invertible. -/
theorem isUnit_subCov_empty (C : Matrix V V ℝ) : IsUnit (subCov C ∅) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (by simp)

/-- The partial covariance given the empty set is the covariance. -/
theorem partialCov_empty (C : Matrix V V ℝ) (a b : V) : partialCov C ∅ a b = C a b := by
  simp [partialCov, regCoeff]

/-- **The instrumental moment condition from the graph.** In a linear SEM with uncorrelated
errors, let `z` be a nondescendant of `x` (so `z ≠ x`), let `y ≠ x`, and let `z` and `y` be
d-separated by the empty set in the graph with the edges into `x` removed. Then
`Σ z y = T y x Σ z x`, where `T y x` is the total effect of `x` on `y`. -/
theorem cov_eq_T_mul_cov_of_dSep (hΩ : M.Ω.IsDiag) {x y z : V}
    (hz : z ∉ M.G.descendantsOf {x}) (hy : y ≠ x)
    (hsep : (M.G.deleteIncoming {x}).DSep {z} {y} ∅) : M.cov z y = M.T y x * M.cov z x := by
  have hzx : z ≠ x := fun h => hz ⟨x, rfl, h ▸ ReflTransGen.refl⟩
  have hnt : ¬ TransGen M.G.Adj x z := fun h => hz ⟨x, rfl, h.to_reflTransGen⟩
  rw [M.cov_eq_cov_cutOutgoing_add hy hnt]
  have hsep' : (M.cutOutgoing x).G.DSep {z} {y} ↑(∅ : Finset V) := by
    rw [Finset.coe_empty]
    exact Digraph.dSep_deleteOutgoing_of_dSep_deleteIncoming (fun _ hs => hs.elim) hzx hy hsep
  have h0 := (M.cutOutgoing x).partialCov_eq_zero_of_dSep hΩ hsep' (isUnit_subCov_empty _)
  rw [partialCov_empty] at h0
  rw [h0, zero_add]

/-- The conditional form: with a set `S` of covariates that are not descendants of `x`, an
invertible covariance block of `S`, and `z`, `y` d-separated by `S` in the graph with the
edges into `x` removed, the partial covariances given `S` satisfy
`Σ_{zy·S} = T y x Σ_{zx·S}`. -/
theorem partialCov_eq_T_mul_partialCov_of_dSep (hΩ : M.Ω.IsDiag) {x y z : V} {S : Finset V}
    (hz : z ∉ M.G.descendantsOf {x}) (hS : ∀ s ∈ S, s ∉ M.G.descendantsOf {x}) (hy : y ≠ x)
    (hsep : (M.G.deleteIncoming {x}).DSep {z} {y} ↑S) (hu : IsUnit (subCov M.cov S)) :
    partialCov M.cov S z y = M.T y x * partialCov M.cov S z x := by
  have hzx : z ≠ x := fun h => hz ⟨x, rfl, h ▸ ReflTransGen.refl⟩
  have hnt : ∀ {s}, s ∉ M.G.descendantsOf {x} → ¬ TransGen M.G.Adj x s :=
    fun hs h => hs ⟨x, rfl, h.to_reflTransGen⟩
  have hsub : subCov (M.cutOutgoing x).cov S = subCov M.cov S := by
    ext s t
    exact M.cov_cutOutgoing (hnt (hS s s.2)) (hnt (hS t t.2))
  have hu' : IsUnit (subCov (M.cutOutgoing x).cov S) := hsub ▸ hu
  have hsep' : (M.cutOutgoing x).G.DSep {z} {y} ↑S :=
    Digraph.dSep_deleteOutgoing_of_dSep_deleteIncoming (fun s hs => hS s hs) hzx hy hsep
  have h0 := (M.cutOutgoing x).partialCov_eq_zero_of_dSep hΩ hsep' hu'
  have hγ := regCoeff_isRegCoeff (C := (M.cutOutgoing x).cov) y hu'
  have hγx := regCoeff_isRegCoeff (C := M.cov) x hu
  -- the covariance with a vertex of `S` is unchanged when the coefficient vanishes off `S`
  have e1 : ∀ s, s ∉ M.G.descendantsOf {x} → ∀ t,
      M.cov s t * regCoeff (M.cutOutgoing x).cov S y t =
        (M.cutOutgoing x).cov s t * regCoeff (M.cutOutgoing x).cov S y t := by
    intro s hs t
    by_cases ht : t ∈ S
    · rw [M.cov_cutOutgoing (hnt hs) (hnt (hS t ht))]
    · simp [hγ.1 t ht]
  have hR : IsRegCoeff M.cov S y
      (regCoeff (M.cutOutgoing x).cov S y + M.T y x • regCoeff M.cov S x) := by
    refine ⟨fun v hv => by simp [hγ.1 v hv, hγx.1 v hv], fun s hs => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun t _ => e1 s (hS s hs) t, hγ.2 s hs]
    have e2 : ∑ t, M.cov s t * (M.T y x * regCoeff M.cov S x t) = M.T y x * M.cov s x := by
      rw [← hγx.2 s hs, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [e2, M.cov_eq_cov_cutOutgoing_add hy (hnt (hS s hs))]
  have hreg := ((isRegCoeff_iff_eq_regCoeff hu).1 hR).symm
  have e4 : ∑ t, M.cov z t * (M.T y x * regCoeff M.cov S x t) =
      M.T y x * ∑ t, M.cov z t * regCoeff M.cov S x t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [partialCov] at h0
  rw [partialCov, partialCov, hreg, M.cov_eq_cov_cutOutgoing_add hy (hnt hz)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun t _ => e1 z hz t]
  linear_combination h0 - e4

/-- The total effect of `x` on `y ≠ x` is the path coefficient `B y x` when no other parent of
`y` (a vertex `p ≠ x` with `B y p ≠ 0`) is a descendant of `x`. -/
theorem T_eq_B_of_forall {x y : V} (hy : y ≠ x)
    (h : ∀ p, p ≠ x → M.B y p ≠ 0 → ¬ ReflTransGen M.G.Adj x p) : M.T y x = M.B y x := by
  have e := congrFun (congrFun M.T_eq_one_add_B_mul_T y) x
  rw [Matrix.add_apply, Matrix.one_apply_ne hy, zero_add, Matrix.mul_apply] at e
  rw [e, Finset.sum_eq_single x]
  · rw [M.T_apply_self, mul_one]
  · intro p _ hpx
    by_cases hB : M.B y p = 0
    · rw [hB, zero_mul]
    · rw [M.T_apply_eq_zero (h p hpx hB), mul_zero]
  · simp

/-- The moment condition for a pretreatment instrument (`Digraph.IsPretreatmentInstrument`
with no covariates): `Σ z y = T y x Σ z x`. -/
theorem cov_eq_T_mul_cov_of_isPretreatmentInstrument (hΩ : M.Ω.IsDiag) {x y z : V}
    (hI : M.G.IsPretreatmentInstrument {z} {x} {y} ∅) : M.cov z y = M.T y x * M.cov z x :=
  M.cov_eq_T_mul_cov_of_dSep hΩ (hI.2 z rfl) (Set.disjoint_singleton.1 hI.1.1.2.2.1).symm
    hI.1.2.2.1

/-- For a pretreatment instrument with a nonzero first stage `Σ z x ≠ 0`, the instrumental
ratio `Σ z y / Σ z x` is the total effect `T y x`. -/
theorem cov_div_cov_eq_T_of_isPretreatmentInstrument (hΩ : M.Ω.IsDiag) {x y z : V}
    (hI : M.G.IsPretreatmentInstrument {z} {x} {y} ∅) (hzx : M.cov z x ≠ 0) :
    M.cov z y / M.cov z x = M.T y x := by
  rw [M.cov_eq_T_mul_cov_of_isPretreatmentInstrument hΩ hI, mul_div_assoc, div_self hzx,
    mul_one]

open MeasureTheory ProbabilityTheory

variable {Ω' : Type*} [MeasurableSpace Ω'] {M} {μ : Measure Ω'} {ε : V → Ω' → ℝ}

/-- **The graphical instrument criterion gives a valid linear IV model.** For a realization of
the errors of a linear SEM with uncorrelated errors and a pretreatment instrument `z` for `x`
on `y` with no covariates, the linear IV model with slope `T y x` (treatment `X x`, instrument
`X z`, outcome `X y`) satisfies exogeneity; with a nonzero first stage it satisfies relevance,
and the covariance ratio is the total effect `T y x`. -/
theorem ErrorRealization.linearIV_of_isPretreatmentInstrument [IsProbabilityMeasure μ]
    (h : M.ErrorRealization μ ε) (hΩ : M.Ω.IsDiag) {x y z : V}
    (hI : M.G.IsPretreatmentInstrument {z} {x} {y} ∅) (hzx : M.cov z x ≠ 0) :
    (M.toLinearIVModel ε x y z (M.T y x)).Exogeneity μ ∧
      (M.toLinearIVModel ε x y z (M.T y x)).Relevance μ ∧
      cov[(M.toLinearIVModel ε x y z (M.T y x)).Z, (M.toLinearIVModel ε x y z (M.T y x)).Y; μ] /
          cov[(M.toLinearIVModel ε x y z (M.T y x)).Z,
            (M.toLinearIVModel ε x y z (M.T y x)).D; μ] = M.T y x :=
  ⟨(h.toLinearIVModel_exogeneity_iff x y z _).2
      (M.cov_eq_T_mul_cov_of_isPretreatmentInstrument hΩ hI),
    (h.toLinearIVModel_relevance_iff x y z _).2 hzx,
    (h.toLinearIVModel_covRatio x y z _).trans
      (M.cov_div_cov_eq_T_of_isPretreatmentInstrument hΩ hI hzx)⟩

/-! ### An instrument affected by the treatment -/

namespace DescendantInstrumentModel

open CausalInference.InstrumentExamples Criteria

/-- The linear model on `descendantInstrument` (`X = 0`, `Z = 1`, `Y = 2`, `U = 3`):
`X = U + ε_X`, `Z = X + ε_Z`, `Y = U + ε_Y`, with uncorrelated unit errors. `X` has no effect
on `Y`. -/
def model : LinearSEM (Fin 4) where
  G := descendantInstrument
  acyclic := by decide +kernel
  B := !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]
  B_support v u h := by
    fin_cases v <;> fin_cases u <;> simp_all [descendantInstrument, ofEdges]
  Ω := 1
  Ω_posSemidef := Matrix.PosSemidef.one

theorem T_eq : model.T = !![1, 0, 0, 1; 1, 1, 0, 1; 0, 0, 1, 1; 0, 0, 0, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]

/-- Dropping "pretreatment" breaks the moment condition: in `model`, the errors are
uncorrelated, `Y ≠ X`, `Z` and `Y` are d-separated in the graph with the edges into `X`
removed, and `Z` passes the graphical test within the setting of Definition 7.4.1; only the
requirement that `Z` is not a descendant of `X` fails. The covariances are `Σ z y = 1` and
`Σ z x = 2`, the total effect is `T y x = 0`, so `Σ z y ≠ T y x Σ z x` and the instrumental
ratio is `1/2` for a zero effect. -/
theorem counterexample :
    model.Ω.IsDiag ∧ (2 : Fin 4) ≠ 0 ∧
      (model.G.deleteIncoming {0}).DSep {1} {2} ∅ ∧
      model.G.IsInstrumentIn {1} {0} {2} ∅ ∧ (1 : Fin 4) ∈ model.G.descendantsOf {0} ∧
      model.cov 1 2 = 1 ∧ model.cov 1 0 = 2 ∧ model.T 2 0 = 0 ∧
      model.cov 1 2 ≠ model.T 2 0 * model.cov 1 0 := by
  have hC : ∀ i j, model.cov i j = ∑ a, (!![1, 0, 0, 1; 1, 1, 0, 1; 0, 0, 1, 1; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) ℝ) i a * (!![1, 0, 0, 1; 1, 1, 0, 1; 0, 0, 1, 1; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) ℝ) j a := by
    intro i j
    rw [cov_apply, T_eq]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [model, Matrix.one_apply]
  have h12 : model.cov 1 2 = 1 := by rw [hC]; simp [Fin.sum_univ_four]
  have h10 : model.cov 1 0 = 2 := by rw [hC]; simp [Fin.sum_univ_four]; norm_num
  have hT : model.T 2 0 = 0 := by rw [T_eq]; simp
  refine ⟨Matrix.isDiag_one, by decide, (descendantInstrument_test.1).2.2.1,
    descendantInstrument_test.1, descendantInstrument_test.2.1, h12, h10, hT, ?_⟩
  rw [h12, h10, hT]
  norm_num

end DescendantInstrumentModel

end LinearSEM

end CausalInference
