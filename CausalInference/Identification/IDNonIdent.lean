/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDFailure
public import CausalInference.Identification.QModels

/-!
# Tools for non-identifiability

Two facts toward a completeness theorem for the identification algorithm; the completeness
theorem itself is not proved here.

* `isIdFailure_not_disjoint`: a failure witness `T` of a district `d` returned by
  `idAlg_eq_none_iff` meets the intervened set `X`, while `d` does not. This is the property of
  the hedges of Shpitser and Pearl (2006), whose larger forest meets `X` and whose smaller one
  does not.
* `QModel.not_identifiableFrom_of_qmarg_eq`: a certificate for non-identifiability. Two Boolean
  models with rational kernels on the same DAG whose rational observed marginals agree and whose
  rational effects differ show that the effect is not identifiable in the class of models with
  strictly positive observed law. Equality of the observed laws is checked through the marginal
  masses `margAt O w`, which `FiniteDist.marginal_eq_of_margAt_eq` turns into equality of the
  marginal laws.
* `IDNonIdentBow.bow_not_identifiableFrom`: the bow graph through the certificate.
-/

@[expose] public section

namespace CausalInference

open Finset

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {H : ADMG V}

/-- The ancestral closure inside `A` is transitive: ancestors of a set of ancestors of `Y` are
ancestors of `Y`. -/
theorem ancIn_subset_of_subset [DecidableRel H.directed.Adj] {A C Y : Finset V}
    (hC : C ⊆ ancIn H A Y) : ancIn H A C ⊆ ancIn H A Y := by
  intro u hu
  obtain ⟨hu, huA⟩ := mem_inter.1 hu
  obtain ⟨s, hs, hp⟩ := ADMG.mem_ancestorsOfFinset.1 hu
  obtain ⟨y, hy, hq⟩ := ADMG.mem_ancestorsOfFinset.1 (mem_inter.1 (hC hs)).1
  exact mem_inter.2 ⟨ADMG.mem_ancestorsOfFinset.2 ⟨y, hy, hp.trans hq⟩, huA⟩

/-- **A failure witness meets the intervened set.** If `d` is a district of `H` restricted to
the ancestors `D` of `Y` inside `O \ X`, and `T ⊆ O` is a failure witness for `d`, then `T`
meets `X`, while `d` is disjoint from `X`. If `T` avoided `X`, every vertex of `T` would be an
ancestor of `Y` inside `O \ X`, so `T ⊆ D`, and `T`, being bidirected-connected and containing
`d`, would lie in the district `d`. -/
theorem isIdFailure_not_disjoint [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
    {O X Y d T : Finset V} (hd : d ∈ H.districtsOn (ancIn H (O \ X) Y)) (hTO : T ⊆ O)
    (hf : IsIdFailure H d T) : ¬ Disjoint T X ∧ Disjoint d X := by
  have hdD : d ⊆ ancIn H (O \ X) Y := ADMG.subset_of_mem_districtsOn hd
  refine ⟨fun hdisj => ?_, disjoint_left.2 fun v hv hvX =>
    (mem_sdiff.1 (ancIn_subset _ _ (hdD hv))).2 hvX⟩
  have hTOX : T ⊆ O \ X := fun t ht => mem_sdiff.2 ⟨hTO ht, disjoint_left.1 hdisj ht⟩
  have hTD : T ⊆ ancIn H (O \ X) Y :=
    (subset_ancIn_of_ancestral hTOX hf.ancestral).trans (ancIn_subset_of_subset hdD)
  obtain ⟨v, -, rfl⟩ := ADMG.mem_districtsOn.1 hd
  have hvT : v ∈ T := hf.ssubset.subset (ADMG.mem_districtFinset.2 (ADMG.mem_district_self v))
  have hsub : T ⊆ (H.restrict ↑(ancIn H (O \ X) Y)).districtFinset v := fun t ht =>
    ADMG.mem_districtFinset.2 (reachable_restrict_mono hTD (hf.connected v hvT t ht))
  exact not_subset_of_ssubset hf.ssubset hsub

end Graph

/-- Two laws of Boolean configurations with the same marginal masses on `O` at every
configuration have the same marginal law on `O`. -/
theorem FiniteDist.marginal_eq_of_margAt_eq {n : ℕ} {p q : FiniteDist (Fin n → Bool)}
    {O : Finset (Fin n)} (h : ∀ w, p.margAt O w = q.margAt O w) :
    p.marginal O = q.marginal O := by
  ext z
  have hz : O.restrict (fun v => if hv : v ∈ O then z ⟨v, hv⟩ else false) = z := by
    funext u
    simp [Finset.restrict]
  rw [← hz, FiniteDist.marginal_restrict, FiniteDist.marginal_restrict, h]

namespace QModel

variable {n : ℕ} {G : Digraph (Fin n)} [DecidableRel G.Adj]

/-- **Certificate for non-identifiability.** Two Boolean models with rational kernels (each
success probability strictly between `0` and `1`) on the same acyclic DAG `G`, with equal
rational marginal masses on `O` and different rational effects, show that the effect
`P(Y = y_Y | do(X := x_X))` is not identifiable from the observed law within the class of
models on `G` whose observed law is strictly positive. -/
theorem not_identifiableFrom_of_qmarg_eq {θ₁ θ₂ : Fin n → (Fin n → Bool) → ℚ}
    (hθ₁ : ∀ v x, 0 < θ₁ v x ∧ θ₁ v x < 1) (hθ₂ : ∀ v x, 0 < θ₂ v x ∧ θ₂ v x < 1)
    (hG : G.IsAcyclic) {O : Finset (Fin n)} (hobs : ∀ w, qmarg G θ₁ O w = qmarg G θ₂ O w)
    {X Y : Finset (Fin n)} {x y : Fin n → Bool}
    (hne : qeffect G θ₁ X x Y y ≠ qeffect G θ₂ X x Y y) :
    ¬ SCM.IdentifiableFrom {m : SCM.Model G (fun _ => Bool) | ∀ w, 0 < m.scm.dist.margAt O w} O
      (fun m => m.scm.effect X x Y y) := by
  intro h
  have := h ⟨_, model G θ₁ hθ₁ hG⟩ (fun w => margAt_model_pos G θ₁ hθ₁ hG O w)
    ⟨_, model G θ₂ hθ₂ hG⟩ (fun w => margAt_model_pos G θ₂ hθ₂ hG O w)
    (FiniteDist.marginal_eq_of_margAt_eq fun w => by
      rw [margAt_model, margAt_model, hobs])
  simp only [effect_model] at this
  exact hne (by exact_mod_cast this)

end QModel

namespace IDNonIdentBow

open QModel SCM.BowExample

/-- Model A on the bow DAG (`U = 0`, `X = 1`, `Y = 2`): `U` a fair bit,
`P(X = 1 | u) = 3/4` or `1/4`, and `P(Y = 1 | x, u) = 3/4` or `1/4` according to `u` only. -/
def θA (v : Fin 3) (x : Fin 3 → Bool) : ℚ :=
  if v = 0 then 1 / 2 else if x 0 then 3 / 4 else 1 / 4

/-- Model B on the bow DAG: the same `U` and `X`, and `P(Y = 1 | x, u) = 5/8` or `3/8`
according to `x` only. -/
def θB (v : Fin 3) (x : Fin 3 → Bool) : ℚ :=
  if v = 0 then 1 / 2 else if v = 1 then (if x 0 then 3 / 4 else 1 / 4)
  else if x 1 then 5 / 8 else 3 / 8

/-- **The bow through the certificate**: models A and B have the same observed law of `(X, Y)`
and the effects `1/2` and `5/8`, so by `QModel.not_identifiableFrom_of_qmarg_eq` the effect is
not identifiable in the class of `SCM.BowExample.not_identifiableFrom_effect`. -/
theorem bow_not_identifiableFrom :
    ¬ SCM.IdentifiableFrom
      {m : SCM.Model bow (fun _ => Bool) | ∀ w, 0 < m.scm.dist.margAt {1, 2} w} {1, 2}
      (fun m => m.scm.effect {1} treat {2} treat) :=
  not_identifiableFrom_of_qmarg_eq (θ₁ := θA) (θ₂ := θB) (by decide +kernel) (by decide +kernel)
    bow_isAcyclic (by decide +kernel) (by decide +kernel)

end IDNonIdentBow

end CausalInference
