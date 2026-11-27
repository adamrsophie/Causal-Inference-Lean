/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDExpr

/-!
# The identification algorithm

The identification algorithm for causal effects in the form of Tian (2002) and Tian and Pearl
(2002), on a finite acyclic directed mixed graph `H` with an observed set `O` (the vertices
outside `O` are isolated in `H`, as in a latent projection). It takes sets `X` and `Y` of
observed vertices and returns either an expression `e : IdExpr V` in the observed law or
failure (`none`). The order `ord : V → ℕ` is a parameter; the soundness theorem asks it to be
a topological order of `H` injective on `O`.

The recursion is on pairs `C ⊆ T` together with an expression `q` for the c-factor `Q[T]`:

* `identify C T q`: let `A` be the ancestral closure of `C` in `H` restricted to `T`.
  If `A = C`, return `∑_{T \ C} q`. If `A ⊂ T`, let `T'` be the union of the districts of `H`
  restricted to `A` that meet `C`; compute an expression for `Q[A]` (the sum of `q` over
  `T \ A`) and from it one for `Q[T']` by Tian's formula (`tianExpr`), and recurse on `C ⊆ T'`.
  Otherwise (`A = T` and `C ≠ T`) fail.
* `idAlg H ord O X Y`: with `D` the ancestral closure of `Y` in `H` restricted to `O \ X`, for
  every district `d` of `H` restricted to `D` let `T_d` be the union of the districts of `H`
  restricted to `O` that meet `d`, and run `identify d T_d` from Tian's formula for `Q[T_d]` in
  the observed law. If every call succeeds, return `∑_{D \ Y} ∏_d e_d`.

The algorithm is Tian's version of the identification algorithm (Tian 2002; Tian and Pearl
2002). Shpitser and Pearl (2006) give a related formulation, the ID algorithm. Only soundness
is proved here; completeness is not. The recursion follows Tian's. Termination: the set `T`
strictly decreases.

## Main definitions

* `ancIn H T C`, `closeIn H A C`: the ancestral closure of `C` inside `T`, and the union of the
  districts inside `A` meeting `C`.
* `tianExpr ord A S q`: Tian's formula `∏_{v ∈ S} (∑_{A \ A^{≤v}} q) / (∑_{A \ A^{<v}} q)`.
* `identify`, `idPart`, `idAlg`: the algorithm.

## Main results

* Unfolding lemmas `identify_of_eq`, `identify_of_ssubset`, `identify_of_not`, `idAlg_eq_some`,
  `idAlg_eq_none`, used to run the algorithm on examples with `decide`.
* Structural facts about `ancIn` and `closeIn` used by the soundness proof.
* `idAlg_margWithin`: every expression returned uses only marginals on subsets of `O`.
-/

@[expose] public section

namespace CausalInference

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ancestral closure of `C` inside `T`: the vertices of `T` from which a directed path of
`H` inside `T` reaches `C`. -/
def ancIn (H : ADMG V) [DecidableRel H.directed.Adj] (T C : Finset V) : Finset V :=
  (H.restrict ↑T).ancestorsOfFinset C ∩ T

/-- The union of the districts of `H` restricted to `A` that meet `C`. -/
def closeIn (H : ADMG V) [DecidableRel H.bidirected.Adj] (A C : Finset V) : Finset V :=
  C.biUnion (H.restrict ↑A).districtFinset ∩ A

/-- Tian's formula as an expression: from an expression `q` for `Q[A]`, the product over
`v ∈ S` of `(∑_{A \ A^{≤v}} q) / (∑_{A \ A^{<v}} q)`, where `A^{≤v}` and `A^{<v}` are the
vertices of `A` up to `v` and before `v` in the order `ord`. -/
def tianExpr (ord : V → ℕ) (A S : Finset V) (q : IdExpr V) : IdExpr V :=
  .prodV S fun v => .div (.sum (A \ A.filter fun u => ord u ≤ ord v) q)
    (.sum (A \ A.filter fun u => ord u < ord v) q)

/-- The recursive step of the identification algorithm (Tian 2002): from an expression `q` for
`Q[T]`, an expression for `Q[C]`, or failure. -/
def identify (H : ADMG V) [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
    (ord : V → ℕ) (C T : Finset V) (q : IdExpr V) : Option (IdExpr V) :=
  if ancIn H T C = C then some (.sum (T \ C) q)
  else if _h : ancIn H T C ⊂ T then
    identify H ord C (closeIn H (ancIn H T C) C)
      (tianExpr ord (ancIn H T C) (closeIn H (ancIn H T C) C) (.sum (T \ ancIn H T C) q))
  else none
termination_by T.card
decreasing_by
  exact lt_of_le_of_lt (card_le_card inter_subset_right) (card_lt_card _h)

/-- The call of `identify` for a district `d`: from Tian's formula for `Q[T_d]` in the observed
law, where `T_d` is the union of the districts of `H` restricted to `O` meeting `d`. -/
def idPart (H : ADMG V) [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
    (ord : V → ℕ) (O d : Finset V) : Option (IdExpr V) :=
  identify H ord d (closeIn H O d) (tianExpr ord O (closeIn H O d) (.marg O))

/-- The identification algorithm (Tian's version): for observed sets `X` and `Y` (disjoint),
an expression for `P(y | do(x))` in the observed law, or failure. -/
def idAlg (H : ADMG V) [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
    (ord : V → ℕ) (O X Y : Finset V) : Option (IdExpr V) :=
  if X ⊆ O ∧ Y ⊆ O \ X then
    if ∀ d ∈ H.districtsOn (ancIn H (O \ X) Y), (idPart H ord O d).isSome then
      some (.sum (ancIn H (O \ X) Y \ Y)
        (.prodSets (H.districtsOn (ancIn H (O \ X) Y))
          fun d => (idPart H ord O d).getD (.marg ∅)))
    else none
  else none

section Unfold

variable (H : ADMG V) [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
  (ord : V → ℕ) {C T : Finset V} (q : IdExpr V)

/-- Unfolding `identify` when the ancestral closure of `C` inside `T` is `C`. -/
theorem identify_of_eq (h : ancIn H T C = C) :
    identify H ord C T q = some (.sum (T \ C) q) := by
  rw [identify, ite_eq_left h]

/-- Unfolding `identify` in the recursive case. -/
theorem identify_of_ssubset (h₁ : ancIn H T C ≠ C) (h₂ : ancIn H T C ⊂ T) :
    identify H ord C T q = identify H ord C (closeIn H (ancIn H T C) C)
      (tianExpr ord (ancIn H T C) (closeIn H (ancIn H T C) C) (.sum (T \ ancIn H T C) q)) := by
  rw [identify, ite_eq_right h₁, dite_eq_left h₂]

/-- Unfolding `identify` in the failure case. -/
theorem identify_of_not (h₁ : ancIn H T C ≠ C) (h₂ : ¬ ancIn H T C ⊂ T) :
    identify H ord C T q = none := by
  rw [identify, ite_eq_right h₁, dite_eq_right h₂]

variable {O X Y : Finset V}

/-- Unfolding `idAlg` when every district call succeeds. -/
theorem idAlg_eq_some (h₁ : X ⊆ O ∧ Y ⊆ O \ X)
    (h₂ : ∀ d ∈ H.districtsOn (ancIn H (O \ X) Y), (idPart H ord O d).isSome) :
    idAlg H ord O X Y = some (.sum (ancIn H (O \ X) Y \ Y)
        (.prodSets (H.districtsOn (ancIn H (O \ X) Y))
          fun d => (idPart H ord O d).getD (.marg ∅))) := by
  rw [idAlg, ite_eq_left h₁, ite_eq_left h₂]

/-- `idAlg` fails as soon as one district call fails. -/
theorem idAlg_eq_none {d : Finset V} (hd : d ∈ H.districtsOn (ancIn H (O \ X) Y))
    (hnone : idPart H ord O d = none) : idAlg H ord O X Y = none := by
  rw [idAlg]
  split_ifs with h₁ h₂
  · exact absurd (h₂ d hd) (by simp [hnone])
  · rfl
  · rfl

end Unfold

/-! ### Structural facts -/

section Facts

variable {H : ADMG V}

/-- The ancestral closure inside `T` is a subset of `T`. -/
theorem ancIn_subset [DecidableRel H.directed.Adj] (T C : Finset V) : ancIn H T C ⊆ T :=
  inter_subset_right

/-- The ancestral closure of `C ⊆ T` inside `T` contains `C`. -/
theorem subset_ancIn [DecidableRel H.directed.Adj] {T C : Finset V} (hC : C ⊆ T) :
    C ⊆ ancIn H T C := fun c hc =>
  mem_inter.2 ⟨ADMG.mem_ancestorsOfFinset.2 ⟨c, hc, Relation.ReflTransGen.refl⟩, hC hc⟩

/-- The ancestral closure inside `T` is closed under the parents that lie in `T`. -/
theorem ancIn_closed [DecidableRel H.directed.Adj] {T C : Finset V} {u v : V} (hu : u ∈ T)
    (hv : v ∈ ancIn H T C) (huv : H.directed.Adj u v) : u ∈ ancIn H T C := by
  obtain ⟨hv, hvT⟩ := mem_inter.1 hv
  obtain ⟨s, hs, hp⟩ := ADMG.mem_ancestorsOfFinset.1 hv
  refine mem_inter.2 ⟨ADMG.mem_ancestorsOfFinset.2 ⟨s, hs, Relation.ReflTransGen.head ?_ hp⟩, hu⟩
  exact ⟨huv, hu, hvT⟩

/-- The union of the districts inside `A` meeting `C` is a subset of `A`. -/
theorem closeIn_subset [DecidableRel H.bidirected.Adj] (A C : Finset V) : closeIn H A C ⊆ A :=
  inter_subset_right

/-- The union of the districts inside `A` meeting `C ⊆ A` contains `C`. -/
theorem subset_closeIn [DecidableRel H.bidirected.Adj] {A C : Finset V} (hC : C ⊆ A) :
    C ⊆ closeIn H A C := fun c hc =>
  mem_inter.2 ⟨mem_biUnion.2 ⟨c, hc, ADMG.mem_districtFinset.2 (ADMG.mem_district_self c)⟩,
    hC hc⟩

/-- The union of the districts inside `A` meeting `C` is closed under the bidirected edges
inside `A`. -/
theorem closeIn_closed [DecidableRel H.bidirected.Adj] {A C : Finset V} {u v : V}
    (hu : u ∈ closeIn H A C) (hv : v ∈ A) (huv : H.bidirected.Adj u v) : v ∈ closeIn H A C := by
  obtain ⟨hu, huA⟩ := mem_inter.1 hu
  obtain ⟨c, hc, hcu⟩ := mem_biUnion.1 hu
  refine mem_inter.2 ⟨mem_biUnion.2 ⟨c, hc, ADMG.mem_districtFinset.2 ?_⟩, hv⟩
  exact (ADMG.mem_districtFinset.1 hcu).trans (SimpleGraph.Adj.reachable ⟨huv, huA, hv⟩)

end Facts

/-! ### The returned expressions use only observed marginals -/

omit [Fintype V] in
/-- Tian's formula uses only the marginals used by `q`. -/
theorem tianExpr_margWithin {O : Finset V} (ord : V → ℕ) (A S : Finset V) {q : IdExpr V}
    (hq : q.MargWithin O) : (tianExpr ord A S q).MargWithin O :=
  fun _ _ => ⟨hq, hq⟩

/-- The expression returned by `identify` uses only marginals on subsets of `O` when `q`
does. -/
theorem identify_margWithin (H : ADMG V) [DecidableRel H.directed.Adj]
    [DecidableRel H.bidirected.Adj] (ord : V → ℕ) {O : Finset V} :
    ∀ (T C : Finset V) (q e : IdExpr V), q.MargWithin O → identify H ord C T q = some e →
      e.MargWithin O := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro C q e hq he
    rw [identify] at he
    split_ifs at he with h₁ h₂
    · cases he
      exact hq
    · exact ih _ ((closeIn_subset _ _).trans_ssubset h₂) C _ e
        (tianExpr_margWithin (q := .sum (T \ ancIn H T C) q) ord _ _ hq) he

/-- **The algorithm uses only the observed law**: every expression returned by `idAlg` uses
only marginals on subsets of `O`. -/
theorem idAlg_margWithin (H : ADMG V) [DecidableRel H.directed.Adj]
    [DecidableRel H.bidirected.Adj] (ord : V → ℕ) {O X Y : Finset V} {e : IdExpr V}
    (he : idAlg H ord O X Y = some e) : e.MargWithin O := by
  rw [idAlg] at he
  split_ifs at he with h₁ h₂
  cases he
  intro d _
  cases hd : idPart H ord O d with
  | none =>
    simp only [hd, Option.getD_none]
    exact empty_subset O
  | some e' =>
    simp only [hd, Option.getD_some]
    exact identify_margWithin H ord _ d _ e'
      (tianExpr_margWithin (q := .marg O) ord O _ (subset_refl O)) hd

end CausalInference
