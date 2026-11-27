/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDFailure
public import CausalInference.Identification.IDFigure38

/-!
# Failure witnesses on the example graphs

The structural reading of failure (`idAlg_eq_none_iff`) on the example graphs: the bow graph has
a failure witness, and the graphs on which the algorithm succeeds have none.

## Main results

* `IDFailureExamples.bow_failure`: the bow graph has a failure witness.
* `IDFailureExamples.frontDoor_no_failure`, `IDFailureExamples.backDoor_no_failure`,
  `IDFailureExamples.fig38_no_failure`: the other three example graphs have none.
-/

@[expose] public section

namespace CausalInference

namespace IDFailureExamples

open Finset IDExamples IDFigure38

/-- The bow graph has a failure witness: a district of the ancestors of `Y` with a single
district `T ⊋ d` in which every vertex is an ancestor of `d` (namely `d = {Y}`, `T = {X, Y}`). -/
theorem bow_failure : ∃ d ∈ bowH.districtsOn (ancIn bowH ({1, 2} \ {1}) {2}),
    ∃ T ⊆ ({1, 2} : Finset (Fin 3)), IsIdFailure bowH d T :=
  (idAlg_eq_none_iff ordFin ⟨by decide, by decide⟩).1 bow_idAlg

/-- The front-door graph has no failure witness. -/
theorem frontDoor_no_failure : ¬ ∃ d ∈ fdH.districtsOn (ancIn fdH ({0, 1, 2} \ {0}) {2}),
    ∃ T ⊆ ({0, 1, 2} : Finset (Fin 4)), IsIdFailure fdH d T := by
  rw [← idAlg_eq_none_iff ordFin ⟨by decide, by decide⟩]
  obtain ⟨e, he, -⟩ := frontDoor_idAlg
  simp [he]

/-- The back-door graph has no failure witness. -/
theorem backDoor_no_failure : ¬ ∃ d ∈ bdH.districtsOn (ancIn bdH ({0, 1, 2} \ {1}) {2}),
    ∃ T ⊆ ({0, 1, 2} : Finset (Fin 3)), IsIdFailure bdH d T := by
  rw [← idAlg_eq_none_iff ordFin ⟨by decide, by decide⟩]
  obtain ⟨e, he, -⟩ := backDoor_idAlg
  simp [he]

/-- The graph of Figure 3.8(f) has no failure witness. -/
theorem fig38_no_failure : ¬ ∃ d ∈ fig38H.districtsOn (ancIn fig38H (obs \ {0}) {3}),
    ∃ T ⊆ obs, IsIdFailure fig38H d T := by
  rw [← idAlg_eq_none_iff ordFin ⟨by decide, by decide⟩]
  obtain ⟨e, he, -⟩ := fig38_idAlg
  simp [he]

end IDFailureExamples

end CausalInference
