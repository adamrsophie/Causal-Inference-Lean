/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.DSeparationDecide

/-!
# d-separation on concrete graphs

Separation and connection statements on small graphs over `Fin n`, each checked by `decide`
through the decision procedure of `CausalInference.Graphical.DSeparationDecide`: the chain, the
fork and the collider (reused from `CausalInference.Graphical.Acyclic`), a collider with a
descendant, the M-structure, a back-door confounding graph, the front-door graph, the
instrumental-variable graph, and a six-vertex graph with less obvious answers.

See Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 1.2.3.
-/

@[expose] public section

namespace CausalInference.DSeparationExamples

open GraphExamples

/-! ### Chain, fork, collider -/

-- The chain `0 → 1 → 2`: open marginally, blocked by the middle vertex.
example : ¬ chain.DSep {0} {2} ∅ := by decide
example : chain.DSep {0} {2} {1} := by decide

-- The fork `1 ← 0 → 2`: open marginally, blocked by the common cause.
example : ¬ fork.DSep {1} {2} ∅ := by decide
example : fork.DSep {1} {2} {0} := by decide

-- The collider `0 → 2 ← 1`: blocked marginally, opened by conditioning on the collider.
example : collider.DSep {0} {1} ∅ := by decide
example : ¬ collider.DSep {0} {1} {2} := by decide

/-- The collider `0 → 2 ← 1` with a descendant `2 → 3` of the collider. -/
def colliderDesc : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ({(0, 2), (1, 2), (2, 3)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel colliderDesc.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

-- Conditioning on a descendant of the collider opens the path.
example : colliderDesc.DSep {0} {1} ∅ := by decide
example : ¬ colliderDesc.DSep {0} {1} {3} := by decide
example : ¬ colliderDesc.DSep {0} {1} {2} := by decide

-- The conventions for overlapping sets: an endpoint in the conditioning set is blocked, and a
-- shared vertex outside it connects.
example : chain.DSep {0} {0} {0} := by decide
example : ¬ chain.DSep {0} {0} ∅ := by decide
example : chain.DSep {0, 1} {1, 2} {1} := by decide

/-! ### The M-structure -/

/-- The M-structure `X ← U₁ → M ← U₂ → Y` with `X = 0`, `U₁ = 1`, `M = 2`, `U₂ = 3`, `Y = 4`. -/
def mStructure : Digraph (Fin 5) where
  Adj i j := (i, j) ∈ ({(1, 0), (1, 2), (3, 2), (3, 4)} : Finset (Fin 5 × Fin 5))

instance : DecidableRel mStructure.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

-- `X` and `Y` are marginally d-separated; conditioning on the collider `M` connects them, and
-- additionally conditioning on `U₁` blocks again.
example : mStructure.DSep {0} {4} ∅ := by decide
example : ¬ mStructure.DSep {0} {4} {2} := by decide
example : mStructure.DSep {0} {4} {1, 2} := by decide
example : mStructure.DSep {0} {4} {2, 3} := by decide

/-! ### Back-door confounding -/

/-- Confounding by `Z`: `Z → X`, `Z → Y`, `X → Y` with `Z = 0`, `X = 1`, `Y = 2`. -/
def backdoor : Digraph (Fin 3) where
  Adj i j := (i, j) ∈ ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3))

instance : DecidableRel backdoor.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

-- After removing the edges out of `X`, the back-door path `X ← Z → Y` is open marginally and
-- blocked by `Z`, as the back-door criterion requires.
example : ¬ (backdoor.deleteOutgoing {1}).DSep {1} {2} ∅ := by decide
example : (backdoor.deleteOutgoing {1}).DSep {1} {2} {0} := by decide
-- In the full graph the direct edge keeps `X` and `Y` connected.
example : ¬ backdoor.DSep {1} {2} {0} := by decide

/-! ### The front-door graph -/

/-- The front-door graph `X → M → Y` with a latent confounder `U → X`, `U → Y`, where `U = 0`,
`X = 1`, `M = 2`, `Y = 3`. -/
def frontdoor : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ({(0, 1), (0, 3), (1, 2), (2, 3)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel frontdoor.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

-- No back-door path from `X` to `M`.
example : (frontdoor.deleteOutgoing {1}).DSep {1} {2} ∅ := by decide
-- The back-door path `M ← X ← U → Y` from `M` to `Y` is open, and `X` blocks it.
example : ¬ (frontdoor.deleteOutgoing {2}).DSep {2} {3} ∅ := by decide
example : (frontdoor.deleteOutgoing {2}).DSep {2} {3} {1} := by decide
-- `X` and `Y` are confounded: the back-door path through `U` cannot be blocked by observed
-- variables other than `U`.
example : ¬ (frontdoor.deleteOutgoing {1}).DSep {1} {3} {2} := by decide
example : (frontdoor.deleteOutgoing {1}).DSep {1} {3} {0} := by decide

/-! ### The instrumental-variable graph -/

/-- The instrumental-variable graph `Z → X → Y` with a latent confounder `U → X`, `U → Y`, where
`Z = 0`, `X = 1`, `Y = 2`, `U = 3`. -/
def instrument : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ({(0, 1), (1, 2), (3, 1), (3, 2)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel instrument.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

-- Relevance: the instrument is connected to the treatment.
example : ¬ instrument.DSep {0} {1} ∅ := by decide
-- Independence: the instrument is d-separated from the confounder.
example : instrument.DSep {0} {3} ∅ := by decide
-- Exclusion: with the edges out of `X` removed, the instrument is d-separated from `Y`.
example : (instrument.deleteOutgoing {1}).DSep {0} {2} ∅ := by decide
-- Conditioning on the treatment, a collider between `Z` and `U`, connects them, so `Z` and `Y`
-- become connected given `X` even without the edge `X → Y`.
example : ¬ instrument.DSep {0} {3} {1} := by decide
example : ¬ (instrument.deleteOutgoing {1}).DSep {0} {2} {1} := by decide

/-! ### A six-vertex graph -/

/-- A six-vertex graph with edges `0 → 1`, `2 → 1`, `1 → 3`, `3 → 4`, `2 → 5`, `5 → 4`,
`0 → 5`. -/
def six : Digraph (Fin 6) where
  Adj i j := (i, j) ∈
    ({(0, 1), (2, 1), (1, 3), (3, 4), (2, 5), (5, 4), (0, 5)} : Finset (Fin 6 × Fin 6))

instance : DecidableRel six.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

example : six.IsAcyclic := by decide
-- `0` and `2` share only the colliders `1`, `5` and `4`.
example : six.DSep {0} {2} ∅ := by decide
-- Conditioning on `3`, a descendant of the collider `1`, connects `0` and `2`.
example : ¬ six.DSep {0} {2} {3} := by decide
-- `{3, 5}` separates `0` from `4`, although conditioning on `5` opens the collider `0 → 5 ← 2`
-- and `3` is a descendant of the collider `1`: every resulting trail runs through `3` or `5`
-- as a non-collider.
example : six.DSep {0} {4} {3, 5} := by decide
example : ¬ six.DSep {0} {4} {3} := by decide
-- `{0, 2}` separates `1` from `5`; adding the common descendant `4` connects them through
-- `1 → 3 → 4 ← 5`.
example : six.DSep {1} {5} {0, 2} := by decide
example : six.DSep {1} {5} {0, 2, 3} := by decide
example : ¬ six.DSep {1} {5} {0, 2, 4} := by decide
-- The local Markov statement at `3`: its parent `1` separates it from its non-descendants.
example : six.DSep {3} {0, 2, 5} {1} := by decide

end CausalInference.DSeparationExamples
