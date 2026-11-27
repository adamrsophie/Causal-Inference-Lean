/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Interaction.Synergism

/-!
# Sufficient-component causes

The sufficient-component-cause model for binary treatments and a binary outcome (Hernán and
Robins, *Causal Inference: What If* (2020), Sections 5.4 and 5.5, Fine Point 5.2, Technical
Point 5.3; Rothman 1976; Greenland and Poole 1988; VanderWeele and Robins 2007, 2008).

One treatment: `Y^a = U0 ∨ (a ∧ U1) ∨ (¬a ∧ U2)`. Two treatments: nine sufficient causes,
listed in Section 5.4 as: by `A = 1`; by `A = 0`; by `E = 1`; by `E = 0`; by `A = 1` and
`E = 1`; by `A = 1` and `E = 0`; by `A = 0` and `E = 1`; by `A = 0` and `E = 0`; by other
mechanisms. We attach background factors `U1, ..., U8` to the first eight in that order and
`U0` to the last, so that
`Y^{a,e} = U0 ∨ (a∧U1) ∨ (¬a∧U2) ∨ (e∧U3) ∨ (¬e∧U4) ∨ (a∧e∧U5) ∨ (a∧¬e∧U6) ∨ (¬a∧e∧U7) ∨
(¬a∧¬e∧U8)`. The text confirms the roles of `U0`, `U1`, `U2`, `U3` and `U5`; the labels of
`U4` and `U6` to `U8` follow the order of the list (the labels in Figure 5.2 are not available
to us), and no result depends on that choice of labels.

## Main definitions

* `OneSufficientCauses`, `OneSufficientCauses.response`: the one-treatment model.
* `SufficientCauses`, `SufficientCauses.response`: the nine-cause two-treatment model.
* `SufficientCauses.HasSynergism`: `A = 1` and `E = 1` occur together in a present sufficient
  cause (`U5 = 1`), the sufficient cause interaction of Section 5.5.
* `SufficientCauses.NoNegativeComponent`: no present sufficient cause contains `A = 0` or
  `E = 0`.

## Main results

* `OneSufficientCauses.response_eq_iff`: the table of Fine Point 5.2.
* `OneSufficientCauses.response_surjective`, `SufficientCauses.response_surjective`: every
  response type arises from some configuration.
* `OneSufficientCauses.not_injective`, `SufficientCauses.not_injective`: a response type may
  arise from several configurations.
* `SufficientCauses.hasSynergism_of_isSynergistic`: an individual with `Y^{11} = 1` and
  `Y^{01} = Y^{10} = 0` has synergism in every sufficient-cause representation (Section 5.5).
* `Population.exists_synergism_of_risk_sub_pos`,
  `Population.exists_synergism_of_interactionContrast_pos`: the empirical tests of Fine
  Point 5.1 detect sufficient cause interaction in every representation of the population.
* `SufficientCauses.isMonotone_iff`: a response type is monotone exactly when it has a
  representation with no sufficient cause containing `A = 0` or `E = 0` (Technical Point 5.3).
* `SufficientCauses.monotone_with_negative_component`: Technical Point 5.3 cannot be read as
  "such causes are never present": a monotone individual can have a nonredundant present
  sufficient cause containing `E = 0`.
-/

@[expose] public section

namespace CausalInference

namespace Interaction

/-- A background-factor configuration for one binary treatment: `u0` completes the sufficient
cause that needs no treatment component, `u1` the one with component `A = 1`, and `u2` the one
with component `A = 0`. -/
structure OneSufficientCauses where
  /-- Background factors sufficient on their own. -/
  u0 : Bool
  /-- Background factors completing a sufficient cause with `A = 1`. -/
  u1 : Bool
  /-- Background factors completing a sufficient cause with `A = 0`. -/
  u2 : Bool
deriving DecidableEq

namespace OneSufficientCauses

/-- The counterfactual outcome `Y^a = U0 ∨ (a ∧ U1) ∨ (¬a ∧ U2)` (What If, Section 5.4). -/
def response (U : OneSufficientCauses) : Bool → Bool := fun a =>
  U.u0 || (a && U.u1) || (!a && U.u2)

/-- The table of What If, Fine Point 5.2, for one treatment (Table 5.1 types: doomed `11`,
helped `Y^0 = 1, Y^1 = 0`, hurt `Y^0 = 0, Y^1 = 1`, immune `00`). -/
theorem response_eq_iff (U : OneSufficientCauses) :
    (U.response = (fun _ => true) ↔ U.u0 = true ∨ (U.u1 = true ∧ U.u2 = true)) ∧
    (U.response = (fun a => !a) ↔ U.u0 = false ∧ U.u1 = false ∧ U.u2 = true) ∧
    (U.response = (fun a => a) ↔ U.u0 = false ∧ U.u1 = true ∧ U.u2 = false) ∧
    (U.response = (fun _ => false) ↔ U.u0 = false ∧ U.u1 = false ∧ U.u2 = false) := by
  rcases U with ⟨u0, u1, u2⟩
  revert u0 u1 u2
  decide

/-- Every one-treatment response type arises from a configuration of background factors. -/
theorem response_surjective : Function.Surjective response := fun r =>
  ⟨⟨false, r true, r false⟩, by funext a; cases a <;> simp [response]⟩

/-- A response type may arise from several configurations: `U0 = 1` alone and `U1 = U2 = 1`
both give the doomed type (What If, Fine Point 5.2). -/
theorem not_injective : ¬ Function.Injective response := fun h =>
  absurd (@h ⟨true, false, false⟩ ⟨false, true, true⟩ (by decide)) (by decide)

end OneSufficientCauses

/-- A background-factor configuration for two binary treatments: `uk = true` means the
background factors `Uk` completing the `k`th sufficient cause are present. The treatment
components are: none for `u0`; `A = 1` for `u1`; `A = 0` for `u2`; `E = 1` for `u3`; `E = 0` for
`u4`; `A = 1, E = 1` for `u5`; `A = 1, E = 0` for `u6`; `A = 0, E = 1` for `u7`;
`A = 0, E = 0` for `u8`. -/
structure SufficientCauses where
  /-- Background factors sufficient on their own. -/
  u0 : Bool := false
  /-- With `A = 1`. -/
  u1 : Bool := false
  /-- With `A = 0`. -/
  u2 : Bool := false
  /-- With `E = 1`. -/
  u3 : Bool := false
  /-- With `E = 0`. -/
  u4 : Bool := false
  /-- With `A = 1` and `E = 1`. -/
  u5 : Bool := false
  /-- With `A = 1` and `E = 0`. -/
  u6 : Bool := false
  /-- With `A = 0` and `E = 1`. -/
  u7 : Bool := false
  /-- With `A = 0` and `E = 0`. -/
  u8 : Bool := false
deriving DecidableEq

namespace SufficientCauses

/-- The response type determined by a configuration: the outcome occurs under `(a, e)` when
some present sufficient cause has all its treatment components satisfied (What If,
Section 5.4). -/
def response (U : SufficientCauses) : ResponseType := fun a e =>
  U.u0 || (a && U.u1) || (!a && U.u2) || (e && U.u3) || (!e && U.u4) || (a && e && U.u5) ||
    (a && !e && U.u6) || (!a && e && U.u7) || (!a && !e && U.u8)

/-- The configuration using only the four sufficient causes with two treatment components,
present exactly where the response type has outcome 1. -/
def ofResponse (r : ResponseType) : SufficientCauses :=
  { u5 := r true true, u6 := r true false, u7 := r false true, u8 := r false false }

/-- Every one of the 16 response types arises from some configuration (What If, Section 5.4;
Greenland and Poole, 1988). -/
theorem response_ofResponse (r : ResponseType) : (ofResponse r).response = r := by
  funext a e
  cases a <;> cases e <;> simp [response, ofResponse]

/-- The map from configurations to response types is onto. -/
theorem response_surjective : Function.Surjective response := fun r =>
  ⟨ofResponse r, response_ofResponse r⟩

/-- The map from configurations to response types is not one to one: `U0 = 1` alone and
`U1 = U2 = 1` both give type 1 (doomed). -/
theorem not_injective : ¬ Function.Injective response := fun h =>
  absurd (@h { u0 := true } { u1 := true, u2 := true } (by decide)) (by decide)

/-- Sufficient cause interaction in the form of synergism (What If, Section 5.5): `A = 1` and
`E = 1` are components of a common present sufficient cause. -/
def HasSynergism (U : SufficientCauses) : Prop := U.u5 = true

/-- Section 5.5 of What If (VanderWeele and Robins, 2007): if an individual has `Y^{11} = 1`
and `Y^{01} = Y^{10} = 0` (types 7 and 8), then every sufficient-cause representation of that
individual contains a sufficient cause with both `A = 1` and `E = 1`. -/
theorem hasSynergism_of_isSynergistic (U : SufficientCauses)
    (h : ResponseType.IsSynergistic U.response) : U.HasSynergism := by
  rcases U with ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8⟩
  obtain ⟨h11, h01, h10⟩ := h
  simp [response] at h11 h01 h10
  simp_all [HasSynergism]

/-- No present sufficient cause has a component `A = 0` or `E = 0`. -/
def NoNegativeComponent (U : SufficientCauses) : Prop :=
  U.u2 = false ∧ U.u4 = false ∧ U.u6 = false ∧ U.u7 = false ∧ U.u8 = false

/-- The configuration used for monotone types: `U0 = Y^{00}`, `U1 = Y^{10}`, `U3 = Y^{01}`,
`U5 = Y^{11}`, all other background factors absent. -/
def monoOfResponse (r : ResponseType) : SufficientCauses :=
  { u0 := r false false, u1 := r true false, u3 := r false true, u5 := r true true }

/-- Technical Point 5.3 of What If, in its exact form: a response type has monotone effects of
`A` and `E` if and only if it is the response of some configuration in which no sufficient
cause contains `A = 0` or `E = 0`. So such causes are never needed under monotonicity. -/
theorem isMonotone_iff (r : ResponseType) :
    ResponseType.IsMonotone r ↔ ∃ U : SufficientCauses, U.NoNegativeComponent ∧ U.response = r
    := by
  constructor
  · intro hm
    refine ⟨monoOfResponse r, ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    revert r
    refine ResponseType.forall_iff.2 ?_
    decide
  · rintro ⟨⟨u0, u1, u2, u3, u4, u5, u6, u7, u8⟩, ⟨h2, h4, h6, h7, h8⟩, rfl⟩
    simp only at h2 h4 h6 h7 h8
    subst h2 h4 h6 h7 h8
    revert u0 u1 u3 u5
    decide

/-- Technical Point 5.3 cannot be read as saying that sufficient causes with `A = 0` or `E = 0`
are never present under monotonicity. The configuration with `U5 = U6 = 1` has a monotone
response (type 6, `1010`: only `A` matters), contains the sufficient cause `{A = 1, E = 0}`, and
removing that cause changes the response. -/
theorem monotone_with_negative_component :
    ResponseType.IsMonotone ({ u5 := true, u6 := true } : SufficientCauses).response ∧
      ¬ ({ u5 := true, u6 := true } : SufficientCauses).NoNegativeComponent ∧
      ({ u5 := true } : SufficientCauses).response ≠
        ({ u5 := true, u6 := true } : SufficientCauses).response := by
  refine ⟨by decide, fun h => absurd h.2.2.1 (by decide), by decide⟩

end SufficientCauses

namespace Population

variable {ι : Type*} [Fintype ι] (P : Population ι)

/-- The first test of Fine Point 5.1 detects sufficient cause interaction (What If,
Section 5.5): if `p11 - p01 - p10 > 0`, then in every sufficient-cause representation
`cfg` of the population some individual of positive mass has a present sufficient cause
containing both `A = 1` and `E = 1`. -/
theorem exists_synergism_of_risk_sub_pos (cfg : ι → SufficientCauses)
    (hcfg : ∀ i, (cfg i).response = P.resp i)
    (h : 0 < P.risk true true - P.risk false true - P.risk true false) :
    ∃ i, 0 < P.weight i ∧ (cfg i).HasSynergism := by
  obtain ⟨i, hi, hs⟩ := P.exists_synergistic_of_risk_sub_pos h
  exact ⟨i, hi, (cfg i).hasSynergism_of_isSynergistic (by rw [hcfg i]; exact hs)⟩

/-- The second test of Fine Point 5.1 detects sufficient cause interaction: if every individual
of positive mass is monotone and `IC > 0`, then in every sufficient-cause representation some
individual of positive mass has a present sufficient cause containing both `A = 1` and
`E = 1`. -/
theorem exists_synergism_of_interactionContrast_pos (cfg : ι → SufficientCauses)
    (hcfg : ∀ i, (cfg i).response = P.resp i)
    (hm : ∀ i, 0 < P.weight i → ResponseType.IsMonotone (P.resp i))
    (h : 0 < P.interactionContrast) :
    ∃ i, 0 < P.weight i ∧ (cfg i).HasSynergism := by
  obtain ⟨i, hi, h8⟩ := P.exists_type8_of_interactionContrast_pos hm h
  exact ⟨i, hi, (cfg i).hasSynergism_of_isSynergistic (by rw [hcfg i]; exact h8.isSynergistic)⟩

end Population

end Interaction

end CausalInference
