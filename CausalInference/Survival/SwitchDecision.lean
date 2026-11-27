/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.FiniteCondIndep
public import CausalInference.Graphical.Criteria.BackDoor

/-!
# Confounding of the switch decision: only the decision maker's information can confound

In a trial with treatment switching, the decision to switch is taken by a clinician (or a
patient) on the basis of the information available at the time. NICE DSU TSD 24 (Bell Gorrod,
Latimer and Abrams, 2024), Section 4.1, Recommendation 6, and Section 4.2.2.1, "Variable
selection and directed acyclic graphs (DAGs)", draw two consequences: unmeasured variables are
a problem only if they were observable to the decision maker, and a value that was missing for
a patient cannot confound that patient's switch, so missingness indicators (or the last
observed value) may enter the switching model. The same section is cited for two-stage
estimation in Section 4.2.3.1.

The setting is a finite sample space with a `FiniteDist`
(`CausalInference.Basic.FiniteDistribution`), and conditional independence is
`FiniteDist.CondIndepFun`, in product form.

## Main results

* `SwitchDecision.condIndepFun_of_decision`: if the switch is `S = f(I, ε)`, a function of the
  information `I` available to the decision maker and of a noise `ε` that is jointly independent
  of the potential outcomes `Y` and of `I`, then `S` is conditionally independent of `Y` given
  `I`. Missing values are covered by letting `I` take values in `Option`, `none` meaning that
  the value was not known.
* `SwitchDecision.condIndepFun_of_decision_comp`: it suffices that the recorded data `D`
  determine the information, `I = h(D)`: then `S` is conditionally independent of `Y` given the
  recorded data. Variables that the decision maker did not know need not be recorded.

The hypothesis must be joint independence of `ε` from `(Y, I)`; independence of `ε` from `Y`
and from `I` separately is not enough (`SwitchDecision.XorExample`). And if the decision uses
information that is not recorded, the conclusion fails (`SwitchDecision.HiddenExample`).

## Figure 1 of TSD 24

`SwitchDecision.fig1a` and `SwitchDecision.fig1b` are the two DAGs of TSD 24, Figure 1 (Section
4.2.2.1), with Karnofsky score `0`, ECOG performance status `1`, switch `2` and survival `3`:
in (a) Karnofsky affects ECOG, the switch and survival, in (b) it affects only ECOG. Checked by
`decide`: in (a) `{ECOG}` fails the back-door criterion relative to (switch, survival) and
`{ECOG, Karnofsky}` meets it; in (b) `{ECOG}` meets it. So in (b) the Karnofsky score need not
be collected, as the text says.

## Source

H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24: Adjusting
survival time estimates in the presence of treatment switching: an update to TSD 16* (2024),
Section 4.1 (Recommendation 6) and Section 4.2.2.1 (Figure 1). The formal statement of the
information-set lemma is ours; the document states it in words.
-/

@[expose] public section

namespace CausalInference

namespace SwitchDecision

open Finset

section Lemma

variable {Ω β γ δ σ : Type*} [Fintype Ω] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
  [DecidableEq σ] {p : FiniteDist Ω}

/-- The noise `ε` of the switch decision is jointly independent of the potential outcomes `Y`
and the information `I`, in product form:
`P(Y = y, I = i, ε = e) = P(Y = y, I = i) * P(ε = e)`. -/
def NoiseIndep (p : FiniteDist Ω) (Y : Ω → β) (I : Ω → γ) (ε : Ω → δ) : Prop :=
  ∀ y i e, p.probOf (fun ω => Y ω = y ∧ I ω = i ∧ ε ω = e) =
    p.probOf (fun ω => Y ω = y ∧ I ω = i) * p.probOf (fun ω => ε ω = e)

/-- Only the information available to the decision maker can confound the switch (TSD 24,
Section 4.1, Recommendation 6, and Section 4.2.2.1). If the switch is `S = f(I, ε)`, where `I`
is the information available when the decision is taken and the noise `ε` is jointly
independent of the potential outcomes `Y` and of `I` (`NoiseIndep`), then `S` is
conditionally independent of `Y` given `I`. The potential outcomes `Y` may take values in any
type, for instance the pair of potential survival times with and without switching. -/
theorem condIndepFun_of_decision (Y : Ω → β) (I : Ω → γ) (ε : Ω → δ) (f : γ → δ → σ)
    (h : NoiseIndep p Y I ε) :
    p.CondIndepFun (fun ω => f (I ω) (ε ω)) Y I := by
  classical
  -- the conditional law of the switch given the information
  set q : γ → σ → ℝ := fun i s =>
    ∑ e ∈ univ.image ε, if f i e = s then p.probOf (fun ω => ε ω = e) else 0 with hq
  have h1 : ∀ s y i, p.probOf (fun ω => f (I ω) (ε ω) = s ∧ Y ω = y ∧ I ω = i) =
      q i s * p.probOf (fun ω => Y ω = y ∧ I ω = i) := by
    intro s y i
    rw [p.probOf_eq_sum ε (univ.image ε) fun ω _ => mem_image_of_mem ε (mem_univ ω), hq,
      sum_mul]
    refine sum_congr rfl fun e _ => ?_
    split_ifs with he
    · rw [mul_comm, ← h y i e]
      exact p.probOf_congr fun ω => ⟨fun h => ⟨h.1.2.1, h.1.2.2, h.2⟩,
        fun h' => ⟨⟨by rw [h'.2.1, h'.2.2]; exact he, h'.1, h'.2.1⟩, h'.2.2⟩⟩
    · rw [zero_mul]
      exact p.probOf_eq_zero fun ω h' => he (by rw [← h'.1.2.2, ← h'.2]; exact h'.1.1)
  have h2 : ∀ s i, p.probOf (fun ω => f (I ω) (ε ω) = s ∧ I ω = i) =
      q i s * p.probOf (fun ω => I ω = i) := by
    intro s i
    rw [p.probOf_eq_sum Y (univ.image Y) fun ω _ => mem_image_of_mem Y (mem_univ ω),
      p.probOf_eq_sum (P := fun ω => I ω = i) Y (univ.image Y)
        fun ω _ => mem_image_of_mem Y (mem_univ ω), mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [p.probOf_congr (Q := fun ω => Y ω = y ∧ I ω = i) fun ω => and_comm, ← h1 s y i]
    exact p.probOf_congr fun ω => ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  intro s y i
  rw [h1, h2]
  ring

omit [DecidableEq γ] in
/-- The recorded data suffice when they determine the decision maker's information. If the
switch is `S = f(I, ε)`, the information is a function `I = h(D)` of the recorded data `D`,
and `ε` is jointly independent of `Y` and `D`, then `S` is conditionally independent of the
potential outcomes `Y` given `D`. A variable that the decision maker did not know does not
enter `I`, so it need not be part of `D`. -/
theorem condIndepFun_of_decision_comp {ρ : Type*} [DecidableEq ρ] (Y : Ω → β) (D : Ω → ρ)
    (h : ρ → γ) (ε : Ω → δ) (f : γ → δ → σ) (hε : NoiseIndep p Y D ε) :
    p.CondIndepFun (fun ω => f (h (D ω)) (ε ω)) Y D := by
  classical
  exact condIndepFun_of_decision Y D ε (fun d e => f (h d) e) hε

end Lemma

/-! ### The noise must be jointly independent -/

namespace XorExample

/-- The sample space: a point is `(y, i)`, the potential outcome and the information. -/
abbrev Ω := Bool × Bool

/-- `Y` and `I` are independent fair bits. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform

/-- The potential outcome. -/
def Y (ω : Ω) : Bool := ω.1

/-- The information available to the decision maker. -/
def I (ω : Ω) : Bool := ω.2

/-- The noise of the decision: the exclusive or of `Y` and `I`. -/
def ε (ω : Ω) : Bool := xor ω.1 ω.2

/-- The noise is independent of the potential outcome and, separately, of the information. -/
theorem pairwise_indep :
    (∀ y e, p.probOf (fun ω => Y ω = y ∧ ε ω = e) =
      p.probOf (fun ω => Y ω = y) * p.probOf (fun ω => ε ω = e)) ∧
    (∀ i e, p.probOf (fun ω => I ω = i ∧ ε ω = e) =
      p.probOf (fun ω => I ω = i) * p.probOf (fun ω => ε ω = e)) := by
  refine ⟨fun y e => ?_, fun i e => ?_⟩ <;>
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter] <;>
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, p, FiniteDist.uniform_apply, Y, I, ε] <;>
  (try cases y) <;> (try cases i) <;> cases e <;> norm_num

/-- The switch `S = ε`, a function of the information and the noise, is not conditionally
independent of the potential outcome given the information: given `I`, the switch reveals
`Y`. So independence of the noise from `Y` and from `I` separately does not suffice for
`condIndepFun_of_decision`. -/
theorem not_condIndepFun : ¬ p.CondIndepFun ε Y I := by
  intro h
  have := h true true false
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter] at this
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, p, FiniteDist.uniform_apply, Y, I, ε]
    at this
  norm_num at this

/-- Hence the noise is not jointly independent of `(Y, I)`. -/
theorem not_noiseIndep : ¬ NoiseIndep p Y I ε := fun h =>
  not_condIndepFun (condIndepFun_of_decision Y I ε (fun _ e => e) h)

end XorExample

/-! ### Information used by the decision maker but not recorded -/

namespace HiddenExample

/-- The sample space: a prognostic value `k`, a fair bit. -/
abbrev Ω := Bool

/-- `k` is a fair bit. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform

/-- The potential outcome is determined by the prognostic value. -/
def Y (ω : Ω) : Bool := ω

/-- The clinician's information: the prognostic value itself. -/
def I (ω : Ω) : Bool := ω

/-- The data recorded in the trial: nothing. -/
def D (_ : Ω) : Unit := ()

/-- The noise of the decision, trivial. -/
def ε (_ : Ω) : Unit := ()

/-- The switch: the clinician switches exactly the patients with `k = true`. -/
def S (ω : Ω) : Bool := I ω

/-- The noise is jointly independent of the potential outcome and the information. -/
theorem noiseIndep : NoiseIndep p Y I ε := by
  intro y i e
  rw [p.probOf_congr (Q := fun _ => True) fun _ => iff_true_intro rfl,
    p.probOf_congr (P := fun ω => Y ω = y ∧ I ω = i ∧ ε ω = e)
      (Q := fun ω => Y ω = y ∧ I ω = i) fun _ => by simp]
  have : p.probOf (fun _ => True) = 1 := by
    rw [FiniteDist.probOf, Finset.filter_true, FiniteDist.prob_univ]
  rw [this, mul_one]

/-- Given the clinician's information the switch is unconfounded
(`condIndepFun_of_decision`), but given the recorded data it is not: the information used by
the decision maker was observable to them and was not collected (TSD 24, Section 4.2.2.1:
imputation may be needed "if the value of a variable was likely to have been known by the
treating clinician but was not recorded"). -/
theorem condIndepFun_info_not_recorded :
    p.CondIndepFun S Y I ∧ ¬ p.CondIndepFun S Y D := by
  refine ⟨condIndepFun_of_decision Y I ε (fun i _ => i) noiseIndep, fun h => ?_⟩
  have := h true true ()
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter] at this
  simp only [Fintype.sum_bool, p, FiniteDist.uniform_apply, Y, S, I] at this
  norm_num at this

end HiddenExample

/-! ### Figure 1 of TSD 24 -/

open Criteria

/-- TSD 24, Figure 1(a): Karnofsky score `0`, ECOG performance status `1`, switch `2`,
survival `3`, with edges Karnofsky to ECOG, switch and survival; ECOG to switch and survival;
switch to survival. Both scores are confounders. -/
abbrev fig1a : Digraph (Fin 4) := ofEdges [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- TSD 24, Figure 1(b): as Figure 1(a) without the edges from Karnofsky to switch and to
survival. Only ECOG is a confounder. -/
abbrev fig1b : Digraph (Fin 4) := ofEdges [(0, 1), (1, 2), (1, 3), (2, 3)]

/-- Both graphs of Figure 1 are acyclic. -/
theorem fig1_isAcyclic : fig1a.IsAcyclic ∧ fig1b.IsAcyclic := by
  constructor <;> decide +kernel

/-- Figure 1(a): ECOG alone does not meet the back-door criterion relative to (switch,
survival), since the path switch, Karnofsky, survival stays open; nor does Karnofsky alone;
the two together do. Failing to collect the Karnofsky score leaves unmeasured confounding. -/
theorem fig1a_backDoor :
    ¬ fig1a.BackDoor {2} {3} {1} ∧ ¬ fig1a.BackDoor {2} {3} {0} ∧
      fig1a.BackDoor {2} {3} {0, 1} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Figure 1(b): ECOG alone meets the back-door criterion relative to (switch, survival), so
the Karnofsky score is not needed; the empty set and Karnofsky alone do not meet it. -/
theorem fig1b_backDoor :
    fig1b.BackDoor {2} {3} {1} ∧ ¬ fig1b.BackDoor {2} {3} ∅ ∧
      ¬ fig1b.BackDoor {2} {3} {0} ∧ fig1b.BackDoor {2} {3} {0, 1} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end SwitchDecision

end CausalInference
