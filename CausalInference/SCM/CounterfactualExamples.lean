/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Counterfactuals
public import CausalInference.SCM.Effects

/-!
# Worked counterfactual examples

## Main results

* The firing squad (Pearl 2009, section 7.1.2, Figure 7.1): `SCM.FiringSquad.s4`, the action
  sentence `¬C ⇒ D_A ∧ ¬B_A`, and `SCM.FiringSquad.s5`, the counterfactual sentence
  `D ⇒ D_{¬A}`, at every noise value of the deterministic model.
* The probabilistic firing squad (section 7.1.3, equations (7.7) and (7.8)):
  `SCM.FiringSquad.counterfactual_alive`,
  `P(¬D_{¬A} | D) = q(1 - p) / (1 - (1 - q)(1 - p))` by abduction, action and prediction.
* The betting example (sections 7.2.2 and 7.5.1): the bet is not probabilistically relevant to
  winning (`SCM.Betting.probOf_win_and_bet`), yet it changes the outcome at every noise value
  (`SCM.Betting.win_heads_ne_win_tails`); "had I bet differently I would have lost" has
  probability one given that I bet heads and won (`SCM.Betting.counterfactual_lose`); and the
  relevance appears once the coin is in the context (`SCM.Betting.probOf_win_given_coin`).

Source: Pearl (2009), *Causality*, 2nd edition, sections 7.1.2, 7.1.3, 7.2.2 and 7.5.1.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

/-- A coin with probability `p` of `true`. -/
noncomputable def bernoulliDist (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDist Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp [hp0, hp1]
  sum_eq_one := by simp

/-! ### The firing squad -/

namespace FiringSquad

/-- The firing-squad graph (Pearl 2009, Figure 7.1) on `Fin 4`: the captain `C = 0` signals to
the riflemen `A = 1` and `B = 2`, whose shots kill the prisoner `D = 3`. The court order `U` is
the noise of `C`. -/
def squad : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ({(0, 1), (0, 2), (1, 3), (2, 3)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel squad.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem squad_isAcyclic : squad.IsAcyclic := by decide

theorem mem_parents_of_adj {i j : Fin 4} (h : squad.Adj i j) : i ∈ squad.parentsFinset j :=
  Digraph.mem_parentsFinset.2 h

theorem c_mem_parents {v : Fin 4} (h : v = 1 ∨ v = 2) : (0 : Fin 4) ∈ squad.parentsFinset v := by
  rcases h with rfl | rfl <;> exact mem_parents_of_adj (by decide)

theorem a_mem_parents {v : Fin 4} (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≠ 2) :
    (1 : Fin 4) ∈ squad.parentsFinset v := by
  fin_cases v
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact mem_parents_of_adj (by decide)

theorem b_mem_parents {v : Fin 4} (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≠ 2) :
    (2 : Fin 4) ∈ squad.parentsFinset v := by
  fin_cases v
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact mem_parents_of_adj (by decide)

/-- The structural functions of the firing squad, with rifleman `A` shooting when the captain
signals or (if `nervous` is true) when his own noise bit `W` is true:
`C = U`, `A = C ∨ (nervous ∧ W)`, `B = C`, `D = A ∨ B`. -/
def squadF (nervous : Bool) (v : Fin 4) (z : squad.parentsFinset v → Bool) (e : Bool) :
    Bool :=
  if h0 : v = 0 then e
  else if h1 : v = 1 then z ⟨0, c_mem_parents (Or.inl h1)⟩ || (nervous && e)
  else if h2 : v = 2 then z ⟨0, c_mem_parents (Or.inr h2)⟩
  else z ⟨1, a_mem_parents h0 h1 h2⟩ || z ⟨2, b_mem_parents h0 h1 h2⟩

/-- The deterministic firing squad (Pearl 2009, section 7.1.2, model `M`): `C = U`, `A = C`,
`B = C`, `D = A ∨ B`. The noise laws (fair bits) play no role in the deterministic sentences. -/
noncomputable def squadDet : SCM squad (fun _ => Bool) (fun _ => Bool) where
  acyclic := squad_isAcyclic
  f := squadF false
  noise _ := FiniteDist.uniform

theorem squadDet_solve (u : Fin 4 → Bool) : squadDet.solve u = ![u 0, u 0, u 0, u 0] := by
  refine (squadDet.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [squadDet, squadF, Finset.restrict]

/-- A constant configuration. -/
def const (b : Bool) : Fin 4 → Bool := fun _ => b

theorem squadDet_solve_intervene (b : Bool) (u : Fin 4 → Bool) :
    (squadDet.intervene {1} (const b)).solve u = ![u 0, b, u 0, b || u 0] := by
  refine ((squadDet.intervene {1} (const b)).eq_solve_of_isSolution ?_).symm
  refine squadDet.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [squadDet, squadF, Finset.restrict]

/-- **Sentence S4** (Pearl 2009, section 7.1.2, action): if the captain gave no signal and
rifleman `A` decides to shoot, then the prisoner dies and `B` does not shoot:
`¬C ⇒ D_A ∧ ¬B_A`, at every noise value. -/
theorem s4 (u : Fin 4 → Bool) (hC : squadDet.solve u 0 = false) :
    (squadDet.intervene {1} (const true)).solve u 3 = true ∧
      (squadDet.intervene {1} (const true)).solve u 2 = false := by
  rw [squadDet_solve] at hC
  simp only [Matrix.cons_val_zero] at hC
  rw [squadDet_solve_intervene]
  simp [hC]

/-- **Sentence S5** (Pearl 2009, section 7.1.2, counterfactual): if the prisoner is dead, then
the prisoner would be dead even if rifleman `A` had not shot: `D ⇒ D_{¬A}`, at every noise
value. -/
theorem s5 (u : Fin 4 → Bool) (hD : squadDet.solve u 3 = true) :
    (squadDet.intervene {1} (const false)).solve u 3 = true := by
  rw [squadDet_solve] at hD
  rw [squadDet_solve_intervene]
  simpa using hD

/-- The noise laws of the probabilistic firing squad: the court order `U` (noise of `C`) is true
with probability `p`, the nervousness `W` of rifleman `A` (noise of `A`) with probability `q`,
independently; the noises of `B` and `D` are unused fair bits. -/
noncomputable def squadNoise (p q : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) (v : Fin 4) :
    FiniteDist Bool :=
  if v = 0 then bernoulliDist p hp.1 hp.2 else if v = 1 then bernoulliDist q hq.1 hq.2
  else FiniteDist.uniform

/-- The probabilistic firing squad (Pearl 2009, section 7.1.3): `C = U`, `A = C ∨ W`, `B = C`,
`D = A ∨ B`, with `P(U) = p` and `P(W) = q` independent, as in equation (7.7). -/
noncomputable def squadProb (p q : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    SCM squad (fun _ => Bool) (fun _ => Bool) where
  acyclic := squad_isAcyclic
  f := squadF true
  noise := squadNoise p q hp hq

variable {p q : ℝ} {hp : 0 ≤ p ∧ p ≤ 1} {hq : 0 ≤ q ∧ q ≤ 1}

theorem squadProb_solve (u : Fin 4 → Bool) :
    (squadProb p q hp hq).solve u = ![u 0, u 0 || u 1, u 0, u 0 || u 1] := by
  refine ((squadProb p q hp hq).isSolution_iff.1 fun v => ?_).symm
  cases h0 : u 0 <;> cases h1 : u 1 <;> fin_cases v <;>
    simp [squadProb, squadF, Finset.restrict, h0, h1]

theorem squadProb_solve_intervene (u : Fin 4 → Bool) :
    ((squadProb p q hp hq).intervene {1} (const false)).solve u = ![u 0, false, u 0, u 0] := by
  refine (((squadProb p q hp hq).intervene {1} (const false)).eq_solve_of_isSolution ?_).symm
  refine (squadProb p q hp hq).isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [squadProb, squadF, Finset.restrict]

/-- Probabilities of events depending on the court order `U` and the nervousness `W`. -/
theorem probOf_noise_pair (P : Bool × Bool → Prop) [DecidablePred P] :
    (squadProb p q hp hq).noiseDist.probOf (fun u => P (u 0, u 1)) =
      (if P (true, true) then p * q else 0) + (if P (true, false) then p * (1 - q) else 0) +
        (if P (false, true) then (1 - p) * q else 0) +
          (if P (false, false) then (1 - p) * (1 - q) else 0) := by
  rw [show (squadProb p q hp hq).noiseDist.probOf (fun u => P (u 0, u 1)) =
      ((squadProb p q hp hq).noiseDist.map fun u => (u 0, u 1)).probOf P from
    (FiniteDist.probOf_map _ _ P).symm]
  change ((FiniteDist.pi (squadNoise p q hp hq)).map fun u : Fin 4 → Bool => (u 0, u 1)).probOf
    P = _
  rw [FiniteDist.map_pi_eval_pair _ (by decide)]
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, FiniteDist.prod_apply, squadNoise, bernoulliDist]
  norm_num
  ring

/-- The probability that the prisoner dies is `1 - (1 - q)(1 - p)`. -/
theorem probOf_dies :
    (squadProb p q hp hq).dist.probOf (fun y => y 3 = true) = 1 - (1 - q) * (1 - p) := by
  rw [probOf_dist]
  simp only [squadProb_solve, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [probOf_noise_pair (fun r => (r.1 || r.2) = true)]
  norm_num
  ring

/-- The prisoner dies with positive probability when `0 < p` or `0 < q`. -/
theorem probOf_dies_pos (hpq : 0 < p ∨ 0 < q) :
    0 < (squadProb p q hp hq).dist.probOf (fun y => y 3 = true) := by
  rw [probOf_dies]
  rcases hpq with h | h <;> nlinarith [hp.1, hp.2, hq.1, hq.2]

/-- **The probabilistic firing squad** (Pearl 2009, section 7.1.3, equations (7.7) and (7.8)):
the probability that the prisoner would be alive had rifleman `A` not shot, given that the
prisoner is dead, is `P(¬D_{¬A} | D) = q(1 - p) / (1 - (1 - q)(1 - p))`. The hypothesis
`0 < p ∨ 0 < q` makes the evidence `D` possible. -/
theorem counterfactual_alive (hpq : 0 < p ∨ 0 < q) :
    (squadProb p q hp hq).counterfactualProb (fun y => y 3 = true) (probOf_dies_pos hpq) {1}
      (const false) (fun y => y 3 = false) = q * (1 - p) / (1 - (1 - q) * (1 - p)) := by
  rw [counterfactualProb_eq, probOf_dies]
  congr 1
  simp only [squadProb_solve, squadProb_solve_intervene, Matrix.cons_val_three,
    Matrix.tail_cons, Matrix.head_cons]
  rw [probOf_noise_pair (fun r => (r.1 || r.2) = true ∧ r.1 = false)]
  simp
  ring

end FiringSquad

/-! ### The betting example -/

namespace Betting

open GraphExamples

/-- The betting model (Pearl 2009, sections 7.2.2 and 7.5.1) on the collider `0 → 2 ← 1`: the
bet `C = 0` (`true` for heads) and the fair coin `F = 1` are fair noise bits, and the bettor wins
(`E = 2`) exactly when the bet matches the coin. -/
noncomputable def model : SCM collider (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide
  f v z e := if h : v = 2 then
      decide (z ⟨0, Digraph.mem_parentsFinset.2 ⟨by decide, h⟩⟩ =
        z ⟨1, Digraph.mem_parentsFinset.2 ⟨by decide, h⟩⟩)
    else e
  noise _ := FiniteDist.uniform

theorem model_solve (u : Fin 3 → Bool) : model.solve u = ![u 0, u 1, decide (u 0 = u 1)] := by
  refine (model.isSolution_iff.1 fun v => ?_).symm
  fin_cases v
  · simp [model]
  · simp [model]
  · exact decide_eq_decide.2 Iff.rfl

/-- A constant configuration. -/
def const (b : Bool) : Fin 3 → Bool := fun _ => b

theorem model_solve_intervene (b : Bool) (u : Fin 3 → Bool) :
    (model.intervene {0} (const b)).solve u = ![b, u 1, decide (b = u 1)] := by
  refine ((model.intervene {0} (const b)).eq_solve_of_isSolution ?_).symm
  refine model.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v
    · simp at hv
    · simp [model]
    · exact decide_eq_decide.2 Iff.rfl

theorem probOf_noise_pair (P : Bool × Bool → Prop) [DecidablePred P] :
    model.noiseDist.probOf (fun u => P (u 0, u 1)) =
      (if P (false, false) then 1 / 4 else 0) + (if P (false, true) then 1 / 4 else 0) +
        (if P (true, false) then 1 / 4 else 0) + (if P (true, true) then 1 / 4 else 0) := by
  rw [show model.noiseDist.probOf (fun u => P (u 0, u 1)) =
      (model.noiseDist.map fun u => (u 0, u 1)).probOf P from
    (FiniteDist.probOf_map _ _ P).symm]
  change ((FiniteDist.pi fun _ => FiniteDist.uniform).map fun u : Fin 3 → Bool => (u 0, u 1)).probOf
    P = _
  rw [FiniteDist.map_pi_eval_pair _ (by decide)]
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, FiniteDist.prod_apply, FiniteDist.uniform_apply, Fintype.card_bool]
  split_ifs <;> norm_num

/-- **The bet is not probabilistically relevant to winning** (Pearl 2009, section 7.5.1): the
probability of winning together with each bet is `1/4`, and each bet has probability `1/2`, so
`P(win | heads) = P(win | tails) = 1/2`. -/
theorem probOf_win_and_bet (b : Bool) :
    model.dist.probOf (fun y => y 2 = true ∧ y 0 = b) = 1 / 4 ∧
      model.dist.probOf (fun y => y 0 = b) = 1 / 2 := by
  rw [probOf_dist, probOf_dist]
  simp only [model_solve, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [probOf_noise_pair (fun r => decide (r.1 = r.2) = true ∧ r.1 = b),
    probOf_noise_pair (fun r => r.1 = b)]
  cases b <;> norm_num

/-- **The bet is causally relevant to winning** (Pearl 2009, sections 7.2.2 and 7.5.1): at every
noise value, the outcome under the bet heads differs from the outcome under the bet tails. -/
theorem win_heads_ne_win_tails (u : Fin 3 → Bool) :
    (model.intervene {0} (const true)).solve u 2 ≠ (model.intervene {0} (const false)).solve u 2
    := by
  rw [model_solve_intervene, model_solve_intervene]
  cases u 1 <;> simp

theorem probOf_won_heads_pos :
    0 < model.dist.probOf (fun y => y 0 = true ∧ y 2 = true) := by
  rw [probOf_dist]
  simp only [model_solve, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  rw [probOf_noise_pair (fun r => r.1 = true ∧ decide (r.1 = r.2) = true)]
  norm_num

/-- **"Had I bet differently I would have lost"** (Pearl 2009, section 7.2.2): given that I bet
heads and won, the probability that I would have lost had I bet tails is one. -/
theorem counterfactual_lose :
    model.counterfactualProb (fun y => y 0 = true ∧ y 2 = true) probOf_won_heads_pos {0}
      (const false) (fun y => y 2 = false) = 1 := by
  rw [counterfactualProb_eq, probOf_dist]
  simp only [model_solve, model_solve_intervene, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  rw [probOf_noise_pair (fun r => (r.1 = true ∧ decide (r.1 = r.2) = true) ∧
      decide (false = r.2) = false),
    probOf_noise_pair (fun r => r.1 = true ∧ decide (r.1 = r.2) = true)]
  norm_num

/-- **The coin reveals the relevance** (Pearl 2009, section 7.5.1): within the context
`F = heads`, the bet heads wins with probability one and the bet tails with probability zero; in
product form, `P(win, heads, F = heads) = P(heads, F = heads) = 1/4` and
`P(win, tails, F = heads) = 0`. -/
theorem probOf_win_given_coin :
    model.dist.probOf (fun y => y 2 = true ∧ y 0 = true ∧ y 1 = true) = 1 / 4 ∧
      model.dist.probOf (fun y => y 0 = true ∧ y 1 = true) = 1 / 4 ∧
      model.dist.probOf (fun y => y 2 = true ∧ y 0 = false ∧ y 1 = true) = 0 := by
  simp only [probOf_dist, model_solve, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [probOf_noise_pair (fun r => decide (r.1 = r.2) = true ∧ r.1 = true ∧ r.2 = true),
    probOf_noise_pair (fun r => r.1 = true ∧ r.2 = true),
    probOf_noise_pair (fun r => decide (r.1 = r.2) = true ∧ r.1 = false ∧ r.2 = true)]
  norm_num

end Betting

end SCM

end CausalInference
