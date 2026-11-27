/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Counterfactuals
public import CausalInference.SCM.Effects
public import CausalInference.SCM.TwinNetwork

/-!
# Worked counterfactual examples

## Main results

* The firing squad (Pearl 2009, section 7.1.2, Figure 7.1): `SCM.FiringSquad.s4`, the action
  sentence `¬C ⇒ D_A ∧ ¬B_A`, and `SCM.FiringSquad.s5`, the counterfactual sentence
  `D ⇒ D_{¬A}`, at every noise value of the deterministic model.
* The probabilistic firing squad (section 7.1.3, equations (7.7) and (7.8)):
  `SCM.FiringSquad.counterfactual_alive`,
  `P(¬D_{¬A} | D) = q(1 - p) / (1 - (1 - q)(1 - p))` by abduction, action and prediction.
* The betting example (sections 7.2.2 and 7.5.2): the bet is not probabilistically relevant to
  winning (`SCM.Betting.probOf_win_and_bet`), yet it changes the outcome at every noise value
  (`SCM.Betting.win_heads_ne_win_tails`); "had I bet differently I would have lost" has
  probability one given that I bet heads and won (`SCM.Betting.counterfactual_lose`); and the
  relevance appears once the coin is in the context (`SCM.Betting.probOf_win_given_coin`).
* The smoking model (sections 7.3.2 and 7.4.4, Figure 7.5), with the genotype `U₁` as an
  unobserved root vertex: the exclusion restrictions (7.27) to (7.29)
  (`SCM.Smoking.z_exclusion`, `SCM.Smoking.x_exclusion`, `SCM.Smoking.y_exclusion`), the
  independence restriction (7.30) (`SCM.Smoking.probOf_zx_and`,
  `SCM.Smoking.condIndepFun_zx_yz_x`), the front-door formula (7.37) derived from them by
  composition and consistency (`SCM.Smoking.frontDoor`), the implied independence
  `Y_z ⫫ Z_x | {Z, X}` (`SCM.Smoking.condIndepFun_yz_zx_given_zx`), and a model in which
  `Y_z ⫫ Z_x | Z` fails (`SCM.Smoking.not_condIndepFun_yz_zx_given_z`).

Source: Pearl (2009), *Causality*, 2nd edition, sections 7.1.2, 7.1.3, 7.2.2, 7.3.2, 7.4.4 and
7.5.2.
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

/-- The betting model (Pearl 2009, sections 7.2.2 and 7.5.2) on the collider `0 → 2 ← 1`: the
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

/-- **The bet is not probabilistically relevant to winning** (Pearl 2009, section 7.5.2): the
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

/-- **The bet is causally relevant to winning** (Pearl 2009, sections 7.2.2 and 7.5.2): at every
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

/-- **The coin reveals the relevance** (Pearl 2009, section 7.5.2, Definition 7.5.1): within
the context `F = heads`, the bet heads wins with probability one and the bet tails with
probability zero. In product form, `P(win, heads, F = heads) = P(heads, F = heads) = 1/4` and
`P(win, tails, F = heads) = 0`, while the conditioning event of the second has mass
`P(tails, F = heads) = 1/4`; the conditional probabilities themselves are in
`probOf_win_cond_coin`. -/
theorem probOf_win_given_coin :
    model.dist.probOf (fun y => y 2 = true ∧ y 0 = true ∧ y 1 = true) = 1 / 4 ∧
      model.dist.probOf (fun y => y 0 = true ∧ y 1 = true) = 1 / 4 ∧
      model.dist.probOf (fun y => y 2 = true ∧ y 0 = false ∧ y 1 = true) = 0 ∧
      model.dist.probOf (fun y => y 0 = false ∧ y 1 = true) = 1 / 4 := by
  simp only [probOf_dist, model_solve, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [probOf_noise_pair (fun r => decide (r.1 = r.2) = true ∧ r.1 = true ∧ r.2 = true),
    probOf_noise_pair (fun r => r.1 = true ∧ r.2 = true),
    probOf_noise_pair (fun r => decide (r.1 = r.2) = true ∧ r.1 = false ∧ r.2 = true),
    probOf_noise_pair (fun r => r.1 = false ∧ r.2 = true)]
  norm_num

/-- **The coin reveals the relevance, as conditional probabilities** (Pearl 2009,
section 7.5.2): `P(win | heads, F = heads) = 1` and `P(win | tails, F = heads) = 0`, both
conditioning events having probability `1/4`. So the bet satisfies Definition 7.5.1 of causal
relevance with the background condition `F = heads`. -/
theorem probOf_win_cond_coin :
    model.dist.probOf (fun y => y 2 = true ∧ y 0 = true ∧ y 1 = true) /
        model.dist.probOf (fun y => y 0 = true ∧ y 1 = true) = 1 ∧
      model.dist.probOf (fun y => y 2 = true ∧ y 0 = false ∧ y 1 = true) /
        model.dist.probOf (fun y => y 0 = false ∧ y 1 = true) = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := probOf_win_given_coin
  rw [h1, h2, h3]
  norm_num

end Betting

/-! ### The smoking model: counterfactual restrictions and the front-door formula -/

namespace Smoking

/-- The smoking graph (Pearl 2009, section 7.3.2, Figure 7.5) on `Fin 4`. The genotype `U₁ = 0`
is an unobserved root vertex with the arrows `U₁ → X` and `U₁ → Y`; smoking `X = 1` feeds the tar
`Z = 2`, which feeds the cancer `Y = 3`. The noise of `Z` plays the role of `U₂`; in a model on
this graph it is independent of `U₁`, as in Figure 7.5. -/
def graph : Digraph (Fin 4) where
  Adj i j := (i, j) ∈ ({(0, 1), (0, 3), (1, 2), (2, 3)} : Finset (Fin 4 × Fin 4))

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

theorem graph_isAcyclic : graph.IsAcyclic := by decide

theorem parents_two : graph.parentsFinset 2 = {1} := by decide

theorem parents_three {p : Fin 4} (hp : p ∈ graph.parentsFinset 3) : p = 0 ∨ p = 2 := by
  have key : ∀ q ∈ graph.parentsFinset 3, q = 0 ∨ q = 2 := by decide
  exact key p hp

variable {α ε : Fin 4 → Type*} [∀ v, Fintype (ε v)] (M : SCM graph α ε)

/-- `Z_x(u) = f_Z(x, u_Z)`: under an intervention on `X`, the tar is its structural function at
the set value of `X` and its own noise. -/
theorem solve_intervene_two {S : Finset (Fin 4)} (hS : 1 ∈ S) (h2 : 2 ∉ S) (x : ∀ v, α v)
    (u : ∀ v, ε v) :
    (M.intervene S x).solve u 2 = M.f 2 ((graph.parentsFinset 2).restrict x) (u 2) :=
  M.solve_intervene_of_parents_subset (by rw [parents_two]; exact singleton_subset_iff.2 hS)
    h2 x u

/-- **Exclusion restriction (7.27)** (Pearl 2009, section 7.3.2): `Z_x(u) = Z_{yx}(u)`. -/
theorem z_exclusion (x : ∀ v, α v) (u : ∀ v, ε v) :
    (M.intervene {1} x).solve u 2 = (M.intervene {1, 3} x).solve u 2 := by
  rw [solve_intervene_two M (S := {1}) (by decide) (by decide),
    solve_intervene_two M (S := {1, 3}) (by decide) (by decide)]

/-- **Exclusion restriction (7.28)** (Pearl 2009, section 7.3.2): an intervention on `Z`, on `Y`,
or on both does not change smoking: `X_y(u) = X_{zy}(u) = X_z(u) = X(u)`. -/
theorem x_exclusion {S : Finset (Fin 4)} (hS : S ⊆ {2, 3}) (z : ∀ v, α v) (u : ∀ v, ε v) :
    (M.intervene S z).solve u 1 = M.solve u 1 := by
  refine M.solve_intervene_of_notMem_descendantsOf u fun h => ?_
  obtain ⟨s, hs, hsp⟩ := Digraph.mem_descendantsOf.1 h
  have hs' : s ∈ ({2, 3} : Finset (Fin 4)) := hS (mem_coe.1 hs)
  have key : ∀ t ∈ ({2, 3} : Finset (Fin 4)), t ≠ 1 ∧ ¬ graph.IsAncestor t 1 := by decide
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hsp with h' | h'
  · exact (key s hs').1 h'.symm
  · exact (key s hs').2 h'

/-- The genotype is a root: no intervention that leaves it alone changes it. -/
theorem solve_intervene_zero {S : Finset (Fin 4)} (hS : 0 ∉ S) (z : ∀ v, α v)
    (u : ∀ v, ε v) : (M.intervene S z).solve u 0 = M.solve u 0 := by
  refine M.solve_intervene_of_notMem_descendantsOf u fun h => ?_
  obtain ⟨s, hs, hsp⟩ := Digraph.mem_descendantsOf.1 h
  have key : ∀ t : Fin 4, ¬ graph.IsAncestor t 0 := by decide
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hsp with h' | h'
  · exact hS (by rw [h']; exact mem_coe.1 hs)
  · exact key s h'

/-- **Exclusion restriction (7.29)** (Pearl 2009, section 7.3.2): once the tar is set, a further
intervention on smoking does not change the cancer: `Y_z(u) = Y_{zx}(u)`. The intervention on
`{X, Z}` may assign any value to `X`; it agrees with `z` on `Z`. -/
theorem y_exclusion (z z' : ∀ v, α v) (hz : z' 2 = z 2) (u : ∀ v, ε v) :
    (M.intervene ({1} ∪ {2}) z').solve u 3 = (M.intervene {2} z).solve u 3 := by
  rw [M.solve_intervene_of_notMem u (show (3 : Fin 4) ∉ ({1} ∪ {2} : Finset (Fin 4)) by decide),
    M.solve_intervene_of_notMem u (show (3 : Fin 4) ∉ ({2} : Finset (Fin 4)) by decide)]
  congr 1
  funext ⟨p, hp⟩
  simp only [Finset.restrict]
  rcases parents_three hp with rfl | rfl
  · rw [solve_intervene_zero M (S := {1} ∪ {2}) (by decide),
      solve_intervene_zero M (S := {2}) (by decide)]
  · rw [M.solve_intervene_of_mem u (show (2 : Fin 4) ∈ ({1} ∪ {2} : Finset (Fin 4)) by decide),
      M.solve_intervene_of_mem u (show (2 : Fin 4) ∈ ({2} : Finset (Fin 4)) by decide), hz]

variable [∀ v, DecidableEq (α v)]

omit [∀ v, DecidableEq (α v)] in
/-- **Independence restriction (7.30)** (Pearl 2009, section 7.3.2), in product form: the tar
under interventions on smoking is independent of the pair made of the cancer under an
intervention on the tar and of smoking, `Z_x ⫫ {Y_z, X}`. The statement allows two
interventions `x`, `x'` on smoking at once: the pair `(Z_x, Z_{x'})` is a function of the noise
of `Z` alone, and `(Y_z, X)` does not depend on it. -/
theorem probOf_zx_and (x x' z : ∀ v, α v) (B : α 2 → α 2 → Prop) [∀ a b, Decidable (B a b)]
    (E : α 3 → α 1 → Prop) [∀ a b, Decidable (E a b)] :
    M.noiseDist.probOf (fun u => B ((M.intervene {1} x).solve u 2)
        ((M.intervene {1} x').solve u 2) ∧ E ((M.intervene {2} z).solve u 3) (M.solve u 1)) =
      M.noiseDist.probOf (fun u => B ((M.intervene {1} x).solve u 2)
          ((M.intervene {1} x').solve u 2)) *
        M.noiseDist.probOf (fun u => E ((M.intervene {2} z).solve u 3) (M.solve u 1)) := by
  simp only [solve_intervene_two M (S := {1}) (by decide) (by decide)]
  have hX : ∀ u' : ∀ v, ε v, M.solve u' 1 = (M.intervene {2} z).solve u' 1 :=
    fun u' => (x_exclusion M (by decide) z u').symm
  have hE : ∀ (u : ∀ v, ε v) (e : ε 2),
      E ((M.intervene {2} z).solve (Function.update u 2 e) 3) (M.solve (Function.update u 2 e) 1)
        ↔ E ((M.intervene {2} z).solve u 3) (M.solve u 1) := by
    intro u e
    have hc : (M.intervene {2} z).solve (Function.update u 2 e) = (M.intervene {2} z).solve u :=
      M.solve_intervene_congr_noise z fun v hv =>
        Function.update_of_ne (fun h => hv (mem_singleton.2 h)) _ _
    rw [hX, hX u, hc]
  have key := FiniteDist.probOf_pi_and_of_indep M.noise 2
    (fun e => B (M.f 2 ((graph.parentsFinset 2).restrict x) e)
      (M.f 2 ((graph.parentsFinset 2).restrict x') e))
    (fun u => E ((M.intervene {2} z).solve u 3) (M.solve u 1)) hE
  have key1 := FiniteDist.probOf_pi_and_of_indep M.noise 2
    (fun e => B (M.f 2 ((graph.parentsFinset 2).restrict x) e)
      (M.f 2 ((graph.parentsFinset 2).restrict x') e)) (fun _ => True) fun _ _ => Iff.rfl
  have h1 : (FiniteDist.pi M.noise).probOf (fun _ => True) = 1 := by
    rw [FiniteDist.probOf, filter_true, FiniteDist.prob_univ]
  beta_reduce at key key1
  rw [h1, mul_one] at key1
  rw [noiseDist, key, ← key1]
  congr 1
  exact FiniteDist.probOf_congr _ fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- **Independence restriction (7.30)** (Pearl 2009, section 7.3.2), as an independence of random
variables: `Z_x ⫫ {Y_z, X}`. -/
theorem condIndepFun_zx_yz_x [∀ v, Finite (α v)] (x z : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => (M.intervene {1} x).solve u 2)
      (fun u => ((M.intervene {2} z).solve u 3, M.solve u 1)) (fun _ => ()) := by
  rw [FiniteDist.condIndepFun_iff_exists_mul]
  refine ⟨fun a _ => M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 2 = a),
    fun b _ => M.noiseDist.probOf (fun u => (M.intervene {2} z).solve u 3 = b.1 ∧
      M.solve u 1 = b.2), fun a b c => ?_⟩
  dsimp only
  rw [← probOf_zx_and M x x z (fun p _ => p = a) (fun q r => q = b.1 ∧ r = b.2)]
  refine FiniteDist.probOf_congr _ fun u => ?_
  simp only [Prod.ext_iff, and_true]

omit [∀ v, DecidableEq (α v)] in
/-- Consistency for an intervention on smoking: where `X(u) = x`, `V_x(u) = V(u)`. -/
theorem solve_intervene_one_of_eq {x : ∀ v, α v} {u : ∀ v, ε v} (h : M.solve u 1 = x 1) :
    (M.intervene {1} x).solve u = M.solve u :=
  M.solve_intervene_of_agree fun v hv => by rw [mem_singleton.1 hv]; exact h

omit [∀ v, DecidableEq (α v)] in
/-- Consistency for an intervention on the tar: where `Z(u) = z`, `V_z(u) = V(u)`. -/
theorem solve_intervene_two_of_eq {z : ∀ v, α v} {u : ∀ v, ε v} (h : M.solve u 2 = z 2) :
    (M.intervene {2} z).solve u = M.solve u :=
  M.solve_intervene_of_agree fun v hv => by rw [mem_singleton.1 hv]; exact h

/-- **`Y_z ⫫ Z_x | {Z, X}`** (Pearl 2009, section 7.4.4): in every model on the smoking graph,
the cancer under an intervention on the tar is conditionally independent of the tar under an
intervention on smoking, given the factual tar and smoking. Given `X = d`, the factual tar is
`Z_{x'}` for the intervention `x'` that sets smoking to `d` (consistency), so the pair
`(Z_x, Z)` is a function of the noise of `Z`, while `(Y_z, X)` does not depend on it (7.30). -/
theorem condIndepFun_yz_zx_given_zx [∀ v, Finite (α v)] (x z : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => (M.intervene {2} z).solve u 3)
      (fun u => (M.intervene {1} x).solve u 2) (fun u => (M.solve u 2, M.solve u 1)) := by
  rw [FiniteDist.condIndepFun_iff_exists_mul]
  refine ⟨fun a c => M.noiseDist.probOf
      (fun u => (M.intervene {2} z).solve u 3 = a ∧ M.solve u 1 = c.2),
    fun b c => M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 2 = b ∧
      (M.intervene {1} (Function.update x 1 c.2)).solve u 2 = c.1), fun a b c => ?_⟩
  dsimp only
  rw [mul_comm, ← probOf_zx_and M x (Function.update x 1 c.2) z (fun p q => p = b ∧ q = c.1)
    (fun q r => q = a ∧ r = c.2)]
  refine FiniteDist.probOf_congr _ fun u => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h3, h4⟩ := Prod.ext_iff.1 h3
    have hc : (M.intervene {1} (Function.update x 1 c.2)).solve u = M.solve u :=
      solve_intervene_one_of_eq M (by rw [Function.update_self]; exact h4)
    exact ⟨⟨h2, by rw [hc]; exact h3⟩, h1, h4⟩
  · rintro ⟨⟨h2, h3⟩, h1, h4⟩
    have hc : (M.intervene {1} (Function.update x 1 c.2)).solve u = M.solve u :=
      solve_intervene_one_of_eq M (by rw [Function.update_self]; exact h4)
    rw [hc] at h3
    exact ⟨h1, h2, Prod.ext h3 h4⟩

/-- **Task 1** (Pearl 2009, equation (7.31)), in product form: `P(Z_x = c) P(x) = P(c, x)`, by
(7.30) and composition. -/
theorem task1 (x : ∀ v, α v) (c : α 2) :
    M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 2 = c) *
        M.noiseDist.probOf (fun u => M.solve u 1 = x 1) =
      M.noiseDist.probOf (fun u => M.solve u 2 = c ∧ M.solve u 1 = x 1) := by
  have h := probOf_zx_and M x x x (fun p _ => p = c) (fun _ r => r = x 1)
  beta_reduce at h
  rw [← h]
  refine FiniteDist.probOf_congr _ fun u => ?_
  constructor
  · rintro ⟨h1, h2⟩
    rw [solve_intervene_one_of_eq M h2] at h1
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [solve_intervene_one_of_eq M h2]
    exact ⟨h1, h2⟩

/-- **Task 2** (Pearl 2009, equation (7.33)), in product form: for the intervention `do(X := d)`
written as `x` with `x 1 = d`, and an intervention `z` on the tar with `z 2 = c`,
`P(y, c, d) = P(Z_x = c) P(Y_z = y, X = d)` and `P(c, d) = P(Z_x = c) P(X = d)`. -/
theorem task2 (x z : ∀ v, α v) (y : α 3) :
    M.noiseDist.probOf (fun u => M.solve u 3 = y ∧ M.solve u 2 = z 2 ∧ M.solve u 1 = x 1) =
        M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 2 = z 2) *
          M.noiseDist.probOf (fun u => (M.intervene {2} z).solve u 3 = y ∧ M.solve u 1 = x 1) ∧
      M.noiseDist.probOf (fun u => M.solve u 2 = z 2 ∧ M.solve u 1 = x 1) =
        M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 2 = z 2) *
          M.noiseDist.probOf (fun u => M.solve u 1 = x 1) := by
  refine ⟨?_, ?_⟩
  · have h := probOf_zx_and M x x z (fun p _ => p = z 2) (fun q r => q = y ∧ r = x 1)
    beta_reduce at h
    rw [← h]
    refine FiniteDist.probOf_congr _ fun u => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [solve_intervene_one_of_eq M h3]
      rw [solve_intervene_two_of_eq M h2]
      exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩
      rw [solve_intervene_one_of_eq M h3] at h2
      rw [solve_intervene_two_of_eq M h2] at h1
      exact ⟨h1, h2, h3⟩
  · rw [← task1 M x (z 2)]

/-- **Task 3** (Pearl 2009, equations (7.35) and (7.36)): by composition and (7.29),
`Y_x(u) = Y_{z}(u)` where `z = Z_x(u)`; with (7.30),
`P(Y_x = y) = Σ_c P(Y_{z_c} = y) P(Z_x = c)`, where `z_c` sets the tar to `c`. -/
theorem task3 [∀ v, Fintype (α v)] (x : ∀ v, α v) (zc : α 2 → ∀ v, α v)
    (hzc : ∀ c, zc c 2 = c) (y : α 3) :
    M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 3 = y) =
      ∑ c, M.noiseDist.probOf (fun u => (M.intervene {2} (zc c)).solve u 3 = y) *
        M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 2 = c) := by
  rw [FiniteDist.probOf_eq_sum_univ (P := fun u => (M.intervene {1} x).solve u 3 = y) _
    (fun u => (M.intervene {1} x).solve u 2)]
  refine sum_congr rfl fun c _ => ?_
  have h := probOf_zx_and M x x (zc c) (fun p _ => p = c) (fun q _ => q = y)
  beta_reduce at h
  rw [mul_comm, ← h]
  refine FiniteDist.probOf_congr _ fun u => ?_
  have hcomp : (M.intervene {1} x).solve u 2 = c →
      (M.intervene {1} x).solve u 3 = (M.intervene {2} (zc c)).solve u 3 := by
    intro hc
    rw [← M.solve_intervene_union_of_agree (X := {1}) (W := {2}) (w := zc c) (x := x) (u := u)
      fun v hv => by rw [mem_singleton.1 hv, hzc, hc]]
    exact y_exclusion M (zc c) _ (by simp) u
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (hcomp h2).symm.trans h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨(hcomp h2).trans h1, h2⟩

/-- **The front-door formula by counterfactual algebra** (Pearl 2009, section 7.3.2,
equation (7.37)): in every model on the smoking graph, if every pair of values of the tar and of
smoking has positive probability, the causal effect of smoking on cancer is
`P(Y_x = y) = Σ_z P(z | x) Σ_{x'} P(y | z, x') P(x')`.
The proof is Pearl's derivation: Tasks 1, 2 and 3 from the exclusion restrictions (7.27) to
(7.29), the independence restriction (7.30), composition and consistency. -/
theorem frontDoor [∀ v, Fintype (α v)] (x : ∀ v, α v) (y : α 3)
    (hpos : ∀ (c : α 2) (d : α 1), 0 < M.dist.probOf (fun w => w 2 = c ∧ w 1 = d)) :
    (M.intervene {1} x).dist.probOf (fun w => w 3 = y) =
      ∑ c : α 2, M.dist.probOf (fun w => w 2 = c ∧ w 1 = x 1) /
          M.dist.probOf (fun w => w 1 = x 1) *
        ∑ d : α 1, M.dist.probOf (fun w => w 3 = y ∧ w 2 = c ∧ w 1 = d) /
            M.dist.probOf (fun w => w 2 = c ∧ w 1 = d) * M.dist.probOf (fun w => w 1 = d) := by
  simp only [probOf_dist]
  change M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 3 = y) = _
  rw [task3 M x (fun c => Function.update x 2 c) (fun c => Function.update_self ..) y]
  refine sum_congr rfl fun c _ => ?_
  have hpos' : ∀ (c : α 2) (d : α 1),
      0 < M.noiseDist.probOf (fun u => M.solve u 2 = c ∧ M.solve u 1 = d) := by
    intro c d
    have := hpos c d
    rwa [probOf_dist] at this
  -- Task 1
  have hX : 0 < M.noiseDist.probOf (fun u => M.solve u 1 = x 1) :=
    (hpos' c (x 1)).trans_le (FiniteDist.probOf_mono _ fun _ h => h.2)
  have t1 : M.noiseDist.probOf (fun u => (M.intervene {1} x).solve u 2 = c) =
      M.noiseDist.probOf (fun u => M.solve u 2 = c ∧ M.solve u 1 = x 1) /
        M.noiseDist.probOf (fun u => M.solve u 1 = x 1) := by
    rw [eq_div_iff hX.ne', task1 M]
  refine (mul_comm _ _).trans ?_
  rw [t1]
  congr 1
  -- Task 2
  rw [FiniteDist.probOf_eq_sum_univ
    (P := fun u => (M.intervene {2} (Function.update x 2 c)).solve u 3 = y) _
    (fun u => M.solve u 1)]
  refine sum_congr rfl fun d _ => ?_
  obtain ⟨h1, h2⟩ := task2 M (Function.update x 1 d) (Function.update x 2 c) y
  simp only [Function.update_self] at h1 h2
  rw [h1, h2]
  have hcd := hpos' c d
  rw [h2] at hcd
  have hA : M.noiseDist.probOf
      (fun u => (M.intervene {1} (Function.update x 1 d)).solve u 2 = c) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcd
    exact lt_irrefl _ hcd
  have hB : M.noiseDist.probOf (fun u => M.solve u 1 = d) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcd
    exact lt_irrefl _ hcd
  rw [mul_div_mul_left _ _ hA, div_mul_cancel₀ _ hB]

/-- A model on the smoking graph with fair noise bits `e₀, e₁, e₂, e₃`: `U₁ := e₀`, `X := U₁`,
`Z := X xor e₂`, `Y := h(Z, U₁)`. The choices `h = xor` and `h = or` both give models in which
`Y_z ⫫ Z_x | Z` fails (`not_condIndepFun_yz_zx_given_z_xor`, `not_condIndepFun_yz_zx_given_z_or`).
-/
noncomputable def cexModel (h : Bool → Bool → Bool) :
    SCM graph (fun _ => Bool) (fun _ => Bool) where
  acyclic := graph_isAcyclic
  f v z e :=
    if h1 : v = 1 then z ⟨0, by subst h1; exact Digraph.mem_parentsFinset.2 (by decide)⟩
    else if h2 : v = 2 then
      xor (z ⟨1, by subst h2; exact Digraph.mem_parentsFinset.2 (by decide)⟩) e
    else if h3 : v = 3 then
      h (z ⟨2, by subst h3; exact Digraph.mem_parentsFinset.2 (by decide)⟩)
        (z ⟨0, by subst h3; exact Digraph.mem_parentsFinset.2 (by decide)⟩)
    else e
  noise _ := FiniteDist.uniform

/-- A constant configuration. -/
def const (b : Bool) : Fin 4 → Bool := fun _ => b

variable (h : Bool → Bool → Bool)

theorem cexModel_solve (u : Fin 4 → Bool) :
    (cexModel h).solve u = ![u 0, u 0, xor (u 0) (u 2), h (xor (u 0) (u 2)) (u 0)] := by
  refine ((cexModel h).isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [cexModel, Finset.restrict]

theorem cexModel_solve_intervene_x (u : Fin 4 → Bool) :
    ((cexModel h).intervene {1} (const false)).solve u = ![u 0, false, u 2, h (u 2) (u 0)] := by
  refine (((cexModel h).intervene {1} (const false)).eq_solve_of_isSolution ?_).symm
  refine (cexModel h).isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [cexModel, Finset.restrict]

theorem cexModel_solve_intervene_z (u : Fin 4 → Bool) :
    ((cexModel h).intervene {2} (const false)).solve u = ![u 0, u 0, false, h false (u 0)] := by
  refine (((cexModel h).intervene {2} (const false)).eq_solve_of_isSolution ?_).symm
  refine (cexModel h).isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [cexModel, Finset.restrict]

/-- Probabilities of events depending on the noises of `U₁` and of `Z` in the model
`cexModel`. -/
theorem probOf_noise_pair (P : Bool × Bool → Prop) [DecidablePred P] :
    (cexModel h).noiseDist.probOf (fun u => P (u 0, u 2)) =
      (if P (false, false) then 1 / 4 else 0) + (if P (false, true) then 1 / 4 else 0) +
        (if P (true, false) then 1 / 4 else 0) + (if P (true, true) then 1 / 4 else 0) := by
  rw [← FiniteDist.probOf_map (cexModel h).noiseDist (fun u => (u 0, u 2)) P]
  change ((FiniteDist.pi fun _ => FiniteDist.uniform).map fun u : Fin 4 → Bool => (u 0, u 2)).probOf
    P = _
  rw [FiniteDist.map_pi_eval_pair _ (by decide)]
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, FiniteDist.prod_apply, FiniteDist.uniform_apply, Fintype.card_bool]
  split_ifs <;> norm_num

/-- **`Y_z ⫫ Z_x | Z` is not implied** (Pearl 2009, section 7.4.4): in the model `cexModel h`
with `h(false, b) = b` (both the exclusive or and the disjunction qualify), `Y_{z = 0} = U₁` and
`Z_{x = 0} = e₂`; given `Z = 0` the two are equal and each is a fair bit, so they are not
conditionally independent. At `Y_z = Z_x = 1`, `Z = 0` the product form reads
`1/4 * 1/2 = 1/8` on the left and `1/4 * 1/4 = 1/16` on the right. The model is a model on the
smoking graph, so `Y_z ⫫ Z_x | {Z, X}` holds in it (`condIndepFun_yz_zx_given_zx`). -/
theorem not_condIndepFun_yz_zx_given_z (hh : ∀ b, h false b = b) :
    ¬ (cexModel h).noiseDist.CondIndepFun
      (fun u => ((cexModel h).intervene {2} (const false)).solve u 3)
      (fun u => ((cexModel h).intervene {1} (const false)).solve u 2)
      (fun u => (cexModel h).solve u 2) := by
  intro hci
  have key := hci true true false
  simp only [cexModel_solve_intervene_z, cexModel_solve_intervene_x, cexModel_solve, hh,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at key
  rw [probOf_noise_pair h (fun q => q.1 = true ∧ q.2 = true ∧ xor q.1 q.2 = false),
    probOf_noise_pair h (fun q => xor q.1 q.2 = false),
    probOf_noise_pair h (fun q => q.1 = true ∧ xor q.1 q.2 = false),
    probOf_noise_pair h (fun q => q.2 = true ∧ xor q.1 q.2 = false)] at key
  norm_num at key

/-- The countermodel with `Y := Z xor U₁`. -/
theorem not_condIndepFun_yz_zx_given_z_xor :
    ¬ (cexModel xor).noiseDist.CondIndepFun
      (fun u => ((cexModel xor).intervene {2} (const false)).solve u 3)
      (fun u => ((cexModel xor).intervene {1} (const false)).solve u 2)
      (fun u => (cexModel xor).solve u 2) :=
  not_condIndepFun_yz_zx_given_z xor fun b => by cases b <;> rfl

/-- The countermodel with `Y := Z ∨ U₁`. -/
theorem not_condIndepFun_yz_zx_given_z_or :
    ¬ (cexModel (· || ·)).noiseDist.CondIndepFun
      (fun u => ((cexModel (· || ·)).intervene {2} (const false)).solve u 3)
      (fun u => ((cexModel (· || ·)).intervene {1} (const false)).solve u 2)
      (fun u => (cexModel (· || ·)).solve u 2) :=
  not_condIndepFun_yz_zx_given_z (· || ·) fun b => by cases b <;> rfl

end Smoking

end SCM

end CausalInference
