/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Bridge

/-!
# Dynamic regimes at a general finite horizon

The g-formula for deterministic dynamic treatment regimes at any finite number `K` of time
points, in the finite setting of `CausalInference.Longitudinal.Basic`. A dynamic regime is a
`Longitudinal.DynamicRegime`: at time `t` it assigns a treatment as a function of the covariate
history `l_0, …, l_t` and the treatment history before `t` (Hernán and Robins, Fine Point 19.1;
Pearl 2009, section 4.4, "conditional plans").

## Main definitions

* `DynamicRegime.headRule`, `DynamicRegime.tailRegime`: the rule at time `0`, and the regime
  followed after time `0` given the first covariate.
* `DynamicRegime.path g l`: the treatment path `a^g` prescribed by `g` along the covariate path
  `l`, defined recursively; `DynamicRegime.path_spec` shows `a^g_t = g_t(l̄_t, ā^g_{t-1})`.
* `DynamicRegime.Follows g A L ω`: the individual `ω` follows `g`, that is
  `A_t = g_t(L̄_t, Ā_{t-1})` at every time; `DynamicRegime.follows_iff` shows this is
  `Ā = a^g(L̄)` (Technical Point 19.1).
* `Longitudinal.gFormulaDyn`, `Longitudinal.iceGFormulaDyn`: the sum-product and the recursive
  forms of the g-formula for `g` (Technical Point 21.1), equal by
  `Longitudinal.gFormulaDyn_eq_iceGFormulaDyn`.
* `Longitudinal.SeqExchangeableDyn`, `Longitudinal.SeqPositiveDyn`: sequential exchangeability
  for a target along `g` (mean independence form) and sequential positivity for `g`.

## Main results

* `Longitudinal.condMean_eq_iceGFormulaDyn`: the core identification theorem, by induction on
  `K` generalizing over the mass function.
* `Longitudinal.expect_eq_gFormulaDyn`: **the dynamic g-formula**. If an individual who follows
  `g` has observed outcome equal to the potential outcome `Y^g` (the consistency condition for
  dynamic regimes of Technical Point 19.2), and sequential exchangeability for `Y^g` and
  sequential positivity for `g` hold, then `E[Y^g] = gFormulaDyn p A L g Y`. Here the potential
  outcome `Y^g` is a given random variable.
* `Longitudinal.Model.cfPath`, `Longitudinal.Model.YpoDyn`: in a `Model`, the counterfactual
  treatment path `ā^g(ω)`, built from the potential covariates `Lpo` and the regime, and the
  potential outcome `Y^g = Y(ā^g)`. Under `Model.Nonanticipating` the path is the unique solution
  of `ā = g.path (L^ā(ω))` (`Model.cfPath_spec`, `Model.cfPath_eq_of_fixed`).
  `Longitudinal.Model.Y_eq_YpoDyn_of_follows`: consistency along `g` is derived from
  `Model.Consistent` and `Model.Nonanticipating`. `Longitudinal.Model.expect_YpoDyn_eq_gFormulaDyn`:
  the dynamic g-formula in a model. `Longitudinal.Model.YpoDyn_ofStatic` and
  `Longitudinal.Model.ofTwoTime_YpoDyn`: the construction gives `Y(ā)` for a static regime and
  `dynamicOutcome2` at two time points.
* `Longitudinal.gFormulaDyn_ofStatic`, `Longitudinal.iceGFormulaDyn_ofStatic`,
  `Longitudinal.Model.seqExchangeableDyn_ofStatic_iff`,
  `Longitudinal.Model.seqPositiveDyn_ofStatic_iff`: static regimes are the constant case.
* `Longitudinal.gFormula2_eq_wmass_mul_gFormulaDyn`, `Longitudinal.gFormulaDyn_two_eq_gFormula2`,
  `DynamicRegime.path_two`, `DynamicRegime.follows_two_iff`,
  `Longitudinal.seqExchangeableDyn_two_iff`, `Longitudinal.seqPositiveDyn_two_iff`: at two time
  points the general form and its assumptions are the `gFormula2` and the assumptions of
  `gFormula2_dynamic`.
* `Longitudinal.DynamicExample.dynamic_beats_static`: a sequentially randomized trial with two
  time points in which the dynamic regime "treat at time `1` if and only if the covariate is
  `true`" has `E[Y^g] = 1` while every static regime has `E[Y(a0, a1)] = 1/2`; the g-formulas
  reproduce both values; `Longitudinal.DynamicExample.g_optimal`: no dynamic regime does better.
  The hypotheses of the identification theorem hold for the nonstatic regime `g`
  (`DynamicExample.consistent_g`, `DynamicExample.seqExchangeableDyn_g`,
  `DynamicExample.seqPositiveDyn_g`), the value of the g-formula is derived from it, and
  `DynamicExample.model_expect_YpoDyn` restates the example on its `Model`.
* `Longitudinal.PositivityFailureExample.not_seqPositive_and_gFormulaDyn_ne`: without sequential
  positivity the totalized dynamic g-formula can differ from `E[Y^g]`.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), chapter 19 and Technical
  Points 19.1, 19.2, 21.1.
* J. Pearl, *Causality*, 2nd edition (2009), section 4.4.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

namespace DynamicRegime

variable {𝒜 𝓛 : Type*}

/-- The decision rule at time `0` of a dynamic regime with `K + 1` time points, as a function of
the first covariate (there is no earlier treatment). -/
def headRule {K : ℕ} (g : DynamicRegime (K + 1) 𝒜 𝓛) (l0 : 𝓛) : 𝒜 :=
  g 0 (fun _ => l0) Fin.elim0

/-- The regime followed after time `0` by an individual with first covariate `l0` who received
the first treatment prescribed by `g`: a dynamic regime with `K` time points whose rule at time
`t` is the rule of `g` at time `t + 1`, with `l0` and `g.headRule l0` prepended to the
histories. -/
def tailRegime {K : ℕ} (g : DynamicRegime (K + 1) 𝒜 𝓛) (l0 : 𝓛) : DynamicRegime K 𝒜 𝓛 :=
  fun t lt la => g t.succ (Fin.cons l0 lt) (Fin.cons (g.headRule l0) la)

/-- The treatment path prescribed by the dynamic regime `g` along the covariate path `l`:
`a^g_t = g_t(l̄_t, ā^g_{t-1})`, defined recursively (Hernán and Robins, Technical Point 21.1).
The value at `t` depends only on `l_0, …, l_t` (`DynamicRegime.path_spec`). -/
def path : {K : ℕ} → DynamicRegime K 𝒜 𝓛 → (Fin K → 𝓛) → Fin K → 𝒜
  | 0, _, _ => Fin.elim0
  | _ + 1, g, l => Fin.cons (g.headRule (l 0)) ((g.tailRegime (l 0)).path (Fin.tail l))

theorem path_cons {K : ℕ} (g : DynamicRegime (K + 1) 𝒜 𝓛) (l0 : 𝓛) (l : Fin K → 𝓛) :
    g.path (Fin.cons l0 l) = Fin.cons (g.headRule l0) ((g.tailRegime l0).path l) := rfl

theorem path_zero {K : ℕ} (g : DynamicRegime (K + 1) 𝒜 𝓛) (l : Fin (K + 1) → 𝓛) :
    g.path l 0 = g.headRule (l 0) := rfl

/-- **The prescribed path follows the rules of the regime.** At every time `t`, the treatment
prescribed by `g` along the covariate path `l` is the rule `g_t` applied to the covariate history
`l_0, …, l_t` and to the prescribed treatment history before `t`:
`a^g_t = g_t(l̄_t, ā^g_{t-1})`. -/
theorem path_spec : ∀ {K : ℕ} (g : DynamicRegime K 𝒜 𝓛) (l : Fin K → 𝓛) (t : Fin K),
    g.path l t = g t (fun s => l (Fin.castLE t.isLt s))
      (fun s => g.path l (Fin.castLE t.isLt.le s))
  | 0, _, _, t => t.elim0
  | K + 1, g, l, t => by
    refine Fin.cases ?_ (fun t => ?_) t
    · change g 0 _ _ = g 0 _ _
      congr 1
      · funext s
        refine congrArg l (Fin.ext ?_)
        have := s.isLt
        simp only [Fin.val_zero] at this ⊢
        change 0 = (s : ℕ)
        omega
      · funext s
        exact s.elim0
    · change path (g.tailRegime (l 0)) (Fin.tail l) t = _
      rw [path_spec (g.tailRegime (l 0)) (Fin.tail l) t]
      change g t.succ _ _ = g t.succ _ _
      congr 1
      · funext s
        refine Fin.cases ?_ (fun s => ?_) s
        · simp only [Fin.cons_zero]
          exact congrArg l (Fin.ext (by simp))
        · simp only [Fin.cons_succ, Fin.tail]
          exact congrArg l (Fin.ext (by simp))
      · funext s
        refine Fin.cases ?_ (fun s => ?_) s
        · simp only [Fin.cons_zero]
          calc _ = g.path l 0 := rfl
            _ = _ := congrArg (g.path l) (Fin.ext (by simp))
        · simp only [Fin.cons_succ]
          calc _ = g.path l (Fin.castLE t.isLt.le s).succ := rfl
            _ = _ := congrArg (g.path l) (Fin.ext (by simp))

/-- **The prescribed treatment at time `t` depends only on the covariates up to time `t`:** two
covariate paths that agree at every time `s ≤ t` give the same prescribed treatment at `t`. -/
theorem path_congr : ∀ {K : ℕ} (g : DynamicRegime K 𝒜 𝓛) {l l' : Fin K → 𝓛} (t : Fin K),
    (∀ s, s ≤ t → l s = l' s) → g.path l t = g.path l' t
  | 0, _, _, _, t, _ => t.elim0
  | K + 1, g, l, l', t, h => by
    have h0 : l 0 = l' 0 := h 0 (Fin.zero_le _)
    refine Fin.cases (motive := fun t => (∀ s, s ≤ t → l s = l' s) → g.path l t = g.path l' t)
      (fun _ => ?_) (fun t ht => ?_) t h
    · rw [path_zero, path_zero, h0]
    · change (g.tailRegime (l 0)).path (Fin.tail l) t =
        (g.tailRegime (l' 0)).path (Fin.tail l') t
      rw [h0]
      exact path_congr _ t fun s hs => ht s.succ (Fin.succ_le_succ_iff.2 hs)

/-- The static regime `a`, seen as a dynamic regime, prescribes `a` along every covariate path. -/
@[simp] theorem path_ofStatic : ∀ {K : ℕ} (a : Fin K → 𝒜) (l : Fin K → 𝓛),
    (ofStatic a : DynamicRegime K 𝒜 𝓛).path l = a
  | 0, a, _ => funext fun t => t.elim0
  | K + 1, a, l => by
    change Fin.cons (a 0) ((ofStatic (Fin.tail a) : DynamicRegime K 𝒜 𝓛).path (Fin.tail l)) = a
    rw [path_ofStatic, Fin.cons_self_tail]

/-- The individual `ω` follows the dynamic regime `g`: at every time `t` the observed treatment
`A_t` is the rule `g_t` applied to the observed covariate history `L̄_t` and to the observed
treatment history `Ā_{t-1}`. -/
def Follows {Ω : Type*} {K : ℕ} (g : DynamicRegime K 𝒜 𝓛) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (ω : Ω) : Prop :=
  ∀ t : Fin K, A t ω = g t (fun s => L (Fin.castLE t.isLt s) ω)
    (fun s => A (Fin.castLE t.isLt.le s) ω)

/-- **Following a regime is following its prescribed path** (Hernán and Robins, Technical Point
19.1): an individual follows `g`, with the rule at each time applied to the observed treatment
history, if and only if the observed treatments are the treatment path that `g` prescribes along
the observed covariate path. -/
theorem follows_iff {Ω : Type*} {K : ℕ} (g : DynamicRegime K 𝒜 𝓛) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (ω : Ω) :
    g.Follows A L ω ↔ ∀ t, A t ω = g.path (fun s => L s ω) t := by
  constructor
  · intro h
    suffices ∀ n (t : Fin K), (t : ℕ) = n → A t ω = g.path (fun s => L s ω) t from
      fun t => this t t rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht
      rw [h t, path_spec]
      congr 1
      funext s
      exact ih s (by rw [← ht]; exact s.isLt) _ rfl
  · intro h t
    rw [h t, path_spec]
    congr 1
    funext s
    exact (h _).symm

end DynamicRegime

section GFormula

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [Fintype 𝓛]
  [DecidableEq 𝓛]

/-- The sum-product form of the g-formula for the deterministic dynamic regime `g` under the
mass function `m` (Hernán and Robins, Technical Point 21.1): the static formula with the
treatment `a_t` replaced by the prescribed `a^g_t`,
`Σ_{l̄} E[Y | L_s = l_s, A_s = a^g_s(l̄) for all s < K]
  · Π_{t < K} P(L_t = l_t | L_s = l_s, A_s = a^g_s(l̄) for all s < t)`.
The visits are indexed from `0`, so the terminal event fixes the visits `t < K`. A ratio with
zero denominator is read as `0`; the identification theorem carries sequential positivity. -/
noncomputable def gFormulaDyn {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) (Y : Ω → ℝ) : ℝ :=
  ∑ l : Fin K → 𝓛, condMean m (hist A L (g.path l) l K) Y *
    ∏ t : Fin K, condProb m (hist A L (g.path l) l t) (ev (L t) (l t))

/-- The recursive (iterated conditional expectation) form of the g-formula for the dynamic
regime `g`. With no time points it is `E[Y]`. With `K + 1` time points it is `Σ_l P(L_0 = l) G_l`,
where `G_l` is the recursive form, for the remaining `K` time points and the regime
`g.tailRegime l`, under `m` restricted to the event `L_0 = l, A_0 = g_0(l)`. -/
noncomputable def iceGFormulaDyn : (K : ℕ) → (Ω → ℝ) → (Fin K → Ω → 𝒜) → (Fin K → Ω → 𝓛) →
    DynamicRegime K 𝒜 𝓛 → (Ω → ℝ) → ℝ
  | 0, m, _, _, _, Y => condMean m univ Y
  | K + 1, m, A, L, g, Y => ∑ l, condProb m univ (ev (L 0) l) *
      iceGFormulaDyn K (restrict m (ev (L 0) l ∩ ev (A 0) (g.headRule l))) (Fin.tail A)
        (Fin.tail L) (g.tailRegime l) Y

/-- The sum-product and the recursive forms of the dynamic g-formula are equal, for every mass
function and with no hypotheses, as an identity of the totalized expressions (each ratio is read
as `0` when its denominator vanishes). It is an algebraic identity only; its probabilistic
reading is `expect_eq_gFormulaDyn`, under sequential positivity. -/
theorem gFormulaDyn_eq_iceGFormulaDyn : ∀ (K : ℕ) (m : Ω → ℝ) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (g : DynamicRegime K 𝒜 𝓛) (Y : Ω → ℝ),
    gFormulaDyn m A L g Y = iceGFormulaDyn K m A L g Y
  | 0, m, A, L, g, Y => by simp [gFormulaDyn, iceGFormulaDyn]
  | K + 1, m, A, L, g, Y => by
    rw [iceGFormulaDyn, gFormulaDyn, ← (Fin.consEquiv fun _ => 𝓛).sum_comp,
      Fintype.sum_prod_type]
    refine sum_congr rfl fun l0 _ => ?_
    rw [← gFormulaDyn_eq_iceGFormulaDyn K, gFormulaDyn, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    simp only [Fin.consEquiv_apply, DynamicRegime.path_cons, Fin.prod_univ_succ, Fin.val_zero,
      Fin.val_succ, hist_zero, Fin.cons_zero, Fin.cons_succ, hist_cons_succ, condMean_restrict,
      condProb_restrict, Fin.tail_cons]
    simp only [Fin.tail]
    ring

/-- Sequential exchangeability for the dynamic regime `g` and the target `Z` (a potential
outcome `Y^g`), in the mean independence form: for every time `t` and covariate path `l`, within
the history event `L̄_t = l̄_t, Ā_{t-1} = ā^g_{t-1}(l̄)` the target is mean independent of the
event `A_t = a^g_t(l̄)` (Hernán and Robins, section 19.4, in mean form). -/
def SeqExchangeableDyn {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) (Z : Ω → ℝ) : Prop :=
  ∀ (l : Fin K → 𝓛) (t : Fin K),
    MeanIndepOn m (histL A L (g.path l) l t) (ev (A t) (g.path l t)) Z

/-- Sequential positivity for the dynamic regime `g`: every history event compatible with `g`
of positive mass keeps positive mass after adding `A_t = a^g_t(l̄)` (Hernán and Robins,
Technical Point 19.2, the form for one strategy). -/
def SeqPositiveDyn {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) : Prop :=
  ∀ (l : Fin K → 𝓛) (t : Fin K), 0 < wmass m (histL A L (g.path l) l t) →
    0 < wmass m (histL A L (g.path l) l t ∩ ev (A t) (g.path l t))

/-- **The recursive dynamic g-formula identifies the mean of the target** (core form). For a
nonnegative mass function of positive total mass, a dynamic regime `g` and a target `Z`, under
sequential exchangeability for `Z` and sequential positivity for `g`,
`E[Z] = iceGFormulaDyn K m A L g Z`. -/
theorem condMean_eq_iceGFormulaDyn : ∀ (K : ℕ) {m : Ω → ℝ} (_hm : ∀ ω, 0 ≤ m ω)
    (_hm0 : 0 < wmass m univ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) (Z : Ω → ℝ) (_hex : SeqExchangeableDyn m A L g Z)
    (_hpos : SeqPositiveDyn m A L g),
    condMean m univ Z = iceGFormulaDyn K m A L g Z
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | K + 1, m, hm, hm0, A, L, g, Z, hex, hpos => by
    rw [condMean_eq_sum_condProb_mul hm hm0 (L 0), iceGFormulaDyn]
    refine sum_congr rfl fun l0 _ => ?_
    rw [univ_inter]
    rcases (wmass_nonneg hm (ev (L 0) l0)).eq_or_lt with h0 | h0
    · rw [condProb_eq_zero_of_wmass_inter_eq_zero hm0 (by rw [univ_inter]; exact h0.symm)]
      simp
    congr 1
    have hL0 : histL A L (g.path fun _ => l0) (fun _ => l0) 0 = ev (L 0) l0 := by
      simp [histL]
    have hA0 : g.path (fun _ => l0) 0 = g.headRule l0 := rfl
    have hH : 0 < wmass m (ev (L 0) l0 ∩ ev (A 0) (g.headRule l0)) := by
      have := hpos (fun _ => l0) 0
      rw [hL0, hA0] at this
      exact this h0
    have hex0 := hex (fun _ => l0) 0
    rw [hL0, hA0] at hex0
    rw [← (meanIndepOn_iff_condMean_eq hm hH).1 hex0,
      show condMean m (ev (L 0) l0 ∩ ev (A 0) (g.headRule l0)) Z =
        condMean (restrict m (ev (L 0) l0 ∩ ev (A 0) (g.headRule l0))) univ Z by
          rw [condMean_restrict, inter_univ]]
    refine condMean_eq_iceGFormulaDyn K (restrict_nonneg hm _)
      (by rw [wmass_restrict, inter_univ]; exact hH) _ _ _ Z (fun l t => ?_) (fun l t => ?_)
    · have := hex (Fin.cons l0 l) t.succ
      rw [DynamicRegime.path_cons, histL_cons_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.tail_cons] at this
      rw [meanIndepOn_restrict]
      exact this
    · have := hpos (Fin.cons l0 l) t.succ
      rw [DynamicRegime.path_cons, histL_cons_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.tail_cons] at this
      rw [wmass_restrict, wmass_restrict, ← inter_assoc]
      exact this

/-- If two functions agree on every full history event compatible with `g`, their dynamic
g-formulas agree. -/
theorem gFormulaDyn_congr {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) {Y Z : Ω → ℝ}
    (h : ∀ l, ∀ ω ∈ hist A L (g.path l) l K, Y ω = Z ω) :
    gFormulaDyn m A L g Y = gFormulaDyn m A L g Z := by
  refine sum_congr rfl fun l _ => ?_
  rw [condMean, condMean, wsum_congr (h l)]

/-- **The g-formula for a deterministic dynamic regime at a general finite horizon** (Hernán and
Robins, Technical Point 21.1; Robins 1986). Let `p` be a finite probability distribution, `g` a
dynamic regime with `K` time points and `Yg` the potential outcome under `g`. Assume the
consistency condition for dynamic regimes of Technical Point 19.2 (an individual who follows `g`
has observed outcome `Y = Yg`), sequential exchangeability for `Yg` along `g` (mean independence
form) and sequential positivity for `g`. Then `E[Y^g] = gFormulaDyn p A L g Y`, and this equals
the recursive form. -/
theorem expect_eq_gFormulaDyn {K : ℕ} (p : FiniteDist Ω) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (Y : Ω → ℝ) (g : DynamicRegime K 𝒜 𝓛) (Yg : Ω → ℝ)
    (hcons : ∀ ω, g.Follows A L ω → Y ω = Yg ω) (hex : SeqExchangeableDyn p A L g Yg)
    (hpos : SeqPositiveDyn p A L g) :
    p.expect Yg = gFormulaDyn p A L g Y ∧
      gFormulaDyn p A L g Y = iceGFormulaDyn K p A L g Y := by
  refine ⟨?_, gFormulaDyn_eq_iceGFormulaDyn K _ _ _ _ _⟩
  have h1 : wmass p univ = 1 := p.sum_eq_one
  have hexp : p.expect Yg = condMean p univ Yg := by
    rw [condMean, h1, div_one]
    rfl
  rw [hexp, condMean_eq_iceGFormulaDyn K p.nonneg (by rw [h1]; exact one_pos) A L g Yg hex hpos,
    ← gFormulaDyn_eq_iceGFormulaDyn]
  refine gFormulaDyn_congr _ _ _ _ fun l ω hω => (hcons ω ?_).symm
  simp only [hist, mem_filter, mem_univ, true_and] at hω
  have hl : (fun s => L s ω) = l := funext fun s => (hω s s.isLt).1
  refine (g.follows_iff A L ω).2 fun t => ?_
  rw [hl]
  exact (hω t t.isLt).2

/-- **Static regimes are the constant case.** For the static regime `a` seen as a dynamic
regime, the dynamic g-formula is the static g-formula `gFormula`. -/
theorem gFormulaDyn_ofStatic {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) (Y : Ω → ℝ) :
    gFormulaDyn m A L (DynamicRegime.ofStatic a) Y = gFormula m A L a Y := by
  simp only [gFormulaDyn, DynamicRegime.path_ofStatic]
  rfl

/-- For the static regime `a` seen as a dynamic regime, the recursive dynamic g-formula is the
recursive static g-formula `iceGFormula`. -/
theorem iceGFormulaDyn_ofStatic {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) (Y : Ω → ℝ) :
    iceGFormulaDyn K m A L (DynamicRegime.ofStatic a) Y = iceGFormula K m A L a Y := by
  rw [← gFormulaDyn_eq_iceGFormulaDyn, gFormulaDyn_ofStatic, gFormula_eq_iceGFormula]

omit [Fintype 𝓛] in
/-- For a static regime, sequential exchangeability along the regime seen as a dynamic regime is
the static sequential exchangeability `Model.SeqExchangeable`. -/
theorem Model.seqExchangeableDyn_ofStatic_iff {K : ℕ} (M : Model Ω K 𝒜 𝓛) (a : Fin K → 𝒜) :
    SeqExchangeableDyn M.p M.A M.L (DynamicRegime.ofStatic a) (M.Ypo a) ↔
      M.SeqExchangeable a := by
  simp only [SeqExchangeableDyn, DynamicRegime.path_ofStatic, Model.SeqExchangeable]

omit [Fintype 𝓛] in
/-- For a static regime, sequential positivity for the regime seen as a dynamic regime is the
static sequential positivity `Model.SeqPositive`. -/
theorem Model.seqPositiveDyn_ofStatic_iff {K : ℕ} (M : Model Ω K 𝒜 𝓛) (a : Fin K → 𝒜) :
    SeqPositiveDyn M.p M.A M.L (DynamicRegime.ofStatic a) ↔ M.SeqPositive a := by
  simp only [SeqPositiveDyn, DynamicRegime.path_ofStatic, Model.SeqPositive]

end GFormula

section TwoTime

namespace DynamicRegime

variable {𝒜 𝓛 : Type*}

/-- At two time points the decision rule at time `0` is `DynamicRegime.first`. -/
theorem headRule_two (g : DynamicRegime 2 𝒜 𝓛) (l0 : 𝓛) : g.headRule l0 = g.first l0 := rfl

/-- At two time points the decision rule at time `1`, after the first covariate `l0` and the
prescribed first treatment, is `DynamicRegime.second` evaluated at that treatment. -/
theorem tailRegime_headRule_two (g : DynamicRegime 2 𝒜 𝓛) (l0 l1 : 𝓛) :
    (g.tailRegime l0).headRule l1 = g.second l0 l1 (g.first l0) := by
  change g 1 _ _ = g 1 _ _
  congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- At two time points the prescribed treatment path along the covariate path `(l0, l1)` is
`(g.first l0, g.second l0 l1 (g.first l0))`, as in `gFormula2_dynamic`. -/
theorem path_two (g : DynamicRegime 2 𝒜 𝓛) (l : Fin 2 → 𝓛) :
    g.path l = ![g.first (l 0), g.second (l 0) (l 1) (g.first (l 0))] := by
  funext t
  fin_cases t
  · rfl
  · exact tailRegime_headRule_two g (l 0) (l 1)

/-- At two time points, following the regime `g` is the antecedent of the consistency
hypothesis of `gFormula2_dynamic`: `A0 = g.first L0` and `A1 = g.second L0 L1 (g.first L0)`. -/
theorem follows_two_iff {Ω : Type*} (g : DynamicRegime 2 𝒜 𝓛) (A : Fin 2 → Ω → 𝒜)
    (L : Fin 2 → Ω → 𝓛) (ω : Ω) :
    g.Follows A L ω ↔ A 0 ω = g.first (L 0 ω) ∧
      A 1 ω = g.second (L 0 ω) (L 1 ω) (g.first (L 0 ω)) := by
  rw [follows_iff, path_two, Fin.forall_fin_two]
  rfl

end DynamicRegime

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [Fintype 𝓛]
  [DecidableEq 𝓛]

/-- **The general-horizon dynamic g-formula at two time points is the two time point dynamic
g-formula.** For a nonnegative mass function and a dynamic regime `g` with two time points, the
unnormalized `gFormula2` with the treatment values prescribed by `g` equals the total mass times
`gFormulaDyn`. Both sides are the totalized expressions (a ratio with zero denominator is read
as `0`), so this is an identity of functionals, not a statement about conditional probabilities
on null events. -/
theorem gFormula2_eq_wmass_mul_gFormulaDyn {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω)
    (A : Fin 2 → Ω → 𝒜) (L : Fin 2 → Ω → 𝓛) (g : DynamicRegime 2 𝒜 𝓛) (Y : Ω → ℝ) :
    gFormula2 m (L 0) (A 0) (L 1) (A 1) g.first (fun l0 l1 => g.second l0 l1 (g.first l0)) Y =
      wmass m univ * gFormulaDyn m A L g Y := by
  rw [gFormulaDyn_eq_iceGFormulaDyn, iceGFormulaDyn, gFormula2, mul_sum]
  refine sum_congr rfl fun l0 _ => ?_
  simp only [iceGFormulaDyn, condProb_restrict, condMean_restrict, restrict_restrict, mul_sum,
    DynamicRegime.tailRegime_headRule_two, DynamicRegime.headRule_two]
  refine sum_congr rfl fun l1 _ => ?_
  have h1 : (Fin.succ (0 : Fin 1)) = (1 : Fin 2) := rfl
  simp only [Fin.tail, h1, inter_univ, inter_assoc]
  have hL0 : wmass m univ * condProb m univ (ev (L 0) l0) = wmass m (ev (L 0) l0) := by
    rw [condProb, univ_inter]
    rcases (wmass_nonneg hm univ).eq_or_lt with h | h
    · rw [← h, zero_mul]
      exact le_antisymm (wmass_nonneg hm _) (h ▸ wmass_mono hm (subset_univ _))
    · field_simp
  rw [← mul_assoc, hL0]
  ring

/-- For a finite probability distribution, the dynamic g-formula at two time points equals the
two time point g-formula `gFormula2` with the treatment values prescribed by `g`. -/
theorem gFormulaDyn_two_eq_gFormula2 (p : FiniteDist Ω) (A : Fin 2 → Ω → 𝒜)
    (L : Fin 2 → Ω → 𝓛) (g : DynamicRegime 2 𝒜 𝓛) (Y : Ω → ℝ) :
    gFormulaDyn p A L g Y =
      gFormula2 p (L 0) (A 0) (L 1) (A 1) g.first (fun l0 l1 => g.second l0 l1 (g.first l0)) Y := by
  have h1 : wmass p univ = 1 := p.sum_eq_one
  rw [gFormula2_eq_wmass_mul_gFormulaDyn p.nonneg, h1, one_mul]

omit [Fintype 𝓛] in
/-- **Translation of sequential exchangeability for a dynamic regime.** At two time points,
sequential exchangeability along `g` (`SeqExchangeableDyn`) is the two time point condition
`SeqExchangeable2` with the treatment values `g.first l0` and `g.second l0 l1 (g.first l0)`
used in `gFormula2_dynamic`. -/
theorem seqExchangeableDyn_two_iff (m : Ω → ℝ) (A : Fin 2 → Ω → 𝒜) (L : Fin 2 → Ω → 𝓛)
    (g : DynamicRegime 2 𝒜 𝓛) (Z : Ω → ℝ) :
    SeqExchangeableDyn m A L g Z ↔ SeqExchangeable2 m (L 0) (A 0) (L 1) (A 1) g.first
      (fun l0 l1 => g.second l0 l1 (g.first l0)) Z := by
  constructor
  · intro h
    refine ⟨fun l0 => ?_, fun l0 l1 => ?_⟩
    · simpa [histL_two_zero, DynamicRegime.path_two] using h ![l0, l0] 0
    · simpa [histL_two_one, DynamicRegime.path_two] using h ![l0, l1] 1
  · rintro ⟨h0, h1⟩ l t
    fin_cases t
    · simpa [histL_two_zero, DynamicRegime.path_two] using h0 (l 0)
    · simpa [histL_two_one, DynamicRegime.path_two] using h1 (l 0) (l 1)

omit [Fintype 𝓛] in
/-- **Translation of sequential positivity for a dynamic regime.** At two time points,
sequential positivity for `g` (`SeqPositiveDyn`) is the two time point condition `SeqPositive2`
with the treatment values prescribed by `g`. -/
theorem seqPositiveDyn_two_iff (m : Ω → ℝ) (A : Fin 2 → Ω → 𝒜) (L : Fin 2 → Ω → 𝓛)
    (g : DynamicRegime 2 𝒜 𝓛) :
    SeqPositiveDyn m A L g ↔ SeqPositive2 m (L 0) (A 0) (L 1) (A 1) g.first
      (fun l0 l1 => g.second l0 l1 (g.first l0)) := by
  constructor
  · intro h
    refine ⟨fun l0 => ?_, fun l0 l1 => ?_⟩
    · simpa [histL_two_zero, DynamicRegime.path_two] using h ![l0, l0] 0
    · simpa [histL_two_one, DynamicRegime.path_two] using h ![l0, l1] 1
  · rintro ⟨h0, h1⟩ l t
    fin_cases t
    · simpa [histL_two_zero, DynamicRegime.path_two] using h0 (l 0)
    · simpa [histL_two_one, DynamicRegime.path_two] using h1 (l 0) (l 1)

end TwoTime

section PotentialOutcome

/-! ### The potential outcome under a dynamic regime in a model -/

namespace Model

variable {Ω : Type*} [Fintype Ω] {𝒜 𝓛 : Type*} {K : ℕ} (M : Model Ω K 𝒜 𝓛)

/-- One step of the construction of the counterfactual treatment path of `ω` under the dynamic
regime `g`: from a candidate treatment path `a`, the path that `g` prescribes along the
potential covariates `L^a(ω)` under `a`. -/
def cfStep (g : DynamicRegime K 𝒜 𝓛) (ω : Ω) (a : Fin K → 𝒜) : Fin K → 𝒜 :=
  g.path fun t => M.Lpo a t ω

/-- The counterfactual treatment path `ā^g(ω)` of `ω` under the dynamic regime `g`: the `K`-fold
iterate of `cfStep` from the constant path at the default treatment. Under
`Model.Nonanticipating` it is the unique path `a` with `a = g.path (L^a(ω))`, that is
`a_t = g_t(L̄^a_t(ω), ā_{t-1})` at every time (`cfPath_spec`, `cfPath_eq_of_fixed`), so it does
not depend on the starting path. -/
def cfPath [Inhabited 𝒜] (g : DynamicRegime K 𝒜 𝓛) (ω : Ω) : Fin K → 𝒜 :=
  (M.cfStep g ω)^[K] fun _ => default

/-- The potential outcome `Y^g` under the dynamic regime `g`: the static potential outcome under
the counterfactual treatment path `ā^g(ω)` (Hernán and Robins, Technical Point 19.2). -/
def YpoDyn [Inhabited 𝒜] (g : DynamicRegime K 𝒜 𝓛) (ω : Ω) : ℝ :=
  M.Ypo (M.cfPath g ω) ω

variable {M}

/-- Under nonanticipation, two candidate paths that agree before time `n` give steps that agree
up to time `n`. -/
theorem cfStep_agree (hna : M.Nonanticipating) (g : DynamicRegime K 𝒜 𝓛) (ω : Ω)
    {a a' : Fin K → 𝒜} {n : ℕ} (h : ∀ s : Fin K, (s : ℕ) < n → a s = a' s) (t : Fin K)
    (ht : (t : ℕ) < n + 1) : M.cfStep g ω a t = M.cfStep g ω a' t := by
  refine g.path_congr t fun s hs => ?_
  rw [hna a a' s fun r hr => h r ?_]
  have := Fin.lt_def.1 hr
  have := Fin.le_def.1 hs
  omega

/-- Under nonanticipation, the `n`-th and the `(n + 1)`-th iterates of `cfStep` agree before
time `n`. -/
theorem cfStep_iterate_agree (hna : M.Nonanticipating) (g : DynamicRegime K 𝒜 𝓛) (ω : Ω)
    (x : Fin K → 𝒜) :
    ∀ n (t : Fin K), (t : ℕ) < n → (M.cfStep g ω)^[n] x t = (M.cfStep g ω)^[n + 1] x t
  | 0, _, ht => absurd ht (Nat.not_lt_zero _)
  | n + 1, t, ht => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact cfStep_agree hna g ω (cfStep_iterate_agree hna g ω x n) t ht

/-- **The counterfactual path is a fixed point**: under nonanticipation,
`ā^g(ω) = g.path (L^{ā^g(ω)}(ω))`. -/
theorem cfPath_spec [Inhabited 𝒜] (hna : M.Nonanticipating) (g : DynamicRegime K 𝒜 𝓛)
    (ω : Ω) : M.cfStep g ω (M.cfPath g ω) = M.cfPath g ω := by
  funext t
  rw [cfPath, ← Function.iterate_succ_apply' (M.cfStep g ω)]
  exact (cfStep_iterate_agree hna g ω _ K t t.isLt).symm

/-- **Uniqueness of the counterfactual path**: under nonanticipation, two fixed points of
`cfStep` are equal. -/
theorem eq_of_cfStep_fixed (hna : M.Nonanticipating) (g : DynamicRegime K 𝒜 𝓛) (ω : Ω)
    {a b : Fin K → 𝒜} (ha : M.cfStep g ω a = a) (hb : M.cfStep g ω b = b) : a = b := by
  suffices ∀ n (t : Fin K), (t : ℕ) < n → a t = b t from funext fun t => this K t t.isLt
  intro n
  induction n with
  | zero => exact fun t ht => absurd ht (Nat.not_lt_zero _)
  | succ n ih =>
    intro t ht
    rw [← ha, ← hb]
    exact cfStep_agree hna g ω ih t ht

/-- Under nonanticipation, every fixed point of `cfStep` is the counterfactual path. -/
theorem cfPath_eq_of_fixed [Inhabited 𝒜] (hna : M.Nonanticipating) (g : DynamicRegime K 𝒜 𝓛)
    (ω : Ω) {b : Fin K → 𝒜} (hb : M.cfStep g ω b = b) : M.cfPath g ω = b :=
  eq_of_cfStep_fixed hna g ω (cfPath_spec hna g ω) hb

/-- **Consistency of the counterfactual path on followers**: under nonanticipation and covariate
consistency, an individual who follows `g` has counterfactual treatment path equal to the
observed one. -/
theorem cfPath_eq_of_follows [Inhabited 𝒜] (hna : M.Nonanticipating)
    (hcov : M.CovariateConsistent) (g : DynamicRegime K 𝒜 𝓛) {ω : Ω}
    (h : g.Follows M.A M.L ω) : M.cfPath g ω = fun t => M.A t ω := by
  refine cfPath_eq_of_fixed hna g ω (funext fun t => ?_)
  have hL : (fun s => M.Lpo (fun t => M.A t ω) s ω) = fun s => M.L s ω :=
    funext fun s => (hcov _ ω s fun _ _ => rfl).symm
  rw [cfStep, hL]
  exact ((g.follows_iff M.A M.L ω).1 h t).symm

/-- **Consistency for a dynamic regime** (Hernán and Robins, Technical Point 19.2), derived from
the model: under nonanticipation and consistency (`Model.Consistent`), an individual who follows
`g` has observed outcome equal to the potential outcome `Y^g`. -/
theorem Y_eq_YpoDyn_of_follows [Inhabited 𝒜] (hna : M.Nonanticipating) (hcons : M.Consistent)
    (g : DynamicRegime K 𝒜 𝓛) {ω : Ω} (h : g.Follows M.A M.L ω) : M.Y ω = M.YpoDyn g ω := by
  rw [YpoDyn, cfPath_eq_of_follows hna hcons.2 g h]
  exact hcons.1 _ ω fun _ => rfl

/-- For a static regime seen as a dynamic regime, the potential outcome `Y^g` is the static
potential outcome. -/
theorem YpoDyn_ofStatic [Inhabited 𝒜] (a : Fin K → 𝒜) :
    M.YpoDyn (DynamicRegime.ofStatic a) = M.Ypo a := by
  funext ω
  have : M.cfPath (DynamicRegime.ofStatic a) ω = a := by
    cases K with
    | zero => exact funext fun t => t.elim0
    | succ K =>
      rw [cfPath, Function.iterate_succ_apply']
      exact DynamicRegime.path_ofStatic a _
  rw [YpoDyn, this]

/-- **The dynamic g-formula in a model** (Hernán and Robins, Technical Point 21.1). In a
longitudinal model, assume nonanticipation, consistency, sequential exchangeability for the
potential outcome `Y^g` along `g` (mean independence form) and sequential positivity for `g`.
Then `E[Y^g] = gFormulaDyn p A L g Y`. Consistency along `g` is derived
(`Y_eq_YpoDyn_of_follows`), not assumed. -/
theorem expect_YpoDyn_eq_gFormulaDyn [Inhabited 𝒜] [DecidableEq Ω] [DecidableEq 𝒜]
    [Fintype 𝓛] [DecidableEq 𝓛] (hna : M.Nonanticipating) (hcons : M.Consistent)
    (g : DynamicRegime K 𝒜 𝓛) (hex : SeqExchangeableDyn M.p M.A M.L g (M.YpoDyn g))
    (hpos : SeqPositiveDyn M.p M.A M.L g) :
    M.p.expect (M.YpoDyn g) = gFormulaDyn M.p M.A M.L g M.Y :=
  (expect_eq_gFormulaDyn M.p M.A M.L M.Y g _
    (fun _ h => Y_eq_YpoDyn_of_follows hna hcons g h) hex hpos).1

/-- **At two time points the potential outcome under a dynamic regime is `dynamicOutcome2`.** On
the model built from two time point data, `Y^g` is the potential outcome `dynamicOutcome2` of
`TwoTime.lean`. -/
theorem ofTwoTime_YpoDyn [Inhabited 𝒜] (p : FiniteDist Ω) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜)
    (L1 : Ω → 𝓛) (A1 : Ω → 𝒜) (Y : Ω → ℝ) (Ypo : 𝒜 → 𝒜 → Ω → ℝ) (L1po : 𝒜 → Ω → 𝓛)
    (g : DynamicRegime 2 𝒜 𝓛) :
    (ofTwoTime p L0 A0 L1 A1 Y Ypo L1po).YpoDyn g = dynamicOutcome2 L0 L1po Ypo g := by
  funext ω
  set b : Fin 2 → 𝒜 :=
    ![g.first (L0 ω), g.second (L0 ω) (L1po (g.first (L0 ω)) ω) (g.first (L0 ω))] with hb
  have hfix : (ofTwoTime p L0 A0 L1 A1 Y Ypo L1po).cfStep g ω b = b := by
    rw [cfStep, DynamicRegime.path_two, hb]
    rfl
  rw [YpoDyn, cfPath_eq_of_fixed (ofTwoTime_nonanticipating p L0 A0 L1 A1 Y Ypo L1po) g ω hfix,
    hb]
  rfl

end Model

end PotentialOutcome

namespace DynamicExample

/-! ### A dynamic regime that beats every static regime -/

/-- The sample space: a point is `(a0, u, a1)`. -/
abbrev Ω := Bool × Bool × Bool

/-- The uniform distribution: the first treatment `a0`, the covariate `u` and the second
treatment `a1` are fair and independent (a sequentially randomized trial). -/
noncomputable def p : FiniteDist Ω where
  mass := fun _ => (1 / 8 : ℝ)
  nonneg _ := by norm_num
  sum_eq_one := by norm_num [Finset.sum_const]

/-- The baseline covariate, constant. -/
def L0 (_ : Ω) : Bool := false

/-- The first treatment. -/
def A0 (ω : Ω) : Bool := ω.1

/-- The covariate at time `1`, unaffected by the first treatment. -/
def L1 (ω : Ω) : Bool := ω.2.1

/-- The second treatment. -/
def A1 (ω : Ω) : Bool := ω.2.2

/-- The outcome: `1` if the second treatment matches the covariate at time `1`, else `0`. -/
noncomputable def Y (ω : Ω) : ℝ := if ω.2.2 = ω.2.1 then 1 else 0

/-- The static potential outcomes: `1` if the second treatment `a1` matches the covariate. -/
noncomputable def Ypo (_ a1 : Bool) (ω : Ω) : ℝ := if a1 = ω.2.1 then 1 else 0

/-- The potential covariate at time `1`, the same under every first treatment. -/
def L1po (_ : Bool) (ω : Ω) : Bool := ω.2.1

/-- The dynamic regime "at each time, treat if and only if the current covariate is `true`":
`g_t(l̄_t, ā_{t-1}) = l_t`. -/
def g : DynamicRegime 2 Bool Bool := fun t l _ => l (Fin.last t)

/-- The rule of `g` at time `0` returns the first covariate. -/
theorem g_first (l0 : Bool) : g.first l0 = l0 := rfl

/-- The rule of `g` at time `1` returns the covariate at time `1`. -/
theorem g_second (l0 l1 a0 : Bool) : g.second l0 l1 a0 = l1 := rfl

/-- The treatments as a family indexed by time. -/
def A : Fin 2 → Ω → Bool := ![A0, A1]

/-- The covariates as a family indexed by time. -/
def L : Fin 2 → Ω → Bool := ![L0, L1]

/-- Outcome consistency for every static regime. -/
theorem outcome_consistent (ω : Ω) (a0 a1 : Bool) (_h0 : A0 ω = a0) (h1 : A1 ω = a1) :
    Y ω = Ypo a0 a1 ω := by
  rw [← h1]; rfl

/-- The mean of every static potential outcome is `1/2`. -/
theorem expect_Ypo (a0 a1 : Bool) : p.expect (Ypo a0 a1) = 1 / 2 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a1 <;> norm_num [p, Ypo]

/-- The mean of the potential outcome under the dynamic regime `g` is `1`. -/
theorem expect_dynamic : p.expect (dynamicOutcome2 L0 L1po Ypo g) = 1 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [p, dynamicOutcome2, Ypo, L1po, g_second]

/-- The static g-formula equals `1/2` for every static regime. -/
theorem gFormula_static (a : Fin 2 → Bool) : gFormula p A L a Y = 1 / 2 := by
  rw [gFormula_two_eq_gFormula2]
  simp only [gFormula2, condMean, condProb, wsum, wmass, ev, filter_inter, inter_filter,
    univ_inter, filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a 0 <;> cases a 1 <;> norm_num [p, A, L, A0, A1, L0, L1, Y]

/-- The potential outcome under `g` is `1` for every individual: the second treatment prescribed
by `g` is the covariate at time `1`. -/
theorem dynamicOutcome_eq_one : dynamicOutcome2 L0 L1po Ypo g = fun _ => 1 := by
  funext ω
  simp [dynamicOutcome2, Ypo, L1po, g_second]

/-- Consistency along `g`: an individual who follows `g` has observed outcome `Y = Y^g`. -/
theorem consistent_g (ω : Ω) (h : g.Follows A L ω) : Y ω = dynamicOutcome2 L0 L1po Ypo g ω := by
  rw [DynamicRegime.follows_two_iff] at h
  exact dynamicOutcome2_consistent g (fun ω a0 a1 h0 h1 => outcome_consistent ω a0 a1 h0 h1)
    (fun _ _ _ => rfl) ω h.1 h.2

/-- Sequential exchangeability for `Y^g` along `g` holds: `Y^g` is constant. -/
theorem seqExchangeableDyn_g : SeqExchangeableDyn p A L g (dynamicOutcome2 L0 L1po Ypo g) := by
  rw [dynamicOutcome_eq_one]
  exact fun _ _ => meanIndepOn_const _ _ _ 1

/-- Sequential positivity for `g` holds: both treatments are randomized with probability `1/2`. -/
theorem seqPositiveDyn_g : SeqPositiveDyn p A L g := by
  rw [seqPositiveDyn_two_iff]
  refine ⟨fun l0 h => ?_, fun l0 l1 h => ?_⟩
  · revert h
    cases l0 <;> norm_num [A, L, wmass, ev, sum_filter, Fintype.sum_prod_type, p, A0, L0,
      g_first]
    exact ⟨(false, false, false), by simp⟩
  · revert h
    cases l0 <;> cases l1 <;> norm_num [A, L, wmass, ev, sum_filter, Fintype.sum_prod_type, p,
      A0, A1, L0, L1, g_first, g_second]
    · exact fun _ => ⟨(false, false, false), by simp⟩
    · exact fun _ => ⟨(false, true, true), by simp⟩

/-- The dynamic g-formula for `g` equals `1`, obtained from the identification theorem
`expect_eq_gFormulaDyn` (whose three hypotheses hold here) and `E[Y^g] = 1`. -/
theorem gFormulaDyn_g : gFormulaDyn p A L g Y = 1 := by
  rw [← (expect_eq_gFormulaDyn p A L Y g _ consistent_g seqExchangeableDyn_g seqPositiveDyn_g).1,
    expect_dynamic]

/-- The trial as a longitudinal model with two time points. -/
noncomputable def model : Model Ω 2 Bool Bool := Model.ofTwoTime p L0 A0 L1 A1 Y Ypo L1po

/-- **The dynamic g-formula on the model.** In the model of the trial, nonanticipation and
consistency hold, the model-level potential outcome `Y^g` is `dynamicOutcome2`, and
`E[Y^g] = gFormulaDyn p A L g Y = 1` by `Model.expect_YpoDyn_eq_gFormulaDyn`. -/
theorem model_expect_YpoDyn :
    model.YpoDyn g = dynamicOutcome2 L0 L1po Ypo g ∧
      model.p.expect (model.YpoDyn g) = gFormulaDyn model.p model.A model.L g model.Y ∧
      model.p.expect (model.YpoDyn g) = 1 := by
  have hY : model.YpoDyn g = dynamicOutcome2 L0 L1po Ypo g := Model.ofTwoTime_YpoDyn ..
  have hcons : model.Consistent :=
    ⟨(Model.ofTwoTime_outcomeConsistent_iff p L0 A0 L1 A1 Y Ypo L1po).2
      fun ω a0 a1 h0 h1 => outcome_consistent ω a0 a1 h0 h1,
      (Model.ofTwoTime_covariateConsistent_iff p L0 A0 L1 A1 Y Ypo L1po).2 fun _ _ _ => rfl⟩
  have hna : model.Nonanticipating := Model.ofTwoTime_nonanticipating p L0 A0 L1 A1 Y Ypo L1po
  have hid := Model.expect_YpoDyn_eq_gFormulaDyn hna hcons g
    (by rw [hY]; exact seqExchangeableDyn_g) seqPositiveDyn_g
  exact ⟨hY, hid, by rw [hY]; exact expect_dynamic⟩

/-- **A dynamic regime beats every static regime.** In this sequentially randomized trial, the
dynamic regime `g` ("treat at time `1` if and only if the covariate is `true`") has
`E[Y^g] = 1`, while every static regime `(a0, a1)` has `E[Y(a0, a1)] = 1/2`; the g-formulas
computed from the observed data reproduce both values. -/
theorem dynamic_beats_static :
    (∀ a0 a1 : Bool, p.expect (Ypo a0 a1) < p.expect (dynamicOutcome2 L0 L1po Ypo g)) ∧
      ∀ a : Fin 2 → Bool, gFormula p A L a Y < gFormulaDyn p A L g Y := by
  refine ⟨fun a0 a1 => ?_, fun a => ?_⟩
  · rw [expect_Ypo, expect_dynamic]; norm_num
  · rw [gFormula_static, gFormulaDyn_g]; norm_num

/-- **The regime `g` is optimal among all dynamic regimes.** Every dynamic regime `g'` with two
time points has `E[Y^{g'}] ≤ E[Y^g] = 1`, since the outcome is at most `1`. -/
theorem g_optimal (g' : DynamicRegime 2 Bool Bool) :
    p.expect (dynamicOutcome2 L0 L1po Ypo g') ≤ p.expect (dynamicOutcome2 L0 L1po Ypo g) := by
  rw [expect_dynamic, ← p.expect_const 1]
  refine p.expect_mono fun ω => ?_
  simp only [dynamicOutcome2, Ypo]
  split_ifs <;> norm_num

end DynamicExample

namespace PositivityFailureExample

/-! ### Without positivity the dynamic g-formula fails -/

/-- The uniform distribution on the two values of a fair binary covariate. -/
noncomputable def p : FiniteDist Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  sum_eq_one := by norm_num

/-- The covariate at the single time point: the sample point itself. -/
def L : Fin 1 → Bool → Bool := fun _ ω => ω

/-- The treatment: nobody is treated. -/
def A : Fin 1 → Bool → Bool := fun _ _ => false

/-- The regime "treat if and only if the covariate is `true`". -/
def g : DynamicRegime 1 Bool Bool := fun t l _ => l (Fin.last t)

/-- The observed outcome, equal to `1`. -/
def Y : Bool → ℝ := fun _ => 1

/-- The potential outcome under `g`, equal to `1`. -/
def Yg : Bool → ℝ := fun _ => 1

/-- **Positivity cannot be dropped from the dynamic g-formula.** With one time point, a fair
binary covariate `L`, no treated individual and the regime `g(L) = L`, consistency along `g` and
sequential exchangeability for `Y^g = 1` hold but sequential positivity fails (at `L = true` the
regime prescribes a treatment nobody receives); the totalized g-formula is `1/2` while
`E[Y^g] = 1`. -/
theorem not_seqPositive_and_gFormulaDyn_ne :
    (∀ ω, g.Follows A L ω → Y ω = Yg ω) ∧ SeqExchangeableDyn p A L g Yg ∧
      ¬ SeqPositiveDyn p A L g ∧ p.expect Yg = 1 ∧ gFormulaDyn p A L g Y = 1 / 2 := by
  refine ⟨fun _ _ => rfl, fun _ _ => meanIndepOn_const _ _ _ 1, fun h => ?_, p.expect_const 1, ?_⟩
  · have := h (fun _ => true) 0
    revert this
    norm_num [histL, hist, wmass, ev, sum_filter, p, A, L, g, DynamicRegime.path_zero,
      DynamicRegime.headRule]
    decide
  · rw [gFormulaDyn_eq_iceGFormulaDyn]
    simp only [iceGFormulaDyn, condProb, condMean, wmass, wsum, restrict, ev, filter_inter,
      inter_filter, univ_inter, filter_filter, sum_filter, Fintype.sum_bool]
    norm_num [p, A, L, g, Y, DynamicRegime.headRule]

end PositivityFailureExample

end Longitudinal

end CausalInference
