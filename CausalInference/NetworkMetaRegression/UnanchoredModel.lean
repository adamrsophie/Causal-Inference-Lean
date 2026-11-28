/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.IdentifiabilityInstances
public import CausalInference.IndirectComparison.Constancy

/-!
# The unanchored multilevel model

An **unanchored** comparison has no common comparator: study `j_A` reports individual data on
treatment `a` only, study `j_B` reports the aggregate mean of treatment `b` only. In the
multilevel model (`MultilevelModel`) the two observed arms have the linear predictors

`η_A(x) = (μ_{j_A} + γ_a) + xᵀ(β₁ + β₂,a)`, `η_B(x) = (μ_{j_B} + γ_b) + xᵀ(β₁ + β₂,b)`,

so the data depend on the model only through the **cell intercepts** `μ_{j_A} + γ_a`,
`μ_{j_B} + γ_b` (`cellIntercept`) and the **cell slopes** `β₁ + β₂,a`, `β₁ + β₂,b`
(`cellSlope`). The estimand of `b` against `a` in a target with covariate law `F*` is the
marginal estimand `linkMarginal g F* m_A m_B` of the two observed surfaces, each at the baseline
of its own study.

The **shared prognostic effects** assumption is the equality of the two cell slopes; in the
multilevel model it is the shared effect modifier assumption for `{a, b}`
(`sharedEffectModifiers_pair_iff_cellSlope`): the prognostic effects `β₁` cancel.

## Main definitions

* `MultilevelModel.cellIntercept`, `MultilevelModel.cellSlope`.
* `MultilevelModel.unanchoredData`: the individual data law of study `j_A` (covariate law
  `F_A` composed with the outcome law of mean `m_A(x)`) paired with the aggregate mean of `b`
  in study `j_B` under its covariate law `F_B`.

## Main results

* `unanchoredData_congr`, `unanchoredData_eq_of_cell_eq`: the data depend on the model only
  through the cell parameters.
* **Conflation** (`not_pointIdentified_γ_unanchored`, `not_pointIdentified_μ_unanchored`): the
  treatment effect `γ_a` and the study intercept `μ_{j_A}` are not identified, by two concrete
  models with the same data.
* **Constant contrast** (`linkContrast_unanchored_iff`): for a link `g` inverting `g⁻¹` and a
  covariate law of full affine rank, the conditional contrast of the two observed surfaces is
  almost everywhere constant exactly under shared effect modifiers, and its value is the
  difference of the cell intercepts.
* **Absolute constancy is equality of study baselines**
  (`structurallyInvariant_iff_μ_eq`): between two populations in which the model surfaces of
  arm `t` at the study baselines are conditional mean functions, absolute constancy
  (`StructurallyInvariant`) holds exactly when the two study intercepts agree.
* **Relative constancy constrains the support only** (`relativeConstancy_not_pointwise`).

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis
  Transport

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-! ### Cell parameters -/

/-- The **cell intercept** `μ_j + γ_k` of arm `k` in study `j`. -/
def cellIntercept (M : MultilevelModel J K p) (j : J) (k : K) : ℝ := M.μ j + M.γ k

/-- The **cell slope** `β₁ + β₂,k` of arm `k`. -/
def cellSlope (M : MultilevelModel J K p) (k : K) : Fin p → ℝ := M.β₁ + M.β₂ k

/-- The surface of arm `k` at the baseline of study `j` is `g⁻¹` of the cell predictor. -/
theorem surface_eq_cell (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (j : J) (k : K) :
    M.surface ginv (M.μ j) k = fun x => ginv (M.cellIntercept j k + x ⬝ᵥ M.cellSlope k) :=
  funext fun x => by rw [surface, eta_eq_affine]; rfl

/-- The arm mean of `k` at the baseline of study `j` is the shift mean at the cell intercept. -/
theorem armMean_eq_cell (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (j : J)
    (F : Measure (Fin p → ℝ)) (k : K) :
    M.armMean ginv (M.μ j) F k =
      shiftMean F ginv (fun x => x ⬝ᵥ M.cellSlope k) (M.cellIntercept j k) :=
  armMean_eq_shiftMean ginv M (M.μ j) F k

/-- **Shared prognostic effects are shared effect modifiers.** The cell slopes of `a` and `b`
agree exactly when `a` and `b` share their effect modifiers: the prognostic effects cancel. -/
theorem sharedEffectModifiers_pair_iff_cellSlope (M : MultilevelModel J K p) (a b : K) :
    M.SharedEffectModifiers {a, b} ↔ M.cellSlope a = M.cellSlope b := by
  rw [sharedEffectModifiers_iff]
  constructor
  · intro h
    simp only [cellSlope, h a (by simp) b (by simp)]
  · intro h c hc d hd
    have h' : M.β₂ a = M.β₂ b := add_left_cancel h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp [h']

/-! ### The data of the unanchored network -/

/-- The **data of the unanchored network**. The outcome law of a patient with covariates `x` is
`π (m(x))` for a Markov kernel `π` (an outcome family indexed by its mean, in the results); the
individual data of study `j_A` on arm `a` have the joint law `F_A ⊗ π(m_A(·))` of covariates and
outcome, with `m_A` the surface of `a` at the baseline `μ_{j_A}`; study `j_B` reports the
aggregate mean of `b` at the baseline `μ_{j_B}` under its covariate law `F_B`. -/
noncomputable def unanchoredData (π : Kernel ℝ ℝ) {ginv : ℝ → ℝ} (hginv : Measurable ginv)
    (FA FB : Measure (Fin p → ℝ)) (jA jB : J) (a b : K) (M : MultilevelModel J K p) :
    Measure ((Fin p → ℝ) × ℝ) × ℝ :=
  (FA ⊗ₘ π.comap (M.surface ginv (M.μ jA) a) (M.measurable_surface hginv _ a),
    M.armMean ginv (M.μ jB) FB b)

variable {π : Kernel ℝ ℝ} {ginv : ℝ → ℝ} {hginv : Measurable ginv} {FA FB : Measure (Fin p → ℝ)}
  {jA jB : J} {a b : K}

/-- Two models with the same surface of `a` in `j_A` and the same aggregate mean of `b` in
`j_B` have the same data. -/
theorem unanchoredData_congr {M M' : MultilevelModel J K p}
    (ha : M.surface ginv (M.μ jA) a = M'.surface ginv (M'.μ jA) a)
    (hb : M.armMean ginv (M.μ jB) FB b = M'.armMean ginv (M'.μ jB) FB b) :
    unanchoredData π hginv FA FB jA jB a b M = unanchoredData π hginv FA FB jA jB a b M' := by
  have hk : π.comap (M.surface ginv (M.μ jA) a) (M.measurable_surface hginv _ a) =
      π.comap (M'.surface ginv (M'.μ jA) a) (M'.measurable_surface hginv _ a) := by
    ext1 x
    simp only [Kernel.comap_apply, ha]
  simp only [unanchoredData, hk, hb]

/-- **The data depend on the model only through the cell parameters** `μ_{j_A} + γ_a`,
`β₁ + β₂,a`, `μ_{j_B} + γ_b`, `β₁ + β₂,b`. -/
theorem unanchoredData_eq_of_cell_eq {M M' : MultilevelModel J K p}
    (hia : M.cellIntercept jA a = M'.cellIntercept jA a) (hsa : M.cellSlope a = M'.cellSlope a)
    (hib : M.cellIntercept jB b = M'.cellIntercept jB b) (hsb : M.cellSlope b = M'.cellSlope b) :
    unanchoredData π hginv FA FB jA jB a b M = unanchoredData π hginv FA FB jA jB a b M' :=
  unanchoredData_congr (by rw [surface_eq_cell, surface_eq_cell, hia, hsa])
    (by rw [armMean_eq_cell, armMean_eq_cell, hib, hsb])

/-! ### Conflation of the study intercept and the treatment effect -/

section Conflation

variable [DecidableEq J] [DecidableEq K]

/-- The model with all parameters `0` except `μ_{j_A} = 1` and `γ_a = -1`. -/
def conflatedModel (jA : J) (a : K) : MultilevelModel J K p :=
  ⟨Function.update 0 jA 1, 0, Function.update 0 a (-1), 0⟩

/-- The two models `⟨0, 0, 0, 0⟩` and `conflatedModel` have the same unanchored data whenever
`j_A ≠ j_B` and `a ≠ b`: their cell parameters agree. -/
theorem unanchoredData_conflatedModel (hj : jA ≠ jB) (hab : a ≠ b) :
    unanchoredData π hginv FA FB jA jB a b (conflatedModel (p := p) jA a) =
      unanchoredData π hginv FA FB jA jB a b ⟨0, 0, 0, 0⟩ := by
  refine unanchoredData_eq_of_cell_eq ?_ ?_ ?_ ?_ <;>
    simp [conflatedModel, cellIntercept, cellSlope, Function.update_of_ne hj.symm,
      Function.update_of_ne hab.symm]

omit [DecidableEq J] [DecidableEq K] in
/-- **The treatment effect is not identified in the unanchored network.** If `j_A ≠ j_B` and
`a ≠ b`, then `γ_a` is not point identified from the unanchored data, among all models: the
models `⟨0, 0, 0, 0⟩` and `conflatedModel` have the same data and `γ_a = 0`, `γ_a = -1`. -/
theorem not_pointIdentified_γ_unanchored (hj : jA ≠ jB) (hab : a ≠ b) :
    ¬PointIdentified (Set.univ : Set (MultilevelModel J K p))
      (unanchoredData π hginv FA FB jA jB a b) (fun M => M.γ a) := by
  classical
  intro h
  have := h _ trivial _ trivial (unanchoredData_conflatedModel hj hab)
  simp [conflatedModel] at this

omit [DecidableEq J] [DecidableEq K] in
/-- **The study intercept is not identified in the unanchored network**: under the hypotheses
of `not_pointIdentified_γ_unanchored`, `μ_{j_A}` is `1` in `conflatedModel` and `0` in the
model `⟨0, 0, 0, 0⟩`. -/
theorem not_pointIdentified_μ_unanchored (hj : jA ≠ jB) (hab : a ≠ b) :
    ¬PointIdentified (Set.univ : Set (MultilevelModel J K p))
      (unanchoredData π hginv FA FB jA jB a b) (fun M => M.μ jA) := by
  classical
  intro h
  have := h _ trivial _ trivial (unanchoredData_conflatedModel hj hab)
  simp [conflatedModel] at this

/-- **Instance of the conflation theorems** with two studies and two treatments indexed by
`Bool`, one covariate, the identity link and the outcome kernel `x ↦ δ_x`. -/
theorem not_pointIdentified_γ_unanchored_instance :
    ¬PointIdentified (Set.univ : Set (MultilevelModel Bool Bool 1))
        (unanchoredData (Kernel.deterministic id measurable_id) measurable_id (binaryLaw (1 / 2))
          (binaryLaw (1 / 2)) true false true false) (fun M => M.γ true) ∧
      ¬PointIdentified (Set.univ : Set (MultilevelModel Bool Bool 1))
        (unanchoredData (Kernel.deterministic id measurable_id) measurable_id (binaryLaw (1 / 2))
          (binaryLaw (1 / 2)) true false true false) (fun M => M.μ true) :=
  ⟨not_pointIdentified_γ_unanchored (by decide) (by decide),
    not_pointIdentified_μ_unanchored (by decide) (by decide)⟩

end Conflation

/-! ### The conditional contrast of the two observed surfaces -/

/-- **The conditional contrast is constant exactly under shared prognostic effects.** Let
`g (g⁻¹ y) = y` for every `y`. Under shared effect modifiers for `{a, b}` the contrast
`g(m_B(x)) - g(m_A(x))` of the surfaces of `b` in `j_B` and `a` in `j_A` is the difference
`(μ_{j_B} + γ_b) - (μ_{j_A} + γ_a)` of the cell intercepts at every `x`. Conversely, if the
contrast is almost everywhere constant under a covariate law of full affine rank, `a` and `b`
share their effect modifiers. -/
theorem linkContrast_unanchored_iff {g : ℝ → ℝ} (hg : ∀ y, g (ginv y) = y)
    (M : MultilevelModel J K p) (jA jB : J) (a b : K) {F : Measure (Fin p → ℝ)}
    (hF : AffineRank F) :
    (M.SharedEffectModifiers {a, b} ↔ ∃ c, ∀ᵐ x ∂F,
      linkContrast g (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b) x = c) ∧
      (M.SharedEffectModifiers {a, b} → ∀ x,
        linkContrast g (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b) x =
          M.cellIntercept jB b - M.cellIntercept jA a) := by
  have e : ∀ x, linkContrast g (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b) x =
      (M.cellIntercept jB b + x ⬝ᵥ M.cellSlope b) - (M.cellIntercept jA a + x ⬝ᵥ M.cellSlope a) :=
    fun x => by simp only [linkContrast, surface_eq_cell, hg]
  have hconst : M.SharedEffectModifiers {a, b} → ∀ x,
      linkContrast g (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b) x =
        M.cellIntercept jB b - M.cellIntercept jA a := fun h x => by
    rw [e, (sharedEffectModifiers_pair_iff_cellSlope M a b).1 h]
    ring
  refine ⟨⟨fun h => ⟨_, ae_of_all _ (hconst h)⟩, fun ⟨c, hc⟩ => ?_⟩, hconst⟩
  rw [sharedEffectModifiers_pair_iff_cellSlope]
  have := hF.eq (s := M.cellIntercept jB b - c) (b := M.cellSlope b)
    (s' := M.cellIntercept jA a) (b' := M.cellSlope a) (hc.mono fun x hx => by
      rw [e] at hx
      linarith)
  exact this.2.symm

/-- **Instance of the constant contrast theorem** on the identity scale with `binaryLaw (1/2)`:
the model with cell intercepts `1` and `3` and the common slope `2` has contrast `2` at every
covariate value, and `a` and `b` share their effect modifiers. -/
theorem linkContrast_unanchored_instance :
    let M : MultilevelModel Bool Bool 1 := ⟨fun j => if j then 1 else 3, fun _ => 2, 0, 0⟩
    (∃ c, ∀ᵐ x ∂binaryLaw (1 / 2), linkContrast id (M.surface id (M.μ true) true)
        (M.surface id (M.μ false) false) x = c) ∧
      ∀ x, linkContrast id (M.surface id (M.μ true) true) (M.surface id (M.μ false) false) x =
        2 := by
  intro M
  have hS : M.SharedEffectModifiers {true, false} := by
    rw [sharedEffectModifiers_iff]; intro _ _ _ _; rfl
  obtain ⟨h1, h2⟩ := linkContrast_unanchored_iff (g := id) (ginv := id) (fun _ => rfl) M true
    false true false affineRank_binaryLaw_half
  refine ⟨h1.1 hS, fun x => ?_⟩
  rw [h2 hS x]
  simp [M, cellIntercept]
  norm_num

/-! ### Absolute constancy between the two studies -/

section Constancy

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- **Absolute constancy is equality of the study baselines.** Let `g⁻¹` be injective, and let
`P` and `Q` be populations (of studies `j_A` and `j_B`) with measurable covariates in which the
model surface of arm `t` at the study baseline is a conditional mean function of `Y(t)`. If
`Q_X ≪ P_X` and `Q_X ≠ 0`, absolute constancy of arm `t` from `P` to `Q` holds exactly when
`μ_{j_A} = μ_{j_B}`. -/
theorem structurallyInvariant_iff_μ_eq (hinj : Function.Injective ginv)
    (M : MultilevelModel J K p) {P : Population Ω₁ (Fin p → ℝ) K}
    {Q : Population Ω₂ (Fin p → ℝ) K} (hXP : Measurable P.X) (hXQ : Measurable Q.X)
    (hov : Q.covLaw ≪ P.covLaw) (hQ : Q.covLaw ≠ 0) {t : K}
    (hP : P.IsCondMean t (M.surface ginv (M.μ jA) t))
    (hQt : Q.IsCondMean t (M.surface ginv (M.μ jB) t)) :
    StructurallyInvariant P.μ P.X (P.Y t) Q.μ Q.X (Q.Y t) ↔ M.μ jA = M.μ jB := by
  constructor
  · rintro ⟨m, hm⟩
    rw [Population.isCommonRegression_iff] at hm
    have h1 : ∀ᵐ x ∂Q.covLaw, M.surface ginv (M.μ jA) t x = m x := hov.ae_le (hP.ae_eq hXP hm.1)
    have h2 : ∀ᵐ x ∂Q.covLaw, M.surface ginv (M.μ jB) t x = m x := hQt.ae_eq hXQ hm.2
    have : (ae Q.covLaw).NeBot := ae_neBot.2 hQ
    obtain ⟨x, hx⟩ := (Filter.Eventually.and h1 h2).exists
    have := hinj (hx.1.trans hx.2.symm)
    have h3 := M.eta_sub_eta (M.μ jA) (M.μ jB) t x
    rw [this, sub_self] at h3
    linarith
  · intro h
    refine ⟨M.surface ginv (M.μ jA) t, ?_⟩
    rw [Population.isCommonRegression_iff]
    exact ⟨hP, h ▸ hQt⟩

end Constancy

/-- **Instance of `structurallyInvariant_iff_μ_eq`**: with one covariate, the identity link and
both populations the surface populations of the model `⟨μ, 0, 0, 0⟩` with `μ true = 0`,
`μ false = 1` under `binaryLaw (1/2)`, absolute constancy of arm `true` fails, since the study
intercepts differ. -/
theorem structurallyInvariant_iff_μ_eq_instance :
    let M : MultilevelModel Bool Bool 1 := ⟨fun j => if j then 0 else 1, 0, 0, 0⟩
    ¬StructurallyInvariant (binaryLaw (1 / 2)) id (M.surface id (M.μ true) true)
      (binaryLaw (1 / 2)) id (M.surface id (M.μ false) true) := by
  intro M
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have hc : ∀ α : ℝ, (⟨binaryLaw (1 / 2), id, fun t => M.surface id α t⟩ :
      Population (Fin 1 → ℝ) (Fin 1 → ℝ) Bool).IsCondMean true (M.surface id α true) :=
    fun α => Population.isCondMean_of_eq_comp measurable_id
      (M.measurable_surface measurable_id α true) rfl (integrable_binaryLaw _ _)
  have hcov : (⟨binaryLaw (1 / 2), id, fun t => M.surface id (M.μ false) t⟩ :
      Population (Fin 1 → ℝ) (Fin 1 → ℝ) Bool).covLaw = binaryLaw (1 / 2) := by
    simp [Population.covLaw]
  have hP : (⟨binaryLaw (1 / 2), id, fun t => M.surface id (M.μ true) t⟩ :
      Population (Fin 1 → ℝ) (Fin 1 → ℝ) Bool).covLaw = binaryLaw (1 / 2) := by
    simp [Population.covLaw]
  have h := structurallyInvariant_iff_μ_eq (jA := true) (jB := false) (ginv := id)
    Function.injective_id M measurable_id measurable_id (by rw [hP, hcov])
    (by rw [hcov]; exact IsProbabilityMeasure.ne_zero _) (hc _) (hc _)
  intro hs
  have := h.1 hs
  simp [M] at this

/-! ### Relative constancy and the support -/

/-- The population on the covariate space `Bool` with a single unit, covariate `false` and all
potential outcomes `0`. -/
noncomputable def falsePopulation : Population Unit Bool Bool :=
  ⟨Measure.dirac (), fun _ => false, fun _ _ => 0⟩

/-- **Relative constancy does not constrain the conditional contrast off the support.** With
both populations `falsePopulation`, relative constancy of `true` against `false` on the
identity scale holds, the functions `m₁ ≡ 0` and `m₂ t x = 1{t ∧ x}` are conditional mean
functions of both arms, and yet their conditional contrasts differ at the covariate value
`true`, which the covariate laws do not charge. -/
theorem relativeConstancy_not_pointwise :
    RelativeConstancy id falsePopulation falsePopulation false true ∧
      (∀ t, falsePopulation.IsCondMean t (fun _ => 0)) ∧
      (∀ t, falsePopulation.IsCondMean t (fun x => if t && x then 1 else 0)) ∧
      linkContrast id (fun _ => 0) (fun _ => 0) true ≠
        linkContrast id (fun x => if false && x then 1 else 0)
          (fun x => if true && x then 1 else 0) true := by
  have : IsFiniteMeasure falsePopulation.μ := by unfold falsePopulation; infer_instance
  have hcm : ∀ (t : Bool) (m : Bool → ℝ), m false = 0 → falsePopulation.IsCondMean t m :=
    fun t m hm => Population.isCondMean_of_eq_comp (R := falsePopulation) measurable_const
      (measurable_of_countable m) (funext fun _ => hm.symm) (integrable_const _)
  refine ⟨RelativeConstancy.refl (hcm _ (fun _ => 0) rfl) (hcm _ (fun _ => 0) rfl),
    fun t => hcm t (fun _ => 0) rfl,
    fun t => hcm t _ (by simp), ?_⟩
  simp [linkContrast]

end MultilevelModel

end NetworkMetaRegression

end CausalInference
