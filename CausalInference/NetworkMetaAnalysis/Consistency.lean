/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.Incidence
public import CausalInference.IndirectComparison.Constancy
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Network meta-analysis: the consistency equations and their closure

A family `d a b` of relative effects (the effect of `b` relative to `a`) for all ordered pairs of
treatments is **consistent** (`IsConsistent`) when `d_ab = d_cb - d_ca` for all treatments
`a, b, c`: the effect of `b` relative to `a` is the indirect comparison through any third
treatment `c`. The closure of these equations:

* a consistent family has zero diagonal, is antisymmetric and additive along paths
  (`IsConsistent.self`, `IsConsistent.antisymm`, `isConsistent_iff_add`);
* every contrast is determined by the **basic parameters** `d_rk` against a reference `r`:
  `d_ab = d_rb - d_ra` (`IsConsistent.eq_sub_reference`);
* consistency holds exactly when there is a vector `θ` of treatment levels with
  `d_ab = θ_b - θ_a` (`isConsistent_iff_exists_level`), unique once `θ_r = 0`
  (`IsConsistent.existsUnique_level`);
* the consistent families form a subspace of dimension `T - 1`, inside the antisymmetric
  families of dimension `C(T, 2)`, so consistency imposes `C(T - 1, 2)` independent constraints
  (`finrank_consistentContrasts_add_one`, `consistentContrasts_loop_count`).

On a network of comparisons `e : E` (an ordered pair `tail e → head e`), contrasts `δ : E → ℝ`
assigned to the comparisons are consistent when they are the contrasts of one level vector,
`δ = B θ` for the incidence matrix `B`, equivalently `δ = X d` for the reduced design and basic
parameters `d` (`exists_level_iff_exists_basic`), with `d` unique for a connected network. The
**cycle conditions**: `δ` is consistent exactly when `∑_e c_e δ_e = 0` for every circulation
`c` (a flow on the comparisons with `Bᵀ c = 0`, a combination of cycles)
(`exists_level_iff_circulation`); in a triangle `a → b → c`, `a → c` this is
`δ_ab + δ_bc = δ_ac` (`triangle_of_exists_level`).

Constant relative effects across populations give a consistent network contrast
(`ConstantRelativeEffects.exists_isConsistent_networkContrast`); for three treatments this is
the step the triangle results of `IndirectComparison.ConstancyTwoOfThree` take.

## Main definitions

* `IsConsistent`, `consistentContrasts`, `antisymmetricContrasts`.

## Main results

* `isConsistent_iff_add`, `IsConsistent.eq_sub_reference`, `isConsistent_iff_exists_level`,
  `IsConsistent.existsUnique_level`.
* `finrank_consistentContrasts_add_one`, `consistentContrasts_loop_count`.
* `exists_level_iff_exists_basic`, `existsUnique_basic_of_connected`,
  `exists_level_iff_circulation`, `triangle_of_exists_level`.
* `ConstantRelativeEffects.exists_isConsistent_networkContrast`.

## References

* G. Lu and A. E. Ades, *Combination of direct and indirect evidence in mixed treatment
  comparisons*, Statistics in Medicine 23 (2004).
* G. Lu and A. E. Ades, *Assessing evidence inconsistency in mixed treatment comparisons*,
  Journal of the American Statistical Association 101 (2006).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix

/-! ### Consistency of a family of relative effects -/

section Closure

variable {K : Type*}

/-- A family `d a b` of relative effects (the effect of `b` relative to `a`) is **consistent**
when `d_ab = d_cb - d_ca` for all treatments `a, b, c`: every direct contrast equals the
indirect comparison through every third treatment. -/
def IsConsistent (d : K → K → ℝ) : Prop := ∀ a b c, d a b = d c b - d c a

variable {d : K → K → ℝ}

/-- A consistent family has zero diagonal. -/
theorem IsConsistent.self (h : IsConsistent d) (a : K) : d a a = 0 := by
  have := h a a a; linarith

/-- A consistent family is antisymmetric: `d_ba = -d_ab`. -/
theorem IsConsistent.antisymm (h : IsConsistent d) (a b : K) : d b a = -d a b := by
  have := h b a a; have := h.self a; linarith

/-- **Consistency is additivity along paths**: `d_ab + d_bc = d_ac` for all `a, b, c`. -/
theorem isConsistent_iff_add : IsConsistent d ↔ ∀ a b c, d a b + d b c = d a c := by
  refine ⟨fun h a b c => ?_, fun h a b c => ?_⟩
  · have := h a c b; have := h.antisymm b a; linarith
  · have h1 := h a a a
    have h2 := h c a c
    have h3 := h c a b
    linarith

/-- **Closure: the basic parameters determine every contrast.** For a consistent family and a
reference treatment `r`, `d_ab = d_rb - d_ra`. -/
theorem IsConsistent.eq_sub_reference (h : IsConsistent d) (r a b : K) :
    d a b = d r b - d r a :=
  h a b r

/-- **Consistency is the existence of treatment levels**: `d` is consistent exactly when
`d_ab = θ_b - θ_a` for some vector `θ`. -/
theorem isConsistent_iff_exists_level : IsConsistent d ↔ ∃ θ : K → ℝ, ∀ a b, d a b = θ b - θ a := by
  constructor
  · intro h
    by_cases hK : Nonempty K
    · obtain ⟨r⟩ := hK
      exact ⟨d r, h.eq_sub_reference r⟩
    · exact ⟨0, fun a => absurd ⟨a⟩ hK⟩
  · rintro ⟨θ, hθ⟩ a b c
    rw [hθ, hθ, hθ]; ring

/-- **The level vector is unique once the reference is fixed**: a consistent family has exactly
one level vector `θ` with `θ_r = 0`, namely `θ_k = d_rk`. -/
theorem IsConsistent.existsUnique_level (h : IsConsistent d) (r : K) :
    ∃! θ : K → ℝ, θ r = 0 ∧ ∀ a b, d a b = θ b - θ a := by
  refine ⟨d r, ⟨h.self r, h.eq_sub_reference r⟩, fun θ ⟨hr, hθ⟩ => funext fun k => ?_⟩
  rw [hθ r k, hr, sub_zero]

/-- The level contrasts `θ_b - θ_a` of a vector are consistent. -/
theorem isConsistent_sub (θ : K → ℝ) : IsConsistent fun a b => θ b - θ a :=
  isConsistent_iff_exists_level.2 ⟨θ, fun _ _ => rfl⟩

variable (K) in
/-- The subspace of **antisymmetric contrast families**, `d_ba = -d_ab`. -/
def antisymmetricContrasts : Submodule ℝ (K → K → ℝ) where
  carrier := {e | ∀ a b, e b a = -e a b}
  add_mem' {e e'} he he' a b := by
    simp only [Set.mem_ofPred_eq] at he he'
    simp only [Pi.add_apply, he a b, he' a b]; ring
  zero_mem' a b := by simp
  smul_mem' c e he a b := by
    simp only [Set.mem_ofPred_eq] at he
    simp only [Pi.smul_apply, smul_eq_mul, he a b]; ring

variable (K) in
/-- The subspace of **consistent contrast families**. -/
def consistentContrasts : Submodule ℝ (K → K → ℝ) where
  carrier := {e | IsConsistent e}
  add_mem' {e e'} he he' a b c := by
    simp only [Set.mem_ofPred_eq] at he he'
    simp only [Pi.add_apply]; linarith [he a b c, he' a b c]
  zero_mem' a b c := by simp
  smul_mem' c e he a b d := by
    simp only [Set.mem_ofPred_eq] at he
    simp only [Pi.smul_apply, smul_eq_mul, he a b d]; ring

theorem mem_consistentContrasts {e : K → K → ℝ} : e ∈ consistentContrasts K ↔ IsConsistent e :=
  Iff.rfl

theorem mem_antisymmetricContrasts {e : K → K → ℝ} :
    e ∈ antisymmetricContrasts K ↔ ∀ a b, e b a = -e a b := Iff.rfl

theorem consistentContrasts_le_antisymmetricContrasts :
    consistentContrasts K ≤ antisymmetricContrasts K :=
  fun _ he => mem_antisymmetricContrasts.2 (IsConsistent.antisymm he)

/-- **The dimension of the consistent families**: `T - 1` (stated as `dim + 1 = T`), for a
nonempty finite set of treatments (`r` is any treatment). The map from the basic parameters
`d_k`, `k ≠ r`, to the level contrasts of the padded vector is injective onto the consistent
families. -/
theorem finrank_consistentContrasts_add_one [Fintype K] (r : K) :
    Module.finrank ℝ (consistentContrasts K) + 1 = Fintype.card K := by
  classical
  let T : ({k // k ≠ r} → ℝ) →ₗ[ℝ] (K → K → ℝ) :=
    { toFun := fun d a b => padReference r d b - padReference r d a
      map_add' := fun d d' => by
        funext a b; simp only [padReference_add, Pi.add_apply]; ring
      map_smul' := fun c d => by
        funext a b
        simp only [padReference_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hinj : Function.Injective T := fun d d' h => padReference_injective r <| funext fun k => by
    have := congrFun (congrFun h r) k
    simpa [T] using this
  have hrange : LinearMap.range T = consistentContrasts K := by
    ext e
    rw [LinearMap.mem_range, mem_consistentContrasts]
    constructor
    · rintro ⟨d, rfl⟩
      exact isConsistent_sub _
    · intro he
      refine ⟨fun k => e r k.1, funext fun a => funext fun b => ?_⟩
      simp only [T, LinearMap.coe_mk, AddHom.coe_mk, padReference_restrict (he.self r)]
      exact (he.eq_sub_reference r a b).symm
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
    card_ne_reference_add_one]

/-- The antisymmetric families are coordinatized by the values `e_ab`, `a < b`. -/
noncomputable def antisymmetricContrastsEquiv [LinearOrder K] :
    antisymmetricContrasts K ≃ₗ[ℝ] ({x : K × K // x.1 < x.2} → ℝ) where
  toFun e x := e.1 x.1.1 x.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun a b => if h : a < b then f ⟨(a, b), h⟩ else
      if h' : b < a then -f ⟨(b, a), h'⟩ else 0, mem_antisymmetricContrasts.2 fun a b => by
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp
    · simp [h, not_lt_of_gt h]⟩
  left_inv e := by
    apply Subtype.ext
    funext a b
    have he := mem_antisymmetricContrasts.1 e.2
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h]
    · simp only [lt_irrefl, dite_false]
      linarith [he a a]
    · simp only [not_lt_of_gt h, h, dite_false, dite_true]
      linarith [he a b]
  right_inv f := by
    funext x
    simp [x.2]

/-- **Counting the consistency constraints**: the antisymmetric families have dimension
`C(T, 2)`, and `C(T, 2) = (T - 1) + C(T - 1, 2)`, so consistency imposes `C(T - 1, 2)`
independent linear constraints on the `C(T, 2)` pairwise contrasts. -/
theorem consistentContrasts_loop_count [Fintype K] [LinearOrder K] (r : K) :
    Module.finrank ℝ (antisymmetricContrasts K) = (Fintype.card K).choose 2 ∧
      Module.finrank ℝ (antisymmetricContrasts K) =
        Module.finrank ℝ (consistentContrasts K) + (Fintype.card K - 1).choose 2 := by
  classical
  have hA : Module.finrank ℝ (antisymmetricContrasts K) = (Fintype.card K).choose 2 := by
    rw [LinearEquiv.finrank_eq antisymmetricContrastsEquiv, Module.finrank_fintype_fun_eq_card,
      Fintype.card_subtype, Fintype.card_product_filter_lt]
  refine ⟨hA, ?_⟩
  have hD := finrank_consistentContrasts_add_one (K := K) r
  rw [hA]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card K = m + 1 := ⟨_, hD.symm⟩
  have hc : (m + 1).choose 2 = m + m.choose 2 := by
    have := Nat.choose_succ_succ m 1
    simp only [Nat.choose_one_right] at this
    exact this
  rw [hm, Nat.add_sub_cancel, hc]
  omega

end Closure

/-! ### Consistency on a network of comparisons -/

section Network

variable {E K : Type*} [Fintype K] [DecidableEq K]

/-- **Level contrasts are reduced design contrasts**: the comparison contrasts `δ` are the
contrasts `θ_{head e} - θ_{tail e}` of some level vector exactly when `δ = X d` for the reduced
design with reference `r` and some basic parameters `d`. -/
theorem exists_level_iff_exists_basic (tail head : E → K) (r : K) (δ : E → ℝ) :
    (∃ θ : K → ℝ, incidenceMatrix tail head *ᵥ θ = δ) ↔
      ∃ d, reducedDesign tail head r *ᵥ d = δ := by
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨fun k => θ k.1 - θ r, ?_⟩
    rw [reducedDesign_mulVec]
    have : padReference r (fun k : {k // k ≠ r} => θ k.1 - θ r) = fun k => θ k - θ r := by
      exact padReference_restrict (θ := fun x => θ x - θ r) (sub_self _)
    rw [this]
    funext e
    rw [incidenceMatrix_mulVec, incidenceMatrix_mulVec]; ring
  · rintro ⟨d, rfl⟩
    exact ⟨padReference r d, (reducedDesign_mulVec tail head r d).symm⟩

/-- **The basic parameters of a consistent network are unique when it is connected.** -/
theorem existsUnique_basic_of_connected (tail head : E → K) (r : K) {δ : E → ℝ}
    (hcon : (comparisonGraph tail head).Connected)
    (hδ : ∃ θ : K → ℝ, incidenceMatrix tail head *ᵥ θ = δ) :
    ∃! d, reducedDesign tail head r *ᵥ d = δ := by
  obtain ⟨d, hd⟩ := (exists_level_iff_exists_basic tail head r δ).1 hδ
  exact ⟨d, hd, fun d' hd' => (reducedDesign_injective_iff tail head r).2 hcon (hd'.trans hd.symm)⟩

/-- **The cycle conditions.** Contrasts `δ` on the comparisons are the contrasts of a level
vector exactly when `∑_e c_e δ_e = 0` for every circulation `c`, a flow on the comparisons with
zero net flow at every treatment (`Bᵀ c = 0`). -/
theorem exists_level_iff_circulation [Fintype E] (tail head : E → K) (δ : E → ℝ) :
    (∃ θ : K → ℝ, incidenceMatrix tail head *ᵥ θ = δ) ↔
      ∀ c : E → ℝ, (incidenceMatrix tail head)ᵀ *ᵥ c = 0 → c ⬝ᵥ δ = 0 := by
  classical
  set B := incidenceMatrix tail head
  constructor
  · rintro ⟨θ, rfl⟩ c hc
    rw [dotProduct_mulVec, ← mulVec_transpose, hc, zero_dotProduct]
  · intro h
    by_contra hne
    have hx : δ ∉ LinearMap.range B.mulVecLin := fun ⟨θ, hθ⟩ => hne ⟨θ, hθ⟩
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    let c : E → ℝ := fun e => f (Pi.single e 1)
    have hfc : ∀ v : E → ℝ, f v = c ⬝ᵥ v := by
      intro v
      conv_lhs => rw [← Finset.univ_sum_single v]
      simp only [map_sum, dotProduct, c]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [show Pi.single e (v e) = v e • (Pi.single e 1 : E → ℝ) by
        ext x; by_cases hx : x = e <;> simp [hx], map_smul, smul_eq_mul,
        mul_comm]
    have hzero : ∀ θ, f (B *ᵥ θ) = 0 := by
      intro θ
      have : f (B *ᵥ θ) ∈ (LinearMap.range B.mulVecLin).map f :=
        Submodule.mem_map_of_mem ⟨θ, rfl⟩
      rw [hmap] at this
      exact (Submodule.mem_bot ℝ).1 this
    have hcirc : Bᵀ *ᵥ c = 0 := by
      funext k
      have := hzero (Pi.single k 1)
      rw [hfc, dotProduct_mulVec, ← mulVec_transpose] at this
      rw [Pi.zero_apply, ← this, dotProduct_single, mul_one]
    exact hf (by rw [hfc]; exact h c hcirc)

/-- **The triangle cycle condition**: for comparisons `e₁ : a → b`, `e₂ : b → c` and
`e₃ : a → c` of three distinct comparisons, level contrasts satisfy `δ₁ + δ₂ = δ₃`. -/
theorem triangle_of_exists_level (tail head : E → K) {δ : E → ℝ}
    (hδ : ∃ θ : K → ℝ, incidenceMatrix tail head *ᵥ θ = δ) {e₁ e₂ e₃ : E}
    (h₁₂ : head e₁ = tail e₂) (h₁₃ : tail e₁ = tail e₃) (h₂₃ : head e₂ = head e₃) :
    δ e₁ + δ e₂ = δ e₃ := by
  obtain ⟨θ, rfl⟩ := hδ
  simp only [incidenceMatrix_mulVec, h₁₂, h₁₃, h₂₃]
  ring

end Network

/-! ### Constant relative effects give a consistent network -/

section Constancy

open IndirectComparison

variable {J ι 𝒳 : Type*} {Ω : J → Type*} [∀ j, MeasurableSpace (Ω j)] {g : ℝ → ℝ}
  {P : ∀ j, Population (Ω j) 𝒳 ι}

/-- The relative effects of one population on the scale `g` are consistent: they are the level
contrasts of `t ↦ g(E[Y(t)])`. -/
theorem isConsistent_marginalEffect {Ω' : Type*} [MeasurableSpace Ω'] (Q : Population Ω' 𝒳 ι) :
    IsConsistent fun a b => Q.marginalEffect g a b :=
  isConsistent_sub fun t => g (Q.armMean t)

/-- **Constant relative effects give a consistent network contrast.** If the relative effects
on the scale `g` are constant across a nonempty family of populations for all pairs of
treatments, there is one network contrast `d`, the effect in every population, and it is
consistent. -/
theorem ConstantRelativeEffects.exists_isConsistent_networkContrast [Nonempty J]
    (h : ConstantRelativeEffects g P Set.univ) :
    ∃ d : ι → ι → ℝ, IsConsistent d ∧ ∀ a b j, (P j).marginalEffect g a b = d a b := by
  obtain ⟨d, hd⟩ := h.exists_networkContrast
  obtain ⟨j₀⟩ := ‹Nonempty J›
  refine ⟨d, ?_, hd⟩
  have : d = fun a b => (P j₀).marginalEffect g a b := funext fun a => funext fun b =>
    (hd a b j₀).symm
  rw [this]
  exact isConsistent_marginalEffect _

end Constancy

end NetworkMetaAnalysis

end CausalInference
