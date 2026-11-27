/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.Faithfulness
public import CausalInference.LinearSEM.SingleDoorGeneric

/-!
# Faithful laws exist for every acyclic graph

The laws over binary variables that factorize according to an acyclic graph `G` are
parametrized by their conditional probability tables: one number `θ (v, z)` for every vertex `v`
and every configuration `z` of its parents, the probability that `v` is true given `z`. The mass
of a configuration is a polynomial in the parameters (`Digraph.massPoly`), and so are the
marginal masses; a conditional independence statement `X ⫫ Y | Z` is the vanishing of the
polynomials `Digraph.ciPoly X Y Z x` (cross multiplied, without division) for all
configurations `x`.

For every triple that is not d-separated, the completeness of d-separation
(`Digraph.dSep_iff_forall_factorizes_condIndep'`) gives a factorizing law that violates the
statement; the conditional probability tables of that law form a parameter point at which one of
the polynomials does not vanish, so that polynomial is nonzero and its zero set is Lebesgue null
(`CausalInference.LinearSEM.SingleDoorGeneric.volume_zeroSet_eq_zero_of_fintype`). There are
finitely many triples, so the parameters in the open box `(0, 1)` whose law is not faithful form
a null set (`Digraph.volume_unfaithful_eq_zero`), while the box has positive measure. Hence a
faithful law exists (`Digraph.exists_factorizes_isFaithful`), as in Spirtes, Glymour and Scheines
(1993) and Meek (1995).

The laws over binary variables are then transported to arbitrary finite value types with at
least two values (`Digraph.exists_factorizes_isFaithful_of_nontrivial`). This gives the
observational characterization of Markov equivalence for such value types
(`Digraph.markovEquivalent_iff_forall_factorizes_of_nontrivial`).

## References

* P. Spirtes, C. Glymour and R. Scheines (1993).
* C. Meek (1995).
-/

@[expose] public section

namespace Digraph

open CausalInference Finset MeasureTheory MvPolynomial

variable {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]

/-! ### Conditional probability tables -/

/-- The entries of a conditional probability table over binary variables: a vertex and a
configuration of its parents. -/
abbrev CPTIndex : Type _ := Σ v : V, ((u : G.parentsFinset v) → Bool)

/-- A parameter point: a real number for every entry of the conditional probability tables. -/
abbrev CPTParam : Type _ := G.CPTIndex → ℝ

/-- Clamp a real number to the unit interval. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp01_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right h1, max_eq_right h0]

/-- The Markov kernels with the conditional probability tables `θ`, clamped to the unit
interval: the vertex `v` is true with probability `θ (v, z)` given the parent configuration
`z`. -/
noncomputable def cptKernels (θ : G.CPTParam) : G.MarkovKernels (fun _ => Bool) where
  kernel v z a := if a then clamp01 (θ ⟨v, z⟩) else 1 - clamp01 (θ ⟨v, z⟩)
  nonneg v z a := by
    cases a
    · simpa using clamp01_le_one (θ ⟨v, z⟩)
    · simpa using clamp01_nonneg (θ ⟨v, z⟩)
  sum_eq_one v z := by simp

variable {G} in
/-- The law over binary variables with the conditional probability tables `θ`. -/
noncomputable def cptLaw (hG : G.IsAcyclic) (θ : G.CPTParam) : FiniteDist (V → Bool) :=
  (G.cptKernels θ).jointDist hG

theorem factorizes_cptLaw (hG : G.IsAcyclic) (θ : G.CPTParam) : G.Factorizes (cptLaw hG θ) :=
  (G.cptKernels θ).factorizes_jointDist hG

/-- The conditional probability tables of Markov kernels over binary variables. -/
noncomputable def paramOfKernels (k : G.MarkovKernels (fun _ => Bool)) : G.CPTParam :=
  fun i => k.kernel i.1 i.2 true

/-! ### Masses and conditional independence as polynomials -/

/-- The mass of the configuration `ω` as a polynomial in the conditional probability tables. -/
noncomputable def massPoly (ω : V → Bool) : MvPolynomial G.CPTIndex ℝ :=
  ∏ v, if ω v then X ⟨v, (G.parentsFinset v).restrict ω⟩
    else 1 - X ⟨v, (G.parentsFinset v).restrict ω⟩

/-- The marginal mass at `x` on `S` as a polynomial. -/
noncomputable def margPoly (S : Finset V) (x : V → Bool) : MvPolynomial G.CPTIndex ℝ :=
  ∑ ω ∈ FiniteDist.agreeOn S x, G.massPoly ω

/-- The cylinder identity of `X ⫫ Y | Z` at the configuration `x`, as a polynomial: its
vanishing for all `x` is the conditional independence (`Digraph.condIndep_iff_eval_ciPoly`). -/
noncomputable def ciPoly (X Y Z : Finset V) (x : V → Bool) : MvPolynomial G.CPTIndex ℝ :=
  G.margPoly (X ∪ Y ∪ Z) x * G.margPoly Z x - G.margPoly (X ∪ Z) x * G.margPoly (Y ∪ Z) x

omit [DecidableEq V] in
/-- At the conditional probability tables of Markov kernels, the mass polynomial is the product
of the factors. -/
theorem eval_massPoly_paramOfKernels (k : G.MarkovKernels (fun _ => Bool)) (ω : V → Bool) :
    eval (G.paramOfKernels k) (G.massPoly ω) = ∏ v, k.factor v ω := by
  rw [massPoly, map_prod]
  refine prod_congr rfl fun v _ => ?_
  have hsum := k.sum_eq_one v ((G.parentsFinset v).restrict ω)
  rw [Fintype.sum_bool] at hsum
  have hθ : G.paramOfKernels k ⟨v, (G.parentsFinset v).restrict ω⟩ =
      k.kernel v ((G.parentsFinset v).restrict ω) true := rfl
  simp only [MarkovKernels.factor]
  cases ω v
  · simp only [Bool.false_eq_true, ↓reduceIte, map_sub, map_one, eval_X, hθ]
    linarith
  · simp only [↓reduceIte, eval_X, hθ]

/-- For a law that factorizes with kernels `k`, the cylinder polynomials evaluate at the
conditional probability tables of `k` to the cylinder identities of the law. -/
theorem eval_ciPoly_of_factor {p : FiniteDist (V → Bool)} (k : G.MarkovKernels (fun _ => Bool))
    (hk : ∀ x, p x = ∏ v, k.factor v x) (X Y Z : Finset V) (x : V → Bool) :
    eval (G.paramOfKernels k) (G.ciPoly X Y Z x) =
      p.margAt (X ∪ Y ∪ Z) x * p.margAt Z x - p.margAt (X ∪ Z) x * p.margAt (Y ∪ Z) x := by
  have hm : ∀ S, eval (G.paramOfKernels k) (G.margPoly S x) = p.margAt S x := fun S => by
    rw [margPoly, map_sum, FiniteDist.margAt, FiniteDist.prob]
    exact sum_congr rfl fun ω _ => by rw [eval_massPoly_paramOfKernels, hk]
  simp only [ciPoly, map_sub, map_mul, hm]

/-- The parameters in the open unit box. -/
def cptBox : Set G.CPTParam := {θ | ∀ i, 0 < θ i ∧ θ i < 1}

omit [DecidableEq V] in
theorem paramOfKernels_cptKernels {θ : G.CPTParam} (hθ : θ ∈ G.cptBox) :
    G.paramOfKernels (G.cptKernels θ) = θ := by
  funext i
  simp [paramOfKernels, cptKernels, clamp01_of_mem (hθ i).1.le (hθ i).2.le]

/-- **Conditional independence is the vanishing of polynomials.** For parameters in the open box,
`X ⫫ Y | Z` holds in the law with conditional probability tables `θ` if and only if all the
cylinder polynomials vanish at `θ`. -/
theorem condIndep_iff_eval_ciPoly (hG : G.IsAcyclic) {θ : G.CPTParam} (hθ : θ ∈ G.cptBox)
    {X Y Z : Finset V} :
    (cptLaw hG θ).CondIndep X Y Z ↔ ∀ x, eval θ (G.ciPoly X Y Z x) = 0 := by
  rw [FiniteDist.condIndep_iff_margAt_mul]
  refine forall_congr' fun x => ?_
  have := G.eval_ciPoly_of_factor (p := cptLaw hG θ) (G.cptKernels θ) (fun _ => rfl) X Y Z x
  rw [paramOfKernels_cptKernels G hθ] at this
  rw [this, sub_eq_zero]

/-- **A dependent triple gives a nonzero polynomial.** If `X` and `Y` are not d-separated by `Z`
in an acyclic graph, some cylinder polynomial of `X ⫫ Y | Z` is nonzero. -/
theorem exists_ciPoly_ne_zero (hG : G.IsAcyclic) {X Y Z : Finset V}
    (h : ¬ G.DSep ↑X ↑Y ↑Z) : ∃ x, G.ciPoly X Y Z x ≠ 0 := by
  rw [dSep_iff_forall_factorizes_condIndep' hG] at h
  push Not at h
  obtain ⟨p, ⟨k, hk⟩, hn⟩ := h
  rw [FiniteDist.condIndep_iff_margAt_mul] at hn
  push Not at hn
  obtain ⟨x, hx⟩ := hn
  refine ⟨x, fun h0 => hx ?_⟩
  have := G.eval_ciPoly_of_factor k hk X Y Z x
  rw [h0, map_zero] at this
  linarith

/-! ### Faithfulness for almost all parameters -/

variable {G} in
/-- The parameters in the open box whose law is not faithful to `G`. -/
def unfaithfulParams (hG : G.IsAcyclic) : Set G.CPTParam :=
  {θ | θ ∈ G.cptBox ∧ ¬ (cptLaw hG θ).IsFaithful G}

/-- **The unfaithful parameters form a null set.** For an acyclic graph `G` on a finite vertex
type, the conditional probability tables in the open unit box whose law over binary variables is
not faithful to `G` form a Lebesgue null set. -/
theorem volume_unfaithful_eq_zero (hG : G.IsAcyclic) : volume (unfaithfulParams hG) = 0 := by
  classical
  have hex : ∀ T : Finset V × Finset V × Finset V, ∃ x : V → Bool,
      ¬ G.DSep ↑T.1 ↑T.2.1 ↑T.2.2 → G.ciPoly T.1 T.2.1 T.2.2 x ≠ 0 := by
    intro T
    by_cases h : G.DSep ↑T.1 ↑T.2.1 ↑T.2.2
    · exact ⟨fun _ => true, fun hn => absurd h hn⟩
    · obtain ⟨x, hx⟩ := G.exists_ciPoly_ne_zero hG h
      exact ⟨x, fun _ => hx⟩
  choose xs hxs using hex
  set s : Finset V × Finset V × Finset V → Set G.CPTParam := fun T =>
    {θ | ¬ G.DSep ↑T.1 ↑T.2.1 ↑T.2.2 ∧ eval θ (G.ciPoly T.1 T.2.1 T.2.2 (xs T)) = 0}
  have hsub : unfaithfulParams hG ⊆ ⋃ T, s T := by
    rintro θ ⟨hθ, hnf⟩
    simp only [FiniteDist.IsFaithful, not_forall] at hnf
    obtain ⟨X, Y, Z, hci, hn⟩ := hnf
    exact Set.mem_iUnion.2 ⟨(X, Y, Z), hn, (G.condIndep_iff_eval_ciPoly hG hθ).1 hci _⟩
  refine measure_mono_null hsub (measure_iUnion_null fun T => ?_)
  by_cases h : G.DSep ↑T.1 ↑T.2.1 ↑T.2.2
  · have : s T = ∅ := Set.eq_empty_of_forall_notMem fun θ hθ => hθ.1 h
    rw [this, measure_empty]
  · exact measure_mono_null (fun θ hθ => hθ.2)
      (LinearSEM.SingleDoorGeneric.volume_zeroSet_eq_zero_of_fintype (hxs T h))

omit [DecidableEq V] in
theorem isOpen_cptBox : IsOpen G.cptBox := by
  have : G.cptBox = ⋂ i, ({θ : G.CPTParam | 0 < θ i} ∩ {θ | θ i < 1}) := by
    ext θ
    simp [cptBox]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

theorem volume_cptBox_pos : 0 < volume G.cptBox :=
  G.isOpen_cptBox.measure_pos volume ⟨fun _ => 1 / 2, fun _ => by norm_num⟩

/-- Some parameter point in the open box has a faithful law. -/
theorem exists_cptBox_isFaithful (hG : G.IsAcyclic) :
    ∃ θ ∈ G.cptBox, (cptLaw hG θ).IsFaithful G := by
  by_contra hn
  push Not at hn
  have hsub : G.cptBox ⊆ unfaithfulParams hG := fun θ hθ => ⟨hθ, hn θ hθ⟩
  exact absurd (measure_mono_null hsub (G.volume_unfaithful_eq_zero hG)) G.volume_cptBox_pos.ne'

/-- **Faithful laws exist** (Spirtes, Glymour and Scheines 1993; Meek 1995). For every acyclic
graph `G` on a finite vertex type there is a law over binary variables that factorizes according
to `G` and is faithful to `G`. -/
theorem exists_factorizes_isFaithful (hG : G.IsAcyclic) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧ p.IsFaithful G := by
  obtain ⟨θ, -, hθ⟩ := G.exists_cptBox_isFaithful hG
  exact ⟨cptLaw hG θ, G.factorizes_cptLaw hG θ, hθ⟩

/-- A faithful law that is also Markov to `G`: conditional independence in it is exactly
d-separation in `G`. -/
theorem exists_condIndep_iff_dSep (hG : G.IsAcyclic) :
    ∃ p : FiniteDist (V → Bool), G.Factorizes p ∧
      ∀ X Y Z : Finset V, p.CondIndep X Y Z ↔ G.DSep ↑X ↑Y ↑Z := by
  obtain ⟨p, hp, hF⟩ := G.exists_factorizes_isFaithful hG
  exact ⟨p, hp, fun X Y Z => hF.condIndep_iff_dSep (hp.globalMarkov hG)⟩

/-! ### Arbitrary value types -/

section Transport

variable {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (α v)] in
variable {G} in
/-- The configuration over `α` that takes the value `a v` where `ω v` is true and `b v` where
it is false. -/
def boolEmbed (a b : ∀ v, α v) (ω : V → Bool) : ∀ v, α v := fun v => if ω v then a v else b v

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
theorem boolEmbed_injective {a b : ∀ v, α v} (hab : ∀ v, a v ≠ b v) :
    Function.Injective (boolEmbed (V := V) a b) := by
  intro ω ω' h
  funext v
  have := congrFun h v
  simp only [boolEmbed] at this
  cases hω : ω v <;> cases hω' : ω' v <;> simp only [hω, hω', Bool.false_eq_true,
    ↓reduceIte] at this
  · rfl
  · exact absurd this.symm (hab v)
  · exact absurd this (hab v)
  · rfl

variable {G} in
/-- Markov kernels over binary variables transported to `α`: the value `a v` stands for true,
`b v` for false, and the other values have mass zero. -/
def MarkovKernels.transport (k : G.MarkovKernels (fun _ => Bool)) (a b : ∀ v, α v)
    (hab : ∀ v, a v ≠ b v) : G.MarkovKernels α where
  kernel v z t :=
    if t = a v then k.kernel v (fun u => decide (z u = a u)) true
    else if t = b v then k.kernel v (fun u => decide (z u = a u)) false else 0
  nonneg v z t := by
    split_ifs
    · exact k.nonneg _ _ _
    · exact k.nonneg _ _ _
    · exact le_rfl
  sum_eq_one v z := by
    have hpt : ∀ t : α v, (if t = a v then k.kernel v (fun u => decide (z u = a u)) true
        else if t = b v then k.kernel v (fun u => decide (z u = a u)) false else 0) =
        (if t = a v then k.kernel v (fun u => decide (z u = a u)) true else 0) +
          (if t = b v then k.kernel v (fun u => decide (z u = a u)) false else 0) := by
      intro t
      by_cases ha : t = a v
      · subst ha
        simp [hab v]
      · simp [ha]
    rw [Finset.sum_congr rfl fun t _ => hpt t, sum_add_distrib, sum_ite_eq', sum_ite_eq']
    simp only [mem_univ, ↓reduceIte]
    simpa [Fintype.sum_bool] using k.sum_eq_one v (fun u => decide (z u = a u))

omit [DecidableEq V] in
variable {G} in
theorem MarkovKernels.transport_factor_boolEmbed (k : G.MarkovKernels (fun _ => Bool))
    {a b : ∀ v, α v} (hab : ∀ v, a v ≠ b v) (v : V) (ω : V → Bool) :
    (k.transport a b hab).factor v (boolEmbed a b ω) = k.factor v ω := by
  have hz : (fun u : G.parentsFinset v =>
      decide (((G.parentsFinset v).restrict (boolEmbed a b ω)) u = a u)) =
      (G.parentsFinset v).restrict ω := by
    funext u
    simp only [Finset.restrict, boolEmbed]
    rcases Bool.eq_false_or_eq_true (ω u) with h | h <;> simp [h, Ne.symm (hab u)]
  simp only [MarkovKernels.factor, transport]
  rw [hz]
  cases hω : ω v
  · simp [boolEmbed, hω, Ne.symm (hab v)]
  · simp [boolEmbed, hω]

omit [DecidableEq V] in
variable {G} in
theorem MarkovKernels.transport_factor_eq_zero (k : G.MarkovKernels (fun _ => Bool))
    {a b : ∀ v, α v} (hab : ∀ v, a v ≠ b v) {v : V} {y : ∀ v, α v} (ha : y v ≠ a v)
    (hb : y v ≠ b v) : (k.transport a b hab).factor v y = 0 := by
  simp [MarkovKernels.factor, transport, ha, hb]

variable {G} in
/-- The joint law of the transported kernels gives the configurations outside the image of
`boolEmbed a b` mass zero and gives `boolEmbed a b ω` the mass of `ω`. -/
theorem MarkovKernels.margAt_transport (k : G.MarkovKernels (fun _ => Bool)) (hG : G.IsAcyclic)
    {a b : ∀ v, α v} (hab : ∀ v, a v ≠ b v) (S : Finset V) (x : V → Bool) :
    ((k.transport a b hab).jointDist hG).margAt S (boolEmbed a b x) =
      (k.jointDist hG).margAt S x := by
  classical
  have hinj := boolEmbed_injective (V := V) hab
  simp only [FiniteDist.margAt, FiniteDist.prob]
  have hsub : (FiniteDist.agreeOn S x).image (boolEmbed a b) ⊆
      FiniteDist.agreeOn S (boolEmbed a b x) := by
    intro y hy
    obtain ⟨ω, hω, rfl⟩ := mem_image.1 hy
    rw [FiniteDist.mem_agreeOn] at hω ⊢
    intro v hv
    simp [boolEmbed, hω v hv]
  rw [← sum_subset hsub, sum_image fun ω _ ω' _ h => hinj h]
  · refine sum_congr rfl fun ω _ => ?_
    simp only [MarkovKernels.jointDist_apply, k.transport_factor_boolEmbed hab]
  · intro y hy hn
    rw [MarkovKernels.jointDist_apply]
    by_contra hne
    apply hn
    have hall : ∀ v, y v = a v ∨ y v = b v := by
      intro v
      by_contra hv
      push Not at hv
      exact hne (prod_eq_zero (mem_univ v) (k.transport_factor_eq_zero hab hv.1 hv.2))
    refine mem_image.2 ⟨fun v => decide (y v = a v), ?_, ?_⟩
    · rw [FiniteDist.mem_agreeOn] at hy ⊢
      intro v hv
      rw [hy v hv]
      rcases Bool.eq_false_or_eq_true (x v) with h | h <;> simp [boolEmbed, h, Ne.symm (hab v)]
    · funext v
      rcases hall v with h | h
      · simp [boolEmbed, h]
      · simp [boolEmbed, h, Ne.symm (hab v)]

/-- **Faithful laws exist over arbitrary value types.** For every acyclic graph `G` on a finite
vertex type and finite value types `α v` with at least two values each, some law on
configurations factorizes according to `G` and is faithful to `G`. -/
theorem exists_factorizes_isFaithful_of_nontrivial [∀ v, Nontrivial (α v)]
    (hG : G.IsAcyclic) : ∃ p : FiniteDist (∀ v, α v), G.Factorizes p ∧ p.IsFaithful G := by
  classical
  have hpair : ∀ v, ∃ ab : α v × α v, ab.1 ≠ ab.2 := fun v => by
    obtain ⟨a, b, h⟩ := exists_pair_ne (α v)
    exact ⟨(a, b), h⟩
  choose ab hab using hpair
  obtain ⟨θ, -, hθ⟩ := G.exists_cptBox_isFaithful hG
  set k := (G.cptKernels θ).transport (fun v => (ab v).1) (fun v => (ab v).2) hab
  refine ⟨k.jointDist hG, k.factorizes_jointDist hG, fun X Y Z hci => hθ X Y Z ?_⟩
  rw [FiniteDist.condIndep_iff_margAt_mul] at hci ⊢
  intro x
  have := hci (boolEmbed (fun v => (ab v).1) (fun v => (ab v).2) x)
  simp only [k, MarkovKernels.margAt_transport] at this
  exact this

omit [∀ v, DecidableEq (α v)] in
/-- **Markov equivalence is observational equivalence over arbitrary value types** (Pearl 2009,
section 1.2.3). Two acyclic graphs on a finite vertex type are Markov equivalent if and only if
the same laws factorize according to them, over any finite value types with at least two values
each. -/
theorem markovEquivalent_iff_forall_factorizes_of_nontrivial [∀ v, Nontrivial (α v)]
    {H : Digraph V} [DecidableRel H.Adj] (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    MarkovEquivalent G H ↔ ∀ p : FiniteDist (∀ v, α v), G.Factorizes p ↔ H.Factorizes p := by
  classical
  refine ⟨fun h p => h.factorizes_iff hG hH, fun h => ?_⟩
  have key : ∀ (K L : Digraph V) [DecidableRel K.Adj] [DecidableRel L.Adj], K.IsAcyclic →
      L.IsAcyclic → (∀ p : FiniteDist (∀ v, α v), K.Factorizes p → L.Factorizes p) →
      ∀ X Y Z : Finset V, L.DSep ↑X ↑Y ↑Z → K.DSep ↑X ↑Y ↑Z := by
    intro K L _ _ hK hL hKL X Y Z hsep
    obtain ⟨p, hp, hF⟩ := K.exists_factorizes_isFaithful_of_nontrivial (α := α) hK
    exact hF X Y Z ((hKL p hp).globalMarkov hL X Y Z hsep)
  intro X Y Z
  obtain ⟨X, rfl⟩ : ∃ X' : Finset V, (X' : Set V) = X := ⟨X.toFinset, Set.coe_toFinset X⟩
  obtain ⟨Y, rfl⟩ : ∃ Y' : Finset V, (Y' : Set V) = Y := ⟨Y.toFinset, Set.coe_toFinset Y⟩
  obtain ⟨Z, rfl⟩ : ∃ Z' : Finset V, (Z' : Set V) = Z := ⟨Z.toFinset, Set.coe_toFinset Z⟩
  exact ⟨key H G hH hG (fun p => (h p).2) X Y Z, key G H hG hH (fun p => (h p).1) X Y Z⟩

end Transport

end Digraph
