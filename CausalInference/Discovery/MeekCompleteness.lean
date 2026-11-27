/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.PC
public import CausalInference.Discovery.FaithfulExistence

/-!
# Toward the completeness of the orientation rules, and the PC output

This file collects what is proved about the completeness of the orientation rules R1 to R4
(Meek 1995) and its consequences for the PC algorithm.

## Reversible edges and covered edges

* `Digraph.isReversible_iff_exists_isCovered`: an edge of an acyclic graph is reversible if and
  only if it is covered in some Markov equivalent acyclic graph (Chickering 1995). This uses the
  transformational characterization `Digraph.reflTransGen_coveredReversal`.
* `Digraph.IsPartialPattern.of_markovEquivalent`: a partial pattern for `G` is a partial pattern
  for every Markov equivalent acyclic graph.
* `Digraph.IsPartialPattern.isArrow_of_transGen`,
  `Digraph.IsPartialPattern.not_transGen_of_isLine`:
  in a partial pattern closed under the rules, a directed path between adjacent vertices forces
  the edge between them in its direction; in particular no directed path joins the ends of an
  undirected edge.
* `Digraph.IsPartialPattern.exists_isCovered_of_isLine_of_mem`,
  `Digraph.IsPartialPattern.exists_isCovered_of_isLine`: in a partial pattern closed under the
  rules, if some edge is undirected then some undirected edge is covered in `G`, also inside any
  set closed under parents: take the undirected edge `p → q` of `G` whose head `q` is first in a
  topological order, and among those the tail `p` that is last; rules R1 and R2 and the
  v-structure condition rule out every obstruction. Hence
  `Digraph.IsPartialPattern.exists_isReversible_of_isLine`: a closed partial pattern with an
  undirected edge has an undirected edge that is reversible.
* `Digraph.meekComplete_iff`: the completeness statement `Digraph.MeekComplete` is equivalent to
  the statement that every undirected edge of a closed partial pattern is reversible.

What is missing for `Digraph.MeekComplete V` is that *every* undirected edge is reversible, not
just one: by `Digraph.meekComplete_iff` and `Digraph.isReversible_iff_exists_isCovered`, that for
every undirected edge `u ∼ v` of a closed partial pattern with `u → v` in `G`, some acyclic graph
Markov equivalent to `G` has `u → v` covered. The argument above finds one covered undirected
edge, but not a prescribed one, and repeating it can cycle: for the undirected triangle with
`a → b`, `b → y`, `a → y` in `G`, it reverses `a → b`, and in the resulting graph it reverses
`b → a` back.

## The PC output

* `Digraph.pcOutput_congr`: the output depends only on the oracle as a relation.
* `Digraph.pcOutput_eq_iff_markovEquivalent`: under d-separation oracles of two acyclic graphs,
  the PC algorithm gives the same output if and only if the graphs are Markov equivalent. This
  does not need the completeness of the rules.
* `Digraph.pcOutput_condIndep_eq_pattern`: under the conditional independence oracle of a law
  that is Markov and faithful to `G`, the output is the pattern, given `Digraph.MeekComplete`.
* `Digraph.exists_law_pcOutput`: every finite acyclic graph has a law over binary variables,
  factorizing according to it, with whose conditional independence oracle the PC algorithm
  returns the skeleton, directs exactly the v-structures after the collider phase, and directs
  only compelled edges.

## References

* D. M. Chickering (1995).
* C. Meek (1995).
-/

@[expose] public section

namespace Digraph

open Relation Finset

variable {V : Type*} {G H P : Digraph V}

/-! ### Partial patterns along the equivalence class -/

/-- A partial pattern for `G` is a partial pattern for every Markov equivalent acyclic graph. -/
theorem IsPartialPattern.of_markovEquivalent [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) (hGH : MarkovEquivalent G H) :
    P.IsPartialPattern H := by
  obtain ⟨hsk, hv⟩ := (markovEquivalent_iff hG hH).1 hGH
  refine ⟨hP.irrefl, hP.skeleton_eq.trans hsk, fun u v h => ?_,
    fun a c b h => hP.isArrow_of_isVStructure a c b ((hv a c b).2 h)⟩
  have hc := hP.isCompelled u v h
  exact ⟨hc.2 H hH hGH, fun K hK hHK => hc.2 K hK (hGH.trans hHK)⟩

/-- An edge of a partial pattern is an edge of `G` in some direction. -/
theorem IsPartialPattern.adj_or_adj_of_adj (hP : P.IsPartialPattern G) {a b : V}
    (h : P.Adj a b) : G.Adj a b ∨ G.Adj b a := by
  have hne : a ≠ b := fun e => hP.irrefl a (e ▸ h)
  have hs : P.skeleton.Adj a b := skeleton_adj.2 ⟨hne, Or.inl h⟩
  rw [hP.skeleton_eq] at hs
  exact (skeleton_adj.1 hs).2

/-- An edge of `G` is an edge of a partial pattern in some direction. -/
theorem IsPartialPattern.adj_or_adj_of_gAdj (hP : P.IsPartialPattern G) (hG : G.IsAcyclic)
    {a b : V} (h : G.Adj a b) : P.Adj a b ∨ P.Adj b a := by
  have hs : G.skeleton.Adj a b := skeleton_adj.2 ⟨hG.ne_of_adj h, Or.inl h⟩
  rw [← hP.skeleton_eq] at hs
  exact (skeleton_adj.1 hs).2

/-- An edge `a → b` of `G` is, in a partial pattern, either the directed edge `a → b` or an
undirected edge. -/
theorem IsPartialPattern.isArrow_or_isLine (hP : P.IsPartialPattern G) (hG : G.IsAcyclic)
    {a b : V} (h : G.Adj a b) : P.IsArrow a b ∨ P.IsLine a b := by
  by_cases hab : P.Adj a b
  · by_cases hba : P.Adj b a
    · exact Or.inr ⟨hab, hba⟩
    · exact Or.inl ⟨hab, hba⟩
  · have hba := (hP.adj_or_adj_of_gAdj hG h).resolve_left hab
    exact absurd (hP.isCompelled b a ⟨hba, hab⟩).1 (hG.asymm h)

/-- Nonadjacency in `G` is nonadjacency in a partial pattern. -/
theorem IsPartialPattern.not_adj_of_not_gAdj (hP : P.IsPartialPattern G) {a b : V}
    (h₁ : ¬ G.Adj a b) (h₂ : ¬ G.Adj b a) : ¬ P.Adj a b :=
  fun h => (hP.adj_or_adj_of_adj h).elim h₁ h₂

/-! ### Reversible edges are covered edges -/

/-- **Reversible edges are the covered edges of equivalent graphs** (Chickering 1995). An edge
`u → v` of a finite acyclic graph `G` is reversible if and only if it is covered in some acyclic
graph Markov equivalent to `G`. -/
theorem isReversible_iff_exists_isCovered [Finite V] (hG : G.IsAcyclic) {u v : V}
    (huv : G.Adj u v) :
    G.IsReversible u v ↔ ∃ H : Digraph V, H.IsAcyclic ∧ MarkovEquivalent G H ∧ H.IsCovered u v := by
  constructor
  · rintro ⟨-, H, hH, hGH, hvu⟩
    obtain ⟨hsk, hv⟩ := (markovEquivalent_iff hG hH).1 hGH
    suffices key : ∀ K, ReflTransGen CoveredReversal G K → K.Adj v u →
        ∃ H : Digraph V, H.IsAcyclic ∧ MarkovEquivalent G H ∧ H.IsCovered u v from
      key H (reflTransGen_coveredReversal hG hH hsk hv) hvu
    intro K hK
    induction hK with
    | refl => exact fun h => absurd h (hG.asymm huv)
    | @tail K K' hGK hstep ih =>
      obtain ⟨hKa, x, y, hc, rfl⟩ := hstep
      intro hK'
      by_cases hKvu : K.Adj v u
      · exact ih hKvu
      · rw [reverseEdge_adj] at hK'
        rcases hK' with ⟨h, -⟩ | ⟨rfl, rfl⟩
        · exact absurd h hKvu
        · exact ⟨K, hKa, markovEquivalent_of_reflTransGen_coveredReversal hGK, hc⟩
  · rintro ⟨H, hH, hGH, hc⟩
    refine ⟨huv, H.reverseEdge u v, hc.isAcyclic_reverseEdge hH,
      hGH.trans (hc.markovEquivalent_reverseEdge hH), ?_⟩
    rw [reverseEdge_adj]
    exact Or.inr ⟨rfl, rfl⟩

/-! ### A covered undirected edge -/

/-- **A covered undirected edge inside an ancestral set.** Let `P` be a partial pattern for a
finite acyclic graph `G` to which no rule applies, and let `R` be a set of vertices closed under
taking parents in `G`. If some undirected edge `u ∼ v` of `P` has `u → v` in `G` with `v ∈ R`,
then some undirected edge `p ∼ q` of `P` with `q ∈ R` is a covered edge `p → q` of `G`. The head
`q` is first in a topological order among such heads, and `p` is last among the undirected
parents of `q`. -/
theorem IsPartialPattern.exists_isCovered_of_isLine_of_mem [Finite V]
    (hP : P.IsPartialPattern G) (hG : G.IsAcyclic) (hcl : ∀ a b, ¬ MeekRule P a b) {R : Set V}
    (hR : ∀ a b, G.Adj a b → b ∈ R → a ∈ R) {u v : V} (huv : P.IsLine u v) (hGuv : G.Adj u v)
    (hv : v ∈ R) : ∃ p q, q ∈ R ∧ P.IsLine p q ∧ G.IsCovered p q := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  set S := (univ : Finset (V × V)).filter fun e => G.Adj e.1 e.2 ∧ P.IsLine e.1 e.2 ∧ e.2 ∈ R
  have hS : S.Nonempty := ⟨(u, v), mem_filter.2 ⟨mem_univ _, hGuv, huv, hv⟩⟩
  obtain ⟨⟨a₀, q⟩, he₀, hmin⟩ := S.exists_min_image (fun e => f e.2) hS
  obtain ⟨-, hGa₀, hLa₀, hqR⟩ := mem_filter.1 he₀
  set T := (univ : Finset V).filter fun a => G.Adj a q ∧ P.IsLine a q
  have hT : T.Nonempty := ⟨a₀, mem_filter.2 ⟨mem_univ _, hGa₀, hLa₀⟩⟩
  obtain ⟨p, hp, hmax⟩ := T.exists_max_image f hT
  obtain ⟨hpG, hpL⟩ := (mem_filter.1 hp).2
  have hminS : ∀ a b, G.Adj a b → P.IsLine a b → b ∈ R → f q ≤ f b := fun a b h₁ h₂ h₃ =>
    hmin (a, b) (mem_filter.2 ⟨mem_univ _, h₁, h₂, h₃⟩)
  have hmaxT : ∀ a, G.Adj a q → P.IsLine a q → f a ≤ f p := fun a h₁ h₂ =>
    hmax a (mem_filter.2 ⟨mem_univ _, h₁, h₂⟩)
  refine ⟨p, q, hqR, hpL, hpG, fun w => ⟨fun hwq => ?_, ?_⟩⟩
  · by_cases hwp : w = p
    · exact Or.inl hwp
    refine Or.inr ?_
    have hadj : G.Adj w p ∨ G.Adj p w := by
      by_contra hn
      push Not at hn
      exact (hP.isArrow_of_isVStructure p q w
        ⟨hpG, hwq, fun h => hwp h.symm, hn.2, hn.1⟩).2 hpL.2
    rcases hadj with h | hpw
    · exact h
    exfalso
    rcases hP.isArrow_or_isLine hG hwq with harr | hline
    · rcases hP.isArrow_or_isLine hG hpw with harr' | hline'
      · exact hcl p q (Or.inr (Or.inl ⟨hpL, w, harr', harr⟩))
      · have h₁ := hminS p w hpw hline' (hR w q hwq hqR)
        have h₂ := hf hwq
        omega
    · have h₁ := hmaxT w hwq hline
      have h₂ := hf hpw
      omega
  · rintro (rfl | hwp)
    · exact hpG
    by_contra hwq
    have hqw : ¬ G.Adj q w := fun hqw =>
      hG q (TransGen.head hqw (TransGen.head hwp (TransGen.single hpG)))
    rcases hP.isArrow_or_isLine hG hwp with harr | hline
    · refine hcl p q (Or.inl ⟨hpL, w, harr, ?_, hP.not_adj_of_not_gAdj hwq hqw,
        hP.not_adj_of_not_gAdj hqw hwq⟩)
      rintro rfl
      exact hG.asymm hwp hpG
    · have h₁ := hminS w p hwp hline (hR p q hpG hqR)
      have h₂ := hf hpG
      omega

/-- **A closed partial pattern with an undirected edge has a covered undirected edge.** Let `P`
be a partial pattern for a finite acyclic graph `G` to which no rule applies. If `P` has an
undirected edge, then some undirected edge `p ∼ q` of `P` is a covered edge `p → q` of `G`. -/
theorem IsPartialPattern.exists_isCovered_of_isLine [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic) (hcl : ∀ a b, ¬ MeekRule P a b) {u v : V} (huv : P.IsLine u v) :
    ∃ p q, P.IsLine p q ∧ G.IsCovered p q := by
  rcases hP.adj_or_adj_of_adj huv.1 with h | h
  · obtain ⟨p, q, -, hl, hc⟩ := hP.exists_isCovered_of_isLine_of_mem hG hcl
      (R := Set.univ) (fun _ _ _ _ => trivial) huv h trivial
    exact ⟨p, q, hl, hc⟩
  · obtain ⟨p, q, -, hl, hc⟩ := hP.exists_isCovered_of_isLine_of_mem hG hcl
      (R := Set.univ) (fun _ _ _ _ => trivial) huv.symm h trivial
    exact ⟨p, q, hl, hc⟩

/-- In a closed partial pattern, a directed path between adjacent vertices `x` and `y` forces the
edge between them to be the directed edge `x → y`. -/
theorem IsPartialPattern.isArrow_of_transGen (hP : P.IsPartialPattern G) (hG : G.IsAcyclic)
    (hcl : ∀ a b, ¬ MeekRule P a b) {x y : V} (h : TransGen P.IsArrow x y)
    (hxy : P.Adj x y ∨ P.Adj y x) : P.IsArrow x y := by
  have hGpath : ∀ {a b}, TransGen P.IsArrow a b → TransGen G.Adj a b := by
    intro a b h
    induction h with
    | single hab => exact TransGen.single (hP.isCompelled _ _ hab).1
    | tail _ hab ih => exact ih.tail (hP.isCompelled _ _ hab).1
  induction h with
  | single hab => exact hab
  | @tail c y hxc hcy ih =>
    by_contra hn
    have hline : P.IsLine x y := by
      rcases hxy with hxy | hyx
      · exact ⟨hxy, by_contra fun h => hn ⟨hxy, h⟩⟩
      · refine ⟨by_contra fun h => ?_, hyx⟩
        exact hG x (TransGen.tail (hGpath (TransGen.tail hxc hcy))
          (hP.isCompelled y x ⟨hyx, h⟩).1)
    have hcx : c ≠ x := by
      rintro rfl
      exact hcy.2 hline.2
    by_cases hadj : P.Adj x c ∨ P.Adj c x
    · exact hcl x y (Or.inr (Or.inl ⟨hline, c, ih hadj, hcy⟩))
    · push Not at hadj
      exact hcl y x (Or.inl ⟨hline.symm, c, hcy, hcx, hadj.2, hadj.1⟩)

/-- In a closed partial pattern, there is no directed path between the ends of an undirected
edge. -/
theorem IsPartialPattern.not_transGen_of_isLine (hP : P.IsPartialPattern G) (hG : G.IsAcyclic)
    (hcl : ∀ a b, ¬ MeekRule P a b) {x y : V} (hl : P.IsLine x y) :
    ¬ TransGen P.IsArrow x y :=
  fun h => (hP.isArrow_of_transGen hG hcl h (Or.inl hl.1)).2 hl.2

/-- **A closed partial pattern with an undirected edge has a reversible undirected edge.** -/
theorem IsPartialPattern.exists_isReversible_of_isLine [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic) (hcl : ∀ a b, ¬ MeekRule P a b) {u v : V} (huv : P.IsLine u v) :
    ∃ p q, P.IsLine p q ∧ G.IsReversible p q := by
  obtain ⟨p, q, hl, hc⟩ := hP.exists_isCovered_of_isLine hG hcl huv
  exact ⟨p, q, hl,
    (isReversible_iff_exists_isCovered hG hc.1).2 ⟨G, hG, MarkovEquivalent.refl G, hc⟩⟩

/-- The completeness of the rules is equivalent to the reversibility of every undirected edge
of every closed partial pattern. -/
theorem meekComplete_iff [Fintype V] [DecidableEq V] :
    MeekComplete V ↔ ∀ G P : Digraph V, G.IsAcyclic → P.IsPartialPattern G →
      (∀ a b, ¬ MeekRule P a b) → ∀ u v, P.IsLine u v → G.Adj u v → G.IsReversible u v := by
  constructor
  · intro h G P hG hP hcl u v hl huv
    refine (isCompelled_or_isReversible hG huv).1.resolve_left fun hc => ?_
    exact (h G P hG hP hcl u v hc).2 hl.2
  · intro h G P hG hP hcl u v hc
    rcases hP.isArrow_or_isLine hG hc.1 with harr | hl
    · exact harr
    · exact absurd ⟨hc, h G P hG hP hcl u v hl hc.1⟩ (isCompelled_or_isReversible hG hc.1).2

/-! ### The PC output and Markov equivalence -/

section PC

variable [Fintype V] [DecidableEq V]

/-- The PC output depends only on the oracle as a relation. -/
theorem pcOutput_congr {I I' : V → V → Finset V → Prop} [∀ x y S, Decidable (I x y S)]
    [∀ x y S, Decidable (I' x y S)] (h : ∀ x y S, I x y S ↔ I' x y S) :
    pcOutput I = pcOutput I' := by
  have : I = I' := funext fun x => funext fun y => funext fun S => propext (h x y S)
  subst this
  congr

omit [Fintype V] [DecidableEq V] in
/-- A partial pattern for two acyclic graphs forces their v-structures to agree. -/
theorem IsPartialPattern.isVStructure_of_isPartialPattern (hG : P.IsPartialPattern G)
    (hH : P.IsPartialPattern H) {a c b : V} (h : G.IsVStructure a c b) :
    H.IsVStructure a c b := by
  have hsk : G.skeleton = H.skeleton := hG.skeleton_eq.symm.trans hH.skeleton_eq
  have hn : ¬ H.skeleton.Adj a b := by
    rw [← hsk, skeleton_adj]
    rintro ⟨-, h' | h'⟩
    · exact h.2.2.2.1 h'
    · exact h.2.2.2.2 h'
  refine ⟨(hH.isCompelled a c (hG.isArrow_of_isVStructure a c b h)).1,
    (hH.isCompelled b c (hG.isArrow_of_isVStructure b c a h.symm)).1, h.2.2.1,
    fun h' => hn (skeleton_adj.2 ⟨h.2.2.1, Or.inl h'⟩),
    fun h' => hn (skeleton_adj.2 ⟨h.2.2.1, Or.inr h'⟩)⟩

/-- **The PC output identifies the equivalence class.** Under d-separation oracles of two acyclic
graphs `G` and `H` on a finite vertex type, the PC algorithm gives the same output if and only if
`G` and `H` are Markov equivalent. -/
theorem pcOutput_eq_iff_markovEquivalent {I I' : V → V → Finset V → Prop}
    [∀ x y S, Decidable (I x y S)] [∀ x y S, Decidable (I' x y S)]
    (hI : ∀ x y S, I x y S ↔ G.DSep {x} {y} ↑S) (hI' : ∀ x y S, I' x y S ↔ H.DSep {x} {y} ↑S)
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    pcOutput I = pcOutput I' ↔ MarkovEquivalent G H := by
  constructor
  · intro heq
    have hPG := pcOutput_isPartialPattern hI hG
    have hPH := pcOutput_isPartialPattern hI' hH
    rw [heq] at hPG
    exact (markovEquivalent_iff hG hH).2 ⟨hPG.skeleton_eq.symm.trans hPH.skeleton_eq,
      fun a c b => ⟨hPG.isVStructure_of_isPartialPattern hPH,
        hPH.isVStructure_of_isPartialPattern hPG⟩⟩
  · intro hGH
    exact pcOutput_congr fun x y S => by rw [hI, hI', hGH]

/-- **The PC algorithm with a Markov and faithful law.** Under the conditional independence
oracle of a law that is Markov and faithful to a finite acyclic graph `G`, the output of the PC
algorithm is the pattern of `G`, given the completeness of the rules (`Digraph.MeekComplete`,
not proved here). -/
theorem pcOutput_condIndep_eq_pattern {α : V → Type*} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] {p : CausalInference.FiniteDist (∀ v, α v)}
    [∀ x y S, Decidable (p.CondIndep {x} {y} S)] (hG : G.IsAcyclic) (hM : G.GlobalMarkov p)
    (hF : p.IsFaithful G) (hMeek : MeekComplete V) :
    toDigraph (pcOutput fun x y S => p.CondIndep {x} {y} S) = pattern G :=
  pcOutput_eq_pattern (condIndep_oracle_iff_dSep hM hF) hG hMeek

open Classical in
/-- **The PC algorithm on data from a faithful law.** Every finite acyclic graph `G` has a law
over binary variables that factorizes according to `G` and such that, with the conditional
independence oracle of the law, the adjacency phase returns the skeleton of `G`, the collider
phase finds exactly the v-structures of `G`, and the output is a partial pattern for `G`: every
edge it directs is compelled. -/
theorem exists_law_pcOutput [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    ∃ p : CausalInference.FiniteDist (V → Bool), G.Factorizes p ∧ p.IsFaithful G ∧
      (∀ x y, (x, y) ∈ pcAdj (fun x y S => p.CondIndep {x} {y} S) ↔ G.skeleton.Adj x y) ∧
      toDigraph (pcColliders fun x y S => p.CondIndep {x} {y} S) = vStructurePattern G ∧
      (toDigraph (pcOutput fun x y S => p.CondIndep {x} {y} S)).IsPartialPattern G := by
  obtain ⟨p, hp, hF⟩ := G.exists_factorizes_isFaithful hG
  have hI := condIndep_oracle_iff_dSep (hp.globalMarkov hG) hF
  exact ⟨p, hp, hF, fun x y => mem_pcAdj_iff hI hG, toDigraph_pcColliders hI hG,
    pcOutput_isPartialPattern hI hG⟩

end PC

end Digraph
