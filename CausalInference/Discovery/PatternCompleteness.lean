/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.MeekCompleteness
public import CausalInference.Discovery.Simplicial

/-!
# Completeness of the orientation rules

This file proves the completeness of the orientation rules R1 to R4 (Meek 1995):
`Digraph.meekComplete V` for every finite vertex type `V`. In every partial pattern for a finite
acyclic graph `G` to which no rule applies, every compelled edge of `G` is directed. Hence the
pattern of `G` is the only such partial pattern (`Digraph.IsPartialPattern.eq_pattern_of_closed`),
and the PC algorithm returns the pattern under a d-separation oracle
(`Digraph.pcOutput_eq_pattern'`) and under the conditional independence oracle of a law that is
Markov and faithful to `G` (`Digraph.pcOutput_condIndep_eq_pattern'`).

## Outline

1. **Strong rule one.** Let `F` be the closure of the v-structure pattern of `G` under the rules.
   Then a directed edge `a → b` and an undirected edge `b ∼ c` of `F` force the directed edge
   `a → c` (`Digraph.closure_isArrow_of_isArrow_of_isLine`). The proof is by induction along the
   passes of the rules, with a case analysis on the rule that directed `a → b`
   (`Digraph.isArrow_of_isVStructure_of_isLine`, `Digraph.isArrow_of_meekRule_of_isLine`).
2. **No partially directed cycles.** Under strong rule one, a directed edge `a → b` has no
   path of edges of either kind from `b` back to `a`
   (`Digraph.IsPartialPattern.not_reflTransGen_of_isArrow`).
3. **An elimination candidate.** In every nonempty set `W` of vertices there is a vertex `x` with
   no directed edge to `W` whose undirected neighbors in `W` are adjacent to all its other
   neighbors in `W` (the criterion of Dor and Tarsi 1992), and `x` can be taken different from
   the head `v` of a given undirected edge `u ∼ v` inside `W`
   (`Digraph.IsPartialPattern.exists_isElimCandidate`). It is a simplicial vertex of a terminal
   component of the undirected edges in `W`, found with `Digraph.exists_isSimplicialIn`.
4. **An extension.** Removing candidates one at a time orders the vertices; directing every edge
   toward the vertex removed first gives an acyclic graph Markov equivalent to `G` that contains
   all directed edges and has `v → u` (`Digraph.IsPartialPattern.exists_elimOrder`,
   `Digraph.IsPartialPattern.isReversible_of_isLine`). So the closure is the pattern
   (`Digraph.closure_eq_pattern`).
5. **Any closed partial pattern.** Every directed edge of the closure is directed in every
   partial pattern for `G` to which no rule applies (`Digraph.isArrow_of_meekRule_of_closed`), by
   induction along the passes again.

## References

* C. Meek (1995).
* D. Dor and M. Tarsi (1992).
* G. A. Dirac (1961).
-/

@[expose] public section

namespace Digraph

open Relation Finset

variable {V : Type*} {G P F T : Digraph V} {a b c : V}

/-! ### Elementary facts about partially directed graphs -/

/-- Two adjacent vertices are joined by a directed edge in one direction or by an undirected
edge. -/
theorem isArrow_or_isArrow_or_isLine {Q : Digraph V} {x y : V} (h : Q.Adj x y ∨ Q.Adj y x) :
    Q.IsArrow x y ∨ Q.IsArrow y x ∨ Q.IsLine x y := by
  by_cases h₁ : Q.Adj x y <;> by_cases h₂ : Q.Adj y x
  · exact Or.inr (Or.inr ⟨h₁, h₂⟩)
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr (Or.inl ⟨h₂, h₁⟩)
  · exact absurd h (by tauto)

/-- Adjacency in one partial pattern for `G` is adjacency in every other. -/
theorem IsPartialPattern.adj_or_adj_of_adj_or_adj (hP : P.IsPartialPattern G)
    (hF : F.IsPartialPattern G) (hG : G.IsAcyclic) {x y : V} (h : P.Adj x y ∨ P.Adj y x) :
    F.Adj x y ∨ F.Adj y x := by
  rcases h with h | h
  · rcases hP.adj_or_adj_of_adj h with h' | h'
    · exact hF.adj_or_adj_of_gAdj hG h'
    · exact (hF.adj_or_adj_of_gAdj hG h').symm
  · rcases hP.adj_or_adj_of_adj h with h' | h'
    · exact (hF.adj_or_adj_of_gAdj hG h').symm
    · exact hF.adj_or_adj_of_gAdj hG h'

/-- Arrows survive a pass of the rules. -/
theorem IsArrow.meekPass (h : P.IsArrow a b) : (meekPass P).IsArrow a b :=
  ⟨⟨h.1, fun hr => h.2 hr.isLine.1⟩, fun h' => h.2 h'.1⟩

theorem IsArrow.iterate_meekPass (h : P.IsArrow a b) (k : ℕ) :
    (Digraph.meekPass^[k] P).IsArrow a b := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.meekPass

/-- Passes of the rules only remove arcs. -/
theorem adj_of_iterate_meekPass {k : ℕ} (h : (Digraph.meekPass^[k] P).Adj a b) : P.Adj a b := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at h
    exact ih h.1

/-- A directed edge after a pass of the rules was directed before, or a rule directed it. -/
theorem isArrow_or_meekRule_of_isArrow_meekPass (h : (meekPass P).IsArrow a b) :
    P.IsArrow a b ∨ MeekRule P a b := by
  by_cases hba : P.Adj b a
  · refine Or.inr ?_
    by_contra hr
    exact h.2 ⟨hba, hr⟩
  · exact Or.inl ⟨h.1.1, hba⟩

/-! ### Strong rule one for the closure of the v-structure pattern -/

/-- In a partially directed graph to which no rule applies, a directed edge `a → b` and an
undirected edge `b ∼ c` with `a ∼ c` not undirected force the directed edge `a → c`. -/
theorem isArrow_of_not_isLine_of_closed (hcl : ∀ a b, ¬ MeekRule F a b) (hab : F.IsArrow a b)
    (hbc : F.IsLine b c) (hn : ¬ F.IsLine a c) : F.IsArrow a c := by
  have hac : a ≠ c := by
    rintro rfl
    exact hab.2 hbc.1
  have hadj : F.Adj a c ∨ F.Adj c a := by
    by_contra h
    push Not at h
    exact hcl b c (Or.inl ⟨hbc, a, hab, hac, h.1, h.2⟩)
  rcases isArrow_or_isArrow_or_isLine hadj with h | h | h
  · exact h
  · exact absurd (Or.inr (Or.inl ⟨hbc.symm, a, h, hab⟩)) (hcl c b)
  · exact absurd h hn

/-- **Strong rule one, base case.** In a closed partial pattern `F` for `G`, the edge `a → b` of a
v-structure `a → b ← d` of `G` and an undirected edge `b ∼ c` force `a → c`. -/
theorem isArrow_of_isVStructure_of_isLine (hF : F.IsPartialPattern G)
    (hcl : ∀ a b, ¬ MeekRule F a b) {d : V} (hv : G.IsVStructure a b d) (hbc : F.IsLine b c) :
    F.IsArrow a c := by
  have hab := hF.isArrow_of_isVStructure a b d hv
  have hdb := hF.isArrow_of_isVStructure d b a hv.symm
  have hn₁ := hF.not_adj_of_not_gAdj hv.2.2.2.1 hv.2.2.2.2
  have hn₂ := hF.not_adj_of_not_gAdj hv.2.2.2.2 hv.2.2.2.1
  refine isArrow_of_not_isLine_of_closed hcl hab hbc fun hac => ?_
  by_cases hdc : F.IsLine d c
  · exact hcl c b (Or.inr (Or.inr (Or.inl ⟨hbc.symm, a, d, hac.symm, hab, hdc.symm, hdb,
      hv.2.2.1, hn₁, hn₂⟩)))
  · have hdc' := isArrow_of_not_isLine_of_closed hcl hdb hbc hdc
    exact hcl c a (Or.inl ⟨hac.symm, d, hdc', hv.2.2.1.symm, hn₂, hn₁⟩)

/-- **Strong rule one, induction step.** Let `F` be a closed partial pattern for `G` and `P` a
partial pattern for `G` whose arrows are arrows of `F`, whose arcs contain those of `F`, and whose
arrows satisfy strong rule one in `F`. If a rule directs `a ∼ b` in `P` and `a → b` is directed in
`F`, then `a → b` and an undirected edge `b ∼ c` of `F` force `a → c` in `F`. -/
theorem isArrow_of_meekRule_of_isLine (hF : F.IsPartialPattern G) (hG : G.IsAcyclic)
    (hcl : ∀ a b, ¬ MeekRule F a b) (hP : P.IsPartialPattern G)
    (hPF : ∀ x y, P.IsArrow x y → F.IsArrow x y) (hFP : ∀ x y, F.Adj x y → P.Adj x y)
    (ih : ∀ x y, P.IsArrow x y → ∀ z, F.IsLine y z → F.IsArrow x z)
    (hr : MeekRule P a b) (habF : F.IsArrow a b) (hbc : F.IsLine b c) : F.IsArrow a c := by
  have hnF : ∀ {x y}, ¬ P.Adj x y → ¬ F.Adj x y := fun h h' => h (hFP _ _ h')
  have hadjF : ∀ {x y}, (P.Adj x y ∨ P.Adj y x) → F.Adj x y ∨ F.Adj y x :=
    hP.adj_or_adj_of_adj_or_adj hF hG
  refine isArrow_of_not_isLine_of_closed hcl habF hbc fun hac => ?_
  rcases hr with ⟨-, e, hea, heb, hn₁, hn₂⟩ | ⟨-, e, hae, heb⟩ |
      ⟨-, e, f, hlae, heb, hlaf, hfb, hef, hn₁, hn₂⟩ |
      ⟨-, e, f, hlae, hef, hfb, heb, hn₁, hn₂, hadf⟩
  · -- rule R1: `e → a ∼ b`
    have hec := ih e a hea c hac
    exact hcl c b (Or.inl ⟨hbc.symm, e, hec, heb, hnF hn₁, hnF hn₂⟩)
  · -- rule R2: `a → e → b`
    have hec := ih e b heb c hbc
    exact hcl a c (Or.inr (Or.inl ⟨hac, e, hPF a e hae, hec⟩))
  · -- rule R3: `a ∼ e → b` and `a ∼ f → b`
    have hec := ih e b heb c hbc
    have hfc := ih f b hfb c hbc
    have hvs : ¬ (F.IsArrow e a ∧ F.IsArrow f a) := by
      rintro ⟨h₁, h₂⟩
      have hGef : ¬ G.Adj e f := fun h => by
        rcases hP.adj_or_adj_of_gAdj hG h with h' | h'
        · exact hn₁ h'
        · exact hn₂ h'
      have hGfe : ¬ G.Adj f e := fun h => by
        rcases hP.adj_or_adj_of_gAdj hG h with h' | h'
        · exact hn₂ h'
        · exact hn₁ h'
      exact (hP.isArrow_of_isVStructure e a f ⟨(hF.isCompelled e a h₁).1,
        (hF.isCompelled f a h₂).1, hef, hGef, hGfe⟩).2 hlae.1
    rcases isArrow_or_isArrow_or_isLine (hadjF (Or.inl hlae.1)) with hae | hea | hle
    · exact hcl a c (Or.inr (Or.inl ⟨hac, e, hae, hec⟩))
    · rcases isArrow_or_isArrow_or_isLine (hadjF (Or.inl hlaf.1)) with haf | hfa | hlf
      · exact hcl a c (Or.inr (Or.inl ⟨hac, f, haf, hfc⟩))
      · exact hvs ⟨hea, hfa⟩
      · exact hcl a f (Or.inl ⟨hlf, e, hea, hef, hnF hn₁, hnF hn₂⟩)
    · rcases isArrow_or_isArrow_or_isLine (hadjF (Or.inl hlaf.1)) with haf | hfa | hlf
      · exact hcl a c (Or.inr (Or.inl ⟨hac, f, haf, hfc⟩))
      · exact hcl a e (Or.inl ⟨hle, f, hfa, hef.symm, hnF hn₂, hnF hn₁⟩)
      · exact hcl a c (Or.inr (Or.inr (Or.inl ⟨hac, e, f, hle, hec, hlf, hfc, hef,
          hnF hn₁, hnF hn₂⟩)))
  · -- rule R4: `a ∼ e → f` and `e → f → b`
    have hefF := hPF e f hef
    have hfc := ih f b hfb c hbc
    have hec : e ≠ c := by
      rintro rfl
      exact hnF hn₂ hbc.1
    have hcyc : ¬ F.IsArrow c e := fun h => hG c (TransGen.head (hF.isCompelled c e h).1
      (TransGen.head (hF.isCompelled e f hefF).1 (TransGen.single (hF.isCompelled f c hfc).1)))
    have hecF : ¬ (F.Adj e c ∨ F.Adj c e) := by
      intro h
      rcases isArrow_or_isArrow_or_isLine h with h' | h' | h'
      · exact hcl c b (Or.inl ⟨hbc.symm, e, h', heb, hnF hn₁, hnF hn₂⟩)
      · exact hcyc h'
      · exact hcl e c (Or.inr (Or.inl ⟨h', f, hefF, hfc⟩))
    have hea_false : ¬ F.IsArrow e a := by
      intro hea
      refine hecF ?_
      by_contra h
      push Not at h
      exact hcl a c (Or.inl ⟨hac, e, hea, hec, h.1, h.2⟩)
    rcases isArrow_or_isArrow_or_isLine (hadjF hadf) with haf | hfa | hlf
    · exact hcl a c (Or.inr (Or.inl ⟨hac, f, haf, hfc⟩))
    · rcases isArrow_or_isArrow_or_isLine (hadjF (Or.inl hlae.1)) with hae | hea | hle
      · exact hG a (TransGen.head (hF.isCompelled a e hae).1 (TransGen.head
          (hF.isCompelled e f hefF).1 (TransGen.single (hF.isCompelled f a hfa).1)))
      · exact hea_false hea
      · exact hcl e a (Or.inr (Or.inl ⟨hle.symm, f, hefF, hfa⟩))
    · rcases isArrow_or_isArrow_or_isLine (hadjF (Or.inl hlae.1)) with hae | hea | hle
      · exact hcl a f (Or.inr (Or.inl ⟨hlf, e, hae, hefF⟩))
      · exact hea_false hea
      · refine hecF ?_
        by_contra h
        push Not at h
        exact hcl a c (Or.inr (Or.inr (Or.inr ⟨hac, e, f, hle, hefF, hfc, hec, h.1, h.2,
          Or.inl hlf.1⟩)))

/-! ### No partially directed cycles -/

/-- **No partially directed cycles.** In a partial pattern for an acyclic graph that satisfies
strong rule one, a directed edge `a → b` has no path of edges of either kind from `b` back
to `a`. -/
theorem IsPartialPattern.not_reflTransGen_of_isArrow {Q : Digraph V}
    (hP : Q.IsPartialPattern G) (hG : G.IsAcyclic)
    (hii : ∀ a b c, Q.IsArrow a b → Q.IsLine b c → Q.IsArrow a c) (hab : Q.IsArrow a b) :
    ¬ ReflTransGen Q.Adj b a := by
  intro h
  have key : ∀ c, ReflTransGen Q.Adj b c → ∃ d, Q.IsArrow d c ∧ ReflTransGen G.Adj a d := by
    intro c hc
    induction hc with
    | refl => exact ⟨a, hab, ReflTransGen.refl⟩
    | @tail c c₂ _ hcc ih =>
      obtain ⟨d, hdc, had⟩ := ih
      by_cases h₂ : Q.Adj c₂ c
      · exact ⟨d, hii d c c₂ hdc ⟨hcc, h₂⟩, had⟩
      · exact ⟨c, ⟨hcc, h₂⟩, had.tail (hP.isCompelled d c hdc).1⟩
  obtain ⟨d, hda, had⟩ := key a h
  exact hG a (TransGen.tail' had (hP.isCompelled d a hda).1)

/-! ### Elimination candidates and the extension -/

/-- The vertex `x` of `W` is an elimination candidate in `W`: no directed edge leaves `x` toward
`W`, and every undirected neighbor of `x` in `W` is adjacent to every other neighbor of `x` in
`W`. -/
def IsElimCandidate (Q : Digraph V) (W : Finset V) (x : V) : Prop :=
  x ∈ W ∧ (∀ y ∈ W, ¬ Q.IsArrow x y) ∧
    ∀ y ∈ W, ∀ z ∈ W, Q.IsLine x y → (Q.Adj x z ∨ Q.Adj z x) → y ≠ z →
      (Q.Adj y z ∨ Q.Adj z y)

section Extension

variable [Finite V]

/-- **An elimination candidate.** Let `Q` be a partial pattern for a finite acyclic graph `G`
that satisfies strong rule one. Every nonempty set `W` of vertices has an elimination candidate,
and the candidate can be taken different from `v` whenever `W` contains an undirected edge
`u ∼ v`. -/
theorem IsPartialPattern.exists_isElimCandidate {Q : Digraph V} (hP : Q.IsPartialPattern G)
    (hG : G.IsAcyclic) (hii : ∀ a b c, Q.IsArrow a b → Q.IsLine b c → Q.IsArrow a c)
    (W : Finset V) (hW : W.Nonempty) (v : V) :
    ∃ x, IsElimCandidate Q W x ∧ ∀ u ∈ W, v ∈ W → Q.IsLine u v → x ≠ v := by
  classical
  let RW : V → V → Prop := fun p q => p ∈ W ∧ q ∈ W ∧ Q.Adj p q
  let reach : V → Finset V := fun x => W.filter fun y => ReflTransGen RW x y
  obtain ⟨x, hxW, hmin⟩ := W.exists_min_image (fun x => (reach x).card) hW
  have hrefl : x ∈ reach x := mem_filter.2 ⟨hxW, ReflTransGen.refl⟩
  have hsub : ∀ y ∈ reach x, reach y ⊆ reach x := fun y hy z hz =>
    mem_filter.2 ⟨(mem_filter.1 hz).1, (mem_filter.1 hy).2.trans (mem_filter.1 hz).2⟩
  have hback : ∀ y ∈ reach x, ReflTransGen RW y x := by
    intro y hy
    have heq : reach y = reach x :=
      eq_of_subset_of_card_le (hsub y hy) (hmin y (mem_filter.1 hy).1)
    have hx : x ∈ reach y := heq ▸ hrefl
    exact (mem_filter.1 hx).2
  have hmono : ∀ {p q}, ReflTransGen RW p q → ReflTransGen Q.Adj p q := by
    intro p q h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ h ih => exact ih.tail h.2.2
  have hCW : ∀ y ∈ reach x, y ∈ W := fun y hy => (mem_filter.1 hy).1
  have hclosed : ∀ y ∈ reach x, ∀ w ∈ W, Q.Adj y w → w ∈ reach x := fun y hy w hw h =>
    mem_filter.2 ⟨hw, (mem_filter.1 hy).2.tail ⟨hCW y hy, hw, h⟩⟩
  have hnoarrow : ∀ y ∈ reach x, ∀ w ∈ W, ¬ Q.IsArrow y w := by
    intro y hy w hw h
    exact hP.not_reflTransGen_of_isArrow hG hii h
      (hmono ((hback w (hclosed y hy w hw h.1)).trans (mem_filter.1 hy).2))
  have hline : ∀ y ∈ reach x, ∀ w ∈ W, Q.Adj y w → Q.IsLine y w := fun y hy w hw h =>
    ⟨h, by_contra fun h' => hnoarrow y hy w hw ⟨h, h'⟩⟩
  have hadjC : ∀ y ∈ reach x, ∀ z ∈ reach x, (Q.Adj y z ∨ Q.Adj z y) → Q.IsLine y z := by
    rintro y hy z hz (h | h)
    · exact hline y hy z (hCW z hz) h
    · exact (hline z hz y (hCW y hy) h).symm
  have hor : ∀ a ∈ reach x, ∀ b ∈ reach x, Q.IsLine a b → G.Adj a b ∨ G.Adj b a :=
    fun _ _ _ _ h => hP.adj_or_adj_of_adj h.1
  have hvs : ∀ a ∈ reach x, ∀ b ∈ reach x, ∀ c ∈ reach x, Q.IsLine a c → Q.IsLine b c →
      G.Adj a c → G.Adj b c → a ≠ b → Q.IsLine a b := by
    intro a ha b hb c _ hac _ hGac hGbc hab
    by_cases hG' : G.Adj a b ∨ G.Adj b a
    · rcases hG' with h | h
      · exact hadjC a ha b hb (hP.adj_or_adj_of_gAdj hG h)
      · exact hadjC a ha b hb (hP.adj_or_adj_of_gAdj hG h).symm
    · push Not at hG'
      exact absurd hac.2 (hP.isArrow_of_isVStructure a c b ⟨hGac, hGbc, hab, hG'.1, hG'.2⟩).2
  obtain ⟨x', hx'C, hsimp, hx'v⟩ := exists_isSimplicialIn (L := Q.IsLine)
    (fun _ _ h => h.symm) hG (reach x) hor hvs ⟨x, hrefl⟩ v
  refine ⟨x', ⟨hCW x' hx'C, hnoarrow x' hx'C, ?_⟩, ?_⟩
  · intro y hy z hz hxy hxz hyz
    have hyC := hclosed x' hx'C y hy hxy.1
    by_cases hzC : z ∈ reach x
    · exact Or.inl (hsimp y hyC z hzC hxy (hadjC x' hx'C z hzC hxz) hyz).1
    · have hzx : Q.Adj z x' := hxz.resolve_left fun h => hzC (hclosed x' hx'C z hz h)
      have hxz' : ¬ Q.Adj x' z := fun h => hzC (hclosed x' hx'C z hz h)
      exact Or.inr (hii z x' y ⟨hzx, hxz'⟩ hxy).1
  · intro u hu hv hl
    by_cases hvC : v ∈ reach x
    · have huC := hclosed v hvC u hu hl.2
      exact hx'v u huC (fun e => hP.irrefl u (e ▸ hl.1 : Q.Adj u u))
    · exact fun e => hvC (e ▸ hx'C)

/-- **The extension order.** Let `Q` be a partial pattern for a finite acyclic graph `G` that
satisfies strong rule one, and let `u, v` be vertices. Every set `W` of vertices has a labeling
`t`, injective on `W`, such that directed edges of `Q` in `W` go from larger to smaller labels,
every pair of nonadjacent vertices of `W` with a common neighbor in `W` of smaller label points
into it along directed edges of `Q`, and an undirected edge `u ∼ v` inside `W` has
`t u < t v`. -/
theorem IsPartialPattern.exists_elimOrder {Q : Digraph V} (hP : Q.IsPartialPattern G)
    (hG : G.IsAcyclic) (hii : ∀ a b c, Q.IsArrow a b → Q.IsLine b c → Q.IsArrow a c)
    (u v : V) (W : Finset V) :
    ∃ t : V → ℕ, Set.InjOn t W ∧
      (∀ a ∈ W, ∀ b ∈ W, Q.IsArrow a b → t b < t a) ∧
      (∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W, (Q.Adj a c ∨ Q.Adj c a) → (Q.Adj b c ∨ Q.Adj c b) →
        t c < t a → t c < t b → a ≠ b → ¬ (Q.Adj a b ∨ Q.Adj b a) → Q.IsArrow a c) ∧
      (u ∈ W → v ∈ W → Q.IsLine u v → t u < t v) := by
  classical
  induction W using Finset.strongInduction with
  | H W ih =>
  rcases W.eq_empty_or_nonempty with rfl | hW
  · exact ⟨fun _ => 0, by simp, by simp, by simp, by simp⟩
  obtain ⟨x, ⟨hxW, hxout, hxsimp⟩, hxv⟩ := hP.exists_isElimCandidate hG hii W hW v
  obtain ⟨t', hinj, harr, hvs, htarget⟩ := ih (W.erase x) (erase_ssubset hxW)
  have hmem : ∀ {y}, y ∈ W → y ≠ x → y ∈ W.erase x := fun hy hne => mem_erase.2 ⟨hne, hy⟩
  refine ⟨fun y => if y = x then 0 else t' y + 1, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only at hab
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · simp [hax, hbx] at hab
    · simp [hax, hbx] at hab
    · simp only [hax, hbx, ↓reduceIte, add_left_inj] at hab
      exact hinj (mem_coe.2 (hmem (mem_coe.1 ha) hax)) (mem_coe.2 (hmem (mem_coe.1 hb) hbx)) hab
  · intro a ha b hb hab
    have hne : a ≠ b := fun e => hP.irrefl a (e ▸ hab.1 : Q.Adj a a) |>.elim
    by_cases hax : a = x
    · exact absurd hab (hax ▸ hxout b hb)
    by_cases hbx : b = x
    · simp [hax, hbx]
    · have := harr a (hmem ha hax) b (hmem hb hbx) hab
      simp [hax, hbx, this]
  · intro a ha b hb c hc hac hbc hca hcb hab hnab
    by_cases hcx : c = x
    · subst hcx
      by_cases hl : Q.IsLine c a
      · exact absurd (hxsimp a ha b hb hl (Or.symm hbc) hab) hnab
      rcases isArrow_or_isArrow_or_isLine hac with h | h | h
      · exact h
      · exact absurd h (hxout a ha)
      · exact absurd h.symm hl
    · have hax : a ≠ x := by
        rintro rfl
        simp [hcx] at hca
      have hbx : b ≠ x := by
        rintro rfl
        simp [hcx] at hcb
      simp only [hax, hbx, hcx, ↓reduceIte, add_lt_add_iff_right] at hca hcb
      exact hvs a (hmem ha hax) b (hmem hb hbx) c (hmem hc hcx) hac hbc hca hcb hab hnab
  · intro hu hv hl
    have hxv' := hxv u hu hv hl
    by_cases hux : u = x
    · simp [hux, Ne.symm hxv']
    · have hvx : v ≠ x := Ne.symm hxv'
      have := htarget (hmem hu hux) (hmem hv hvx) hl
      simp [hux, hvx, this]

/-- **Undirected edges are reversible.** Let `Q` be a partial pattern for a finite acyclic graph
`G` that satisfies strong rule one. If `u ∼ v` is undirected in `Q` and `u → v` is an edge of
`G`, then `u → v` is reversible in `G`. -/
theorem IsPartialPattern.isReversible_of_isLine {Q : Digraph V} (hP : Q.IsPartialPattern G)
    (hG : G.IsAcyclic) (hii : ∀ a b c, Q.IsArrow a b → Q.IsLine b c → Q.IsArrow a c)
    {u v : V} (hl : Q.IsLine u v) (huv : G.Adj u v) : G.IsReversible u v := by
  have := Fintype.ofFinite V
  obtain ⟨t, hinj, harr, hvs, htarget⟩ := hP.exists_elimOrder hG hii u v univ
  let H : Digraph V := { Adj := fun a b => (Q.Adj a b ∨ Q.Adj b a) ∧ t b < t a }
  have hH : H.IsAcyclic := isAcyclic_of_adj_lt (α := ℕᵒᵈ) (fun x => OrderDual.toDual (t x))
    fun _ _ h => OrderDual.toDual_lt_toDual.2 h.2
  have hHiff : ∀ a b, a ≠ b → ((H.Adj a b ∨ H.Adj b a) ↔ (Q.Adj a b ∨ Q.Adj b a)) := by
    intro a b hab
    have ht : t a ≠ t b := fun h => hab (hinj (by simp) (by simp) h)
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1.symm
    · intro h
      rcases lt_or_gt_of_ne ht with h' | h'
      · exact Or.inr ⟨h.symm, h'⟩
      · exact Or.inl ⟨h, h'⟩
  have hQG : ∀ a b, (Q.Adj a b ∨ Q.Adj b a) ↔ (G.Adj a b ∨ G.Adj b a) := fun _ _ =>
    hP.adj_or_adj_iff hG rfl
  have hsk : G.skeleton = H.skeleton := by
    ext a b
    rw [skeleton_adj, skeleton_adj]
    refine and_congr_right fun hab => ?_
    rw [hHiff a b hab, hQG]
  have hGH : MarkovEquivalent G H := by
    refine (markovEquivalent_iff hG hH).2 ⟨hsk, fun a c b => ⟨fun h => ?_, fun h => ?_⟩⟩
    · have hac := hP.isArrow_of_isVStructure a c b h
      have hbc := hP.isArrow_of_isVStructure b c a h.symm
      have hnG : ¬ (G.Adj a b ∨ G.Adj b a) := by
        rintro (h' | h')
        · exact h.2.2.2.1 h'
        · exact h.2.2.2.2 h'
      have hnH : ¬ (H.Adj a b ∨ H.Adj b a) := fun h' =>
        hnG ((hQG a b).1 ((hHiff a b h.2.2.1).1 h'))
      exact ⟨⟨Or.inl hac.1, harr a (mem_univ _) c (mem_univ _) hac⟩,
        ⟨Or.inl hbc.1, harr b (mem_univ _) c (mem_univ _) hbc⟩, h.2.2.1,
        fun h' => hnH (Or.inl h'), fun h' => hnH (Or.inr h')⟩
    · obtain ⟨hac, hbc, hab, hn₁, hn₂⟩ := h
      have hnQ : ¬ (Q.Adj a b ∨ Q.Adj b a) := fun h' => by
        rcases (hHiff a b hab).2 h' with h'' | h''
        · exact hn₁ h''
        · exact hn₂ h''
      have hac' := hvs a (mem_univ _) b (mem_univ _) c (mem_univ _) hac.1 hbc.1 hac.2 hbc.2 hab
        hnQ
      have hbc' := hvs b (mem_univ _) a (mem_univ _) c (mem_univ _) hbc.1 hac.1 hbc.2 hac.2
        hab.symm fun h' => hnQ h'.symm
      have hnG : ¬ (G.Adj a b ∨ G.Adj b a) := fun h' => hnQ ((hQG a b).2 h')
      exact ⟨(hP.isCompelled a c hac').1, (hP.isCompelled b c hbc').1, hab,
        fun h' => hnG (Or.inl h'), fun h' => hnG (Or.inr h')⟩
  exact ⟨huv, H, hH, hGH, Or.inr hl.1, htarget (mem_univ _) (mem_univ _) hl⟩

theorem isPartialPattern_iterate (hG : G.IsAcyclic) (n : ℕ) :
    (Digraph.meekPass^[n] (vStructurePattern G)).IsPartialPattern G :=
  (isPartialPattern_vStructurePattern hG).iterate_meekPass hG n

end Extension

/-- An arrow of the v-structure pattern belongs to a v-structure. -/
theorem exists_isVStructure_of_isArrow (h : (vStructurePattern G).IsArrow a b) :
    ∃ d, G.IsVStructure a b d := by
  have h₂ := h.2
  simp only [vStructurePattern, not_and, not_not] at h₂
  exact h₂ h.1.1.symm

/-! ### The closure of the v-structure pattern -/

section Closure

variable [Fintype V]

/-- The closure of the v-structure pattern under the rules: `(card V) ^ 2` passes. -/
def closure (G : Digraph V) : Digraph V :=
  Digraph.meekPass^[Fintype.card V ^ 2] (vStructurePattern G)

theorem isPartialPattern_closure (hG : G.IsAcyclic) : (closure G).IsPartialPattern G :=
  isPartialPattern_iterate hG _

/-- No rule applies to the closure. -/
theorem forall_not_meekRule_closure (G : Digraph V) : ∀ a b, ¬ MeekRule (closure G) a b := by
  classical
  have hA : toDigraph ((univ : Finset (V × V)).filter fun p => (vStructurePattern G).Adj p.1 p.2)
      = vStructurePattern G := by
    ext u v
    simp
  have := forall_not_meekRule_iterate
    ((univ : Finset (V × V)).filter fun p => (vStructurePattern G).Adj p.1 p.2)
  rwa [toDigraph_iterate_meekPassF, hA] at this

/-- Arrows of an early pass are arrows of the closure, and arcs of the closure are arcs of every
early pass. -/
theorem isArrow_closure_of_le {n : ℕ} (hn : n ≤ Fintype.card V ^ 2)
    (h : (Digraph.meekPass^[n] (vStructurePattern G)).IsArrow a b) : (closure G).IsArrow a b := by
  have := h.iterate_meekPass (Fintype.card V ^ 2 - n)
  rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hn] at this

theorem adj_of_adj_closure {n : ℕ} (hn : n ≤ Fintype.card V ^ 2) (h : (closure G).Adj a b) :
    (Digraph.meekPass^[n] (vStructurePattern G)).Adj a b := by
  rw [closure, ← Nat.sub_add_cancel hn, Function.iterate_add_apply] at h
  exact adj_of_iterate_meekPass h

/-- **Strong rule one for the closure.** A directed edge `a → b` and an undirected edge `b ∼ c` of
the closure of the v-structure pattern of a finite acyclic graph force the directed edge
`a → c`. -/
theorem closure_isArrow_of_isArrow_of_isLine (hG : G.IsAcyclic) :
    ∀ a b c, (closure G).IsArrow a b → (closure G).IsLine b c → (closure G).IsArrow a c := by
  have hF := isPartialPattern_closure hG
  have hcl := forall_not_meekRule_closure G
  have key : ∀ n ≤ Fintype.card V ^ 2, ∀ x y,
      (Digraph.meekPass^[n] (vStructurePattern G)).IsArrow x y →
      ∀ z, (closure G).IsLine y z → (closure G).IsArrow x z := by
    intro n
    induction n with
    | zero =>
      intro _ x y h z hz
      obtain ⟨d, hd⟩ := exists_isVStructure_of_isArrow h
      exact isArrow_of_isVStructure_of_isLine hF hcl hd hz
    | succ n ih =>
      intro hn x y h z hz
      have h' := h
      rw [Function.iterate_succ_apply'] at h'
      rcases isArrow_or_meekRule_of_isArrow_meekPass h' with h'' | hr
      · exact ih (Nat.le_of_succ_le hn) x y h'' z hz
      · exact isArrow_of_meekRule_of_isLine hF hG hcl (isPartialPattern_iterate hG n)
          (fun _ _ h => isArrow_closure_of_le (Nat.le_of_succ_le hn) h)
          (fun _ _ h => adj_of_adj_closure (Nat.le_of_succ_le hn) h)
          (ih (Nat.le_of_succ_le hn)) hr (isArrow_closure_of_le hn h) hz
  exact fun a b c h hl => key _ le_rfl a b h c hl

/-- **The closure of the v-structure pattern is the pattern** (Meek 1995). -/
theorem closure_eq_pattern (hG : G.IsAcyclic) : closure G = pattern G := by
  have hF := isPartialPattern_closure hG
  have hii := closure_isArrow_of_isArrow_of_isLine hG
  refine hF.eq_pattern hG fun u v hc => ?_
  rcases hF.isArrow_or_isLine hG hc.1 with h | h
  · exact h
  · exact absurd ⟨hc, hF.isReversible_of_isLine hG hii h hc.1⟩
      (isCompelled_or_isReversible hG hc.1).2

/-! ### Every closed partial pattern -/

omit [Fintype V] in
/-- Let `T` be a partial pattern for `G` to which no rule applies, and `P` a partial pattern for
`G` whose arrows are arrows of `T`. If a rule directs `a ∼ b` in `P`, then `a → b` is directed in
`T`. -/
theorem isArrow_of_meekRule_of_closed [Finite V] (hT : T.IsPartialPattern G) (hG : G.IsAcyclic)
    (hcl : ∀ a b, ¬ MeekRule T a b) (hP : P.IsPartialPattern G)
    (hPT : ∀ x y, P.IsArrow x y → T.IsArrow x y) (hr : MeekRule P a b) : T.IsArrow a b := by
  have hadjT : ∀ {x y}, (P.Adj x y ∨ P.Adj y x) → T.Adj x y ∨ T.Adj y x :=
    hP.adj_or_adj_of_adj_or_adj hT hG
  have hnT : ∀ {x y}, ¬ P.Adj x y → ¬ P.Adj y x → ¬ T.Adj x y := fun h₁ h₂ h => by
    rcases hT.adj_or_adj_of_adj_or_adj hP hG (Or.inl h) with h' | h'
    · exact h₁ h'
    · exact h₂ h'
  rcases isArrow_or_isArrow_or_isLine (hadjT (Or.inl hr.isLine.1)) with h | h | hl
  · exact h
  · exact absurd (hT.isCompelled b a h).1 (hG.asymm (hP.isCompelled_of_meekRule hG hr).1)
  exfalso
  rcases hr with ⟨-, e, hea, heb, hn₁, hn₂⟩ | ⟨-, e, hae, heb⟩ |
      ⟨-, e, f, hlae, heb, hlaf, hfb, hef, hn₁, hn₂⟩ |
      ⟨-, e, f, hlae, hef, hfb, heb, hn₁, hn₂, hadf⟩
  · exact hcl a b (Or.inl ⟨hl, e, hPT e a hea, heb, hnT hn₁ hn₂, hnT hn₂ hn₁⟩)
  · exact hcl a b (Or.inr (Or.inl ⟨hl, e, hPT a e hae, hPT e b heb⟩))
  · have hebT := hPT e b heb
    have hfbT := hPT f b hfb
    have hvs : ¬ (T.IsArrow e a ∧ T.IsArrow f a) := by
      rintro ⟨h₁, h₂⟩
      have hGef : ¬ G.Adj e f := fun h => by
        rcases hP.adj_or_adj_of_gAdj hG h with h' | h'
        · exact hn₁ h'
        · exact hn₂ h'
      have hGfe : ¬ G.Adj f e := fun h => by
        rcases hP.adj_or_adj_of_gAdj hG h with h' | h'
        · exact hn₂ h'
        · exact hn₁ h'
      exact (hP.isArrow_of_isVStructure e a f ⟨(hT.isCompelled e a h₁).1,
        (hT.isCompelled f a h₂).1, hef, hGef, hGfe⟩).2 hlae.1
    rcases isArrow_or_isArrow_or_isLine (hadjT (Or.inl hlae.1)) with hae | hea | hle
    · exact hcl a b (Or.inr (Or.inl ⟨hl, e, hae, hebT⟩))
    · rcases isArrow_or_isArrow_or_isLine (hadjT (Or.inl hlaf.1)) with haf | hfa | hlf
      · exact hcl a b (Or.inr (Or.inl ⟨hl, f, haf, hfbT⟩))
      · exact hvs ⟨hea, hfa⟩
      · exact hcl a f (Or.inl ⟨hlf, e, hea, hef, hnT hn₁ hn₂, hnT hn₂ hn₁⟩)
    · rcases isArrow_or_isArrow_or_isLine (hadjT (Or.inl hlaf.1)) with haf | hfa | hlf
      · exact hcl a b (Or.inr (Or.inl ⟨hl, f, haf, hfbT⟩))
      · exact hcl a e (Or.inl ⟨hle, f, hfa, hef.symm, hnT hn₂ hn₁, hnT hn₁ hn₂⟩)
      · exact hcl a b (Or.inr (Or.inr (Or.inl ⟨hl, e, f, hle, hebT, hlf, hfbT, hef,
          hnT hn₁ hn₂, hnT hn₂ hn₁⟩)))
  · have hefT := hPT e f hef
    have hfbT := hPT f b hfb
    rcases isArrow_or_isArrow_or_isLine (hadjT (Or.inl hlae.1)) with hae | hea | hle
    · rcases isArrow_or_isArrow_or_isLine (hadjT hadf) with haf | hfa | hlf
      · exact hcl a b (Or.inr (Or.inl ⟨hl, f, haf, hfbT⟩))
      · exact hG a (TransGen.head (hT.isCompelled a e hae).1 (TransGen.head
          (hT.isCompelled e f hefT).1 (TransGen.single (hT.isCompelled f a hfa).1)))
      · exact hcl a f (Or.inr (Or.inl ⟨hlf, e, hae, hefT⟩))
    · exact hcl a b (Or.inl ⟨hl, e, hea, heb, hnT hn₁ hn₂, hnT hn₂ hn₁⟩)
    · exact hcl a b (Or.inr (Or.inr (Or.inr ⟨hl, e, f, hle, hefT, hfbT, heb, hnT hn₁ hn₂,
        hnT hn₂ hn₁, hadjT hadf⟩)))

/-- Every directed edge of the closure of the v-structure pattern is directed in every partial
pattern for `G` to which no rule applies. -/
theorem isArrow_of_isArrow_closure (hG : G.IsAcyclic) (hT : T.IsPartialPattern G)
    (hcl : ∀ a b, ¬ MeekRule T a b) (h : (closure G).IsArrow a b) : T.IsArrow a b := by
  have key : ∀ n, ∀ x y, (Digraph.meekPass^[n] (vStructurePattern G)).IsArrow x y →
      T.IsArrow x y := by
    intro n
    induction n with
    | zero =>
      intro x y h
      obtain ⟨d, hd⟩ := exists_isVStructure_of_isArrow h
      exact hT.isArrow_of_isVStructure x y d hd
    | succ n ih =>
      intro x y h
      rw [Function.iterate_succ_apply'] at h
      rcases isArrow_or_meekRule_of_isArrow_meekPass h with h' | hr
      · exact ih x y h'
      · exact isArrow_of_meekRule_of_closed hT hG hcl (isPartialPattern_iterate hG n) ih hr
  exact key _ a b h

end Closure

/-! ### Completeness -/

/-- **Completeness of the orientation rules** (Meek 1995). In every partial pattern for a finite
acyclic graph `G` to which no rule applies, every compelled edge of `G` is directed. -/
theorem meekComplete (V : Type*) [Fintype V] [DecidableEq V] : MeekComplete V := by
  intro G P hG hP hcl u v hc
  refine isArrow_of_isArrow_closure hG hP hcl ?_
  rw [closure_eq_pattern hG, pattern_isArrow_iff hG]
  exact hc

section Pattern

variable [Finite V]

/-- **The pattern is the only closed partial pattern.** A partial pattern for a finite acyclic
graph `G` to which no rule applies is the pattern of `G`. -/
theorem IsPartialPattern.eq_pattern_of_closed (hP : P.IsPartialPattern G) (hG : G.IsAcyclic)
    (hcl : ∀ a b, ¬ MeekRule P a b) : P = pattern G := by
  have := Fintype.ofFinite V
  classical
  exact hP.eq_pattern hG (meekComplete V G P hG hP hcl)

/-- The pattern of a finite acyclic graph is a partial pattern for it. -/
theorem isPartialPattern_pattern (hG : G.IsAcyclic) : (pattern G).IsPartialPattern G := by
  have := Fintype.ofFinite V
  rw [← closure_eq_pattern hG]
  exact isPartialPattern_closure hG

/-- No rule applies to the pattern of a finite acyclic graph. -/
theorem forall_not_meekRule_pattern (hG : G.IsAcyclic) :
    ∀ a b, ¬ MeekRule (pattern G) a b := by
  have := Fintype.ofFinite V
  rw [← closure_eq_pattern hG]
  exact forall_not_meekRule_closure G

/-- **The pattern is characterized by the rules.** For a finite acyclic graph `G`, a partially
directed graph is a partial pattern for `G` to which no rule applies if and only if it is the
pattern of `G`. -/
theorem isPartialPattern_and_closed_iff (hG : G.IsAcyclic) :
    (P.IsPartialPattern G ∧ ∀ a b, ¬ MeekRule P a b) ↔ P = pattern G :=
  ⟨fun h => h.1.eq_pattern_of_closed hG h.2,
    fun h => h ▸ ⟨isPartialPattern_pattern hG, forall_not_meekRule_pattern hG⟩⟩

end Pattern

/-! ### The PC algorithm -/

section PC

variable [Fintype V] [DecidableEq V]

/-- **The PC algorithm returns the pattern.** Under a d-separation oracle of a finite acyclic
graph `G`, the output of the PC algorithm is the pattern of `G`. -/
theorem pcOutput_eq_pattern' {I : V → V → Finset V → Prop} [∀ x y S, Decidable (I x y S)]
    (hI : ∀ x y S, I x y S ↔ G.DSep {x} {y} ↑S) (hG : G.IsAcyclic) :
    toDigraph (pcOutput I) = pattern G :=
  pcOutput_eq_pattern hI hG (meekComplete V)

/-- **The PC algorithm with a Markov and faithful law.** Under the conditional independence
oracle of a law that is Markov and faithful to a finite acyclic graph `G`, the output of the PC
algorithm is the pattern of `G`. -/
theorem pcOutput_condIndep_eq_pattern' {α : V → Type*} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] {p : CausalInference.FiniteDist (∀ v, α v)}
    [∀ x y S, Decidable (p.CondIndep {x} {y} S)] (hG : G.IsAcyclic) (hM : G.GlobalMarkov p)
    (hF : p.IsFaithful G) :
    toDigraph (pcOutput fun x y S => p.CondIndep {x} {y} S) = pattern G :=
  pcOutput_condIndep_eq_pattern hG hM hF (meekComplete V)

/-- **The PC algorithm on data from a faithful law returns the pattern.** Every finite acyclic
graph `G` has a law over binary variables that factorizes according to `G` and with whose
conditional independence oracle the PC algorithm returns the pattern of `G`. -/
theorem exists_law_pcOutput_eq_pattern [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    ∃ p : CausalInference.FiniteDist (V → Bool), G.Factorizes p ∧ p.IsFaithful G ∧
      ∀ _ : ∀ x y S, Decidable (p.CondIndep {x} {y} S),
        toDigraph (pcOutput fun x y S => p.CondIndep {x} {y} S) = pattern G := by
  obtain ⟨p, hp, hF⟩ := G.exists_factorizes_isFaithful hG
  exact ⟨p, hp, hF, fun _ => pcOutput_condIndep_eq_pattern' hG (hp.globalMarkov hG) hF⟩

end PC

end Digraph
