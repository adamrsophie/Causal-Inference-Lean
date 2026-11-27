/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Acyclic

/-!
# Simplicial vertices of graphs with an orientation without v-structures

Let `L` be a symmetric relation on a finite set `S` of vertices (an undirected graph), and let an
acyclic graph `G` orient every edge of `L` in such a way that no two nonadjacent vertices of `S`
have a common child in `S` along edges of `L`. Then `L` restricted to `S` is complete, or it has
two nonadjacent simplicial vertices (`Digraph.complete_or_exists_two_isSimplicialIn`). This is
the form of the theorem of Dirac (1961) on chordal graphs used for the completeness of the
orientation rules. The proof removes a sink of `G` in `S`, which is simplicial, and uses
induction. Consequently, for every vertex `v`, some simplicial vertex differs from `v` as soon
as `S` has a vertex other than `v` (`Digraph.exists_isSimplicialIn`).
-/

@[expose] public section

namespace Digraph

open Finset

variable {V : Type*}

/-- The vertex `x` is simplicial in `S` for the relation `L`: any two distinct neighbors of `x`
in `S` are neighbors. -/
def IsSimplicialIn (L : V → V → Prop) (S : Finset V) (x : V) : Prop :=
  ∀ y ∈ S, ∀ z ∈ S, L x y → L x z → y ≠ z → L y z

variable [Finite V] {L : V → V → Prop}

/-- **Two nonadjacent simplicial vertices.** If an acyclic graph `G` orients the edges of a
symmetric relation `L` on a finite set `S` without v-structures inside `S`, then `L` is complete
on `S`, or `S` has two nonadjacent simplicial vertices. -/
theorem complete_or_exists_two_isSimplicialIn (hsymm : ∀ a b, L a b → L b a) {G : Digraph V}
    (hG : G.IsAcyclic) (S : Finset V)
    (hor : ∀ a ∈ S, ∀ b ∈ S, L a b → G.Adj a b ∨ G.Adj b a)
    (hvs : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, L a c → L b c → G.Adj a c → G.Adj b c → a ≠ b →
      L a b) :
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → L a b) ∨
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ¬ L x y ∧ IsSimplicialIn L S x ∧ IsSimplicialIn L S y := by
  classical
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  revert hor hvs
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hor hvs
  by_cases hc : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → L a b
  · exact Or.inl hc
  right
  push Not at hc
  obtain ⟨a, ha, b, hb, hab, hnab⟩ := hc
  obtain ⟨s, hs, hmax⟩ := S.exists_max_image f ⟨a, ha⟩
  have hsink : ∀ y ∈ S, ¬ G.Adj s y := fun y hy h => absurd (hmax y hy) (not_le.2 (hf h))
  have hsimp : IsSimplicialIn L S s := by
    intro y hy z hz hsy hsz hyz
    exact hvs y hy z hz s hs (hsymm _ _ hsy) (hsymm _ _ hsz)
      ((hor s hs y hy hsy).resolve_left (hsink y hy))
      ((hor s hs z hz hsz).resolve_left (hsink z hz)) hyz
  have hmem : ∀ {y}, y ∈ S → y ≠ s → y ∈ S.erase s := fun hy hne => mem_erase.2 ⟨hne, hy⟩
  -- a vertex of `S.erase s` not adjacent to `s` and simplicial there is simplicial in `S`
  have hlift : ∀ x ∈ S.erase s, ¬ L s x → (∀ y ∈ S.erase s, ∀ z ∈ S.erase s, L x y → L x z →
      y ≠ z → L y z) → IsSimplicialIn L S x := by
    intro x _ hsx hx y hy z hz hxy hxz hyz
    have hys : y ≠ s := by
      rintro rfl
      exact hsx (hsymm _ _ hxy)
    have hzs : z ≠ s := by
      rintro rfl
      exact hsx (hsymm _ _ hxz)
    exact hx y (hmem hy hys) z (hmem hz hzs) hxy hxz hyz
  rcases ih (S.erase s) (erase_ssubset hs)
      (fun a ha b hb => hor a (mem_of_mem_erase ha) b (mem_of_mem_erase hb))
      (fun a ha b hb c hc => hvs a (mem_of_mem_erase ha) b (mem_of_mem_erase hb) c
        (mem_of_mem_erase hc)) with hcomp | ⟨x₁, hx₁, x₂, hx₂, hne, hn, hs₁, hs₂⟩
  · -- the rest is complete: a vertex not adjacent to `s` is simplicial
    obtain ⟨w, hw, hws, hsw⟩ : ∃ w ∈ S, w ≠ s ∧ ¬ L s w := by
      by_cases has : a = s
      · subst has
        exact ⟨b, hb, hab.symm, hnab⟩
      · by_cases hbs : b = s
        · subst hbs
          exact ⟨a, ha, has, fun h => hnab (hsymm _ _ h)⟩
        · exact absurd (hcomp a (hmem ha has) b (hmem hb hbs) hab) hnab
    refine ⟨s, hs, w, hw, hws.symm, hsw, hsimp, hlift w (hmem hw hws) hsw ?_⟩
    intro y hy z hz _ _ hyz
    exact hcomp y hy z hz hyz
  · have hx : ¬ L s x₁ ∨ ¬ L s x₂ := by
      by_contra h
      push Not at h
      exact hn (hsimp x₁ (mem_of_mem_erase hx₁) x₂ (mem_of_mem_erase hx₂) h.1 h.2 hne)
    rcases hx with h | h
    · exact ⟨s, hs, x₁, mem_of_mem_erase hx₁, (ne_of_mem_erase hx₁).symm, h, hsimp,
        hlift x₁ hx₁ h hs₁⟩
    · exact ⟨s, hs, x₂, mem_of_mem_erase hx₂, (ne_of_mem_erase hx₂).symm, h, hsimp,
        hlift x₂ hx₂ h hs₂⟩

/-- **A simplicial vertex other than a given one.** Under the hypotheses of
`Digraph.complete_or_exists_two_isSimplicialIn`, a nonempty `S` has a simplicial vertex `x`, and
`x` differs from a given vertex `v` whenever `S` has some vertex other than `v`. -/
theorem exists_isSimplicialIn (hsymm : ∀ a b, L a b → L b a) {G : Digraph V}
    (hG : G.IsAcyclic) (S : Finset V)
    (hor : ∀ a ∈ S, ∀ b ∈ S, L a b → G.Adj a b ∨ G.Adj b a)
    (hvs : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, L a c → L b c → G.Adj a c → G.Adj b c → a ≠ b →
      L a b)
    (hS : S.Nonempty) (v : V) :
    ∃ x ∈ S, IsSimplicialIn L S x ∧ ∀ u ∈ S, u ≠ v → x ≠ v := by
  rcases complete_or_exists_two_isSimplicialIn hsymm hG S hor hvs with hc | ⟨x, hx, y, hy, hxy,
      -, hsx, hsy⟩
  · have hsimp : ∀ x, IsSimplicialIn L S x := fun _ y hy z hz _ _ hyz => hc y hy z hz hyz
    by_cases h : ∃ u ∈ S, u ≠ v
    · obtain ⟨u, hu, huv⟩ := h
      exact ⟨u, hu, hsimp u, fun _ _ _ => huv⟩
    · obtain ⟨w, hw⟩ := hS
      exact ⟨w, hw, hsimp w, fun u hu huv => absurd ⟨u, hu, huv⟩ h⟩
  · by_cases hxv : x = v
    · subst hxv
      exact ⟨y, hy, hsy, fun _ _ _ => Ne.symm hxy⟩
    · exact ⟨x, hx, hsx, fun _ _ _ => hxv⟩

end Digraph
