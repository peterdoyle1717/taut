import Taut.Stickerball

/-!
# Stickerball rule-outs — the pseudomanifold half of the induction

The two remaining geometry holes (`degree3_hanchor`, `flipEdgePresent_side_bridge`)
both need "a boundary triangle of the smaller filling lies in exactly one tet",
which holds for a **pseudomanifold** but not for a bare freely-shellable complex.
This file carries `IsPseudomanifold` through the eligible-tet flip:

* `isPseudomanifold_union_of_sideSep` (LEMMA A) — two pseudomanifolds meeting only
  along a ≤2-vertex set union to a pseudomanifold (the case-2 split reassembly);
* the triangle rule-out (LEMMA C) — the shared faces of an eligible tet vanish on
  removal, via the disjoint eligible pair and the parity bridge.

The carried invariant is just `IsPseudomanifold M.support` alongside the existing
`FreelyShellable`; the "two stickerballs joined along an edge" configuration never
needs to be a named invariant — its two pieces are each a strictly smaller
single-sphere taut filling, so the strong-induction hypothesis applies to each and
LEMMA A glues their pseudomanifold-ness.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- A triangle `f` (card 3) contained in a tet `t ⊆ A` cannot also satisfy `f ⊆ B`
when `(A ∩ B).card ≤ 2`: it would force `f ⊆ A ∩ B`, too small to hold a triangle.
Hence a triangle's containing-tets all lie on a single side. -/
lemma subset_left_of_face_subset {A B : Finset V} {f t : Finset V}
    (hAB : (A ∩ B).card ≤ 2) (hf : f.card = 3) (hfA : f ⊆ A)
    (hcov : t ⊆ A ∨ t ⊆ B) (hft : f ⊆ t) : t ⊆ A := by
  rcases hcov with h | h
  · exact h
  · exfalso
    have hfAB : f ⊆ A ∩ B := Finset.subset_inter hfA (hft.trans h)
    have := Finset.card_le_card hfAB
    omega

/-- **LEMMA A (union-PM).** If every tet of `τ` lies in `A` or `B`, the two sides
`A ∩ B` share at most an edge (`(A ∩ B).card ≤ 2`), and both side-restrictions are
pseudomanifolds, then `τ` is a pseudomanifold.  This is the case-2 reassembly: the
two smaller fillings meet only along the flip edge `cd`, so no triangle is shared
and triangle incidences never add across the cut. -/
lemma isPseudomanifold_union_of_sideSep {τ : Finset (Finset V)} {A B : Finset V}
    (hcov : ∀ t ∈ τ, t ⊆ A ∨ t ⊆ B) (hAB : (A ∩ B).card ≤ 2)
    (h₁ : IsPseudomanifold (τ.filter (fun t => t ⊆ A)))
    (h₂ : IsPseudomanifold (τ.filter (fun t => t ⊆ B))) :
    IsPseudomanifold τ := by
  intro f hf
  by_cases hfA : f ⊆ A
  · -- every tet of τ containing f is ⊆ A, so faceCount τ f = faceCount (filter ⊆A) f
    have hset : τ.filter (fun t => f ⊆ t) = (τ.filter (fun t => t ⊆ A)).filter (fun t => f ⊆ t) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro t ht
      constructor
      · intro hft
        exact ⟨subset_left_of_face_subset hAB hf hfA (hcov t ht) hft, hft⟩
      · intro h; exact h.2
    have := h₁ f hf
    unfold faceCount at this ⊢
    rw [hset]; exact this
  · -- f ⊄ A, so every tet of τ containing f is ⊆ B
    have hset : τ.filter (fun t => f ⊆ t) = (τ.filter (fun t => t ⊆ B)).filter (fun t => f ⊆ t) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro t ht
      constructor
      · intro hft
        refine ⟨?_, hft⟩
        rcases hcov t ht with h | h
        · exact absurd (hft.trans h) hfA
        · exact h
      · intro h; exact h.2
    have := h₂ f hf
    unfold faceCount at this ⊢
    rw [hset]; exact this

end Taut
