import Taut.Pseudomanifold
import Taut.Eligible

/-!
# Bridging the combinatorial stickerball invariants to the chain

`faceCount`/`IsPseudomanifold` are combinatorial (set counts on the support),
while the taut-filling hypotheses speak about the integral boundary `bdry M`.
This file connects them: for a simplicial chain with pure support, a boundary
triangle (`bdry M f = ±1`) of a pseudomanifold support lies in **exactly one**
tet.  This is the "boundary face in one tet" fact the triangle rule-out needs.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- A triangle contained in a tetrahedron is one of its faces, so `bdryGen` is
nonzero there. -/
lemma bdryGen_ne_zero_of_subset {t f : Finset V} (ht : t.card = 4) (hf : f.card = 3)
    (h : f ⊆ t) : bdryGen t f ≠ 0 := by
  have hcard : (t \ f).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h, ht, hf]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
  have hym : y ∈ t \ f := by rw [hy]; exact Finset.mem_singleton.mpr rfl
  have hyt : y ∈ t := (Finset.mem_sdiff.mp hym).1
  have hyf : y ∉ f := (Finset.mem_sdiff.mp hym).2
  have hfe : f = t.erase y := by
    refine Finset.eq_of_subset_of_card_le (fun z hz =>
      Finset.mem_erase.mpr ⟨fun hzy => hyf (hzy ▸ hz), h hz⟩) ?_
    rw [Finset.card_erase_of_mem hyt, ht, hf]
  rw [hfe, bdryGen_apply_erase_of_mem hyt]
  intro h0
  have hss := sgn_mul_self y t
  rw [h0, mul_zero] at hss
  exact absurd hss (by norm_num)

/-- The boundary at a triangle is the signed sum over the tets having it as a
face (the rest of the support contributes nothing). -/
lemma bdry_eq_sum_facets {M : Chain V} {f : Finset V} :
    bdry M f = ∑ t ∈ M.support.filter (fun t => f ⊆ t), M t * bdryGen t f := by
  rw [bdry_apply_eq_sum]
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun t ht htnf => ?_)).symm
  rw [Finset.mem_filter, not_and] at htnf
  have hnsub : ¬ f ⊆ t := htnf ht
  have hg : bdryGen t f = 0 := by
    by_contra h0
    obtain ⟨w, _, hfe⟩ := exists_facet_of_bdryGen_ne_zero h0
    exact hnsub (by rw [hfe]; exact Finset.erase_subset _ _)
  rw [hg, mul_zero]

/-- **Boundary triangle of a pseudomanifold lies in exactly one tet.** For a
simplicial chain with pure support, a triangle whose boundary coefficient is `±1`
sits in exactly one tet of the support: at most two by `IsPseudomanifold`, and
two would cancel to `0` or sum to `±2`, never the boundary value `±1`. -/
lemma faceCount_eq_one_of_boundary {M : Chain V}
    (hS : SimplicialChain M) (hPure : ∀ t ∈ M.support, t.card = 4)
    (hPM : IsPseudomanifold M.support) {f : Finset V} (hf : f.card = 3)
    (hb : bdry M f = 1 ∨ bdry M f = -1) :
    faceCount M.support f = 1 := by
  have hle : faceCount M.support f ≤ 2 := hPM f hf
  have hsum := bdry_eq_sum_facets (M := M) (f := f)
  have hterm : ∀ t ∈ M.support.filter (fun t => f ⊆ t),
      M t * bdryGen t f = 1 ∨ M t * bdryGen t f = -1 := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htM, htf⟩ := ht
    have hMt : M t = 1 ∨ M t = -1 := by
      rcases hS t with h | h | h
      · exact Or.inr h
      · exact absurd h (Finsupp.mem_support_iff.mp htM)
      · exact Or.inl h
    have hgen : bdryGen t f = 1 ∨ bdryGen t f = -1 := by
      rcases bdryGen_apply_mem_pm t f with h | h | h
      · exact Or.inr h
      · exact absurd h (bdryGen_ne_zero_of_subset (hPure t htM) hf htf)
      · exact Or.inl h
    rcases hMt with h1 | h1 <;> rcases hgen with h2 | h2 <;> rw [h1, h2] <;> decide
  have hge : 1 ≤ faceCount M.support f := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    unfold faceCount at h0
    rw [Finset.card_eq_zero] at h0
    rw [h0, Finset.sum_empty] at hsum
    rcases hb with h | h <;> rw [h] at hsum <;> omega
  have hne2 : faceCount M.support f ≠ 2 := by
    intro h2
    unfold faceCount at h2
    obtain ⟨t1, t2, hne, heq⟩ := Finset.card_eq_two.mp h2
    rw [heq, Finset.sum_pair hne] at hsum
    have e1 := hterm t1 (by rw [heq]; exact Finset.mem_insert_self _ _)
    have e2 := hterm t2 (by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
    rcases hb with hb | hb <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
      rw [hb, e1, e2] at hsum <;> omega
  omega

end Taut
