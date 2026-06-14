import Taut.Eligible

/-!
# Degree-3 vertices and the connected-sum cut (M24a, architect: codex 019ec44f, Q1)

A degree-3 vertex `v` of a 2-sphere `σ` (its link is a triangle) gives a non-face
triangle `γ = linkVerts σ v` along which `separates` cuts σ into a tetrahedral cap
(the star of `v`) and a strictly smaller sphere — the paper's connected-sum
reduction. This file establishes the non-face datum `separates` consumes:

* `linkGraph_complete_of_linkVerts_card_three` — a degree-3 link is a triangle;
* `linkVerts_powersetCard_two_subset_edgesOf` — its three edges are edges of σ;
* `linkVerts_not_mem_of_card_three_of_four_lt_verts` — the link triangle is a
  *non-face* once `σ` has more than four vertices (else σ would be the whole
  tetrahedron). The argument: the four faces of the tetrahedron on `insert v γ`
  all lie in σ, they are dual-closed (closedness saturates every tetra edge), and
  σ is dual-connected, so σ *is* that tetrahedron — contradicting `4 < #verts`.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- Reachability stays inside a set closed under neighbours — any vertex type
(the `Set`-valued generalisation of `walk_mem_of_adj_closed`, used on the dual
graph, whose vertices are faces). -/
lemma walk_mem_of_adj_closed' {W : Type*} {G : SimpleGraph W} {S : Set W}
    (hclosed : ∀ u ∈ S, ∀ z, G.Adj u z → z ∈ S) {a x : W} (w : G.Walk a x) :
    a ∈ S → x ∈ S := by
  induction w with
  | nil => exact id
  | cons hadj _ ih => exact fun ha => ih (hclosed _ ha _ hadj)

/-- **A degree-3 link is a triangle.** With exactly three link vertices, any two
distinct ones are adjacent in the link (2-regularity forces it). -/
lemma linkGraph_complete_of_linkVerts_card_three {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) {v x y : V} (hx : x ∈ linkVerts σ v) (hy : y ∈ linkVerts σ v)
    (hxy : x ≠ y) (h3 : (linkVerts σ v).card = 3) : (linkGraph σ v).Adj x y := by
  have hreg := link_two_regular hσ hx
  have hsub : (linkVerts σ v).filter (fun w => (linkGraph σ v).Adj x w)
      ⊆ (linkVerts σ v).erase x := fun w hw => by
    rw [Finset.mem_filter] at hw; exact Finset.mem_erase.mpr ⟨hw.2.ne', hw.1⟩
  have hcardE : ((linkVerts σ v).erase x).card = 2 := by rw [Finset.card_erase_of_mem hx, h3]
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq (hcardE.trans hreg.symm))
  have hymem : y ∈ (linkVerts σ v).filter (fun w => (linkGraph σ v).Adj x w) := by
    rw [heq]; exact Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  exact (Finset.mem_filter.mp hymem).2

/-- **A degree-3 link spans edges of σ:** each pair of its three vertices is an
edge of σ (completed by `v` to a face). -/
lemma linkVerts_powersetCard_two_subset_edgesOf {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) {v : V} (h3 : (linkVerts σ v).card = 3) :
    (linkVerts σ v).powersetCard 2 ⊆ edgesOf σ := by
  intro e he
  rw [Finset.mem_powersetCard] at he
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he.2
  obtain ⟨_, hf⟩ := linkGraph_complete_of_linkVerts_card_three hσ
    (he.1 (Finset.mem_insert_self x {y}))
    (he.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))) hxy h3
  refine mem_edgesOf.mpr ⟨{v, x, y}, hf, ?_, he.2⟩
  intro u hu
  rw [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- **The degree-3 link triangle is a non-face** once `σ` has more than four
vertices. If it were a face, the four faces of the tetrahedron on `insert v γ`
would all lie in σ; closedness saturates every tetra edge with exactly its two
tetra faces, so that tetrahedron is dual-closed; σ is dual-connected, so σ is the
whole tetrahedron — only four vertices, contradiction. -/
lemma linkVerts_not_mem_of_card_three_of_four_lt_verts {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) {v : V} (hv : v ∈ vertsOf σ) (h3 : (linkVerts σ v).card = 3)
    (hbig : 4 < (vertsOf σ).card) : linkVerts σ v ∉ σ := by
  classical
  intro hγσ
  set T : Finset V := insert v (linkVerts σ v) with hTdef
  have hvγ : v ∉ linkVerts σ v := by rw [linkVerts]; exact Finset.notMem_erase _ _
  have hTcard : T.card = 4 := by rw [hTdef, Finset.card_insert_of_notMem hvγ, h3]
  -- the four tetrahedron faces lie in σ
  have htetra : ∀ f ∈ T.powersetCard 3, f ∈ σ := by
    intro f hf
    obtain ⟨w, hwT, rfl⟩ := exists_erase_eq_of_mem_tetFaces hTcard hf
    by_cases hwv : w = v
    · subst hwv; rw [hTdef, Finset.erase_insert hvγ]; exact hγσ
    · have hwγ : w ∈ linkVerts σ v := by
        rw [hTdef, Finset.mem_insert] at hwT; exact hwT.resolve_left hwv
      have hcard2 : ((linkVerts σ v).erase w).card = 2 := by
        rw [Finset.card_erase_of_mem hwγ, h3]
      obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.mp hcard2
      have hxγ : x ∈ linkVerts σ v :=
        Finset.mem_of_mem_erase (hxyeq ▸ Finset.mem_insert_self x {y})
      have hyγ : y ∈ linkVerts σ v :=
        Finset.mem_of_mem_erase (hxyeq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
      obtain ⟨_, hf'⟩ := linkGraph_complete_of_linkVerts_card_three hσ hxγ hyγ hxy h3
      have heq : T.erase w = ({v, x, y} : Finset V) := by
        rw [hTdef, Finset.erase_insert_of_ne (Ne.symm hwv), hxyeq]
      rw [heq]; exact hf'
  -- the tetra faces (as a set of σ-faces) are dual-closed
  set S : Set σ := {f : σ | (f : Finset V) ⊆ T} with hSdef
  have hclosed : ∀ u ∈ S, ∀ z, (dualGraph σ).Adj u z → z ∈ S := by
    rintro u huT z ⟨_, e, he, heu, hez⟩
    have huT' : (u : Finset V) ⊆ T := huT
    have heT : e ⊆ T := heu.trans huT'
    have he2 : e.card = 2 := card_of_mem_edgesOf he
    have hTe : (T \ e).card = 2 := by rw [Finset.card_sdiff_of_subset heT, hTcard, he2]
    obtain ⟨w₁, w₂, hw12, hwe⟩ := Finset.card_eq_two.mp hTe
    have hw1 : w₁ ∈ T \ e := hwe ▸ Finset.mem_insert_self w₁ {w₂}
    have hw2 : w₂ ∈ T \ e := hwe ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂)
    have hw1e : w₁ ∉ e := (Finset.mem_sdiff.mp hw1).2
    have hw2e : w₂ ∉ e := (Finset.mem_sdiff.mp hw2).2
    have hf1T : insert w₁ e ⊆ T := Finset.insert_subset (Finset.mem_sdiff.mp hw1).1 heT
    have hf2T : insert w₂ e ⊆ T := Finset.insert_subset (Finset.mem_sdiff.mp hw2).1 heT
    have hf1σ : insert w₁ e ∈ σ := htetra _
      (Finset.mem_powersetCard.mpr ⟨hf1T, by rw [Finset.card_insert_of_notMem hw1e, he2]⟩)
    have hf2σ : insert w₂ e ∈ σ := htetra _
      (Finset.mem_powersetCard.mpr ⟨hf2T, by rw [Finset.card_insert_of_notMem hw2e, he2]⟩)
    have hins_ne : insert w₁ e ≠ insert w₂ e := by
      intro hc
      have hm : w₁ ∈ insert w₂ e := hc ▸ Finset.mem_insert_self w₁ e
      rw [Finset.mem_insert] at hm
      exact hm.elim (fun h => hw12 h) (fun h => hw1e h)
    have hfilter2 : (σ.filter (fun h => e ⊆ h)).card = 2 := hσ.closed e he
    have hpair_sub : ({insert w₁ e, insert w₂ e} : Finset (Finset V))
        ⊆ σ.filter (fun h => e ⊆ h) := by
      intro h hh; rw [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hf1σ, Finset.subset_insert _ _⟩
      · exact Finset.mem_filter.mpr ⟨hf2σ, Finset.subset_insert _ _⟩
    have hfeq : σ.filter (fun h => e ⊆ h) = {insert w₁ e, insert w₂ e} :=
      (Finset.eq_of_subset_of_card_le hpair_sub
        (le_of_eq (hfilter2.trans (Finset.card_pair hins_ne).symm))).symm
    have hmemg : (z : Finset V) ∈ σ.filter (fun h => e ⊆ h) :=
      Finset.mem_filter.mpr ⟨z.2, hez⟩
    rw [hfeq, Finset.mem_insert, Finset.mem_singleton] at hmemg
    show (z : Finset V) ⊆ T
    rcases hmemg with h | h
    · rw [h]; exact hf1T
    · rw [h]; exact hf2T
  -- dual-connectivity traps every face inside the tetrahedron
  have hσsub : ∀ g ∈ σ, (g : Finset V) ⊆ T := by
    intro g hg
    have hf0S : (⟨linkVerts σ v, hγσ⟩ : σ) ∈ S := by
      show (linkVerts σ v : Finset V) ⊆ T
      rw [hTdef]; exact Finset.subset_insert v _
    obtain ⟨w⟩ := dualGraph_preconnected hσ.toClosedSurface ⟨linkVerts σ v, hγσ⟩ ⟨g, hg⟩
    exact walk_mem_of_adj_closed' hclosed w hf0S
  -- so vertsOf σ = T, of card four — contradiction
  have hverts : vertsOf σ ⊆ T := by
    intro w hw
    obtain ⟨g, hg, hwg⟩ := mem_vertsOf.mp hw
    exact hσsub g hg hwg
  have hcard_le : (vertsOf σ).card ≤ 4 := hTcard ▸ Finset.card_le_card hverts
  omega

/-- **The degree-3 cut datum** (M24a): from a degree-3 vertex of a 2-sphere on more
than four vertices, the link triangle `γ` is a non-face whose edges lie in σ — the
exact hypotheses `separates` consumes. -/
lemma degree3_link_triangle_cut_data {σ : Finset (Finset V)} (hσ : IsSphere2 σ)
    {v : V} (hv : v ∈ vertsOf σ) (h3 : (linkVerts σ v).card = 3)
    (hbig : 4 < (vertsOf σ).card) :
    (linkVerts σ v).card = 3 ∧ (linkVerts σ v).powersetCard 2 ⊆ edgesOf σ ∧
      linkVerts σ v ∉ σ :=
  ⟨h3, linkVerts_powersetCard_two_subset_edgesOf hσ h3,
    linkVerts_not_mem_of_card_three_of_four_lt_verts hσ hv h3 hbig⟩

end Taut
