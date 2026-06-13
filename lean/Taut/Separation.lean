import Taut.Homology2

/-!
# The separation theorem

H₁ = 0 (`range_bd2_eq_ker_bd1`) turned into the geometric cut: a non-face
triangle γ in a combinatorial 2-sphere σ partitions the faces into two sides,
each of which caps with γ to a sphere.

The γ-edge 1-chain is a cycle (each vertex of γ lies in two of its edges), so by
H₁ = 0 it bounds a face-set `W`; `σ₁ := W.support`, `σ₂ := σ \ σ₁`. The defining
identity `∂₂W = vγ` says: every edge has an *even* number of `σ₁`-faces unless it
is a γ-edge, where the count is *odd* (= 1). With σ's `closed` (≤ 2 faces per
edge) this pins the cut and drives the sphere-hood of the pieces.
-/

namespace Taut

open Module Finset

variable {V : Type*} [LinearOrder V]

/-- The 1-chain supported on the edges of `γ`. -/
def gammaChain (σ : Finset (Finset V)) (γ : Finset V) : C1 σ :=
  fun e => if (e : Finset V) ⊆ γ then 1 else 0

/-- The γ-edge 1-chain is a cycle: every vertex lies in an even number of γ's
edges (two, if on γ; none otherwise). -/
lemma bd1_gammaChain {σ : Finset (Finset V)} {γ : Finset V} (hγ3 : γ.card = 3)
    (hγe : γ.powersetCard 2 ⊆ edgesOf σ) : bd1 σ (gammaChain σ γ) = 0 := by
  classical
  funext x
  show bd1 σ (gammaChain σ γ) x = 0
  rw [bd1_apply]
  have hstep : ∀ e : edgesOf σ,
      (if (x : V) ∈ (e : Finset V) then (1 : ZMod 2) else 0) * gammaChain σ γ e
        = (if (x : V) ∈ (e : Finset V) ∧ (e : Finset V) ⊆ γ then (1 : ZMod 2) else 0) := by
    intro e
    simp only [gammaChain]
    by_cases h1 : (x : V) ∈ (e : Finset V) <;> by_cases h2 : (e : Finset V) ⊆ γ <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl (fun e _ => hstep e),
    Finset.sum_coe_sort (edgesOf σ)
      (fun e => if (x : V) ∈ e ∧ e ⊆ γ then (1 : ZMod 2) else 0),
    Finset.sum_boole, card_edges_through_vertex hγe hγ3 x]
  split <;> decide

/-- **The cut exists.** A non-face triangle's edge-cycle bounds a face-set `W`
(this is exactly where H₁ = 0 is spent). -/
theorem exists_cut {σ : Finset (Finset V)} (h : IsSphere2 σ) {γ : Finset V}
    (hγ3 : γ.card = 3) (hγe : γ.powersetCard 2 ⊆ edgesOf σ) :
    ∃ W : C2 σ, bd2 σ W = gammaChain σ γ := by
  have hcyc : gammaChain σ γ ∈ LinearMap.ker (bd1 σ) :=
    LinearMap.mem_ker.mpr (bd1_gammaChain hγ3 hγe)
  rw [← range_bd2_eq_ker_bd1 h] at hcyc
  exact LinearMap.mem_range.mp hcyc

/-! ## The two sides -/

/-- One side of the cut: the faces on which the bounding chain `W` is `1`. -/
noncomputable def cutSet (σ : Finset (Finset V)) (W : C2 σ) : Finset (Finset V) :=
  (Finset.univ.filter (fun f : σ => W f = 1)).image Subtype.val

lemma mem_cutSet {σ : Finset (Finset V)} {W : C2 σ} {g : Finset V} :
    g ∈ cutSet σ W ↔ ∃ hg : g ∈ σ, W ⟨g, hg⟩ = 1 := by
  simp only [cutSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨g', hg'⟩, hW, rfl⟩; exact ⟨hg', hW⟩
  · rintro ⟨hg, hW⟩; exact ⟨⟨g, hg⟩, hW, rfl⟩

lemma cutSet_subset {σ : Finset (Finset V)} {W : C2 σ} : cutSet σ W ⊆ σ := by
  intro g hg; obtain ⟨hg', _⟩ := mem_cutSet.mp hg; exact hg'

/-- The defining parity of the cut: across each edge, the two faces' `W`-values
sum to `1` iff the edge lies on `γ`. -/
lemma edge_cut_parity {σ : Finset (Finset V)} {W : C2 σ} {γ : Finset V}
    (hW : bd2 σ W = gammaChain σ γ) {e : Finset V} (he : e ∈ edgesOf σ)
    {f₁ f₂ : Finset V} (h1 : f₁ ∈ σ) (h2 : f₂ ∈ σ) (hne : f₁ ≠ f₂)
    (he1 : e ⊆ f₁) (he2 : e ⊆ f₂) (huniq : ∀ f ∈ σ, e ⊆ f → f = f₁ ∨ f = f₂) :
    W ⟨f₁, h1⟩ + W ⟨f₂, h2⟩ = if e ⊆ γ then 1 else 0 := by
  have hb := bd2_at_edge W he h1 h2 hne he1 he2 huniq
  rw [hW] at hb
  rw [← hb]
  simp only [gammaChain]

/-! ## The pieces are closed pseudomanifolds -/

variable {σ : Finset (Finset V)} {W : C2 σ} {γ : Finset V}

/-- Edges of a capped side are edges of σ. -/
lemma edgesOf_cut_subset (hγe : γ.powersetCard 2 ⊆ edgesOf σ) :
    edgesOf (insert γ (cutSet σ W)) ⊆ edgesOf σ := by
  intro e he
  obtain ⟨f, hf, hef, hc⟩ := mem_edgesOf.mp he
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact hγe (Finset.mem_powersetCard.mpr ⟨hef, hc⟩)
  · exact mem_edgesOf.mpr ⟨f, cutSet_subset hf, hef, hc⟩

/-- The edge-degree in a capped side splits into the γ-contribution and the
cut-faces through the edge. -/
lemma edgeDeg_cut (hγσ : γ ∉ σ) (e : Finset V) :
    edgeDeg (insert γ (cutSet σ W)) e
      = (if e ⊆ γ then 1 else 0) + ((cutSet σ W).filter (fun f => e ⊆ f)).card := by
  rw [edgeDeg, Finset.filter_insert]
  by_cases heγ : e ⊆ γ
  · rw [if_pos heγ, Finset.card_insert_of_notMem
      (fun hγf => hγσ (cutSet_subset (Finset.mem_of_mem_filter _ hγf))), if_pos heγ, add_comm]
  · rw [if_neg heγ, if_neg heγ, zero_add]

/-- **`closed` for the pieces.** Every edge of a capped side lies in exactly two
of its faces, by the cut parity. -/
lemma closed_cut (h : IsSphere2 σ) (hγ3 : γ.card = 3)
    (hγe : γ.powersetCard 2 ⊆ edgesOf σ) (hγσ : γ ∉ σ) (hW : bd2 σ W = gammaChain σ γ) :
    ∀ e ∈ edgesOf (insert γ (cutSet σ W)),
      edgeDeg (insert γ (cutSet σ W)) e = 2 := by
  classical
  intro e he
  have heσ : e ∈ edgesOf σ := edgesOf_cut_subset hγe he
  obtain ⟨f₁, h1, f₂, h2, hne, he1, he2, huniq⟩ := exists_two_faces h heσ
  -- the cut-faces through e are exactly those of {f₁,f₂} in the cut set
  have hfilter : (cutSet σ W).filter (fun f => e ⊆ f)
      = ({f₁, f₂} : Finset (Finset V)).filter (fun f => f ∈ cutSet σ W) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hg, heg⟩; exact ⟨huniq g (cutSet_subset hg) heg, hg⟩
    · rintro ⟨hg12, hgc⟩; exact ⟨hgc, by rcases hg12 with rfl | rfl; exacts [he1, he2]⟩
  have hpar := edge_cut_parity hW heσ h1 h2 hne he1 he2 huniq
  have hmem1 : f₁ ∈ cutSet σ W ↔ W ⟨f₁, h1⟩ = 1 := by
    rw [mem_cutSet]; exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨h1, hh⟩⟩
  have hmem2 : f₂ ∈ cutSet σ W ↔ W ⟨f₂, h2⟩ = 1 := by
    rw [mem_cutSet]; exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨h2, hh⟩⟩
  rw [edgeDeg_cut hγσ, hfilter, Finset.card_filter, Finset.sum_pair hne]
  simp only [hmem1, hmem2]
  have hzo : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  by_cases heγ : e ⊆ γ
  · -- parity = 1: exactly one face in the cut
    rw [if_pos heγ] at hpar ⊢
    obtain h1' | h1' := hzo (W ⟨f₁, h1⟩) <;> obtain h2' | h2' := hzo (W ⟨f₂, h2⟩) <;>
      rw [h1', h2'] at hpar ⊢ <;> simp_all
  · -- parity = 0: zero or two; `e ∈ edgesOf` of the piece rules out zero
    rw [if_neg heγ] at hpar ⊢
    have hone : W ⟨f₁, h1⟩ = 1 ∨ W ⟨f₂, h2⟩ = 1 := by
      obtain ⟨g, hg, heg, _⟩ := mem_edgesOf.mp he
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact absurd heg heγ
      · rcases huniq g (cutSet_subset hg) heg with rfl | rfl
        · exact Or.inl (hmem1.mp hg)
        · exact Or.inr (hmem2.mp hg)
    obtain h1' | h1' := hzo (W ⟨f₁, h1⟩) <;> obtain h2' | h2' := hzo (W ⟨f₂, h2⟩) <;>
      rw [h1', h2'] at hpar hone ⊢ <;> simp_all

end Taut
