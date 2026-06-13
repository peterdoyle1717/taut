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
  obtain ⟨f₁, h1, f₂, h2, hne, he1, he2, huniq⟩ := exists_two_faces h.toClosedSurface heσ
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

/-! ## The pieces are connected -/

/-- `∂₁c` at a vertex `x` lying on exactly the two support-edges `e₁, e₂` equals
`c e₁ + c e₂`. -/
lemma bd1_eval_two {σ : Finset (Finset V)} {c : C1 σ} {x : V} (hx : x ∈ vertsOf σ)
    {e₁ e₂ : edgesOf σ} (hne : e₁ ≠ e₂) (hx1 : x ∈ (e₁ : Finset V)) (hx2 : x ∈ (e₂ : Finset V))
    (honly : ∀ e : edgesOf σ, x ∈ (e : Finset V) → c e ≠ 0 → e = e₁ ∨ e = e₂) :
    bd1 σ c ⟨x, hx⟩ = c e₁ + c e₂ := by
  classical
  rw [bd1_apply]
  rw [← Finset.sum_subset (Finset.subset_univ {e₁, e₂}) (fun e _ hes => ?_)]
  · rw [Finset.sum_pair hne, if_pos hx1, if_pos hx2, one_mul, one_mul]
  · -- terms off {e₁,e₂} vanish
    by_cases hxe : x ∈ (e : Finset V)
    · by_cases hce : c e = 0
      · rw [hce, mul_zero]
      · rcases honly e hxe hce with rfl | rfl <;> simp_all
    · rw [if_neg hxe, zero_mul]

/-- A 1-cycle supported on the edges of `γ` (a triangle whose 2-subsets are
edges) is `0` or the whole γ-cycle: `∂₁ = 0` forces the three coefficients
equal. -/
lemma gammaCycle_dichotomy {σ : Finset (Finset V)} {γ : Finset V} (hγ3 : γ.card = 3)
    (hγe : γ.powersetCard 2 ⊆ edgesOf σ) {c : C1 σ} (hc : bd1 σ c = 0)
    (hsupp : ∀ e : edgesOf σ, c e ≠ 0 → (e : Finset V) ⊆ γ) :
    c = 0 ∨ c = gammaChain σ γ := by
  classical
  obtain ⟨a, b, d, hab, had, hbd, hγ⟩ := Finset.card_eq_three.mp hγ3
  have mk : ∀ {p q : V}, p ≠ q → ({p, q} : Finset V) ⊆ γ → ({p, q} : Finset V) ∈ edgesOf σ :=
    fun hpq hsub => hγe (Finset.mem_powersetCard.mpr ⟨hsub, Finset.card_pair hpq⟩)
  have sab : ({a, b} : Finset V) ⊆ γ := by
    rw [hγ]; intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto
  have sad : ({a, d} : Finset V) ⊆ γ := by
    rw [hγ]; intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto
  have sbd : ({b, d} : Finset V) ⊆ γ := by
    rw [hγ]; intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto
  set eab : edgesOf σ := ⟨{a, b}, mk hab sab⟩ with heab
  set ead : edgesOf σ := ⟨{a, d}, mk had sad⟩ with head
  set ebd : edgesOf σ := ⟨{b, d}, mk hbd sbd⟩ with hebd
  -- every γ-edge is one of the three
  have tri : ∀ e : edgesOf σ, (e : Finset V) ⊆ γ → e = eab ∨ e = ead ∨ e = ebd := by
    intro e hsub
    obtain ⟨p, q, hpq, hpqe⟩ := Finset.card_eq_two.mp (card_of_mem_edgesOf e.2)
    rw [hγ] at hsub
    have hp : p ∈ ({a, b, d} : Finset V) := hsub (hpqe ▸ by simp)
    have hq : q ∈ ({a, b, d} : Finset V) := hsub (hpqe ▸ by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    have key : (e : Finset V) = {a, b} ∨ (e : Finset V) = {a, d} ∨ (e : Finset V) = {b, d} := by
      rw [hpqe]
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hpq
          | exact Or.inl rfl
          | exact Or.inl (Finset.pair_comm _ _)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inl (Finset.pair_comm _ _))
          | exact Or.inr (Or.inr rfl)
          | exact Or.inr (Or.inr (Finset.pair_comm _ _))
    rcases key with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have ha : a ∈ vertsOf σ := edge_mem_vertsOf (mk hab sab) (by simp)
  have hb : b ∈ vertsOf σ := edge_mem_vertsOf (mk hab sab) (by simp)
  have hd : d ∈ vertsOf σ := edge_mem_vertsOf (mk had sad) (by simp)
  have ne_ab_ad : eab ≠ ead := by
    rw [heab, head, ne_eq, Subtype.mk.injEq]; intro h
    have : b ∈ ({a, d} : Finset V) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
  have ne_ab_bd : eab ≠ ebd := by
    rw [heab, hebd, ne_eq, Subtype.mk.injEq]; intro h
    have : a ∈ ({b, d} : Finset V) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
  have ne_ad_bd : ead ≠ ebd := by
    rw [head, hebd, ne_eq, Subtype.mk.injEq]; intro h
    have : a ∈ ({b, d} : Finset V) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
  -- the three vertex equations
  have hva : c eab + c ead = 0 := by
    have honly : ∀ e : edgesOf σ, a ∈ (e : Finset V) → c e ≠ 0 → e = eab ∨ e = ead := by
      intro e hxe hce
      rcases hone : tri e (hsupp e hce) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hxe) (by rw [hebd]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    rw [← bd1_eval_two ha ne_ab_ad (by rw [heab]; simp) (by rw [head]; simp) honly, hc]; rfl
  have hvb : c eab + c ebd = 0 := by
    have honly : ∀ e : edgesOf σ, b ∈ (e : Finset V) → c e ≠ 0 → e = eab ∨ e = ebd := by
      intro e hxe hce
      rcases tri e (hsupp e hce) with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hxe) (by rw [head]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      · exact Or.inr h
    rw [← bd1_eval_two hb ne_ab_bd (by rw [heab]; simp) (by rw [hebd]; simp) honly, hc]; rfl
  -- so the three coefficients are equal
  have c2 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  have e1 : c ead = c eab := (c2 _ _ hva).symm
  have e2 : c ebd = c eab := (c2 _ _ hvb).symm
  -- c = (c eab) • gammaChain
  have hrep : c = (c eab) • gammaChain σ γ := by
    funext e
    simp only [Pi.smul_apply, gammaChain, smul_eq_mul]
    by_cases hsub : (e : Finset V) ⊆ γ
    · rw [if_pos hsub, mul_one]
      rcases tri e hsub with h | h | h
      · rw [h]
      · rw [h, e1]
      · rw [h, e2]
    · rw [if_neg hsub, mul_zero]
      by_contra hce
      exact hsub (hsupp e hce)
  -- conclude on the value c eab ∈ {0,1}
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (c eab) with h0 | h1
  · left; rw [hrep, h0, zero_smul]
  · right; rw [hrep, h1, one_smul]

/-- The dual graph restricted to a face-set `S`: dual-adjacent and both in `S`. -/
def dualOn (σ : Finset (Finset V)) (S : Finset (Finset V)) : SimpleGraph σ where
  Adj f g := (dualGraph σ).Adj f g ∧ (f : Finset V) ∈ S ∧ (g : Finset V) ∈ S
  symm := by rintro f g ⟨hfg, hf, hg⟩; exact ⟨hfg.symm, hg, hf⟩
  loopless := ⟨fun f h => h.1.1 rfl⟩

@[simp] lemma dualOn_adj {σ S : Finset (Finset V)} {f g : σ} :
    (dualOn σ S).Adj f g ↔
      (dualGraph σ).Adj f g ∧ (f : Finset V) ∈ S ∧ (g : Finset V) ∈ S := Iff.rfl

open Classical in
/-- The indicator 2-chain of the cut-faces dual-reachable from `f₀` inside `S`. -/
noncomputable def reachChain (σ : Finset (Finset V)) (S : Finset (Finset V)) (f₀ : σ) : C2 σ :=
  fun g => if (dualOn σ S).Reachable f₀ g then 1 else 0

lemma reachChain_self {σ : Finset (Finset V)} {S : Finset (Finset V)} {f₀ : σ} :
    reachChain σ S f₀ f₀ = 1 := by
  classical
  simp only [reachChain, if_pos (SimpleGraph.Reachable.refl f₀)]

/-- The reach-set is closed under within-`S` dual adjacency: if `f` is reached and
`g` is dual-adjacent to `f` with both faces in `S`, then `g` is reached. -/
lemma reachChain_closed {σ : Finset (Finset V)} {S : Finset (Finset V)} {f₀ : σ}
    {f g : σ} (hf : reachChain σ S f₀ f = 1) (hfg : (dualGraph σ).Adj f g)
    (hfS : (f : Finset V) ∈ S) (hgS : (g : Finset V) ∈ S) : reachChain σ S f₀ g = 1 := by
  classical
  have hrf : (dualOn σ S).Reachable f₀ f := by
    by_contra hc
    simp only [reachChain, if_neg hc] at hf
    exact one_ne_zero hf.symm
  have hrg : (dualOn σ S).Reachable f₀ g :=
    hrf.trans (SimpleGraph.Adj.reachable (dualOn_adj.mpr ⟨hfg, hfS, hgS⟩))
  simp only [reachChain, if_pos hrg]

/-- Reachability inside `S` stays in `S`. -/
lemma dualOn_walk_mem {σ S : Finset (Finset V)} :
    ∀ {f₀ g : σ}, (dualOn σ S).Walk f₀ g → (f₀ : Finset V) ∈ S → (g : Finset V) ∈ S := by
  intro f₀ g p
  induction p with
  | nil => exact fun h => h
  | cons hab _ ih => exact fun _ => ih ((dualOn_adj.mp hab).2.2)

/-- A reached face is in the side (given the base is). -/
lemma reachChain_mem {σ S : Finset (Finset V)} {f₀ g : σ} (hf₀ : (f₀ : Finset V) ∈ S)
    (hg : reachChain σ S f₀ g = 1) : (g : Finset V) ∈ S := by
  classical
  by_contra hgS
  have : ¬ (dualOn σ S).Reachable f₀ g := fun ⟨p⟩ => hgS (dualOn_walk_mem p hf₀)
  simp only [reachChain, if_neg this] at hg
  exact one_ne_zero hg.symm

lemma reachChain_zero {σ S : Finset (Finset V)} {f₀ g : σ} (hf₀ : (f₀ : Finset V) ∈ S)
    (hg : (g : Finset V) ∉ S) : reachChain σ S f₀ g = 0 := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (reachChain σ S f₀ g) with h | h
  · exact h
  · exact absurd (reachChain_mem hf₀ h) hg

/-- The boundary of the reach-chain vanishes off γ's edges: dual-closedness +
the cut parity. -/
lemma bd2_reachChain_supp {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hW : bd2 σ W = gammaChain σ γ) {f₀ : σ}
    (hf₀ : (f₀ : Finset V) ∈ cutSet σ W) {e : Finset V} (he : e ∈ edgesOf σ) (heγ : ¬ e ⊆ γ) :
    bd2 σ (reachChain σ (cutSet σ W) f₀) ⟨e, he⟩ = 0 := by
  classical
  obtain ⟨f₁, h1, f₂, h2, hne, he1, he2, huniq⟩ := exists_two_faces h.toClosedSurface he
  rw [bd2_at_edge _ he h1 h2 hne he1 he2 huniq]
  have hpar := edge_cut_parity hW he h1 h2 hne he1 he2 huniq
  rw [if_neg heγ] at hpar
  have hmem1 : (f₁ : Finset V) ∈ cutSet σ W ↔ W ⟨f₁, h1⟩ = 1 := by
    rw [mem_cutSet]; exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨h1, hh⟩⟩
  have hmem2 : (f₂ : Finset V) ∈ cutSet σ W ↔ W ⟨f₂, h2⟩ = 1 := by
    rw [mem_cutSet]; exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨h2, hh⟩⟩
  have c2 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  have hWeq : W ⟨f₁, h1⟩ = W ⟨f₂, h2⟩ := c2 _ _ hpar
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (W ⟨f₁, h1⟩) with hv | hv
  · -- both faces in σ₂: reach-chain is 0 on both
    have hn1 : (f₁ : Finset V) ∉ cutSet σ W :=
      fun hc => absurd (hmem1.mp hc) (by rw [hv]; decide)
    have hn2 : (f₂ : Finset V) ∉ cutSet σ W :=
      fun hc => absurd (hmem2.mp hc) (by rw [← hWeq, hv]; decide)
    rw [reachChain_zero hf₀ hn1, reachChain_zero hf₀ hn2, add_zero]
  · -- both faces in σ₁: dual-adjacent, so reach-chain agrees
    have hf1S : (f₁ : Finset V) ∈ cutSet σ W := hmem1.mpr hv
    have hf2S : (f₂ : Finset V) ∈ cutSet σ W := hmem2.mpr (hWeq ▸ hv)
    have hadj : (dualGraph σ).Adj ⟨f₁, h1⟩ ⟨f₂, h2⟩ :=
      dualGraph_adj.mpr ⟨fun heq => hne (congrArg Subtype.val heq), e, he, he1, he2⟩
    -- equal values
    have heq : reachChain σ (cutSet σ W) f₀ ⟨f₁, h1⟩ = reachChain σ (cutSet σ W) f₀ ⟨f₂, h2⟩ := by
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1)
        (reachChain σ (cutSet σ W) f₀ ⟨f₁, h1⟩) with hr | hr
      · rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1)
          (reachChain σ (cutSet σ W) f₀ ⟨f₂, h2⟩) with hr2 | hr2
        · rw [hr, hr2]
        · exact absurd (reachChain_closed hr2 hadj.symm hf2S hf1S) (by rw [hr]; decide)
      · rw [hr]; exact (reachChain_closed hr hadj hf1S hf2S).symm
    rw [heq]
    exact CharTwo.add_self_eq_zero _

/-- **One side is dual-connected.** Every cut-face is dual-reachable from a fixed
cut-face `f₀`; equivalently the reach-chain equals the cut indicator `W`. -/
theorem cutSet_dualConn {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hγ3 : γ.card = 3) (hγe : γ.powersetCard 2 ⊆ edgesOf σ)
    (hW : bd2 σ W = gammaChain σ γ) {f₀ : σ} (hf₀ : W f₀ = 1) :
    reachChain σ (cutSet σ W) f₀ = W := by
  classical
  have hf₀mem : (f₀ : Finset V) ∈ cutSet σ W := mem_cutSet.mpr ⟨f₀.2, hf₀⟩
  have c2 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  -- a 2-cycle is a constant function (ker ∂₂ = span 𝟙)
  have const_of_cycle : ∀ x : C2 σ, bd2 σ x = 0 → ∃ cc : ZMod 2, x = fun _ => cc := by
    intro x hx
    have hmem : x ∈ Submodule.span (ZMod 2) {(fun _ => 1 : C2 σ)} := by
      rw [← ker_bd2_eq_span h.toClosedSurface h.nonempty]; exact LinearMap.mem_ker.mpr hx
    obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨cc, funext fun g => by have := congrFun hcc g; simpa using this.symm⟩
  -- gammaChain ≠ 0 (it is 1 on each edge of γ)
  have hWγ : gammaChain σ γ ≠ 0 := by
    obtain ⟨e0, he0⟩ : (γ.powersetCard 2).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_powersetCard, hγ3]; decide)
    rw [Finset.mem_powersetCard] at he0
    have he0e : e0 ∈ edgesOf σ := hγe (Finset.mem_powersetCard.mpr he0)
    intro h0
    have hv1 : gammaChain σ γ ⟨e0, he0e⟩ = 1 := by simp only [gammaChain, if_pos he0.1]
    rw [h0] at hv1; simp only [Pi.zero_apply] at hv1; exact one_ne_zero hv1.symm
  -- some face is off the cut (else W = 𝟙 and gammaChain = bd2 𝟙 = 0)
  have hσ2 : ∃ g : σ, (g : Finset V) ∉ cutSet σ W := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    have hW1 : W = (fun _ => 1) := by
      funext g; obtain ⟨_, hh⟩ := mem_cutSet.mp (hc g); exact hh
    rw [hW1, bd2_one σ h.closed] at hW
    exact hWγ hW.symm
  have hker : bd1 σ (bd2 σ (reachChain σ (cutSet σ W) f₀)) = 0 := by
    have := bd1_comp_bd2 σ h.pure
    rw [LinearMap.ext_iff] at this; simpa using this _
  have hsupp : ∀ e : edgesOf σ, bd2 σ (reachChain σ (cutSet σ W) f₀) e ≠ 0 →
      (e : Finset V) ⊆ γ := fun e hbe => by
    by_contra heγ; exact hbe (bd2_reachChain_supp h hW hf₀mem e.2 heγ)
  rcases gammaCycle_dichotomy hγ3 hγe hker hsupp with hb0 | hbγ
  · -- bd2 R = 0 ⟹ R is constant; but R f₀ = 1 and R vanishes on σ₂ — impossible
    exfalso
    obtain ⟨cc, hcc⟩ := const_of_cycle _ hb0
    obtain ⟨g, hg⟩ := hσ2
    have e1 : (1 : ZMod 2) = cc := reachChain_self.symm.trans (congrFun hcc f₀)
    have e2 : (0 : ZMod 2) = cc := (reachChain_zero hf₀mem hg).symm.trans (congrFun hcc g)
    exact one_ne_zero (e1.trans e2.symm)
  · -- bd2 R = gammaChain = bd2 W ⟹ R + W is a constant cc; at f₀, cc = 0; so R = W
    have hsum : bd2 σ (reachChain σ (cutSet σ W) f₀ + W) = 0 := by
      rw [map_add, hbγ, hW]; funext e
      simp only [Pi.add_apply, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _
    obtain ⟨cc, hcc⟩ := const_of_cycle _ hsum
    have hf := congrFun hcc f₀
    simp only [Pi.add_apply, hf₀, reachChain_self] at hf
    have hcc0 : cc = 0 := by rw [← hf]; decide
    funext g
    have hg := congrFun hcc g
    rw [hcc0] at hg
    simp only [Pi.add_apply] at hg
    exact c2 _ _ hg

/-! ## From dual-connectivity to skeleton-connectivity -/

/-- Two vertices of a single face are skeleton-reachable. -/
lemma skel_reach_within {τ : Finset (Finset V)} {f : τ} {u w : V}
    (hu : u ∈ (f : Finset V)) (hw : w ∈ (f : Finset V)) : (skel τ).Reachable u w := by
  by_cases huw : u = w
  · exact huw ▸ SimpleGraph.Reachable.refl u
  · refine SimpleGraph.Adj.reachable ⟨huw, mem_edgesOf.mpr ⟨f, f.2, ?_, Finset.card_pair huw⟩⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hu
    · rw [Finset.mem_singleton] at hy; exact hy ▸ hw

/-- Reverse transport: a dual-graph walk yields a skeleton walk between chosen
vertices of its endpoint faces. -/
lemma dualwalk_skel {τ : Finset (Finset V)} :
    ∀ {f g : τ} (_ : (dualGraph τ).Walk f g) {u w : V},
      u ∈ (f : Finset V) → w ∈ (g : Finset V) → (skel τ).Reachable u w := by
  intro f g p
  induction p with
  | nil => intro u w hu hw; exact skel_reach_within hu hw
  | @cons f x g hadj _ ih =>
      intro u w hu hw
      obtain ⟨_, e, he, hef, hex⟩ := dualGraph_adj.mp hadj
      obtain ⟨z, hz⟩ : e.Nonempty := Finset.card_pos.mp (by rw [card_of_mem_edgesOf he]; omega)
      exact (skel_reach_within hu (hef hz)).trans (ih (hex hz) hw)

/-- **Dual-connectivity ⟹ skeleton-connectivity** for any complex of nonempty
faces. -/
lemma skelConn_of_dualPreconn {τ : Finset (Finset V)} (hpre : (dualGraph τ).Preconnected) :
    ConnOn (skel τ) (vertsOf τ) := by
  intro u hu w hw
  obtain ⟨f, hf, huf⟩ := mem_vertsOf.mp hu
  obtain ⟨g, hg, hwg⟩ := mem_vertsOf.mp hw
  obtain ⟨p⟩ := hpre ⟨f, hf⟩ ⟨g, hg⟩
  exact dualwalk_skel p huf hwg

/-- A `dualOn` walk among cut-faces transports to a skeleton walk in the capped
complex `insert γ (cutSet σ W)`. -/
lemma dualOn_skel_insert {σ : Finset (Finset V)} {W : C2 σ} {γ : Finset V} :
    ∀ {a b : σ} (_ : (dualOn σ (cutSet σ W)).Walk a b) {u w : V},
      u ∈ (a : Finset V) → w ∈ (b : Finset V) → (a : Finset V) ∈ cutSet σ W →
      (skel (insert γ (cutSet σ W))).Reachable u w := by
  intro a b p
  induction p with
  | nil => intro u w hu hw haS; exact skel_reach_within (f := ⟨_, Finset.mem_insert_of_mem haS⟩) hu hw
  | @cons a x b hadj q ih =>
      intro u w hu hw haS
      obtain ⟨hadjσ, _, hxS⟩ := dualOn_adj.mp hadj
      obtain ⟨_, e, he, hea, hex⟩ := dualGraph_adj.mp hadjσ
      obtain ⟨z, hz⟩ : e.Nonempty := Finset.card_pos.mp (by rw [card_of_mem_edgesOf he]; omega)
      exact (skel_reach_within (f := ⟨_, Finset.mem_insert_of_mem haS⟩) hu (hea hz)).trans
        (ih (hex hz) hw hxS)

/-- **`conn` for the capped side.** The skeleton of `insert γ (cutSet σ W)` is
connected: every vertex reaches a fixed cut-face vertex (cut-faces via the
dual-connectivity transport, `γ` via its shared edge with a cut-face). -/
theorem conn_cut {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ} {γ : Finset V}
    (hγ3 : γ.card = 3) (hγe : γ.powersetCard 2 ⊆ edgesOf σ)
    (hW : bd2 σ W = gammaChain σ γ) :
    ConnOn (skel (insert γ (cutSet σ W))) (vertsOf (insert γ (cutSet σ W))) := by
  classical
  have c2 : ∀ x y : ZMod 2, x + y = 1 → x = 1 ∨ y = 1 := by decide
  -- a base cut-face f₀ (W f₀ = 1), exists since gammaChain ≠ 0
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : σ, W f₀ = 1 := by
    by_contra hc
    simp only [not_exists] at hc
    have hW0 : W = 0 := by
      funext f
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (W f) with h0 | h1
      · exact h0
      · exact absurd h1 (hc f)
    rw [hW0, map_zero] at hW
    obtain ⟨e0, he0⟩ : (γ.powersetCard 2).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_powersetCard, hγ3]; decide)
    rw [Finset.mem_powersetCard] at he0
    have he0e : e0 ∈ edgesOf σ := hγe (Finset.mem_powersetCard.mpr he0)
    have hv1 : gammaChain σ γ ⟨e0, he0e⟩ = 1 := by simp only [gammaChain, if_pos he0.1]
    rw [← hW] at hv1; simp only [Pi.zero_apply] at hv1; exact one_ne_zero hv1.symm
  have hf₀mem : (f₀ : Finset V) ∈ cutSet σ W := mem_cutSet.mpr ⟨f₀.2, hf₀⟩
  have hdc := cutSet_dualConn h hγ3 hγe hW hf₀
  -- a base vertex c₀ ∈ f₀
  obtain ⟨c₀, hc₀⟩ : (f₀ : Finset V).Nonempty := by
    rw [← Finset.card_pos, h.pure _ f₀.2]; omega
  -- every cut-face vertex reaches c₀
  have reachσ1 : ∀ (g : σ) (x : V), W g = 1 → x ∈ (g : Finset V) →
      (skel (insert γ (cutSet σ W))).Reachable x c₀ := by
    intro g x hWg hxg
    have hgmem : (g : Finset V) ∈ cutSet σ W := mem_cutSet.mpr ⟨g.2, hWg⟩
    have : reachChain σ (cutSet σ W) f₀ g = 1 := by rw [hdc]; exact hWg
    have hr : (dualOn σ (cutSet σ W)).Reachable f₀ g := by
      by_contra hcon; simp only [reachChain, if_neg hcon] at this; exact one_ne_zero this.symm
    obtain ⟨p⟩ := hr
    exact (dualOn_skel_insert p hc₀ hxg hf₀mem).symm
  -- a γ-edge and its cut-side face
  obtain ⟨e0, he0⟩ : (γ.powersetCard 2).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_powersetCard, hγ3]; decide)
  rw [Finset.mem_powersetCard] at he0
  have he0e : e0 ∈ edgesOf σ := hγe (Finset.mem_powersetCard.mpr he0)
  obtain ⟨g1, hg1, g2, hg2, hne, hsub1, hsub2, huniq⟩ := exists_two_faces h.toClosedSurface he0e
  have hpar := edge_cut_parity hW he0e hg1 hg2 hne hsub1 hsub2 huniq
  rw [if_pos he0.1] at hpar
  -- pick the cut-side face f₁ of e0, and a shared vertex v₀ ∈ e0 ⊆ γ ∩ f₁
  obtain ⟨v₀, hv₀⟩ : e0.Nonempty := Finset.card_pos.mp (by rw [he0.2]; omega)
  have hvγ : v₀ ∈ γ := he0.1 hv₀
  have reachγ : (skel (insert γ (cutSet σ W))).Reachable v₀ c₀ := by
    rcases c2 _ _ hpar with hw1 | hw1
    · exact reachσ1 ⟨g1, hg1⟩ v₀ hw1 (hsub1 hv₀)
    · exact reachσ1 ⟨g2, hg2⟩ v₀ hw1 (hsub2 hv₀)
  -- every vertex reaches c₀
  have reachAll : ∀ x ∈ vertsOf (insert γ (cutSet σ W)),
      (skel (insert γ (cutSet σ W))).Reachable x c₀ := by
    intro x hx
    obtain ⟨fx, hfx, hxfx⟩ := mem_vertsOf.mp hx
    rcases Finset.mem_insert.mp hfx with hfxγ | hfxc
    · -- x ∈ γ: reach v₀ within γ, then v₀ → c₀
      have hxγ : x ∈ γ := hfxγ ▸ hxfx
      exact (skel_reach_within (f := ⟨γ, Finset.mem_insert_self γ _⟩) hxγ hvγ).trans reachγ
    · -- x in a cut-face
      obtain ⟨hgσ, hWg⟩ := mem_cutSet.mp hfxc
      exact reachσ1 ⟨fx, hgσ⟩ x hWg hxfx
  intro a ha b hb
  exact (reachAll a ha).trans (reachAll b hb).symm

/-! ## linkConn for the capped pieces -/

/-- Two faces sharing a non-γ edge are on the same side of the cut. -/
lemma W_eq_of_share_edge {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ} {γ : Finset V}
    (hW : bd2 σ W = gammaChain σ γ) {e : Finset V} (he : e ∈ edgesOf σ) (heγ : ¬ e ⊆ γ)
    {f g : σ} (hef : e ⊆ (f : Finset V)) (heg : e ⊆ (g : Finset V)) : W f = W g := by
  classical
  obtain ⟨f₁, h1, f₂, h2, hne, hsub1, hsub2, huniq⟩ := exists_two_faces h.toClosedSurface he
  have c2 : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  -- both f and g are among the two faces f₁, f₂ of e
  have hfg : ∀ {k : σ}, e ⊆ (k : Finset V) → W k = W ⟨f₁, h1⟩ ∨ W k = W ⟨f₂, h2⟩ := by
    intro k hk
    rcases huniq (k : Finset V) k.2 hk with hh | hh
    · exact Or.inl (by rw [show k = ⟨f₁, h1⟩ from Subtype.ext hh])
    · exact Or.inr (by rw [show k = ⟨f₂, h2⟩ from Subtype.ext hh])
  have hpar := edge_cut_parity hW he h1 h2 hne hsub1 hsub2 huniq
  rw [if_neg heγ] at hpar
  have h12 : W ⟨f₁, h1⟩ = W ⟨f₂, h2⟩ := c2 _ _ hpar
  rcases hfg hef with hf | hf <;> rcases hfg heg with hg | hg <;>
    rw [hf, hg] <;> first | rfl | exact h12 | exact h12.symm

/-- Along a link walk at a vertex `v ∉ γ`, all faces lie on the same side. -/
lemma W_eq_along_link {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ} {γ : Finset V}
    (hW : bd2 σ W = gammaChain σ γ) {v : V} (hvγ : v ∉ γ) :
    ∀ {a a' : V} (_ : (linkGraph σ v).Walk a a') {f f' : σ},
      v ∈ (f : Finset V) → a ∈ (f : Finset V) → a ≠ v →
      v ∈ (f' : Finset V) → a' ∈ (f' : Finset V) → a' ≠ v → W f = W f' := by
  -- faces sharing the edge {v,y} (y ≠ v) have equal W
  have step : ∀ {y : V} {k k' : σ}, y ≠ v → v ∈ (k : Finset V) → y ∈ (k : Finset V) →
      v ∈ (k' : Finset V) → y ∈ (k' : Finset V) → W k = W k' := by
    intro y k k' hyv hvk hyk hvk' hyk'
    have hsub : ∀ {m : σ}, v ∈ (m : Finset V) → y ∈ (m : Finset V) →
        ({v, y} : Finset V) ⊆ (m : Finset V) := by
      intro m hvm hym z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hvm
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hym
    have he : ({v, y} : Finset V) ∈ edgesOf σ :=
      mem_edgesOf.mpr ⟨k, k.2, hsub hvk hyk, Finset.card_pair (Ne.symm hyv)⟩
    exact W_eq_of_share_edge h hW he (fun hc => hvγ (hc (Finset.mem_insert_self v _)))
      (hsub hvk hyk) (hsub hvk' hyk')
  intro a a' p
  induction p with
  | nil => intro f f' hvf haf hav hvf' haf' _; exact step hav hvf haf hvf' haf'
  | @cons a x a' hadj q ih =>
      intro f f' hvf haf hav hvf' haf' ha'v
      rw [linkGraph] at hadj
      obtain ⟨hax, hface⟩ := hadj
      have hmem : ({v, a, x} : Finset V) ∈ σ := hface
      have hxv : x ≠ v := by
        intro hxv
        have h3 := h.pure _ hmem
        have hle : ({v, a, x} : Finset V).card ≤ 2 := by
          have hsub : ({v, a, x} : Finset V) ⊆ {v, a} := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact Or.inl hxv
          exact le_trans (Finset.card_le_card hsub)
            (le_trans (Finset.card_insert_le _ _) (by simp))
        omega
      have hvh : v ∈ ({v, a, x} : Finset V) := Finset.mem_insert_self v _
      have hah : a ∈ ({v, a, x} : Finset V) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_self a _)
      have hxh : x ∈ ({v, a, x} : Finset V) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self x))
      exact (step hav hvf haf hvh hah).trans (ih (f := ⟨_, hmem⟩) hvh hxh hxv hvf' haf' ha'v)

/-- All faces through an off-γ vertex lie on the same side (via `linkConn`). -/
lemma W_const_at {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ} {γ : Finset V}
    (hW : bd2 σ W = gammaChain σ γ) {v : V} (hvγ : v ∉ γ) {f g : σ}
    (hvf : v ∈ (f : Finset V)) (hvg : v ∈ (g : Finset V)) : W f = W g := by
  obtain ⟨a, ha⟩ : ((f : Finset V).erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hvf, h.pure _ f.2]; omega
  obtain ⟨c, hc⟩ : ((g : Finset V).erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hvg, h.pure _ g.2]; omega
  have haf := Finset.mem_of_mem_erase ha
  have hcg := Finset.mem_of_mem_erase hc
  have hav := Finset.ne_of_mem_erase ha
  have hcv := Finset.ne_of_mem_erase hc
  have hvV : v ∈ vertsOf σ := mem_vertsOf.mpr ⟨f, f.2, hvf⟩
  have haL : a ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hav, f, f.2, hvf, haf⟩
  have hcL : c ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hcv, g, g.2, hvg, hcg⟩
  obtain ⟨p⟩ := h.linkConn v hvV a haL c hcL
  exact W_eq_along_link h hW hvγ p hvf haf hav hvg hcg hcv

/-! ### linkConn at a γ-vertex (local-closure + reroute, per G1 2026-06-13) -/

/-- A face `{v,x,y}` of a sphere has its non-`v` vertices distinct from `v`. -/
lemma face_two_ne {σ : Finset (Finset V)} (h : IsSphere2 σ) {v x y : V}
    (hf : ({v, x, y} : Finset V) ∈ σ) : x ≠ v ∧ y ≠ v := by
  refine ⟨?_, ?_⟩ <;> intro hev <;> rw [hev] at hf <;> have h3 := h.pure _ hf
  · have hsub : ({v, v, y} : Finset V) ⊆ {v, y} := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto
    have hle : ({v, y} : Finset V).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    have := Finset.card_le_card hsub; omega
  · have hsub : ({v, x, v} : Finset V) ⊆ {v, x} := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto
    have hle : ({v, x} : Finset V).card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    have := Finset.card_le_card hsub; omega

/-- The two non-`v` vertices of `γ` at a γ-vertex `v`. -/
lemma gamma_endpoints_at {γ : Finset V} (hγ3 : γ.card = 3) {v : V} (hvγ : v ∈ γ) :
    ∃ a b, a ≠ b ∧ a ≠ v ∧ b ≠ v ∧ γ = {v, a, b} := by
  have he2 : (γ.erase v).card = 2 := by rw [Finset.card_erase_of_mem hvγ, hγ3]
  obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp he2
  have ha : a ∈ γ.erase v := hpair ▸ (by simp)
  have hb : b ∈ γ.erase v := hpair ▸ (by simp)
  refine ⟨a, b, hab, Finset.ne_of_mem_erase ha, Finset.ne_of_mem_erase hb, ?_⟩
  have : γ = insert v (γ.erase v) := (Finset.insert_erase hvγ).symm
  rw [hpair] at this; exact this

/-- The γ-chord `a — b` is an edge of the capped link at `v`. -/
lemma gamma_chord_adj {σ : Finset (Finset V)} {W : C2 σ} {γ : Finset V} {v a b : V}
    (hab : a ≠ b) (hγeq : γ = {v, a, b}) :
    (linkGraph (insert γ (cutSet σ W)) v).Adj a b :=
  ⟨hab, by rw [← hγeq]; exact Finset.mem_insert_self γ _⟩

/-- **Local closure** at a non-γ link vertex: if `x ∈ linkVerts τ v`, `x ∉ γ`,
and `x — y` is an edge of the σ-link at `v`, then it is also an edge of the
capped link `τ = insert γ (cutSet σ W)`. The shared edge `{v,x}` is non-γ
(as `x ∉ γ`), so `W_eq_of_share_edge` puts the σ-face `{v,x,y}` on the same cut
side as the witness cut-face through `{v,x}` — namely the `W = 1` side. -/
lemma cut_link_closure_nonendpoint {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hW : bd2 σ W = gammaChain σ γ) {v x y : V}
    (hxτ : x ∈ linkVerts (insert γ (cutSet σ W)) v) (hxγ : x ∉ γ)
    (hadj : (linkGraph σ v).Adj x y) :
    (linkGraph (insert γ (cutSet σ W)) v).Adj x y := by
  obtain ⟨hxy, hface⟩ := hadj
  obtain ⟨hxv, F, hFτ, hvF, hxF⟩ := mem_linkVerts.mp hxτ
  have hFne : F ≠ γ := by rintro rfl; exact hxγ hxF
  have hFcut : F ∈ cutSet σ W := (Finset.mem_insert.mp hFτ).resolve_left hFne
  obtain ⟨hFσ, hWF⟩ := mem_cutSet.mp hFcut
  have hev : ({v, x} : Finset V) ∈ edgesOf σ :=
    mem_edgesOf.mpr ⟨{v, x, y}, hface,
      (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto),
      Finset.card_pair (Ne.symm hxv)⟩
  have hevγ : ¬ ({v, x} : Finset V) ⊆ γ := fun hsub => hxγ (hsub (by simp))
  have hsub1 : ({v, x} : Finset V) ⊆ ({v, x, y} : Finset V) := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto
  have hsub2 : ({v, x} : Finset V) ⊆ F :=
    Finset.insert_subset hvF (Finset.singleton_subset_iff.mpr hxF)
  have hWxy : W ⟨{v, x, y}, hface⟩ = W ⟨F, hFσ⟩ :=
    W_eq_of_share_edge h hW hev hevγ hsub1 hsub2
  rw [hWF] at hWxy
  exact ⟨hxy, Finset.mem_insert_of_mem (mem_cutSet.mpr ⟨hface, hWxy⟩)⟩

/-- **Reroute.** A σ-link walk from `x` to *any* γ-vertex `z` lifts to a
reachability `x → a` in the capped link: follow the walk, lifting each edge via
`cut_link_closure_nonendpoint`, until the current vertex is a γ-endpoint —
then jump to `a` (refl if it is `a`, the γ-chord if it is `b`). The walk's
endpoint `z` is kept generic (decoupled from the reach-target `a`) so the walk
induction does not pin the target. -/
lemma reroute_to_gamma_endpoint {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hW : bd2 σ W = gammaChain σ γ) {v a b : V}
    (hab : a ≠ b) (hγeq : γ = {v, a, b}) :
    ∀ {x z : V}, (linkGraph σ v).Walk x z →
      x ∈ linkVerts (insert γ (cutSet σ W)) v → z ∈ γ →
      (linkGraph (insert γ (cutSet σ W)) v).Reachable x a := by
  -- reaching `a` from a γ-endpoint `w` of the link: refl (w=a) or chord (w=b)
  have endpoint : ∀ {w : V}, w ∈ linkVerts (insert γ (cutSet σ W)) v → w ∈ γ →
      (linkGraph (insert γ (cutSet σ W)) v).Reachable w a := by
    intro w hwτ hwγ
    have hwv : w ≠ v := (mem_linkVerts.mp hwτ).1
    rw [hγeq] at hwγ; simp only [Finset.mem_insert, Finset.mem_singleton] at hwγ
    rcases hwγ with rfl | rfl | rfl
    · exact absurd rfl hwv
    · exact SimpleGraph.Reachable.refl _
    · exact (gamma_chord_adj hab hγeq).symm.reachable
  intro x z p
  induction p with
  | nil => intro hxτ hxγ; exact endpoint hxτ hxγ
  | @cons x x' z hadjσ _ ih =>
      intro hxτ hzγ
      by_cases hxγ : x ∈ γ
      · exact endpoint hxτ hxγ
      · have hadjτ := cut_link_closure_nonendpoint h hW hxτ hxγ hadjσ
        have hx'τ : x' ∈ linkVerts (insert γ (cutSet σ W)) v :=
          mem_linkVerts.mpr ⟨(face_two_ne h hadjσ.2).2, {v, x, x'}, hadjτ.2, by simp, by simp⟩
        exact hadjτ.reachable.trans (ih hx'τ hzγ)

/-- **linkConn at a γ-vertex.** For `v ∈ γ`, the capped link at `v` is
connected: every link vertex reaches the γ-endpoint `a` (off-γ vertices via the
reroute, the other γ-endpoint `b` via the chord). -/
lemma linkConn_cut_at_gamma {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hγ3 : γ.card = 3) (hγe : γ.powersetCard 2 ⊆ edgesOf σ)
    (hW : bd2 σ W = gammaChain σ γ) {v : V} (hvγ : v ∈ γ) :
    ConnOn (linkGraph (insert γ (cutSet σ W)) v)
      (linkVerts (insert γ (cutSet σ W)) v) := by
  obtain ⟨a, b, hab, hav, hbv, hγeq⟩ := gamma_endpoints_at hγ3 hvγ
  have hva_edge : ({v, a} : Finset V) ∈ edgesOf σ := hγe (by
    rw [Finset.mem_powersetCard]
    exact ⟨by rw [hγeq]; intro z hz;
                simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; tauto,
           Finset.card_pair (Ne.symm hav)⟩)
  have hvV : v ∈ vertsOf σ := edge_mem_vertsOf hva_edge (by simp)
  have haσ : a ∈ linkVerts σ v := (mem_linkVerts_iff_edge h hav).mpr hva_edge
  have reach_a : ∀ z, z ∈ linkVerts (insert γ (cutSet σ W)) v →
      (linkGraph (insert γ (cutSet σ W)) v).Reachable z a := by
    intro z hz
    by_cases hza : z = a
    · exact hza ▸ SimpleGraph.Reachable.refl _
    by_cases hzb : z = b
    · subst hzb; exact (gamma_chord_adj hab hγeq).symm.reachable
    · have hzv : z ≠ v := (mem_linkVerts.mp hz).1
      have hzγ : z ∉ γ := by
        rw [hγeq]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      have hzσ : z ∈ linkVerts σ v := by
        obtain ⟨_, F, hFτ, hvF, hzF⟩ := mem_linkVerts.mp hz
        have hFne : F ≠ γ := by rintro rfl; exact hzγ hzF
        exact mem_linkVerts.mpr ⟨hzv, F,
          cutSet_subset ((Finset.mem_insert.mp hFτ).resolve_left hFne), hvF, hzF⟩
      obtain ⟨p⟩ := h.linkConn v hvV _ hzσ _ haσ
      exact reroute_to_gamma_endpoint h hW hab hγeq p hz (by rw [hγeq]; simp)
  intro x hx y hy
  exact (reach_a x hx).trans (reach_a y hy).symm

/-- For `v ∉ γ` with a cut-face through `v`, the σ-link at `v` is a *subgraph*
of the capped link: every σ-face through `v` lies on the (single) cut side. -/
lemma linkGraph_le_cut_nonendpoint {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hW : bd2 σ W = gammaChain σ γ) {v : V} (hvγ : v ∉ γ)
    {F : Finset V} (hFσ : F ∈ σ) (hvF : v ∈ F) (hWF : W ⟨F, hFσ⟩ = 1) :
    linkGraph σ v ≤ linkGraph (insert γ (cutSet σ W)) v := by
  intro x y hadj
  obtain ⟨hxy, hface⟩ := hadj
  refine ⟨hxy, Finset.mem_insert_of_mem (mem_cutSet.mpr ⟨hface, ?_⟩)⟩
  have key : W (⟨{v, x, y}, hface⟩ : σ) = W (⟨F, hFσ⟩ : σ) :=
    W_const_at h hW hvγ (by simp) hvF
  rw [key, hWF]

/-- **linkConn off γ.** For `v ∉ γ` (but `v ∈ vertsOf τ`), the capped link at
`v` coincides with the σ-link, whose connectivity is inherited from `σ`. -/
lemma linkConn_cut_off_gamma {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hW : bd2 σ W = gammaChain σ γ) {v : V} (hvγ : v ∉ γ)
    (hvτ : v ∈ vertsOf (insert γ (cutSet σ W))) :
    ConnOn (linkGraph (insert γ (cutSet σ W)) v)
      (linkVerts (insert γ (cutSet σ W)) v) := by
  obtain ⟨F, hFτ, hvF⟩ := mem_vertsOf.mp hvτ
  have hFne : F ≠ γ := fun he => hvγ (he ▸ hvF)
  obtain ⟨hFσ, hWF⟩ := mem_cutSet.mp ((Finset.mem_insert.mp hFτ).resolve_left hFne)
  have hvV : v ∈ vertsOf σ := mem_vertsOf.mpr ⟨F, hFσ, hvF⟩
  have hle := linkGraph_le_cut_nonendpoint h hW hvγ hFσ hvF hWF
  have hLeq : linkVerts (insert γ (cutSet σ W)) v = linkVerts σ v := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨hxv, G, hGτ, hvG, hxG⟩ := mem_linkVerts.mp hx
      have hGne : G ≠ γ := fun he => hvγ (he ▸ hvG)
      exact mem_linkVerts.mpr ⟨hxv, G,
        cutSet_subset ((Finset.mem_insert.mp hGτ).resolve_left hGne), hvG, hxG⟩
    · intro x hx
      obtain ⟨hxv, G, hGσ, hvG, hxG⟩ := mem_linkVerts.mp hx
      have key : W (⟨G, hGσ⟩ : σ) = W (⟨F, hFσ⟩ : σ) := W_const_at h hW hvγ hvG hvF
      have hWG : W ⟨G, hGσ⟩ = 1 := by rw [key, hWF]
      exact mem_linkVerts.mpr ⟨hxv, G,
        Finset.mem_insert_of_mem (mem_cutSet.mpr ⟨hGσ, hWG⟩), hvG, hxG⟩
  intro x hx y hy
  rw [hLeq] at hx hy
  exact (h.linkConn v hvV x hx y hy).mono hle

/-- **`linkConn` for the capped sides of the cut.** Both cases assembled. -/
lemma linkConn_cut {σ : Finset (Finset V)} (h : IsSphere2 σ) {W : C2 σ}
    {γ : Finset V} (hγ3 : γ.card = 3) (hγe : γ.powersetCard 2 ⊆ edgesOf σ)
    (hW : bd2 σ W = gammaChain σ γ) :
    ∀ v ∈ vertsOf (insert γ (cutSet σ W)),
      ConnOn (linkGraph (insert γ (cutSet σ W)) v)
        (linkVerts (insert γ (cutSet σ W)) v) := by
  intro v hvτ
  by_cases hvγ : v ∈ γ
  · exact linkConn_cut_at_gamma h hγ3 hγe hW hvγ
  · exact linkConn_cut_off_gamma h hW hvγ hvτ

end Taut
