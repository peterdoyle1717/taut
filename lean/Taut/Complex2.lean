import Taut.Splitting

/-!
# Combinatorial 2-spheres

The definitional layer for Theorems 2–4 of "Taut fillings".  A pure
2-complex is identified with its facet set `σ : Finset (Finset V)`
(members are the 2-simplices, of card 3); edges and vertices are derived.

`IsSphere2 σ` is the combinatorial replacement for "simplicial
triangulation of S²": pure, closed pseudomanifold (every edge in exactly
two faces), connected vertex links, connected, Euler characteristic 2.
With χ in the definition, the Euler counting relations (`3f = 2e`,
`3v = e + 6`, `2v = f + 4`) are free arithmetic; "links are single
cycles" is derivable (closed pm ⟹ links 2-regular; 2-regular and
connected ⟹ one cycle) rather than assumed.

Validation (build-checked):
* the counting relations above (`three_mul_card_faces`,
  `three_mul_card_verts`, `two_mul_card_verts`);
* the boundary of the tetrahedron on any four distinct vertices is a
  sphere (`isSphere2_tetraBdry`) — the semantic smoke test against a
  vacuous or over-strong definition, and the base-case complex of the
  Theorem 2 induction.
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

/-! ## Derived skeleta of a pure 2-complex -/

/-- The edges (1-simplices) of a complex of triangles. -/
def edgesOf (σ : Finset (Finset V)) : Finset (Finset V) :=
  σ.biUnion (Finset.powersetCard 2)

/-- The vertices of a complex. -/
def vertsOf (σ : Finset (Finset V)) : Finset V := σ.biUnion id

/-- The number of faces containing a given edge. -/
def edgeDeg (σ : Finset (Finset V)) (e : Finset V) : ℕ :=
  (σ.filter (fun f => e ⊆ f)).card

lemma mem_edgesOf {σ : Finset (Finset V)} {e : Finset V} :
    e ∈ edgesOf σ ↔ ∃ f ∈ σ, e ⊆ f ∧ e.card = 2 := by
  simp only [edgesOf, Finset.mem_biUnion, Finset.mem_powersetCard]

lemma card_of_mem_edgesOf {σ : Finset (Finset V)} {e : Finset V}
    (he : e ∈ edgesOf σ) : e.card = 2 := by
  obtain ⟨f, _, _, h⟩ := mem_edgesOf.mp he
  exact h

lemma mem_vertsOf {σ : Finset (Finset V)} {x : V} :
    x ∈ vertsOf σ ↔ ∃ f ∈ σ, x ∈ f := by
  simp [vertsOf]

/-- The 1-skeleton, as a simple graph on all of `V`. -/
def skel (σ : Finset (Finset V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ {a, b} ∈ edgesOf σ
  symm := by
    intro a b h
    exact ⟨h.1.symm, by rw [Finset.pair_comm b a]; exact h.2⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- The link of a vertex, as a simple graph: `a ~ b` iff `{v,a,b}` is a
face. -/
def linkGraph (σ : Finset (Finset V)) (v : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ {v, a, b} ∈ σ
  symm := by
    intro a b h
    refine ⟨h.1.symm, ?_⟩
    rw [Finset.pair_comm b a]
    exact h.2
  loopless := ⟨fun a h => h.1 rfl⟩

/-- The neighbors of `v`: vertices of the faces at `v`, except `v`. -/
def linkVerts (σ : Finset (Finset V)) (v : V) : Finset V :=
  (vertsOf (σ.filter (fun f => v ∈ f))).erase v

/-- Connectivity of a graph on a prescribed finite support. -/
def ConnOn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, G.Reachable a b

/-! ## Combinatorial 2-spheres -/

/-- A combinatorial 2-sphere: pure 2-dimensional, every edge in exactly
two faces, connected vertex links, connected, Euler characteristic 2.
This is the paper's "clean complex" (normal pseudomanifold) sharpened by
`χ = 2`, replacing "simplicial triangulation of S²". -/
structure IsSphere2 (σ : Finset (Finset V)) : Prop where
  pure : ∀ f ∈ σ, f.card = 3
  closed : ∀ e ∈ edgesOf σ, edgeDeg σ e = 2
  linkConn : ∀ v ∈ vertsOf σ, ConnOn (linkGraph σ v) (linkVerts σ v)
  conn : ConnOn (skel σ) (vertsOf σ)
  euler : (vertsOf σ).card + σ.card = (edgesOf σ).card + 2

/-! ## Euler counting -/

/-- Double counting face–edge incidences: `3f = 2e`. -/
theorem three_mul_card_faces {σ : Finset (Finset V)} (h : IsSphere2 σ) :
    3 * σ.card = 2 * (edgesOf σ).card := by
  classical
  have hfilter : ∀ f ∈ σ, (edgesOf σ).filter (fun e => e ⊆ f)
      = f.powersetCard 2 := by
    intro f hf
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨he, hef⟩
      exact ⟨hef, card_of_mem_edgesOf he⟩
    · rintro ⟨hef, hcard⟩
      exact ⟨mem_edgesOf.mpr ⟨f, hf, hef, hcard⟩, hef⟩
  have key : ∑ f ∈ σ, ((edgesOf σ).filter (fun e => e ⊆ f)).card
      = ∑ e ∈ edgesOf σ, (σ.filter (fun f => e ⊆ f)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hcongr : ∀ f ∈ σ, ((edgesOf σ).filter (fun e => e ⊆ f)).card = 3 := by
    intro f hf
    rw [hfilter f hf, Finset.card_powersetCard, h.pure f hf]
    rfl
  have hcl : ∀ e ∈ edgesOf σ, (σ.filter (fun f => e ⊆ f)).card = 2 :=
    h.closed
  have hleft : ∑ f ∈ σ, ((edgesOf σ).filter (fun e => e ⊆ f)).card
      = 3 * σ.card := by
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul, mul_comm]
  have hright : ∑ e ∈ edgesOf σ, (σ.filter (fun f => e ⊆ f)).card
      = 2 * (edgesOf σ).card := by
    rw [Finset.sum_congr rfl hcl, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hleft, key, hright]

/-- `3v = e + 6`. -/
theorem three_mul_card_verts {σ : Finset (Finset V)} (h : IsSphere2 σ) :
    3 * (vertsOf σ).card = (edgesOf σ).card + 6 := by
  have h1 := three_mul_card_faces h
  have h2 := h.euler
  omega

/-- `2v = f + 4`. -/
theorem two_mul_card_verts {σ : Finset (Finset V)} (h : IsSphere2 σ) :
    2 * (vertsOf σ).card = σ.card + 4 := by
  have h1 := three_mul_card_faces h
  have h2 := h.euler
  omega

/-! ## The boundary of the tetrahedron -/

/-- The boundary complex of the tetrahedron on `a, b, c, d`. -/
def tetraBdry (a b c d : V) : Finset (Finset V) :=
  {{a, b, c}, {a, b, d}, {a, c, d}, {b, c, d}}

section Tetra

variable {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
  (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)

include hab hac had hbc hbd hcd

private lemma tetra_T_card : ({a, b, c, d} : Finset V).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]),
    Finset.card_insert_of_notMem (by simp [hcd]),
    Finset.card_singleton]

/-- Membership in `tetraBdry` is "card-3 subset of the vertex set". -/
private lemma tetra_mem :
    ∀ f : Finset V, f ∈ tetraBdry a b c d ↔
      f ⊆ {a, b, c, d} ∧ f.card = 3 := by
  intro f
  constructor
  · intro hf
    rw [tetraBdry] at hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact ⟨by intro x hx; simp at hx ⊢; tauto,
        Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩⟩
    · exact ⟨by intro x hx; simp at hx ⊢; tauto,
        Finset.card_eq_three.mpr ⟨a, b, d, hab, had, hbd, rfl⟩⟩
    · exact ⟨by intro x hx; simp at hx ⊢; tauto,
        Finset.card_eq_three.mpr ⟨a, c, d, hac, had, hcd, rfl⟩⟩
    · exact ⟨by intro x hx; simp at hx ⊢; tauto,
        Finset.card_eq_three.mpr ⟨b, c, d, hbc, hbd, hcd, rfl⟩⟩
  · rintro ⟨hsub, hcard⟩
    have hT := tetra_T_card hab hac had hbc hbd hcd
    have hdiff : (({a, b, c, d} : Finset V) \ f).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hT, hcard]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
    have hf : f = ({a, b, c, d} : Finset V) \ {w} := by
      rw [← hw, Finset.sdiff_sdiff_self_left,
        Finset.inter_eq_right.mpr hsub]
    have hwT : w ∈ ({a, b, c, d} : Finset V) := by
      have : w ∈ ({a, b, c, d} : Finset V) \ f := by
        rw [hw]; exact Finset.mem_singleton_self w
      exact (Finset.mem_sdiff.mp this).1
    rw [tetraBdry]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwT ⊢
    rcases hwT with rfl | rfl | rfl | rfl
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hf]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1 | h1 | h1, h2⟩ <;> first | exact absurd h1 h2 | tauto
      · rintro (rfl | rfl | rfl)
        · exact ⟨by tauto, Ne.symm hab⟩
        · exact ⟨by tauto, Ne.symm hac⟩
        · exact ⟨by tauto, Ne.symm had⟩
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [hf]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1 | h1 | h1, h2⟩ <;> first | exact absurd h1 h2 | tauto
      · rintro (rfl | rfl | rfl)
        · exact ⟨by tauto, hab⟩
        · exact ⟨by tauto, Ne.symm hbc⟩
        · exact ⟨by tauto, Ne.symm hbd⟩
    · refine Or.inr (Or.inl ?_)
      rw [hf]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1 | h1 | h1, h2⟩ <;> first | exact absurd h1 h2 | tauto
      · rintro (rfl | rfl | rfl)
        · exact ⟨by tauto, hac⟩
        · exact ⟨by tauto, hbc⟩
        · exact ⟨by tauto, Ne.symm hcd⟩
    · refine Or.inl ?_
      rw [hf]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1 | h1 | h1, h2⟩ <;> first | exact absurd h1 h2 | tauto
      · rintro (rfl | rfl | rfl)
        · exact ⟨by tauto, had⟩
        · exact ⟨by tauto, hbd⟩
        · exact ⟨by tauto, hcd⟩

private lemma tetra_verts :
    vertsOf (tetraBdry a b c d) = {a, b, c, d} := by
  ext x
  rw [mem_vertsOf]
  constructor
  · rintro ⟨f, hf, hxf⟩
    exact ((tetra_mem hab hac had hbc hbd hcd f).mp hf).1 hxf
  · intro hx
    -- pick two other vertices of T to complete a face
    have h2 : 2 ≤ (({a, b, c, d} : Finset V).erase x).card := by
      rw [Finset.card_erase_of_mem hx, tetra_T_card hab hac had hbc hbd hcd]
      omega
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_pair_of_one_lt_card h2
    refine ⟨{x, y, z}, (tetra_mem hab hac had hbc hbd hcd _).mpr
      ⟨?_, Finset.card_eq_three.mpr
        ⟨x, y, z, Ne.symm (Finset.ne_of_mem_erase hy),
          Ne.symm (Finset.ne_of_mem_erase hz), hyz, rfl⟩⟩,
      Finset.mem_insert_self x _⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hx
    · rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_of_mem_erase hy
      · rw [Finset.mem_singleton] at hu
        exact hu ▸ Finset.mem_of_mem_erase hz

private lemma tetra_edges :
    edgesOf (tetraBdry a b c d) = ({a, b, c, d} : Finset V).powersetCard 2 := by
  ext e
  rw [mem_edgesOf, Finset.mem_powersetCard]
  constructor
  · rintro ⟨f, hf, hef, hcard⟩
    exact ⟨hef.trans ((tetra_mem hab hac had hbc hbd hcd f).mp hf).1, hcard⟩
  · rintro ⟨hsub, hcard⟩
    -- complete the edge to a face with any third vertex
    have h1 : 1 ≤ (({a, b, c, d} : Finset V) \ e).card := by
      rw [Finset.card_sdiff_of_subset hsub, tetra_T_card hab hac had hbc hbd hcd, hcard]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp
      (show 0 < (({a, b, c, d} : Finset V) \ e).card by omega)
    obtain ⟨hzT, hze⟩ := Finset.mem_sdiff.mp hz
    refine ⟨insert z e, (tetra_mem hab hac had hbc hbd hcd _).mpr
      ⟨Finset.insert_subset hzT hsub, ?_⟩,
      Finset.subset_insert z e, hcard⟩
    rw [Finset.card_insert_of_notMem hze, hcard]

/-- Faces containing a fixed edge of the tetrahedron boundary: exactly
the two completions by a vertex outside the edge. -/
private lemma tetra_closed :
    ∀ e ∈ edgesOf (tetraBdry a b c d), edgeDeg (tetraBdry a b c d) e = 2 := by
  intro e he
  rw [tetra_edges hab hac had hbc hbd hcd, Finset.mem_powersetCard] at he
  obtain ⟨hsub, hcard⟩ := he
  have hfilter : (tetraBdry a b c d).filter (fun f => e ⊆ f)
      = (({a, b, c, d} : Finset V) \ e).image (fun z => insert z e) := by
    ext f
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hf, hef⟩
      obtain ⟨hfT, hf3⟩ := (tetra_mem hab hac had hbc hbd hcd f).mp hf
      have hd : (f \ e).card = 1 := by
        rw [Finset.card_sdiff_of_subset hef, hf3, hcard]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hd
      have hzf : z ∈ f \ e := by rw [hz]; exact Finset.mem_singleton_self z
      obtain ⟨hzf', hze⟩ := Finset.mem_sdiff.mp hzf
      refine ⟨z, Finset.mem_sdiff.mpr ⟨hfT hzf', hze⟩, ?_⟩
      have : f = e ∪ (f \ e) := by
        rw [Finset.union_sdiff_of_subset hef]
      rw [this, hz]
      ext x
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      tauto
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hzT, hze⟩ := Finset.mem_sdiff.mp hz
      refine ⟨(tetra_mem hab hac had hbc hbd hcd _).mpr
        ⟨Finset.insert_subset hzT hsub, ?_⟩, Finset.subset_insert z e⟩
      rw [Finset.card_insert_of_notMem hze, hcard]
  rw [edgeDeg, hfilter, Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hsub,
    tetra_T_card hab hac had hbc hbd hcd, hcard]
  intro z₁ h₁ z₂ h₂ hins
  have hins' : insert z₁ e = insert z₂ e := hins
  have hz₁ : z₁ ∈ insert z₂ e := hins' ▸ Finset.mem_insert_self z₁ e
  rcases Finset.mem_insert.mp hz₁ with h | h
  · exact h
  · exact absurd h (Finset.mem_sdiff.mp h₁).2

/-- Validation instance: the boundary of the tetrahedron is a
combinatorial 2-sphere. -/
theorem isSphere2_tetraBdry :
    IsSphere2 (tetraBdry a b c d) := by
  have hmem := tetra_mem hab hac had hbc hbd hcd
  have hverts := tetra_verts hab hac had hbc hbd hcd
  have hT := tetra_T_card hab hac had hbc hbd hcd
  constructor
  · exact fun f hf => ((hmem f).mp hf).2
  · exact tetra_closed hab hac had hbc hbd hcd
  · -- links: every pair of neighbours of v spans a face with v
    intro v hv x hx y hy
    rw [hverts] at hv
    have hmemT : ∀ w, w ∈ linkVerts (tetraBdry a b c d) v →
        w ∈ ({a, b, c, d} : Finset V) ∧ w ≠ v := by
      intro w hw
      have hwv := Finset.ne_of_mem_erase hw
      have hw' := Finset.mem_of_mem_erase hw
      rw [mem_vertsOf] at hw'
      obtain ⟨f, hf, hwf⟩ := hw'
      have hfσ := Finset.mem_of_mem_filter f hf
      exact ⟨hverts ▸ mem_vertsOf.mpr ⟨f, hfσ, hwf⟩, hwv⟩
    obtain ⟨hxT, hxv⟩ := hmemT x hx
    obtain ⟨hyT, hyv⟩ := hmemT y hy
    by_cases hxy : x = y
    · subst hxy; exact ⟨SimpleGraph.Walk.nil⟩
    refine SimpleGraph.Adj.reachable ⟨hxy, ?_⟩
    refine (hmem _).mpr ⟨?_, Finset.card_eq_three.mpr
      ⟨v, x, y, Ne.symm hxv, Ne.symm hyv, hxy, rfl⟩⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hv
    · rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hxT
      · rw [Finset.mem_singleton] at hu
        exact hu ▸ hyT
  · -- the 1-skeleton is complete on the four vertices
    intro x hx y hy
    rw [hverts] at hx hy
    by_cases hxy : x = y
    · subst hxy; exact ⟨SimpleGraph.Walk.nil⟩
    refine SimpleGraph.Adj.reachable ⟨hxy, ?_⟩
    rw [tetra_edges hab hac had hbc hbd hcd, Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_eq_two.mpr ⟨x, y, hxy, rfl⟩⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hx
    · rw [Finset.mem_singleton] at hu
      exact hu ▸ hy
  · -- Euler: 4 + 4 = 6 + 2
    have hS : tetraBdry a b c d = ({a, b, c, d} : Finset V).powersetCard 3 := by
      ext f
      rw [hmem f, Finset.mem_powersetCard]
    rw [hverts, tetra_edges hab hac had hbc hbd hcd, hS,
      Finset.card_powersetCard, Finset.card_powersetCard, hT]
    rfl

end Tetra

end Taut
