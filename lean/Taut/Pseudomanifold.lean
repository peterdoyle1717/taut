import Taut.Ball
import Taut.Complex2

/-!
# Pseudomanifold invariant — the "simplicial" half of a sticker ball

`FreelyShellable`/`IsBall` originally tracked only the shelling (boundary by
symmetric difference), which admits non-simplicial configurations: a triangle
can be re-exposed into a third tet (an edge "flipped back and forth").  A sticker
ball *for us* is a shellable **simplicial** complex, so we carry the
pseudomanifold condition — every triangle lies in at most two tets — as part of
the invariant.  This file sets up the face-incidence bookkeeping.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- Number of tets of `τ` that contain the face `f`. -/
def faceCount (τ : Finset (Finset V)) (f : Finset V) : ℕ :=
  (τ.filter (fun t => f ⊆ t)).card

/-- `τ` is a 3-pseudomanifold: every triangle lies in at most two tets.
With a unit boundary this forces every boundary triangle into exactly one tet
(two would cancel to `0` or sum to `±2`, never the boundary value `±1`). -/
def IsPseudomanifold (τ : Finset (Finset V)) : Prop :=
  ∀ f, f.card = 3 → faceCount τ f ≤ 2

/-- `TriangleBounded3` — the triangle-count condition (`IsPseudomanifold`): every
triangle lies in at most two tets.  This is *not* a normal/clean pseudomanifold:
it admits two balls joined along an edge, or along a single vertex. -/
abbrev TriangleBounded3 (τ : Finset (Finset V)) : Prop := IsPseudomanifold τ

/-- A face contained in no tet has incidence zero — used to discharge the
triangle-cleanliness hypothesis from the triangle rule-out (`s₁,s₂ ∉ M−t`). -/
lemma faceCount_eq_zero {τ : Finset (Finset V)} {f : Finset V}
    (h : ∀ t ∈ τ, ¬ f ⊆ t) : faceCount τ f = 0 := by
  unfold faceCount
  rw [Finset.filter_false_of_mem h]; rfl

lemma faceCount_insert_of_not_mem {τ : Finset (Finset V)} {t : Finset V}
    (ht : t ∉ τ) (f : Finset V) :
    faceCount (insert t τ) f = faceCount τ f + (if f ⊆ t then 1 else 0) := by
  unfold faceCount
  rw [Finset.filter_insert]
  by_cases h : f ⊆ t
  · have hnm : t ∉ τ.filter (fun s => f ⊆ s) :=
      fun hmem => ht (Finset.mem_of_mem_filter t hmem)
    simp only [if_pos h, Finset.card_insert_of_notMem hnm]
  · simp only [if_neg h, Nat.add_zero]

lemma isPseudomanifold_singleton (t : Finset V) :
    IsPseudomanifold ({t} : Finset (Finset V)) := by
  intro f _
  have h : faceCount ({t} : Finset (Finset V)) f ≤ 1 := by
    unfold faceCount
    have hle := Finset.card_filter_le ({t} : Finset (Finset V)) (fun s => f ⊆ s)
    simpa using hle
  omega

/-- **Clean glue preserves the pseudomanifold property.** Inserting a fresh tet
`t` whose every *triangle* lies in at most one existing tet keeps `τ` a
pseudomanifold.  The hypothesis `hclean` is exactly the "no re-exposure"
condition the forward construction must supply at each shelling step. -/
lemma isPseudomanifold_insert {τ : Finset (Finset V)} {t : Finset V}
    (hτ : IsPseudomanifold τ) (ht : t ∉ τ)
    (hclean : ∀ f, f.card = 3 → f ⊆ t → faceCount τ f ≤ 1) :
    IsPseudomanifold (insert t τ) := by
  intro f hf
  rw [faceCount_insert_of_not_mem ht]
  by_cases h : f ⊆ t
  · rw [if_pos h]; have := hclean f hf h; omega
  · rw [if_neg h]; have := hτ f hf; omega

/-! ## Edge-link connectedness — the manifold-along-edges half of a stickerball

`IsPseudomanifold` controls triangle incidence, but a boundary-tracking shelling
cannot see when an edge acquires a disconnected link (a stray ring of tets).  A
genuine simplicial ball has connected edge-links, so a faithful stickerball must
carry that too. -/

/-- The link of an edge `e` in a tet-set `τ`, as a simple graph on apexes:
`x ~ y` iff `e ∪ {x, y}` is a tet of `τ`. -/
def edgeLinkGraph (τ : Finset (Finset V)) (e : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ insert x (insert y e) ∈ τ
  symm := by
    intro x y h
    exact ⟨h.1.symm, by rw [Finset.insert_comm]; exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The apexes of edge `e` in `τ`: the vertices of the tets containing `e`, with
`e` itself removed. -/
def edgeLinkVerts (τ : Finset (Finset V)) (e : Finset V) : Finset V :=
  vertsOf (τ.filter (fun t => e ⊆ t)) \ e

/-- `τ` is *edge-link connected*: for every edge, its apexes are mutually
reachable in the edge-link graph (one connected ring, no stray components). -/
def EdgeLinkConnected (τ : Finset (Finset V)) : Prop :=
  ∀ e : Finset V, e.card = 2 → ConnOn (edgeLinkGraph τ e) (edgeLinkVerts τ e)

/-- An edge contained in no tet has empty apex set — used to discharge the
edge-cleanliness hypothesis from the edge rule-out (`ab ∉ M−t`). -/
lemma edgeLinkVerts_eq_empty {τ : Finset (Finset V)} {e : Finset V}
    (h : ∀ t ∈ τ, ¬ e ⊆ t) : edgeLinkVerts τ e = ∅ := by
  unfold edgeLinkVerts vertsOf
  rw [Finset.filter_false_of_mem h]; simp

lemma edgeLinkGraph_mono {τ τ' : Finset (Finset V)} (h : τ ⊆ τ') (e : Finset V) :
    edgeLinkGraph τ e ≤ edgeLinkGraph τ' e :=
  fun _ _ hxy => ⟨hxy.1, h hxy.2⟩

/-- Reachability in a smaller tet-set's edge-link transfers to the larger one;
contrapositively, **deleting tets cannot reconnect a split edge-link** — the
key fact behind the edge rule-out. -/
lemma edgeLink_reachable_mono {τ τ' : Finset (Finset V)} (h : τ ⊆ τ') (e : Finset V)
    {x y : V} (hr : (edgeLinkGraph τ e).Reachable x y) :
    (edgeLinkGraph τ' e).Reachable x y :=
  hr.mono (edgeLinkGraph_mono h e)

lemma edgeLinkConnected_singleton {t : Finset V} (ht : t.card = 4) :
    EdgeLinkConnected ({t} : Finset (Finset V)) := by
  intro e he x hx y hy
  simp only [edgeLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter,
    Finset.mem_singleton] at hx hy
  obtain ⟨⟨_, ⟨rfl, hesub⟩, hxt⟩, hxe⟩ := hx
  obtain ⟨⟨_, ⟨rfl, _⟩, hyt⟩, hye⟩ := hy
  by_cases hxy : x = y
  · subst hxy; exact ⟨SimpleGraph.Walk.nil⟩
  · refine SimpleGraph.Adj.reachable ⟨hxy, ?_⟩
    rw [Finset.mem_singleton]
    have hxni : x ∉ insert y e := by
      simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hxe⟩
    have hcard : (insert x (insert y e)).card = 4 := by
      rw [Finset.card_insert_of_notMem hxni, Finset.card_insert_of_notMem hye]
      omega
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) (le_of_eq (ht.trans hcard.symm))
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact hxt
    · exact hyt
    · exact hesub hz

lemma insert_apexes_eq {t e : Finset V} {z w : V} (ht : t.card = 4) (he : e.card = 2)
    (hsub : e ⊆ t) (hz : z ∈ t \ e) (hw : w ∈ t \ e) (hzw : z ≠ w) :
    insert z (insert w e) = t := by
  rw [Finset.mem_sdiff] at hz hw
  have hwni : w ∉ e := hw.2
  have hzni : z ∉ insert w e := by
    simp only [Finset.mem_insert, not_or]; exact ⟨hzw, hz.2⟩
  have hcard : (insert z (insert w e)).card = 4 := by
    rw [Finset.card_insert_of_notMem hzni, Finset.card_insert_of_notMem hwni]; omega
  refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (le_of_eq (ht.trans hcard.symm))
  simp only [Finset.mem_insert] at hu
  rcases hu with rfl | rfl | hu
  · exact hz.1
  · exact hw.1
  · exact hsub hu

lemma edgeLinkVerts_insert_of_subset {τ : Finset (Finset V)} {t e : Finset V}
    (h : e ⊆ t) :
    edgeLinkVerts (insert t τ) e = (t \ e) ∪ edgeLinkVerts τ e := by
  unfold edgeLinkVerts vertsOf
  rw [Finset.filter_insert, if_pos h, Finset.biUnion_insert, id_eq,
    Finset.union_sdiff_distrib]

lemma edgeLinkVerts_insert_of_not_subset {τ : Finset (Finset V)} {t e : Finset V}
    (h : ¬ e ⊆ t) :
    edgeLinkVerts (insert t τ) e = edgeLinkVerts τ e := by
  unfold edgeLinkVerts
  rw [Finset.filter_insert, if_neg h]

lemma edgeLinkVerts_union {τ₁ τ₂ : Finset (Finset V)} (e : Finset V) :
    edgeLinkVerts (τ₁ ∪ τ₂) e = edgeLinkVerts τ₁ e ∪ edgeLinkVerts τ₂ e := by
  ext w
  simp only [edgeLinkVerts, Finset.mem_union, Finset.mem_sdiff, mem_vertsOf,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨t, ⟨ht₁ | ht₂, hsub⟩, hwt⟩, hwe⟩
    · exact Or.inl ⟨⟨t, ⟨ht₁, hsub⟩, hwt⟩, hwe⟩
    · exact Or.inr ⟨⟨t, ⟨ht₂, hsub⟩, hwt⟩, hwe⟩
  · rintro (⟨⟨t, ⟨ht, hsub⟩, hwt⟩, hwe⟩ | ⟨⟨t, ⟨ht, hsub⟩, hwt⟩, hwe⟩)
    · exact ⟨⟨t, ⟨Or.inl ht, hsub⟩, hwt⟩, hwe⟩
    · exact ⟨⟨t, ⟨Or.inr ht, hsub⟩, hwt⟩, hwe⟩

/-- **Edge-link connectedness is preserved by inserting a fresh tet**, provided
each edge of the new tet is either new to `τ` or already shares an apex with
`τ`'s link there (the clean-glue compatibility). This is the manifold half of
"clean glue onto a stickerball gives a stickerball". -/
lemma edgeLinkConnected_insert {τ : Finset (Finset V)} {t : Finset V} (ht : t.card = 4)
    (hτ : EdgeLinkConnected τ)
    (hcompat : ∀ e, e ⊆ t → e.card = 2 →
      edgeLinkVerts τ e = ∅ ∨ ((t \ e) ∩ edgeLinkVerts τ e).Nonempty) :
    EdgeLinkConnected (insert t τ) := by
  have hsubins : τ ⊆ insert t τ := Finset.subset_insert t τ
  intro e he x hx y hy
  have hmono : edgeLinkGraph τ e ≤ edgeLinkGraph (insert t τ) e := edgeLinkGraph_mono hsubins e
  by_cases hsub : e ⊆ t
  · rw [edgeLinkVerts_insert_of_subset hsub] at hx hy
    have adj_apex : ∀ {p q : V}, p ∈ t \ e → q ∈ t \ e → p ≠ q →
        (edgeLinkGraph (insert t τ) e).Adj p q := fun {p q} hp hq hpq =>
      ⟨hpq, by rw [insert_apexes_eq ht he hsub hp hq hpq]; exact Finset.mem_insert_self t τ⟩
    rcases hcompat e hsub he with hempty | ⟨w, hw⟩
    · rw [hempty, Finset.union_empty] at hx hy
      by_cases hxy : x = y
      · subst hxy; exact ⟨SimpleGraph.Walk.nil⟩
      · exact (adj_apex hx hy hxy).reachable
    · obtain ⟨hwt, hwold⟩ := Finset.mem_inter.mp hw
      have reach_w : ∀ z ∈ (t \ e) ∪ edgeLinkVerts τ e,
          (edgeLinkGraph (insert t τ) e).Reachable z w := by
        intro z hz
        rcases Finset.mem_union.mp hz with hzt | hzold
        · by_cases hzw : z = w
          · subst hzw; exact ⟨SimpleGraph.Walk.nil⟩
          · exact (adj_apex hzt hwt hzw).reachable
        · exact (hτ e he z hzold w hwold).mono hmono
      exact (reach_w x hx).trans (reach_w y hy).symm
  · rw [edgeLinkVerts_insert_of_not_subset hsub] at hx hy
    exact (hτ e he x hx y hy).mono hmono

/-! ## Rule-out engines

The two ways re-gluing the eligible tet can spoil simpliciality each reduce, via
minimality, to "a smaller filling `M−u` fails to be a stickerball".  These are the
reusable cores: a surviving over-incident triangle breaks `IsPseudomanifold`, and
a surviving disconnected edge-link breaks `EdgeLinkConnected`. -/

lemma faceCount_le_of_subset {τ τ' : Finset (Finset V)} (h : τ' ⊆ τ) (f : Finset V) :
    faceCount τ' f ≤ faceCount τ f := by
  unfold faceCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma faceCount_union_of_disjoint {τ₁ τ₂ : Finset (Finset V)} (hd : Disjoint τ₁ τ₂)
    (f : Finset V) : faceCount (τ₁ ∪ τ₂) f = faceCount τ₁ f + faceCount τ₂ f := by
  unfold faceCount
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hd)]

lemma not_isPseudomanifold_of_faceCount {τ' : Finset (Finset V)} {f : Finset V}
    (hf : f.card = 3) (h3 : 3 ≤ faceCount τ' f) : ¬ IsPseudomanifold τ' :=
  fun hP => by have := hP f hf; omega

/-- **Edge rule-out core.** If two apexes appear in `τ'` but are non-reachable in
a larger `τ`, then `τ'` is not edge-link connected.  Applied with `τ' = M−u ⊆ M`:
deleting `u` cannot reconnect a split link, so a disconnection in `M` survives in
`M−u`. -/
lemma not_edgeLinkConnected_of_subset {τ τ' : Finset (Finset V)} (h : τ' ⊆ τ)
    {e : Finset V} (he : e.card = 2) {x y : V}
    (hx : x ∈ edgeLinkVerts τ' e) (hy : y ∈ edgeLinkVerts τ' e)
    (hnr : ¬ (edgeLinkGraph τ e).Reachable x y) :
    ¬ EdgeLinkConnected τ' :=
  fun hC => hnr (edgeLink_reachable_mono h e (hC e he x hx y hy))

/-! ## Vertex-link connectedness — the manifold-at-vertices half

`EdgeLinkConnected` is still not enough: two tets meeting at a single shared
*vertex* have every triangle in ≤ 1 tet and every edge-link connected, yet they
pinch at that vertex.  Only the vertex link sees it.  A faithful clean complex
must carry it.  Mirrors the edge-link block: the link of `v` is the graph on its
apexes with `x ~ y` iff some tet contains the triangle `{v, x, y}`. -/

/-- The link of a vertex `v` in `τ`, as a simple graph on apexes: `x ~ y` iff
some tet of `τ` contains the triangle `{v, x, y}` (the triangle is present). -/
def vertexLinkGraph (τ : Finset (Finset V)) (v : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ t ∈ τ, {v, x, y} ⊆ t
  symm := by
    rintro x y ⟨hxy, t, ht, hsub⟩
    exact ⟨hxy.symm, t, ht, by rw [Finset.pair_comm y x]; exact hsub⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The apexes of `v` in `τ`: vertices appearing in a tet with `v`, minus `v`. -/
def vertexLinkVerts (τ : Finset (Finset V)) (v : V) : Finset V :=
  vertsOf (τ.filter (fun t => v ∈ t)) \ {v}

/-- `τ` is *vertex-link connected*: for every vertex, its apexes are mutually
reachable in the vertex-link graph (one connected link, no pinch). -/
def VertexLinkConnected (τ : Finset (Finset V)) : Prop :=
  ∀ v : V, ConnOn (vertexLinkGraph τ v) (vertexLinkVerts τ v)

lemma vertexLinkVerts_eq_empty {τ : Finset (Finset V)} {v : V}
    (h : ∀ t ∈ τ, v ∉ t) : vertexLinkVerts τ v = ∅ := by
  unfold vertexLinkVerts vertsOf
  rw [Finset.filter_false_of_mem h]; simp

lemma vertexLinkVerts_union {τ₁ τ₂ : Finset (Finset V)} (v : V) :
    vertexLinkVerts (τ₁ ∪ τ₂) v = vertexLinkVerts τ₁ v ∪ vertexLinkVerts τ₂ v := by
  ext w
  simp only [vertexLinkVerts, Finset.mem_union, Finset.mem_sdiff, mem_vertsOf,
    Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨t, ⟨ht₁ | ht₂, hvt⟩, hwt⟩, hwv⟩
    · exact Or.inl ⟨⟨t, ⟨ht₁, hvt⟩, hwt⟩, hwv⟩
    · exact Or.inr ⟨⟨t, ⟨ht₂, hvt⟩, hwt⟩, hwv⟩
  · rintro (⟨⟨t, ⟨ht, hvt⟩, hwt⟩, hwv⟩ | ⟨⟨t, ⟨ht, hvt⟩, hwt⟩, hwv⟩)
    · exact ⟨⟨t, ⟨Or.inl ht, hvt⟩, hwt⟩, hwv⟩
    · exact ⟨⟨t, ⟨Or.inr ht, hvt⟩, hwt⟩, hwv⟩

lemma vertexLinkGraph_mono {τ τ' : Finset (Finset V)} (h : τ ⊆ τ') (v : V) :
    vertexLinkGraph τ v ≤ vertexLinkGraph τ' v :=
  fun _ _ hxy => ⟨hxy.1, hxy.2.imp fun _ ht => ⟨h ht.1, ht.2⟩⟩

/-- Reachability transfers to a larger tet-set; contrapositively, **deleting tets
cannot reconnect a split vertex-link** — the key fact behind the vertex rule-out. -/
lemma vertexLink_reachable_mono {τ τ' : Finset (Finset V)} (h : τ ⊆ τ') (v : V)
    {x y : V} (hr : (vertexLinkGraph τ v).Reachable x y) :
    (vertexLinkGraph τ' v).Reachable x y :=
  hr.mono (vertexLinkGraph_mono h v)

lemma vertexLinkConnected_singleton (t : Finset V) :
    VertexLinkConnected ({t} : Finset (Finset V)) := by
  intro v x hx y hy
  simp only [vertexLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter,
    Finset.mem_singleton] at hx hy
  obtain ⟨⟨f, ⟨hf, hvf⟩, hxf⟩, _⟩ := hx
  obtain ⟨⟨g, ⟨hg, _⟩, hyg⟩, _⟩ := hy
  rw [hf] at hvf hxf
  rw [hg] at hyg
  by_cases hxy : x = y
  · subst hxy; exact ⟨SimpleGraph.Walk.nil⟩
  · refine SimpleGraph.Adj.reachable ⟨hxy, t, Finset.mem_singleton_self t, ?_⟩
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hvf
    · exact hxf
    · exact hyg

lemma vertexLinkVerts_insert_of_mem {τ : Finset (Finset V)} {t : Finset V} {v : V}
    (h : v ∈ t) :
    vertexLinkVerts (insert t τ) v = (t \ {v}) ∪ vertexLinkVerts τ v := by
  unfold vertexLinkVerts vertsOf
  rw [Finset.filter_insert, if_pos h, Finset.biUnion_insert, id_eq,
    Finset.union_sdiff_distrib]

lemma vertexLinkVerts_insert_of_not_mem {τ : Finset (Finset V)} {t : Finset V} {v : V}
    (h : v ∉ t) :
    vertexLinkVerts (insert t τ) v = vertexLinkVerts τ v := by
  unfold vertexLinkVerts
  rw [Finset.filter_insert, if_neg h]

/-- **Vertex-link connectedness is preserved by inserting a fresh tet**, provided
each vertex of `t` is either new to `τ` or already shares an apex with `τ`'s link
there.  Mirrors `edgeLinkConnected_insert`; the new apexes `t \ {v}` form a clique
in the link (any two lie in `t`), which attaches to the old link via the shared
apex. -/
lemma vertexLinkConnected_insert {τ : Finset (Finset V)} {t : Finset V}
    (hτ : VertexLinkConnected τ)
    (hcompat : ∀ v ∈ t, vertexLinkVerts τ v = ∅ ∨
      ((t \ {v}) ∩ vertexLinkVerts τ v).Nonempty) :
    VertexLinkConnected (insert t τ) := by
  have hsubins : τ ⊆ insert t τ := Finset.subset_insert t τ
  intro v x hx y hy
  have hmono : vertexLinkGraph τ v ≤ vertexLinkGraph (insert t τ) v :=
    vertexLinkGraph_mono hsubins v
  by_cases hv : v ∈ t
  · rw [vertexLinkVerts_insert_of_mem hv] at hx hy
    have adj_apex : ∀ {p q : V}, p ∈ t \ {v} → q ∈ t \ {v} → p ≠ q →
        (vertexLinkGraph (insert t τ) v).Adj p q := by
      intro p q hp hq hpq
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hp hq
      refine ⟨hpq, t, Finset.mem_insert_self t τ, ?_⟩
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hv
      · exact hp.1
      · exact hq.1
    rcases hcompat v hv with hempty | ⟨w, hw⟩
    · rw [hempty, Finset.union_empty] at hx hy
      by_cases hxy : x = y
      · subst hxy; exact ⟨SimpleGraph.Walk.nil⟩
      · exact (adj_apex hx hy hxy).reachable
    · obtain ⟨hwt, hwold⟩ := Finset.mem_inter.mp hw
      have reach_w : ∀ z ∈ (t \ {v}) ∪ vertexLinkVerts τ v,
          (vertexLinkGraph (insert t τ) v).Reachable z w := by
        intro z hz
        rcases Finset.mem_union.mp hz with hzt | hzold
        · by_cases hzw : z = w
          · subst hzw; exact ⟨SimpleGraph.Walk.nil⟩
          · exact (adj_apex hzt hwt hzw).reachable
        · exact (hτ v z hzold w hwold).mono hmono
      exact (reach_w x hx).trans (reach_w y hy).symm
  · rw [vertexLinkVerts_insert_of_not_mem hv] at hx hy
    exact (hτ v x hx y hy).mono hmono

/-- **Vertex rule-out core.** Two apexes present in `τ'` but non-reachable in a
larger `τ` forbid `VertexLinkConnected τ'`.  Applied with `τ' = M−u ⊆ M`: deleting
`u` cannot reconnect a split vertex-link, so a pinch in `M` survives in `M−u`. -/
lemma not_vertexLinkConnected_of_subset {τ τ' : Finset (Finset V)} (h : τ' ⊆ τ)
    {v x y : V} (hx : x ∈ vertexLinkVerts τ' v) (hy : y ∈ vertexLinkVerts τ' v)
    (hnr : ¬ (vertexLinkGraph τ v).Reachable x y) :
    ¬ VertexLinkConnected τ' :=
  fun hC => hnr (vertexLink_reachable_mono h v (hC v x hx y hy))

/-! ## Normal and clean 3-complexes

`TriangleBounded3 ∧ EdgeLinkConnected` is still not the right invariant — it omits
vertex links (two tets sharing one vertex pass both yet pinch).  The honest
condition is `Clean3Complex`: pure, triangle-bounded, and *normal* (both links
connected).  This is what the public shellability predicate must certify. -/

/-- `Pure3 τ`: every tet has 4 vertices (genuine 3-dimensionality). -/
def Pure3 (τ : Finset (Finset V)) : Prop := ∀ t ∈ τ, t.card = 4

/-- `Normal3 τ`: connected edge links *and* connected vertex links — the normal
(no-pinch) condition.  `TriangleBounded3 ∧ EdgeLinkConnected` alone is not normal. -/
def Normal3 (τ : Finset (Finset V)) : Prop :=
  EdgeLinkConnected τ ∧ VertexLinkConnected τ

/-- `Clean3Complex τ`: pure, triangle-bounded, and normal — the honest
"simplicial triangulation of a 3-ball" invariant the public shelling must carry,
not the boundary-only trace.  Exposed under the `Is`-prefixed names
`IsClean3Complex` / `IsNormal3Psman` as the preferred public vocabulary. -/
def Clean3Complex (τ : Finset (Finset V)) : Prop :=
  Pure3 τ ∧ TriangleBounded3 τ ∧ Normal3 τ

/-- **`IsClean3Complex`** — the clean (normal) 3-complex condition: pure, every triangle in one or two
tets, and *both* links connected (`VertexLinkConnected` and `EdgeLinkConnected`).  This is the local
combinatorial-manifold condition; preferred public name for `Clean3Complex`. -/
abbrev IsClean3Complex (τ : Finset (Finset V)) : Prop := Clean3Complex τ

/-- **`IsNormal3Psman`** — synonym for `IsClean3Complex`: a normal 3-pseudomanifold (triangle-bounded
with both links connected, pure). -/
abbrev IsNormal3Psman (τ : Finset (Finset V)) : Prop := Clean3Complex τ

lemma pure3_singleton {t : Finset V} (ht : t.card = 4) :
    Pure3 ({t} : Finset (Finset V)) := by
  intro s hs; rw [Finset.mem_singleton] at hs; subst hs; exact ht

lemma normal3_singleton {t : Finset V} (ht : t.card = 4) :
    Normal3 ({t} : Finset (Finset V)) :=
  ⟨edgeLinkConnected_singleton ht, vertexLinkConnected_singleton t⟩

/-- The base of the clean induction: one tetrahedron is a clean 3-complex. -/
lemma clean3Complex_singleton {t : Finset V} (ht : t.card = 4) :
    Clean3Complex ({t} : Finset (Finset V)) :=
  ⟨pure3_singleton ht, isPseudomanifold_singleton t, normal3_singleton ht⟩

/-- **Clean insertion preserves `Clean3Complex`.** The combiner bundling the three
per-dimension preservation lemmas (triangle count, edge link, vertex link).  These
three compatibilities are discharged from the chain geometry of the shelling step
(unit boundary ⇒ a boundary face lies in exactly one tet); `CleanGlueStep.clean`
gives the no-rogue *shape* but not these quantitative facts on its own. -/
lemma clean3Complex_insert {τ : Finset (Finset V)} {t : Finset V}
    (ht : t.card = 4) (httτ : t ∉ τ) (hτ : Clean3Complex τ)
    (hpmc : ∀ f, f.card = 3 → f ⊆ t → faceCount τ f ≤ 1)
    (helc : ∀ e, e ⊆ t → e.card = 2 →
      edgeLinkVerts τ e = ∅ ∨ ((t \ e) ∩ edgeLinkVerts τ e).Nonempty)
    (hvlc : ∀ v ∈ t, vertexLinkVerts τ v = ∅ ∨
      ((t \ {v}) ∩ vertexLinkVerts τ v).Nonempty) :
    Clean3Complex (insert t τ) := by
  obtain ⟨hpure, hpm, hel, hvl⟩ := hτ
  refine ⟨?_, isPseudomanifold_insert hpm httτ hpmc,
    edgeLinkConnected_insert ht hel helc, vertexLinkConnected_insert hvl hvlc⟩
  intro s hs
  rcases Finset.mem_insert.mp hs with rfl | hsτ
  · exact ht
  · exact hpure s hsτ

end Taut
