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

/-- Inserting a fresh tet bumps the count of exactly the faces it contains. -/
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

/-- A single tetrahedron is a pseudomanifold (each triangle is in at most one tet). -/
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
condition the forward construction must supply at each shelling step; here it is
discharged into the bookkeeping, isolating the genuine content (proving `hclean`
for the flipped-back eligible tet) from the mechanical part. -/
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

/-- Edge-link graphs grow with the tet-set. -/
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

/-- A single tetrahedron is edge-link connected. -/
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

/-! ## The faithful stickerball -/

/-- A **faithful stickerball**: freely shellable *and* genuinely simplicial —
every triangle in at most two tets (`IsPseudomanifold`) and every edge-link
connected (`EdgeLinkConnected`).  This is the invariant the Theorem-2 induction
must carry; the boundary-only `FreelyShellable` alone is too weak (it admits the
re-exposed-face and stray-ring configurations). -/
def IsStickerball (τ B : Finset (Finset V)) : Prop :=
  FreelyShellable τ B ∧ IsPseudomanifold τ ∧ EdgeLinkConnected τ

/-- The base of the induction: one tetrahedron is a stickerball with the
tetrahedron-boundary sphere. -/
lemma isStickerball_singleton {t : Finset V} (ht : t.card = 4) :
    IsStickerball ({t} : Finset (Finset V)) (tetFaces t) := by
  refine ⟨?_, isPseudomanifold_singleton t, edgeLinkConnected_singleton ht⟩
  intro s hs
  rw [Finset.mem_singleton] at hs; subst hs
  exact ⟨[s], rfl, by simp, by simp, ht, rfl⟩

/-! ## Rule-out engines

The two ways re-gluing the eligible tet can spoil simpliciality each reduce, via
minimality, to "a smaller filling `M−u` fails to be a stickerball".  These are the
reusable cores: a surviving over-incident triangle breaks `IsPseudomanifold`, and
a surviving disconnected edge-link breaks `EdgeLinkConnected`. -/

/-- Face incidence is monotone in the tet-set (deleting tets can only lower it). -/
lemma faceCount_le_of_subset {τ τ' : Finset (Finset V)} (h : τ' ⊆ τ) (f : Finset V) :
    faceCount τ' f ≤ faceCount τ f := by
  unfold faceCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- **Triangle rule-out core.** A triangle still in ≥ 3 tets of `τ'` forbids
`IsPseudomanifold τ'`. -/
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

end Taut
