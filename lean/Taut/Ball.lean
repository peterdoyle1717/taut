import Taut.Complex2

/-!
# `GlueStep`: the weak boundary glue primitive

This file holds the single weak boundary-trace primitive on which the clean
shelling layer (`Taut.CleanShelling`) is built: `GlueStep`, one combinatorial
gluing step recorded purely as a boundary update, plus the face abbreviation
`tetFaces`.

**Weak by design.** A `GlueStep` constrains a new tet only against the *current
boundary* `B` (its shared card-3 faces and the symmetric-difference update of the
boundary); it never sees the accumulated tet-set, so on its own it certifies
**nothing** about cleanness, normality, connected vertex/edge links, or actual
ballness.  It is boundary bookkeeping, not a ball certificate.  The clean
predicates that carry the manifold content — `CleanGlueStep` (which wraps a
`GlueStep` in its `weak` field), `IsCleanShelling`, `IsCleanBall`,
`FreelyCleanShellable`, `IsStickerball`, `IsAnyrootedStickerball` — live in
`Taut.CleanShelling`, and the public Theorem 2/3 endpoints conclude those, never
the weak predicate here.

Faces of a tetrahedron `t` (a 4-element set) are its card-3 subsets,
`t.powersetCard 3` (`tetFaces`).  When `t` is glued onto a ball whose boundary is
`B`, the faces of `t` already in `B` become interior and the rest are exposed: the
new boundary is the symmetric difference `(B \ tetFaces t) ∪ (tetFaces t \ B)`.

(The earlier weak shelling family — `ShellFrom`, `IsShelling`, `IsBall`,
`FreelyShellable`, their reassembly lemmas, and the `Boundary*` aliases — has been
removed as dead; the sole surviving reassembly lemma is
`GlueStep.erase_union_disjoint`, which the clean layer lifts to
`CleanGlueStep.erase_union_disjoint`.  See `notes/weak-predicate-cleanup.md`.)
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

/-- The four triangular faces of a tetrahedron `t` (the card-3 subsets). -/
abbrev tetFaces (t : Finset V) : Finset (Finset V) := t.powersetCard 3

/-- **Weak boundary-trace primitive** (boundary bookkeeping only — asserts nothing
about cleanness, normality, connected links, or ballness; the clean layer wraps it
as `CleanGlueStep.weak`).  One gluing step of a shelling: tet `t` is glued onto a
ball whose boundary is `B`, producing the ball with boundary `B'`.

* `card4` — `t` is a tetrahedron (4 vertices);
* `shared` — `t` meets the current boundary in **one or two** of its faces
  (type 1 or 2; type 3 is excluded, as it would create an interior vertex);
* `newBdry` — the new boundary is the symmetric difference of `B` and the
  faces of `t`: shared faces become interior, the rest are exposed.

A glue step is a **purely combinatorial** stick; it does not assert the new
boundary is a 2-sphere (that holds, but is the separate, deferred fact
`glueStep_preserves_isSphere2`, not needed for the main theorem). -/
structure GlueStep (t : Finset V) (B B' : Finset (Finset V)) : Prop where
  card4 : t.card = 4
  shared : (tetFaces t ∩ B).card = 1 ∨ (tetFaces t ∩ B).card = 2
  newBdry : B' = (B \ tetFaces t) ∪ (tetFaces t \ B)

/-- One glue step, transported by erasing the interface face `γ` and adjoining the
disjoint piece `K`, when the tet avoids both.  The one reassembly lemma still in
use: `CleanGlueStep.erase_union_disjoint` lifts it to the clean layer (the degree-3
star-start boundary transport). -/
lemma GlueStep.erase_union_disjoint {t γ : Finset V} {B B' K : Finset (Finset V)}
    (hg : GlueStep t B B') (hdisj : Disjoint (tetFaces t) (insert γ K)) :
    GlueStep t (B.erase γ ∪ K) (B'.erase γ ∪ K) where
  card4 := hg.card4
  shared := by
    have heq : tetFaces t ∩ (B.erase γ ∪ K) = tetFaces t ∩ B := by
      ext s
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro ⟨hsT, (⟨_, hsB⟩ | hsK)⟩
        · exact ⟨hsT, hsB⟩
        · exact absurd hsK (fun h => (Finset.disjoint_left.mp hdisj) hsT (Finset.mem_insert_of_mem h))
      · rintro ⟨hsT, hsB⟩
        refine ⟨hsT, Or.inl ⟨?_, hsB⟩⟩
        intro hsγ
        exact (Finset.disjoint_left.mp hdisj) hsT (hsγ ▸ Finset.mem_insert_self γ K)
    rw [heq]; exact hg.shared
  newBdry := by
    have hγT : γ ∉ tetFaces t :=
      fun h => (Finset.disjoint_left.mp hdisj) h (Finset.mem_insert_self γ K)
    have hKT : ∀ ⦃x⦄, x ∈ tetFaces t → x ∉ K :=
      fun x hx hxK => (Finset.disjoint_left.mp hdisj) hx (Finset.mem_insert_of_mem hxK)
    rw [hg.newBdry]
    ext s
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
    by_cases hsT : s ∈ tetFaces t
    · have hsγ : s ≠ γ := fun h => hγT (h ▸ hsT)
      have hsK : s ∉ K := hKT hsT
      tauto
    · tauto

/-! ## `BoundaryGlueStep` — the weak boundary-bookkeeping name

`GlueStep` is the sole surviving weak boundary-trace predicate.  It is **not** a
ball or shellability claim: it only constrains a new tet against the *current
boundary* `B` (shared card-3 faces, symmetric-difference update); it never sees
the accumulated tet-set, so it cannot detect a rogue lower-dimensional
intersection with an already-built tet, and it asserts **nothing** about
cleanness, normality, connected vertex/edge links, or actual ballness.  The clean
public predicates (`CleanGlueStep`, `IsCleanShelling`, `IsCleanBall`,
`FreelyCleanShellable`, `IsStickerball`, `IsAnyrootedStickerball`) live in
`Taut.CleanShelling`; a `CleanGlueStep` carries a `BoundaryGlueStep` in its `weak`
field.  Public ball/stickerball conclusions use `IsStickerball` /
`IsAnyrootedStickerball`, never this weak predicate. -/

/-- Boundary (weak) glue step — the explicit weak-layer name for `GlueStep`, the
thing `CleanGlueStep.weak` carries.  Weak boundary bookkeeping only (see the
section note above): asserts nothing about cleanness, normality, connected links,
or ballness. -/
abbrev BoundaryGlueStep (t : Finset V) (B B' : Finset (Finset V)) : Prop :=
  GlueStep t B B'

end Taut
