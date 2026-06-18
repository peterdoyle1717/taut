import Taut.Ball
import Taut.Pseudomanifold

/-!
# Clean shellability — the public, by-definition-simplicial shelling

The boundary shelling of `Taut.Ball` is a *boundary trace*: a glue step only
constrains the new tet against the current boundary, so it cannot see a rogue
lower-dimensional intersection with the accumulated complex.  This file adds the
**clean** layer, which threads the accumulated tet-set `τ` and forbids exactly
those rogues: `CleanGlueStep.clean` says every face of the new tet already
present in `τ` lies inside one of the shared boundary triangles.

That single condition rules out, uniformly, all four ways a glue can fail to be
simplicial *as an intersection shape*: doubled tet (`f = t`), rogue old triangle
(`f` card 3), rogue old edge (card 2), rogue old vertex (card 1).  The clean
predicates project to the boundary ones (`.toBoundary…`), so the banked reassembly
lemmas remain usable.

Per the G1 audit (2026-06-18, codex session 019ed979) `CleanGlueStep.clean` is the
correct no-rogue *shape* but does **not** by itself supply the quantitative
compatibilities (`faceCount ≤ 1`, link attachment) that `clean3Complex_insert`
needs — those are chain facts (a boundary face of a unit chain lies in exactly one
tet).  So `CleanGlueStep` **carries them as extra fields** (`newTet`, `hpmc`,
`helc`, `hvlc`), produced by the chain geometry where the step is built.  This makes
the clean shelling **self-certifying**: its prefixes are `Clean3Complex` with no
further chain input (`CleanShellFrom.clean3Complex`, `IsCleanBall.clean3Complex`),
and downstream shelling theory never needs to know about chains.

The exported public predicates of Theorem 2/3 are these clean ones
(`IsCleanBall`, `FreelyCleanShellable`), never the boundary trace.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- One **clean** glue step.  Beyond the boundary glue (`weak`) and the no-rogue
*shape* condition (`clean` — every face of `t` already in `τ` lies in a shared
boundary triangle, i.e. the old complex meets `t` only in the closure of the shared
disk), it carries the *quantitative* clean-insert certificates that
`clean3Complex_insert` consumes.  Per the G1 audit (2026-06-18, session 019ed979)
these do **not** follow from `clean` alone — they are produced by the chain geometry
where the step is built — so they are explicit fields, making the clean shelling
self-certifying. -/
structure CleanGlueStep (t : Finset V) (τ B B' : Finset (Finset V)) : Prop where
  /-- the underlying boundary glue step (one or two shared faces, symmetric difference). -/
  weak : BoundaryGlueStep t B B'
  /-- no rogue old face: every face of `t` already in `τ` lies in a shared boundary triangle. -/
  clean : ∀ f, f ⊆ t → (∃ s ∈ τ, f ⊆ s) → ∃ g ∈ tetFaces t ∩ B, f ⊆ g
  /-- `t` is fresh (rules out a doubled tet). -/
  newTet : t ∉ τ
  /-- each triangle of `t` lies in ≤ 1 old tet (so triangle-count stays ≤ 2). -/
  hpmc : ∀ f, f.card = 3 → f ⊆ t → faceCount τ f ≤ 1
  /-- each edge of `t` is new to `τ` or already shares an apex with `τ`'s edge-link there. -/
  helc : ∀ e, e ⊆ t → e.card = 2 →
    edgeLinkVerts τ e = ∅ ∨ ((t \ e) ∩ edgeLinkVerts τ e).Nonempty
  /-- each vertex of `t` is new to `τ` or already shares an apex with `τ`'s vertex-link there. -/
  hvlc : ∀ v ∈ t, vertexLinkVerts τ v = ∅ ∨
    ((t \ {v}) ∩ vertexLinkVerts τ v).Nonempty

/-- Clean shelling from boundary `B₀`, **threading the accumulated tet-set `τ`**:
each step glues onto the set built so far, then recurses on `insert t τ`. -/
def CleanShellFrom :
    Finset (Finset V) → Finset (Finset V) → List (Finset V) → Finset (Finset V) → Prop
  | _, B₀, [],     B => B = B₀
  | τ, B₀, t :: l, B => ∃ B₁, CleanGlueStep t τ B₀ B₁ ∧ CleanShellFrom (insert t τ) B₁ l B

/-- A clean shelling with final boundary `B`: the head tet is the initial
tetrahedron (accumulated set `{t}`, boundary `tetFaces t`, no glue step), and the
rest are glued on cleanly in order. -/
def IsCleanShelling : List (Finset V) → Finset (Finset V) → Prop
  | [],     _ => False
  | t :: l, B => t.card = 4 ∧ CleanShellFrom {t} (tetFaces t) l B

/-- A *clean ball*: a tet-set admitting a clean shelling (a nodup ordering of its
tets gluing up cleanly to boundary `B`). -/
def IsCleanBall (τ B : Finset (Finset V)) : Prop :=
  ∃ l : List (Finset V), l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B

/-- *Freely clean shellable*: **any** tet can serve as the head of a clean
shelling.  This is the public free-sticker-ball predicate Theorem 3 exports. -/
def FreelyCleanShellable (τ B : Finset (Finset V)) : Prop :=
  ∀ t ∈ τ, ∃ l : List (Finset V),
    l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B

/-! ## Projection to boundary shelling — keeps the banked reassembly usable -/

/-- A clean glue step is a boundary glue step. -/
lemma CleanGlueStep.toBoundary {t : Finset V} {τ B B' : Finset (Finset V)}
    (h : CleanGlueStep t τ B B') : BoundaryGlueStep t B B' := h.weak

/-- A clean shelling-from is a boundary shelling-from (forget the cleanliness). -/
lemma CleanShellFrom.toBoundaryShellFrom {τ B₀ : Finset (Finset V)}
    {l : List (Finset V)} {B : Finset (Finset V)}
    (h : CleanShellFrom τ B₀ l B) : BoundaryShellFrom B₀ l B := by
  induction l generalizing τ B₀ with
  | nil => exact h
  | cons t l ih =>
      obtain ⟨B₁, hg, hrest⟩ := h
      exact ⟨B₁, hg.weak, ih hrest⟩

/-- A clean shelling is a boundary shelling. -/
lemma IsCleanShelling.toBoundaryIsShelling {l : List (Finset V)} {B : Finset (Finset V)}
    (h : IsCleanShelling l B) : BoundaryIsShelling l B := by
  cases l with
  | nil => exact h.elim
  | cons t l => obtain ⟨h1, h2⟩ := h; exact ⟨h1, h2.toBoundaryShellFrom⟩

/-- A clean ball is a boundary ball. -/
lemma IsCleanBall.toBoundaryIsBall {τ B : Finset (Finset V)}
    (h : IsCleanBall τ B) : BoundaryIsBall τ B := by
  obtain ⟨l, hl, hn, hsh⟩ := h
  exact ⟨l, hl, hn, hsh.toBoundaryIsShelling⟩

/-- A freely clean shellable set is freely (boundary) shellable. -/
lemma FreelyCleanShellable.toBoundaryFreelyShellable {τ B : Finset (Finset V)}
    (h : FreelyCleanShellable τ B) : BoundaryFreelyShellable τ B := by
  intro t ht
  obtain ⟨l, hhead, hl, hn, hsh⟩ := h t ht
  exact ⟨l, hhead, hl, hn, hsh.toBoundaryIsShelling⟩

/-! ## A single tetrahedron is a (freely) clean ball -/

/-- A single tetrahedron is a clean shelling with the tetrahedron-boundary sphere. -/
lemma isCleanShelling_singleton {t : Finset V} (ht : t.card = 4) :
    IsCleanShelling [t] (tetFaces t) := ⟨ht, rfl⟩

/-- A single tetrahedron is a clean ball. -/
lemma isCleanBall_singleton {t : Finset V} (ht : t.card = 4) :
    IsCleanBall ({t} : Finset (Finset V)) (tetFaces t) :=
  ⟨[t], by simp, by simp, isCleanShelling_singleton ht⟩

/-- A single tetrahedron is freely clean shellable. -/
lemma freelyCleanShellable_singleton {t : Finset V} (ht : t.card = 4) :
    FreelyCleanShellable ({t} : Finset (Finset V)) (tetFaces t) := by
  intro t' ht'
  rw [Finset.mem_singleton] at ht'
  subst t'
  exact ⟨[t], by simp, by simp, by simp, isCleanShelling_singleton ht⟩

/-! ## Self-certification: clean prefixes are `Clean3Complex`

The quantitative fields of `CleanGlueStep` feed `clean3Complex_insert`, so a clean
shelling carries the honest manifold invariant with **no further chain input** —
the predicate certifies cleanliness by itself. -/

/-- One clean glue step preserves `Clean3Complex`. -/
lemma CleanGlueStep.clean3Complex {t : Finset V} {τ B B' : Finset (Finset V)}
    (hstep : CleanGlueStep t τ B B') (hτ : Clean3Complex τ) :
    Clean3Complex (insert t τ) :=
  clean3Complex_insert hstep.weak.card4 hstep.newTet hτ hstep.hpmc hstep.helc hstep.hvlc

/-- **Clean shelling prefixes are `Clean3Complex`.** Fold the per-step preservation
along the threaded accumulation: starting from a clean `τ`, gluing the tets of `l`
yields the clean complex `τ ∪ l.toFinset`. -/
lemma CleanShellFrom.clean3Complex {τ B₀ : Finset (Finset V)} {l : List (Finset V)}
    {B : Finset (Finset V)} (hτ : Clean3Complex τ) (h : CleanShellFrom τ B₀ l B) :
    Clean3Complex (τ ∪ l.toFinset) := by
  induction l generalizing τ B₀ with
  | nil => simp only [List.toFinset_nil, Finset.union_empty]; exact hτ
  | cons t l ih =>
      obtain ⟨B₁, hstep, hrest⟩ := h
      have hrec := ih (hstep.clean3Complex hτ) hrest
      rw [Finset.insert_union] at hrec
      rw [List.toFinset_cons, Finset.union_insert]
      exact hrec

/-- A clean shelling's tet-set is `Clean3Complex`. -/
lemma IsCleanShelling.clean3Complex {l : List (Finset V)} {B : Finset (Finset V)}
    (h : IsCleanShelling l B) : Clean3Complex l.toFinset := by
  cases l with
  | nil => exact h.elim
  | cons t l =>
      obtain ⟨ht, hsh⟩ := h
      have h2 := CleanShellFrom.clean3Complex (clean3Complex_singleton ht) hsh
      rw [Finset.singleton_union] at h2
      rwa [List.toFinset_cons]

/-- **A clean ball is a clean 3-complex** — the public predicate self-certifies the
honest manifold invariant (no chain hypothesis). -/
lemma IsCleanBall.clean3Complex {τ B : Finset (Finset V)} (h : IsCleanBall τ B) :
    Clean3Complex τ := by
  obtain ⟨l, hl, _, hsh⟩ := h
  rw [← hl]; exact hsh.clean3Complex

/-- **A freely clean shellable set is a clean 3-complex.** -/
lemma FreelyCleanShellable.clean3Complex {τ B : Finset (Finset V)}
    (h : FreelyCleanShellable τ B) (hτ : τ.Nonempty) : Clean3Complex τ := by
  obtain ⟨t, ht⟩ := hτ
  obtain ⟨l, _, hl, _, hsh⟩ := h t ht
  rw [← hl]; exact hsh.clean3Complex

end Taut
