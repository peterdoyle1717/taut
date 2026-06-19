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

/-! ## Clean reassembly — the clean analogues of the weak snoc lemmas

These mirror `Ball.ShellFrom_snoc`/`IsShelling_snoc` and the `Theorem3` grafts
(`FreelyShellable.insert_of_glueStep`, `…exists_shelling_insert_of_glueStep_old`),
threading the accumulated tet-set `τ` that `CleanShellFrom` carries. -/

/-- Append one clean glue step to a `CleanShellFrom`. The step must glue onto the
fully accumulated tet-set `τ₀ ∪ l.toFinset`. -/
lemma CleanShellFrom_snoc {τ₀ B₀ B B' : Finset (Finset V)} {l : List (Finset V)}
    {e : Finset V} (h : CleanShellFrom τ₀ B₀ l B)
    (hg : CleanGlueStep e (τ₀ ∪ l.toFinset) B B') :
    CleanShellFrom τ₀ B₀ (l ++ [e]) B' := by
  induction l generalizing τ₀ B₀ with
  | nil =>
      simp only [List.toFinset_nil, Finset.union_empty] at hg
      simp only [CleanShellFrom] at h
      subst h
      exact ⟨B', hg, rfl⟩
  | cons t l ih =>
      obtain ⟨B₁, hstep, hrest⟩ := h
      have hg' : CleanGlueStep e ((insert t τ₀) ∪ l.toFinset) B B' := by
        have hset : (insert t τ₀) ∪ l.toFinset = τ₀ ∪ (t :: l).toFinset := by
          rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
        rwa [hset]
      exact ⟨B₁, hstep, ih hrest hg'⟩

/-- Append one clean glue step to a clean shelling. -/
lemma IsCleanShelling_snoc {l : List (Finset V)} {B B' : Finset (Finset V)}
    {e : Finset V} (h : IsCleanShelling l B)
    (hg : CleanGlueStep e l.toFinset B B') :
    IsCleanShelling (l ++ [e]) B' := by
  cases l with
  | nil => exact h.elim
  | cons t r =>
      obtain ⟨ht, hsf⟩ := h
      have hg' : CleanGlueStep e ({t} ∪ r.toFinset) B B' := by
        have hset : ({t} : Finset (Finset V)) ∪ r.toFinset = (t :: r).toFinset := by
          rw [List.toFinset_cons, Finset.singleton_union]
        rwa [hset]
      exact ⟨ht, CleanShellFrom_snoc hsf hg'⟩

/-- **Old-target clean snoc.** A freely clean shellable `τ` and a fresh clean-glue
tet `e` give, for any old target `s ∈ τ`, a clean shelling of `insert e τ` starting
at `s` — namely `(τ's clean shelling from s) ++ [e]`. The clean analogue of
`FreelyShellable.exists_shelling_insert_of_glueStep_old`. -/
lemma FreelyCleanShellable.exists_shelling_insert_of_cleanGlueStep_old
    {τ B B' : Finset (Finset V)} {e s : Finset V}
    (hfree : FreelyCleanShellable τ B) (hg : CleanGlueStep e τ B B')
    (heτ : e ∉ τ) (hsτ : s ∈ τ) :
    ∃ l : List (Finset V), l.head? = some s ∧ l.toFinset = insert e τ ∧ l.Nodup ∧
      IsCleanShelling l B' := by
  obtain ⟨l, hhead, hlτ, hnodup, hsh⟩ := hfree s hsτ
  refine ⟨l ++ [e], ?_, ?_, ?_, IsCleanShelling_snoc hsh (hlτ ▸ hg)⟩
  · cases l with
    | nil => exact absurd hsh (by simp [IsCleanShelling])
    | cons a r => rw [List.cons_append]; exact hhead
  · rw [List.toFinset_append, hlτ]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_singleton]
    tauto
  · refine hnodup.append (List.nodup_singleton e) ?_
    rw [List.disjoint_left]
    intro a ha
    simp only [List.mem_singleton]
    rintro rfl
    exact heτ (hlτ ▸ List.mem_toFinset.mpr ha)

/-- **Clean case-1 stick.** A free clean sticker ball `τ` (boundary `B`) plus a
fresh `CleanGlueStep` tet `t` is a free clean sticker ball with `t` adjoined. For an
old target the shelling is `(old clean shelling from target) ++ [t]`; for target `t`
the shelling is `t :: (a clean shelling of τ onto `B'` from `tetFaces t`)` — that
bridge-start relative clean shelling is the hypothesis `hstart_t`. The clean
analogue of `FreelyShellable.insert_of_glueStep`. -/
lemma FreelyCleanShellable.insert_of_cleanGlueStep {τ B B' : Finset (Finset V)}
    {t : Finset V} (hfree : FreelyCleanShellable τ B) (hg : CleanGlueStep t τ B B')
    (hstart_t : ∃ l : List (Finset V), l.toFinset = τ ∧ l.Nodup ∧
      CleanShellFrom {t} (tetFaces t) l B') :
    FreelyCleanShellable (insert t τ) B' := by
  intro s hs
  rcases Finset.mem_insert.mp hs with rfl | hsτ
  · -- target is the new tet (`rcases rfl` substituted the binder `t := s`)
    obtain ⟨l, hlτ, hnodup, hsf⟩ := hstart_t
    refine ⟨s :: l, rfl, ?_, ?_, hg.weak.card4, hsf⟩
    · rw [List.toFinset_cons, hlτ]
    · exact List.nodup_cons.mpr ⟨fun hc => hg.newTet (hlτ ▸ List.mem_toFinset.mpr hc), hnodup⟩
  · -- target is an old tet `s ∈ τ`
    exact FreelyCleanShellable.exists_shelling_insert_of_cleanGlueStep_old hfree hg
      hg.newTet hsτ

/-! ## Clean boundary-piece transport — the clean analogues of the weak
`GlueStep.erase_union_disjoint` / `ShellFrom_erase_union_disjoint` (`Ball`).

The `CleanGlueStep` fields `newTet`/`hpmc`/`helc`/`hvlc` depend only on the
accumulated set `τ`, never on the boundary, so a boundary-only transport leaves
them untouched.  Only `weak` (a `BoundaryGlueStep`, i.e. a `GlueStep`) and
`clean` (which reads `tetFaces t ∩ B`) move, and both follow from the same
tet-avoidance disjointness used in the weak lemmas. -/

/-- One **clean** glue step, transported by erasing the interface face `γ` and
adjoining the disjoint piece `K`, when the tet avoids both.  Mirrors
`GlueStep.erase_union_disjoint` (`Ball`) at the clean level: the `τ`-only fields
are unchanged, and the `clean` field rides on the same intersection rewrite. -/
lemma CleanGlueStep.erase_union_disjoint {t γ : Finset V} {τ B B' K : Finset (Finset V)}
    (hg : CleanGlueStep t τ B B') (hdisj : Disjoint (tetFaces t) (insert γ K)) :
    CleanGlueStep t τ (B.erase γ ∪ K) (B'.erase γ ∪ K) where
  weak := hg.weak.erase_union_disjoint hdisj
  newTet := hg.newTet
  hpmc := hg.hpmc
  helc := hg.helc
  hvlc := hg.hvlc
  clean := by
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
    rw [heq]; exact hg.clean

/-- **Clean boundary-piece transport.** If none of the tets in a clean relative
shelling touches `γ` or the ambient piece `K`, the clean shelling is unchanged
after replacing the carried boundary face `γ` by `K`.  Mirrors
`ShellFrom_erase_union_disjoint` (`Ball`); because `CleanShellFrom` threads the
accumulated tet-set, the induction generalizes `τ₀` (along with the boundaries
`B₀`/`B`) so the `cons` step's IH applies to `insert t τ₀`. -/
lemma CleanShellFrom_erase_union_disjoint {γ : Finset V}
    {K : Finset (Finset V)} {l : List (Finset V)} :
    ∀ {τ₀ B₀ B : Finset (Finset V)}, CleanShellFrom τ₀ B₀ l B →
      (∀ t ∈ l, Disjoint (tetFaces t) (insert γ K)) →
      CleanShellFrom τ₀ (B₀.erase γ ∪ K) l (B.erase γ ∪ K) := by
  induction l with
  | nil =>
      intro τ₀ B₀ B h _
      simp only [CleanShellFrom] at h ⊢
      rw [h]
  | cons t l ih =>
      intro τ₀ B₀ B h hd
      simp only [CleanShellFrom] at h ⊢
      obtain ⟨B₁, hstep, hrest⟩ := h
      exact ⟨B₁.erase γ ∪ K, hstep.erase_union_disjoint (hd t (List.mem_cons.mpr (Or.inl rfl))),
        ih hrest (fun u hu => hd u (List.mem_cons.mpr (Or.inr hu)))⟩

end Taut
