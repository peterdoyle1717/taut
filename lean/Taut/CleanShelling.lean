import Taut.Ball
import Taut.Pseudomanifold

/-!
# Clean shellability — the public, by-definition-simplicial shelling

The **clean** layer threads the accumulated tet-set `τ` and forbids rogue
lower-dimensional intersections: `CleanGlueStep.clean` says every face of the new
tet already present in `τ` lies inside one of the shared boundary triangles.

`CleanGlueStep.clean` is the correct no-rogue *shape* but does **not** by itself
supply the quantitative compatibilities (`faceCount ≤ 1`, link attachment) that
`clean3Complex_insert` needs.  So `CleanGlueStep` **carries them as extra fields**
(`newTet`, `hpmc`, `helc`, `hvlc`).  This makes the clean shelling
**self-certifying**: its prefixes are `Clean3Complex` with no further input
(`CleanShellFrom.clean3Complex`, `IsCleanBall.clean3Complex`).

The exported public predicates of Theorem 2/3 are these clean ones
(`IsCleanBall`, `FreelyCleanShellable`).
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- One **clean** glue step.  Beyond the boundary glue (`weak`) and the no-rogue
*shape* condition (`clean` — every face of `t` already in `τ` lies in a shared
boundary triangle), it carries the *quantitative* clean-insert certificates that
`clean3Complex_insert` consumes.  These do **not** follow from `clean` alone, so
they are explicit fields. -/
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

/-! ## Stickerball predicates (the combinatorial B³ certificate) -/

/-- A **stickerball**: a shellable clean 3-complex with nonempty boundary.  Concretely `IsCleanBall`
(a clean shelling exists — building *up* by sticking tetrahedra on, the reverse of shucking down,
each tetrahedron after the first glued on along **one or two boundary triangles** via `CleanGlueStep`,
whose `weak` field is a `GlueStep` sharing a 1- or 2-triangle face with the running boundary) with
a nonempty boundary `B`.  Being an `IsCleanBall` it is in particular an `IsClean3Complex`
(pure, every triangle in ≤ 2 tets, connected vertex *and* edge links) — see `IsStickerball.isClean3Complex`.

By the standard PL theorem that a shellable normal 3-pseudomanifold with nonempty boundary is a PL
ball, this is the combinatorial certificate for a triangulation of `B³`.  This project proves the
combinatorial certificate; it does **not** formalize that external PL-homeomorphism theorem (see
`notes/future-projects.md`). -/
def IsStickerball (τ B : Finset (Finset V)) : Prop :=
  IsCleanBall τ B ∧ B.Nonempty

/-- An **anyrooted stickerball** is a stickerball whose shelling may start with any prescribed
tetrahedron (`FreelyCleanShellable`).  "Stickerball" by itself is *not* anyrooted — that is the
strengthened property. -/
def IsAnyrootedStickerball (τ B : Finset (Finset V)) : Prop :=
  IsStickerball τ B ∧ FreelyCleanShellable τ B

lemma IsAnyrootedStickerball.toStickerball {τ B : Finset (Finset V)}
    (h : IsAnyrootedStickerball τ B) : IsStickerball τ B := h.1

lemma IsAnyrootedStickerball.freelyCleanShellable {τ B : Finset (Finset V)}
    (h : IsAnyrootedStickerball τ B) : FreelyCleanShellable τ B := h.2

/-- A **rooted stickerball** at `t`: a stickerball (`IsStickerball`) that, in addition, admits a
*monotone* clean shelling whose first tetrahedron is `t` — every later tetrahedron is glued on along
one or two boundary triangles (`CleanGlueStep`).  This is the per-root slice of `FreelyCleanShellable`
(the round-3 writeup audit noted "rooted at `t`" was not yet a standalone predicate; this names it). -/
def IsRootedStickerball (τ B : Finset (Finset V)) (t : Finset V) : Prop :=
  IsStickerball τ B ∧
    ∃ l : List (Finset V), l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B

lemma IsRootedStickerball.toStickerball {τ B : Finset (Finset V)} {t : Finset V}
    (h : IsRootedStickerball τ B t) : IsStickerball τ B := h.1

/-- An **anyroot stickerball** (public name for `IsAnyrootedStickerball`): a stickerball that is
rooted at *every* one of its tetrahedra.  It is a **ball** certificate, not a sphere-shelling
certificate — each shelling is a *monotone* clean shelling (every tetrahedron after the first is glued
on along one or two boundary triangles) and the result carries a nonempty boundary `B`.  This is the
public face Theorem 3 exports for a taut filling. -/
abbrev IsAnyrootStickerball (τ B : Finset (Finset V)) : Prop := IsAnyrootedStickerball τ B

/-- An anyroot stickerball is rooted at every tetrahedron of `τ`. -/
lemma IsAnyrootStickerball.rooted {τ B : Finset (Finset V)}
    (h : IsAnyrootStickerball τ B) : ∀ t ∈ τ, IsRootedStickerball τ B t :=
  fun t ht => ⟨h.1, h.2 t ht⟩

/-- Conversely, a stickerball rooted at every tetrahedron is an anyroot stickerball. -/
lemma IsAnyrootStickerball.of_forall_rooted {τ B : Finset (Finset V)}
    (hB : IsStickerball τ B) (h : ∀ t ∈ τ, IsRootedStickerball τ B t) :
    IsAnyrootStickerball τ B :=
  ⟨hB, fun t ht => (h t ht).2⟩

/-! ## A single tetrahedron is a (freely) clean ball -/

lemma isCleanShelling_singleton {t : Finset V} (ht : t.card = 4) :
    IsCleanShelling [t] (tetFaces t) := ⟨ht, rfl⟩

lemma isCleanBall_singleton {t : Finset V} (ht : t.card = 4) :
    IsCleanBall ({t} : Finset (Finset V)) (tetFaces t) :=
  ⟨[t], by simp, by simp, isCleanShelling_singleton ht⟩

lemma freelyCleanShellable_singleton {t : Finset V} (ht : t.card = 4) :
    FreelyCleanShellable ({t} : Finset (Finset V)) (tetFaces t) := by
  intro t' ht'
  rw [Finset.mem_singleton] at ht'
  subst t'
  exact ⟨[t], by simp, by simp, by simp, isCleanShelling_singleton ht⟩

/-! ## Self-certification: clean prefixes are `Clean3Complex`

The quantitative fields of `CleanGlueStep` feed `clean3Complex_insert`, so a clean
shelling carries the manifold invariant with **no further chain input**. -/

lemma CleanGlueStep.clean3Complex {t : Finset V} {τ B B' : Finset (Finset V)}
    (hstep : CleanGlueStep t τ B B') (hτ : Clean3Complex τ) :
    Clean3Complex (insert t τ) :=
  clean3Complex_insert hstep.weak.card4 hstep.newTet hτ hstep.hpmc hstep.helc hstep.hvlc

/-- **Clean shelling prefixes are `Clean3Complex`.** Starting from a clean `τ`,
gluing the tets of `l` yields the clean complex `τ ∪ l.toFinset`. -/
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
manifold invariant (no chain hypothesis). -/
lemma IsCleanBall.clean3Complex {τ B : Finset (Finset V)} (h : IsCleanBall τ B) :
    Clean3Complex τ := by
  obtain ⟨l, hl, _, hsh⟩ := h
  rw [← hl]; exact hsh.clean3Complex

lemma FreelyCleanShellable.clean3Complex {τ B : Finset (Finset V)}
    (h : FreelyCleanShellable τ B) (hτ : τ.Nonempty) : Clean3Complex τ := by
  obtain ⟨t, ht⟩ := hτ
  obtain ⟨l, _, hl, _, hsh⟩ := h t ht
  rw [← hl]; exact hsh.clean3Complex

lemma IsStickerball.isClean3Complex {τ B : Finset (Finset V)} (h : IsStickerball τ B) :
    IsClean3Complex τ := h.1.clean3Complex

lemma IsAnyrootedStickerball.isClean3Complex {τ B : Finset (Finset V)}
    (h : IsAnyrootedStickerball τ B) : IsClean3Complex τ := h.1.isClean3Complex

/-! ## Clean reassembly

These thread the accumulated tet-set `τ` that `CleanShellFrom` carries. -/

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

/-- **`CleanShellFrom` composes.** Glue `l₁` (accumulating from `τ₀`) then `l₂`,
whose accumulator must start at the fully accumulated tet-set `τ₀ ∪ l₁.toFinset`. -/
lemma CleanShellFrom_append {τ₀ B₀ B₁ B : Finset (Finset V)} {l₁ l₂ : List (Finset V)}
    (h₁ : CleanShellFrom τ₀ B₀ l₁ B₁)
    (h₂ : CleanShellFrom (τ₀ ∪ l₁.toFinset) B₁ l₂ B) :
    CleanShellFrom τ₀ B₀ (l₁ ++ l₂) B := by
  induction l₁ generalizing τ₀ B₀ with
  | nil =>
      simp only [CleanShellFrom] at h₁
      subst h₁
      simpa only [List.toFinset_nil, Finset.union_empty, List.nil_append] using h₂
  | cons t l ih =>
      obtain ⟨B', hstep, hrest⟩ := h₁
      refine ⟨B', hstep, ih hrest ?_⟩
      have hset : (insert t τ₀) ∪ l.toFinset = τ₀ ∪ (t :: l).toFinset := by
        rw [List.toFinset_cons, Finset.union_insert, Finset.insert_union]
      rwa [hset]

/-- A *clean relative shelling*: glue the tets of `τ` onto an ambient boundary `B₀`
(threading `τ₀` as the accumulated old tet-set), ending at `B`.  The invariant the
case-2 clean bridge needs. -/
def CleanRelShellingFrom (τ₀ τ B₀ B : Finset (Finset V)) : Prop :=
  ∃ l : List (Finset V), l.toFinset = τ ∧ l.Nodup ∧ CleanShellFrom τ₀ B₀ l B

/-- **Stitch a clean shelling to a clean continuation over a second region.**
Consume a clean shelling `IsCleanShelling l₁ Bmid` (ending at boundary `Bmid`) and a
clean `CleanShellFrom l₁.toFinset Bmid l₂ B` (continuing over the second region with
the first region's tets as the accumulated old set), and produce a single clean
shelling `IsCleanShelling (l₁ ++ l₂) B`. -/
lemma IsCleanShelling_append_cleanShellFrom {l₁ l₂ : List (Finset V)}
    {Bmid B : Finset (Finset V)} (h : IsCleanShelling l₁ Bmid)
    (hf : CleanShellFrom l₁.toFinset Bmid l₂ B) :
    IsCleanShelling (l₁ ++ l₂) B := by
  cases l₁ with
  | nil => exact h.elim
  | cons t r =>
      obtain ⟨ht, hsf⟩ := h
      refine ⟨ht, ?_⟩
      refine CleanShellFrom_append hsf ?_
      have hset : ({t} : Finset (Finset V)) ∪ r.toFinset = (t :: r).toFinset := by
        rw [List.toFinset_cons, Finset.singleton_union]
      rwa [hset]

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
at `s` — namely `(τ's clean shelling from s) ++ [e]`. -/
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
the shelling is `t :: (a clean shelling of τ onto B' from tetFaces t)` — that
bridge-start relative clean shelling is the hypothesis `hstart_t`. -/
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
  · exact FreelyCleanShellable.exists_shelling_insert_of_cleanGlueStep_old hfree hg
      hg.newTet hsτ

/-! ## Clean boundary-piece transport

The `CleanGlueStep` fields `newTet`/`hpmc`/`helc`/`hvlc` depend only on the
accumulated set `τ`, never on the boundary, so a boundary-only transport leaves
them untouched.  Only `weak` (a `BoundaryGlueStep`) and `clean` (which reads
`tetFaces t ∩ B`) move, both following from tet-avoidance disjointness. -/

/-- One **clean** glue step, transported by erasing the interface face `γ` and
adjoining the disjoint piece `K`, when the tet avoids both.  The `τ`-only fields
are unchanged; the `clean` field rides on an intersection rewrite. -/
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
after replacing the carried boundary face `γ` by `K`.  Because `CleanShellFrom`
threads the accumulated tet-set, the induction generalizes `τ₀` (along with the
boundaries `B₀`/`B`) so the `cons` step's IH applies to `insert t τ₀`. -/
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

/-! ## Clean accumulator enlargement across a seam — the case-2 bridge engine

The case-2 clean bridge shells side 1, sticks the bridge tet `e`, then continues
over side 2 — but the side-2 continuation must thread the **enlarged accumulator**
`Δ := insert e M₁.support` (the side-1 tets plus `e`), not side-2 alone.  Each side-2
glue step's four `τ`-only fields must therefore be re-certified against `Δ ∪ (side-2
prefix)`.  The lemmas below transport one such step, then fold the transport along a
`CleanShellFrom`.

The geometry that makes this work (supplied at the call site, abstracted here):
* `Δ` meets the side-2 region `Bside` only inside the bridge face `f₄`
  (`hΔB : ∀ d ∈ Δ, ∀ x ∈ d, x ∈ Bside → x ∈ f₄`).  So any face of a side-2 tet
  `t ⊆ Bside` shared with `Δ` lies in `f₄` (card ≤ 3), killing all triangle/edge/vertex
  cross terms except those inside `f₄`.
* `f₄` itself lies in a unique side-2 tet `t₄` which is shelled **first**, so it is
  always in the accumulator for the later steps; the seam-cleanliness then reduces to
  the side-2 step's own `clean`/`helc`/`hvlc` via that `t₄`.

The whole transport is driven by the single seam hypothesis `hΔB` plus the
`t₄`-in-accumulator invariant `ht₄τ : t₄ ∈ τ`; everything else is the side-2 step's
own field lifted by union-monotonicity. -/

/-- **One clean glue step, prepend a disjoint cross-seam block `Δ`** (tail step).
The side-2 tet `t ⊆ Bside` (`htB`) glues cleanly at `τ` (`hcg`); `Δ` meets `Bside`
only inside the bridge face `f₄` (`hΔB`), the unique `Bside`-tet through `f₄` is
`t₄`, which is already in the accumulator (`ht₄τ`, `hf₄t₄`).  Then the step is clean
at `Δ ∪ τ`:

* **clean** — a face `f ⊆ t` shared with `Δ` lies in `f₄ ⊆ t₄ ∈ τ`, so it is also
  `τ`-shared and the side-2 `clean` field applies;
* **hpmc** — `f₄ ⊄ t` (else `t = t₄ ∈ τ`, but `t ∉ τ`), so the only triangle of `t`
  that `Δ` could carry is absent; the `Δ`-count is `0` and the side-2 bound survives;
* **helc/hvlc** — an edge/vertex with empty `τ`-link and a nonempty `Δ`-link would lie
  in `f₄ ⊆ t₄ ∈ τ`, making the `τ`-link nonempty (contradiction); so the `Δ`-link is
  empty too, or the side-2 nonempty branch lifts by monotonicity. -/
lemma CleanGlueStep.prepend_crossSeam {t f₄ Bside : Finset V} {Δ τ B B' : Finset (Finset V)}
    (hcg : CleanGlueStep t τ B B')
    (hdisj : Disjoint Δ τ) (htΔ : t ∉ Δ)
    (htB : t ⊆ Bside)
    (hΔB : ∀ d ∈ Δ, ∀ x ∈ d, x ∈ Bside → x ∈ f₄)
    {t₄ : Finset V} (ht₄τ : t₄ ∈ τ) (hf₄t₄ : f₄ ⊆ t₄) (ht₄card : t₄.card = 4)
    (hf₄card : f₄.card = 3) (hf₄nott : ¬ f₄ ⊆ t) :
    CleanGlueStep t (Δ ∪ τ) B B' := by
  classical
  have hsharef₄ : ∀ {f : Finset V}, f ⊆ t → (∃ d ∈ Δ, f ⊆ d) → f ⊆ f₄ := by
    rintro f hft ⟨d, hdΔ, hfd⟩ x hxf
    exact hΔB d hdΔ x (hfd hxf) (htB (hft hxf))
  have hshareτ : ∀ {f : Finset V}, f ⊆ t → (∃ d ∈ Δ, f ⊆ d) → ∃ s ∈ τ, f ⊆ s :=
    fun hft hd => ⟨t₄, ht₄τ, (hsharef₄ hft hd).trans hf₄t₄⟩
  -- For the link branches: an `e`/`v` inside `f₄ ⊆ t₄ ∈ τ` already has a nonempty
  -- `τ`-link (`t₄ \ e`, resp. `t₄ \ {v}`, is nonempty), since `t₄` has 4 > |e|,|{v}| verts.
  have hlinkNeτ_edge : ∀ {e : Finset V}, e ⊆ f₄ → e.card = 2 → edgeLinkVerts τ e ≠ ∅ := by
    intro e hef₄ he2
    have hsub : e ⊆ t₄ := hef₄.trans hf₄t₄
    have hcard : (t₄ \ e).card = 2 := by rw [Finset.card_sdiff_of_subset hsub, ht₄card, he2]
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num : 0 < (t₄ \ e).card)
    rw [Finset.mem_sdiff] at hw
    refine Finset.ne_empty_of_mem (a := w) ?_
    simp only [edgeLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter]
    exact ⟨⟨t₄, ⟨ht₄τ, hsub⟩, hw.1⟩, hw.2⟩
  have hlinkNeτ_vert : ∀ {v : V}, v ∈ f₄ → vertexLinkVerts τ v ≠ ∅ := by
    intro v hvf₄
    have hvt₄ : v ∈ t₄ := hf₄t₄ hvf₄
    have hcard : (t₄ \ {v}).card = 3 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hvt₄), ht₄card,
        Finset.card_singleton]
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num : 0 < (t₄ \ {v}).card)
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
    refine Finset.ne_empty_of_mem (a := w) ?_
    simp only [vertexLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter,
      Finset.mem_singleton]
    exact ⟨⟨t₄, ⟨ht₄τ, hvt₄⟩, hw.1⟩, hw.2⟩
  refine
    { weak := hcg.weak
      newTet := ?_
      clean := ?_
      hpmc := ?_
      helc := ?_
      hvlc := ?_ }
  · rintro f hft ⟨s, hs, hfs⟩
    rw [Finset.mem_union] at hs
    refine hcg.clean f hft ?_
    rcases hs with hsΔ | hsτ
    · exact hshareτ hft ⟨s, hsΔ, hfs⟩
    · exact ⟨s, hsτ, hfs⟩
  · intro h
    rcases Finset.mem_union.mp h with hd | hτ
    · exact htΔ hd
    · exact hcg.newTet hτ
  · intro f hf3 hft
    rw [faceCount_union_of_disjoint hdisj]
    have hΔ0 : faceCount Δ f = 0 := by
      apply faceCount_eq_zero
      intro d hdΔ hfd
      have hff₄ : f ⊆ f₄ := hsharef₄ hft ⟨d, hdΔ, hfd⟩
      have hfeq : f = f₄ := Finset.eq_of_subset_of_card_le hff₄ (by rw [hf3, hf₄card])
      exact hf₄nott (hfeq ▸ hft)
    rw [hΔ0, zero_add]
    exact hcg.hpmc f hf3 hft
  · intro e he he2
    rw [edgeLinkVerts_union]
    rcases hcg.helc e he he2 with hempty | ⟨w, hw⟩
    · left
      rw [hempty, Finset.union_empty]
      apply edgeLinkVerts_eq_empty
      intro d hdΔ hed
      exact absurd hempty (hlinkNeτ_edge (hsharef₄ he ⟨d, hdΔ, hed⟩) he2)
    · right
      rw [Finset.mem_inter] at hw
      exact ⟨w, Finset.mem_inter.mpr ⟨hw.1, Finset.mem_union_right _ hw.2⟩⟩
  · intro v hv
    rw [vertexLinkVerts_union]
    rcases hcg.hvlc v hv with hempty | ⟨w, hw⟩
    · left
      rw [hempty, Finset.union_empty]
      apply vertexLinkVerts_eq_empty
      intro d hdΔ hvd
      exact absurd hempty (hlinkNeτ_vert (hΔB d hdΔ v hvd (htB hv)))
    · right
      rw [Finset.mem_inter] at hw
      exact ⟨w, Finset.mem_inter.mpr ⟨hw.1, Finset.mem_union_right _ hw.2⟩⟩

/-- **The cross-seam head glue: the bridge face's tet against the foreign block.**
The unique `Bside`-tet `t₄` through the bridge face `f₄` is glued onto a boundary
`B` that still carries `f₄` (`hf₄B`), against the foreign block `Δ` that meets `Bside`
only inside `f₄` (`hΔB`).  This is the first side-2 step of the case-2 clean bridge:

* **clean** — a face of `t₄` shared with `Δ` lies in `f₄`, and `f₄ ∈ tetFaces t₄ ∩ B`;
* **hpmc** — a card-3 face of `t₄` shared with `Δ` is `f₄` (card), whose `Δ`-count is
  `≤ 1` (`hf₄countΔ`); other triangles are `Δ`-free;
* **helc/hvlc** — an edge/vertex inside `f₄` has the apex `f₄ \ ·` supplied by the
  foreign tet `e ⊇ f₄` (`he_mem`, `hf₄e`); outside `f₄` the `Δ`-link is empty (`hΔB`). -/
lemma cleanGlueStep_crossSeam_head {t₄ f₄ Bside e : Finset V} {Δ B B' : Finset (Finset V)}
    (hweak : BoundaryGlueStep t₄ B B')
    (ht₄Δ : t₄ ∉ Δ) (ht₄B : t₄ ⊆ Bside) (ht₄card : t₄.card = 4)
    (hΔB : ∀ d ∈ Δ, ∀ x ∈ d, x ∈ Bside → x ∈ f₄)
    (hf₄t₄ : f₄ ⊆ t₄) (hf₄card : f₄.card = 3) (hf₄B : f₄ ∈ B)
    (he_mem : e ∈ Δ) (hf₄e : f₄ ⊆ e) (hf₄countΔ : faceCount Δ f₄ ≤ 1) :
    CleanGlueStep t₄ Δ B B' := by
  classical
  have hf₄tetT : f₄ ∈ tetFaces t₄ := Finset.mem_powersetCard.mpr ⟨hf₄t₄, hf₄card⟩
  have hf₄interB : f₄ ∈ tetFaces t₄ ∩ B := Finset.mem_inter.mpr ⟨hf₄tetT, hf₄B⟩
  have hsharef₄ : ∀ {f : Finset V}, f ⊆ t₄ → (∃ d ∈ Δ, f ⊆ d) → f ⊆ f₄ := by
    rintro f hft ⟨d, hdΔ, hfd⟩ x hxf
    exact hΔB d hdΔ x (hfd hxf) (ht₄B (hft hxf))
  refine
    { weak := hweak
      newTet := ht₄Δ
      clean := ?_
      hpmc := ?_
      helc := ?_
      hvlc := ?_ }
  · rintro f hft hsh
    exact ⟨f₄, hf₄interB, hsharef₄ hft hsh⟩
  · intro f hf3 hft
    by_cases hsh : ∃ d ∈ Δ, f ⊆ d
    · have hfeq : f = f₄ := Finset.eq_of_subset_of_card_le (hsharef₄ hft hsh) (by rw [hf3, hf₄card])
      rw [hfeq]; exact hf₄countΔ
    · rw [faceCount_eq_zero]; · omega
      · intro d hdΔ hfd; exact hsh ⟨d, hdΔ, hfd⟩
  · intro ε hε hε2
    by_cases hεf₄ : ε ⊆ f₄
    · right
      have hcard : (f₄ \ ε).card = 1 := by rw [Finset.card_sdiff_of_subset hεf₄, hf₄card, hε2]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
      have hwf₄ε : w ∈ f₄ \ ε := hw ▸ Finset.mem_singleton_self w
      rw [Finset.mem_sdiff] at hwf₄ε
      obtain ⟨hwf₄, hwε⟩ := hwf₄ε
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [Finset.mem_sdiff]; exact ⟨hf₄t₄ hwf₄, hwε⟩
      · simp only [edgeLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter]
        exact ⟨⟨e, ⟨he_mem, hεf₄.trans hf₄e⟩, hf₄e hwf₄⟩, hwε⟩
    · left
      apply edgeLinkVerts_eq_empty
      intro d hdΔ hεd
      exact hεf₄ (hsharef₄ hε ⟨d, hdΔ, hεd⟩)
  · intro x hx
    by_cases hxf₄ : x ∈ f₄
    · right
      have hcard : (f₄ \ {x}).card = 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hxf₄), hf₄card,
          Finset.card_singleton]
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num : 0 < (f₄ \ {x}).card)
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
      obtain ⟨hwf₄, hwx⟩ := hw
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hf₄t₄ hwf₄, hwx⟩
      · simp only [vertexLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter,
          Finset.mem_singleton]
        exact ⟨⟨e, ⟨he_mem, hf₄e hxf₄⟩, hf₄e hwf₄⟩, hwx⟩
    · left
      apply vertexLinkVerts_eq_empty
      intro d hdΔ hxd
      exact hxf₄ (hΔB d hdΔ x hxd (ht₄B hx))

/-- **Prepend a disjoint cross-seam block to a whole clean shelling-from** (tail
shelling).  Folds `CleanGlueStep.prepend_crossSeam` along a `CleanShellFrom τ₀ B₀ l B`
of side-2 tets (`l`), all contained in `Bside` (`hlB`), disjoint from `Δ` (`hlΔ`), and
not containing the bridge face `f₄` (`hlf₄` — they are the *tail*, after the unique
`f₄`-tet `t₄` has been shelled).  With `Δ` meeting `Bside` only inside `f₄` (`hΔB`) and
the `f₄`-tet `t₄` already in the accumulator (`ht₄τ`, preserved as the accumulator
grows), the shelling stays clean with `Δ` prepended: `CleanShellFrom (Δ ∪ τ₀) B₀ l B`. -/
lemma CleanShellFrom_prepend_crossSeam {Δ : Finset (Finset V)}
    {f₄ Bside t₄ : Finset V} {l : List (Finset V)}
    (hΔB : ∀ d ∈ Δ, ∀ x ∈ d, x ∈ Bside → x ∈ f₄)
    (hf₄t₄ : f₄ ⊆ t₄) (ht₄card : t₄.card = 4) (hf₄card : f₄.card = 3)
    (hlB : ∀ t ∈ l, t ⊆ Bside) (hlΔ : ∀ t ∈ l, t ∉ Δ) (hlf₄ : ∀ t ∈ l, ¬ f₄ ⊆ t) :
    ∀ {τ₀ B₀ B : Finset (Finset V)}, CleanShellFrom τ₀ B₀ l B →
      Disjoint Δ τ₀ → t₄ ∈ τ₀ →
      CleanShellFrom (Δ ∪ τ₀) B₀ l B := by
  induction l with
  | nil =>
      intro τ₀ B₀ B h _ _
      simp only [CleanShellFrom] at h ⊢
      exact h
  | cons t l ih =>
      intro τ₀ B₀ B h hdisj ht₄τ
      simp only [CleanShellFrom] at h ⊢
      obtain ⟨B₁, hstep, hrest⟩ := h
      have htΔ : t ∉ Δ := hlΔ t (List.mem_cons_self ..)
      have hstep' : CleanGlueStep t (Δ ∪ τ₀) B₀ B₁ :=
        hstep.prepend_crossSeam hdisj htΔ (hlB t (List.mem_cons_self ..)) hΔB
          ht₄τ hf₄t₄ ht₄card hf₄card (hlf₄ t (List.mem_cons_self ..))
      refine ⟨B₁, hstep', ?_⟩
      have hdisj' : Disjoint Δ (insert t τ₀) := by
        rw [Finset.disjoint_insert_right]; exact ⟨htΔ, hdisj⟩
      have ht₄τ' : t₄ ∈ insert t τ₀ := Finset.mem_insert_of_mem ht₄τ
      have hrec : CleanShellFrom (Δ ∪ insert t τ₀) B₁ l B :=
        ih (fun u hu => hlB u (List.mem_cons_of_mem _ hu))
          (fun u hu => hlΔ u (List.mem_cons_of_mem _ hu))
          (fun u hu => hlf₄ u (List.mem_cons_of_mem _ hu)) hrest hdisj' ht₄τ'
      rwa [Finset.union_insert] at hrec

/-- **Clean relative shelling over the bridge boundary.**  A freely
clean-shellable side-2 region `τ₂` (boundary `σ₂'`), with a unique tet `t₄` through the
bridge face `f₄`, relatively clean-shells onto the ambient bridge boundary `insert f₄ K`
**with the foreign block `Δ` (the side-1 tets plus the bridge tet) prepended to the
accumulated set** — ending at `σ₂'.erase f₄ ∪ K`.

The shelling starts at `t₄` (free, by `hfree`): `t₄` glues onto `insert f₄ K` sharing
the single face `f₄` (`cleanGlueStep_crossSeam_head`, against the accumulator `Δ`),
exposing the other three faces while carrying `K`; the remaining tets glue on with the
boundary transported (`CleanShellFrom_erase_union_disjoint`, they avoid `insert f₄ K`)
and the accumulator enlarged by `Δ` (`CleanShellFrom_prepend_crossSeam`, with `t₄`
already accumulated).  The two transports are orthogonal — boundary vs. tet-set — so
they compose. -/
lemma freelyCleanShellable_cleanRelShelling_over_bridge
    {Δ τ₂ σ₂' K σ : Finset (Finset V)} {f₄ Bside e : Finset V}
    (hfree : FreelyCleanShellable τ₂ σ₂')
    (huniq : ∃! t, t ∈ τ₂ ∧ f₄ ⊆ t)
    (hf₄card : f₄.card = 3)
    (hΔdisj : Disjoint Δ τ₂)
    (hΔB : ∀ d ∈ Δ, ∀ x ∈ d, x ∈ Bside → x ∈ f₄)
    (hτ₂B : ∀ t ∈ τ₂, t ⊆ Bside)
    (he_mem : e ∈ Δ) (hf₄e : f₄ ⊆ e) (hf₄countΔ : faceCount Δ f₄ ≤ 1)
    (hKdisj : ∀ t ∈ τ₂, Disjoint (tetFaces t) K)
    (hσ : σ = σ₂'.erase f₄ ∪ K) :
    CleanRelShellingFrom Δ τ₂ (insert f₄ K) σ := by
  classical
  obtain ⟨head, ⟨hheadτ, hf₄head⟩, huniq'⟩ := huniq
  have hf₄hd : f₄ ∈ tetFaces head :=
    Finset.mem_powersetCard.mpr ⟨hf₄head, hf₄card⟩
  obtain ⟨l, hlhead, hlτ, hlnodup, hlshell⟩ := hfree head hheadτ
  cases l with
  | nil => simp at hlhead
  | cons hd tail =>
    have hhd : hd = head := by
      simpa only [List.head?_cons, Option.some.injEq] using hlhead
    subst hhd
    obtain ⟨hcard4, hshellfrom⟩ := hlshell
    have hhdB : hd ⊆ Bside := hτ₂B hd hheadτ
    have hhdΔ : hd ∉ Δ := fun hc => (Finset.disjoint_left.mp hΔdisj) hc hheadτ
    have hfirstGlue : CleanGlueStep hd Δ (insert f₄ K) ((tetFaces hd).erase f₄ ∪ K) := by
      refine cleanGlueStep_crossSeam_head ?_ hhdΔ hhdB hcard4 hΔB hf₄head hf₄card
        (Finset.mem_insert_self f₄ K) he_mem hf₄e hf₄countΔ
      have hdisjHd : Disjoint (tetFaces hd) K := hKdisj hd hheadτ
      have hinter : tetFaces hd ∩ insert f₄ K = {f₄} := by
        ext s
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hsT, hsf | hsK⟩
          · exact hsf
          · exact absurd hsK (fun h => (Finset.disjoint_left.mp hdisjHd) hsT h)
        · rintro rfl; exact ⟨hf₄hd, Or.inl rfl⟩
      refine ⟨hcard4, ?_, ?_⟩
      · rw [hinter, Finset.card_singleton]; exact Or.inl rfl
      · ext s
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        by_cases hsK : s ∈ K
        · have hsT : s ∉ tetFaces hd := fun h => (Finset.disjoint_left.mp hdisjHd) h hsK
          tauto
        · by_cases hsT : s ∈ tetFaces hd
          · by_cases hsf : s = f₄
            · subst hsf; tauto
            · tauto
          · have hsf : s ≠ f₄ := fun h => hsT (h ▸ hf₄hd)
            tauto
    have htailDisj : ∀ t ∈ tail, Disjoint (tetFaces t) (insert f₄ K) := by
      intro t ht
      have htτ : t ∈ τ₂ := by
        rw [← hlτ]; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ht)
      have htK : Disjoint (tetFaces t) K := hKdisj t htτ
      have hf₄nt : ¬ f₄ ⊆ t := by
        intro hf₄t
        have : t = hd := huniq' t ⟨htτ, hf₄t⟩
        subst this
        exact (List.nodup_cons.mp hlnodup).1 ht
      have hf₄nT : f₄ ∉ tetFaces t := fun h => hf₄nt (Finset.mem_powersetCard.mp h).1
      rw [Finset.disjoint_left]
      intro x hxT hxins
      rcases Finset.mem_insert.mp hxins with hxf | hxK
      · exact hf₄nT (hxf ▸ hxT)
      · exact (Finset.disjoint_left.mp htK) hxT hxK
    have htailB : ∀ t ∈ tail, t ⊆ Bside := fun t ht => hτ₂B t (by
      rw [← hlτ]; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ht))
    have htailΔ : ∀ t ∈ tail, t ∉ Δ := fun t ht hc =>
      (Finset.disjoint_left.mp hΔdisj) hc (by
        rw [← hlτ]; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ht))
    have htailf₄ : ∀ t ∈ tail, ¬ f₄ ⊆ t := by
      intro t ht hf₄t
      have htτ : t ∈ τ₂ := by
        rw [← hlτ]; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ht)
      have : t = hd := huniq' t ⟨htτ, hf₄t⟩
      subst this
      exact (List.nodup_cons.mp hlnodup).1 ht
    have htailBdry :
        CleanShellFrom {hd} ((tetFaces hd).erase f₄ ∪ K) tail (σ₂'.erase f₄ ∪ K) :=
      CleanShellFrom_erase_union_disjoint hshellfrom htailDisj
    have htailFull :
        CleanShellFrom (Δ ∪ {hd}) ((tetFaces hd).erase f₄ ∪ K) tail (σ₂'.erase f₄ ∪ K) :=
      CleanShellFrom_prepend_crossSeam hΔB hf₄head hcard4 hf₄card htailB htailΔ htailf₄
        htailBdry (by rwa [Finset.disjoint_singleton_right]) (Finset.mem_singleton_self hd)
    have hacc : Δ ∪ ({hd} : Finset (Finset V)) = insert hd Δ := by
      rw [Finset.union_comm, Finset.insert_eq]
    rw [hacc] at htailFull
    refine ⟨hd :: tail, hlτ, hlnodup, ?_⟩
    rw [hσ]
    exact ⟨(tetFaces hd).erase f₄ ∪ K, hfirstGlue, htailFull⟩

/-- **Case-2 clean bridge assembly (one side).** Stitch a clean shelling of side 1
(from a prescribed old target `s`), the bridge tet `e` (a clean glue onto side 1's
boundary), and a clean relative shelling of side 2 over the resulting boundary into a
single clean shelling of `insert e (τ₁ ∪ τ₂)` headed at `s`, threading the enlarged
accumulator `insert e τ₁` that the clean relative shelling requires.
(`τ₁ = l₁.toFinset` is side 1's tet-set.) -/
lemma cleanBridge_assemble {τ₂ σ₁ Bmid σ : Finset (Finset V)} {e s : Finset V}
    {l₁ : List (Finset V)}
    (hsh₁ : IsCleanShelling l₁ σ₁) (hhead₁ : l₁.head? = some s) (hnd₁ : l₁.Nodup)
    (hg : CleanGlueStep e l₁.toFinset σ₁ Bmid)
    (hrel : CleanRelShellingFrom (insert e l₁.toFinset) τ₂ Bmid σ)
    (heτ₁ : e ∉ l₁.toFinset) (hdisj : Disjoint l₁.toFinset τ₂) (heτ₂ : e ∉ τ₂) :
    ∃ l : List (Finset V), l.head? = some s ∧
      l.toFinset = insert e (l₁.toFinset ∪ τ₂) ∧ l.Nodup ∧ IsCleanShelling l σ := by
  classical
  obtain ⟨l₂, hl₂τ, hl₂nodup, hsf₂⟩ := hrel
  have hsh₁e : IsCleanShelling (l₁ ++ [e]) Bmid := IsCleanShelling_snoc hsh₁ hg
  have htoFin : (l₁ ++ [e]).toFinset = insert e l₁.toFinset := by
    rw [List.toFinset_append]
    ext x
    simp only [Finset.mem_union, List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
      Finset.notMem_empty, or_false, Finset.mem_singleton]
    tauto
  have hsf₂' : CleanShellFrom (l₁ ++ [e]).toFinset Bmid l₂ σ := htoFin ▸ hsf₂
  refine ⟨(l₁ ++ [e]) ++ l₂, ?_, ?_, ?_, IsCleanShelling_append_cleanShellFrom hsh₁e hsf₂'⟩
  · cases l₁ with
    | nil => exact absurd hsh₁ (by simp [IsCleanShelling])
    | cons a r => rw [List.append_assoc, List.cons_append]; rwa [List.head?_cons] at hhead₁ ⊢
  · rw [List.toFinset_append, htoFin, hl₂τ]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  · have hel₁ : e ∉ l₁ := fun hc => heτ₁ (List.mem_toFinset.mpr hc)
    have hel₂ : e ∉ l₂ := fun hc => heτ₂ (hl₂τ ▸ List.mem_toFinset.mpr hc)
    have hdl : l₁.Disjoint l₂ := by
      intro a ha₁ ha₂
      exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr ha₁)
        (hl₂τ ▸ List.mem_toFinset.mpr ha₂)
    refine (hnd₁.append (List.nodup_singleton e) ?_).append hl₂nodup ?_
    · rw [List.disjoint_left]; intro a ha; simp only [List.mem_singleton]; rintro rfl; exact hel₁ ha
    · rw [List.disjoint_left]; intro a ha
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha₁ | rfl
      · exact List.disjoint_left.mp hdl ha₁
      · exact hel₂

end Taut
