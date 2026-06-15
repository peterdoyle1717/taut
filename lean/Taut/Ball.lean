import Taut.Complex2

/-!
# Shelling-certified combinatorial 3-balls

The combinatorial replacement for "simplicial triangulation of `B³`",
following the paper's *Shelling* section.  A *shelling* of a ball is an
ordering `(t₁, …, t_k)` of its tetrahedra such that gluing them on one at a
time always maintains a ball; the type of a glued tet is the number of its
faces shared with what is already built (type 1 or 2; type 3 — which would
create an interior vertex — never occurs here).

Following the G1 audit (Q2/Q3 APPROVED, `notes/codex-consults/
2026-06-12-g1-sphere-ball-*`), a ball is encoded as an **explicit shelling
certificate** (a `List` of tets), not an inductive `Prop`: the Theorem 2
reassembly grafts shellings by list concatenation, and free shellability
quantifies over the first element.  A glue step is a purely combinatorial
stick (tet glued by one or two faces); intermediate boundaries are **not**
required to be spheres — that the boundary of a sticker ball is a 2-sphere is
a separate, deferred fact (`glueStep_preserves_isSphere2`), not needed for the
main theorem (whose boundary `σ` is given as a sphere).

`IsBall τ B` is, by design, a *shelling-certified* ball — not a general
combinatorial-ball definition.  It is exactly the object the merged
Theorem 2+3 induction constructs.

Faces of a tetrahedron `t` (a 4-element set) are its card-3 subsets,
`t.powersetCard 3`.  When tet `t` is glued onto a ball whose boundary is the
2-sphere `B`, the faces of `t` already present in `B` become interior and the
new faces are exposed: the new boundary is the symmetric difference
`(B \ t.powersetCard 3) ∪ (t.powersetCard 3 \ B)`.

Validation (build-checked):
* a single tet is a (freely shellable) ball with the tetrahedron-boundary
  sphere as its boundary (`isBall_singleton`, `freelyShellable_singleton`).

That the boundary of a sticker ball is a 2-sphere
(`glueStep_preserves_isSphere2` / `ShellFrom.isSphere2_of_seed`) is true but
**deferred**: it is the classification-of-surfaces fact (closed + connected +
orientable + χ = 2), provable fieldwise, and is *not* on the path of the main
theorem.
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

/-- The four triangular faces of a tetrahedron `t` (the card-3 subsets). -/
abbrev tetFaces (t : Finset V) : Finset (Finset V) := t.powersetCard 3

/-- One gluing step of a shelling: tet `t` is glued onto a ball whose
boundary is `B`, producing the ball with boundary `B'`.

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

/-- Starting from a ball with boundary `B₀`, gluing on the tets of `l` in
order yields a ball with boundary `B`. -/
def ShellFrom : Finset (Finset V) → List (Finset V) → Finset (Finset V) → Prop
  | B₀, [],     B => B = B₀
  | B₀, t :: l, B => ∃ B₁, GlueStep t B₀ B₁ ∧ ShellFrom B₁ l B

/-- `l` is a shelling with final boundary `B`: the head tet is the initial
tetrahedron (its boundary is the tetrahedron-boundary sphere) and the
remaining tets are glued on in order. -/
def IsShelling : List (Finset V) → Finset (Finset V) → Prop
  | [],     _ => False
  | t :: l, B => t.card = 4 ∧ ShellFrom (tetFaces t) l B

/-- A *shelling-certified ball*: a facet set `τ` admitting a shelling (a
nodup ordering of its tets gluing up to boundary `B`). -/
def IsBall (τ B : Finset (Finset V)) : Prop :=
  ∃ l : List (Finset V), l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B

/-- `τ` is *freely shellable* with boundary `B` if **any** of its tets can
serve as the initial tet of a shelling (the paper's "freely shellable":
shucking in reverse can remove any prescribed tet last). -/
def FreelyShellable (τ B : Finset (Finset V)) : Prop :=
  ∀ t ∈ τ, ∃ l : List (Finset V),
    l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B

/-! ## The boundary of a sticker ball is a sphere — DEFERRED

That every intermediate (hence the final) boundary of a sticker ball is a
combinatorial 2-sphere is true but **off the critical path**, so deferred.
Mathematically it is the classification of surfaces — a sphere glued to a tet
along one or two faces stays closed, connected, orientable, with χ = 2, all
preserved by the surgery — but Mathlib has no usable classification theorem,
so the Lean route is fieldwise preservation (the only nontrivial field being
`linkConn`, the manifold/no-pinch condition: an edge subdivision of the vertex
links for type 1, a contraction-at-2 + subdivision-at-2 for type 2).  Targets
(to be proved later by a genuine fieldwise argument — never assumed):

* `glueStep_preserves_isSphere2 (hg : GlueStep t B B') : IsSphere2 B → IsSphere2 B'`
* `ShellFrom.isSphere2_of_seed (h : ShellFrom B₀ l B) : IsSphere2 B₀ → IsSphere2 B`

The main theorem (`theorem3_core`) does not use these: the boundary of
`M.support` is `σ`, which is given as a sphere. -/

/-! ## Reassembly (M22a): appending tets and bridging two balls

Architect: codex 019ec2cc. `ShellFrom`/`IsShelling` are closed under appending
tets at the end; a ball with a `GlueStep` tet on its boundary grows by that tet
(case-1 of the Theorem-2 induction). Gluing two balls through a bridging tet
needs *relative* shellability (`RelShelling`) — that is the genuine hidden-
topology fact (M22b), here reduced to a tautological bridge given the relative
shelling. -/

/-- `ShellFrom` composes: glue `l₁` then `l₂`. -/
lemma ShellFrom_append {B₀ B₁ B₂ : Finset (Finset V)} {l₁ l₂ : List (Finset V)}
    (h₁ : ShellFrom B₀ l₁ B₁) (h₂ : ShellFrom B₁ l₂ B₂) :
    ShellFrom B₀ (l₁ ++ l₂) B₂ := by
  induction l₁ generalizing B₀ with
  | nil => simp only [ShellFrom, List.nil_append] at h₁ ⊢; exact h₁ ▸ h₂
  | cons t l ih =>
      simp only [ShellFrom, List.cons_append] at h₁ ⊢
      obtain ⟨B', hg, hrest⟩ := h₁
      exact ⟨B', hg, ih hrest⟩

/-- Append one `GlueStep` tet to a `ShellFrom`. -/
lemma ShellFrom_snoc {B₀ B B' : Finset (Finset V)} {l : List (Finset V)} {t : Finset V}
    (h : ShellFrom B₀ l B) (hg : GlueStep t B B') : ShellFrom B₀ (l ++ [t]) B' :=
  ShellFrom_append h ⟨B', hg, rfl⟩

/-- Glue a `ShellFrom` of `l₂` onto the end of a shelling `l`. -/
lemma IsShelling_append {l l₂ : List (Finset V)} {B₁ B : Finset (Finset V)}
    (h : IsShelling l B₁) (hf : ShellFrom B₁ l₂ B) : IsShelling (l ++ l₂) B := by
  cases l with
  | nil => simp only [IsShelling] at h
  | cons t r => simp only [IsShelling, List.cons_append] at h ⊢; exact ⟨h.1, ShellFrom_append h.2 hf⟩

/-- Append one `GlueStep` tet to a shelling. -/
lemma IsShelling_snoc {B B' : Finset (Finset V)} {l : List (Finset V)} {t : Finset V}
    (h : IsShelling l B) (hg : GlueStep t B B') : IsShelling (l ++ [t]) B' :=
  IsShelling_append h ⟨B', hg, rfl⟩

/-- **Case-1 reassembly.** A ball whose boundary admits a `GlueStep` for a fresh
tet `t` grows to the ball with `t` adjoined. -/
theorem IsBall.insert_of_glueStep {τ B B' : Finset (Finset V)} {t : Finset V}
    (h : IsBall τ B) (hg : GlueStep t B B') (ht : t ∉ τ) : IsBall (insert t τ) B' := by
  obtain ⟨l, hlτ, hnodup, hsh⟩ := h
  have htl : t ∉ l := fun hc => ht (hlτ ▸ List.mem_toFinset.mpr hc)
  refine ⟨l ++ [t], ?_, ?_, IsShelling_snoc hsh hg⟩
  · rw [List.toFinset_append, hlτ]
    ext s
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_singleton]
    tauto
  · refine hnodup.append (List.nodup_singleton t) ?_
    rw [List.disjoint_left]; intro a ha
    simp only [List.mem_singleton]; rintro rfl; exact htl ha

/-- A *relative shelling*: glue the tets of `τ` onto an ambient boundary `B₀`,
ending at `B`. (`IsBall` is the special case `B₀ = tetFaces (head)`.) This is the
invariant the case-2 bridge needs but `IsBall` does not supply. -/
def RelShelling (τ B₀ B : Finset (Finset V)) : Prop :=
  ∃ l : List (Finset V), l.toFinset = τ ∧ l.Nodup ∧ ShellFrom B₀ l B

/-- **Case-2 bridge (tautological given the relative shelling).** A ball `τ₁`,
a `GlueStep` tet `t` onto its boundary, and a relative shelling of `τ₂` onto the
resulting boundary, assemble into one ball. The hard part — that the separated
ball actually supplies the `RelShelling` — is M22b. -/
theorem IsBall.bridge_of_relShelling {τ₁ τ₂ B₁ Bmid B : Finset (Finset V)} {t : Finset V}
    (h₁ : IsBall τ₁ B₁) (hg : GlueStep t B₁ Bmid) (h₂ : RelShelling τ₂ Bmid B)
    (ht₁ : t ∉ τ₁) (ht₂ : t ∉ τ₂) (hdisj : Disjoint τ₁ τ₂) :
    IsBall (insert t (τ₁ ∪ τ₂)) B := by
  obtain ⟨l₁, hl₁, hn₁, hsh₁⟩ := h₁
  obtain ⟨l₂, hl₂, hn₂, hsf₂⟩ := h₂
  have htl₁ : t ∉ l₁ := fun hc => ht₁ (hl₁ ▸ List.mem_toFinset.mpr hc)
  have htl₂ : t ∉ l₂ := fun hc => ht₂ (hl₂ ▸ List.mem_toFinset.mpr hc)
  have hdl : l₁.Disjoint l₂ := by
    intro a ha ha₂
    exact Finset.disjoint_left.mp hdisj (hl₁ ▸ List.mem_toFinset.mpr ha)
      (hl₂ ▸ List.mem_toFinset.mpr ha₂)
  refine ⟨(l₁ ++ [t]) ++ l₂, ?_, ?_, IsShelling_append (IsShelling_snoc hsh₁ hg) hsf₂⟩
  · rw [List.toFinset_append, List.toFinset_append, hl₁, hl₂]
    ext s
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_singleton]
    tauto
  · refine (hn₁.append (List.nodup_singleton t) ?_).append hn₂ ?_
    · rw [List.disjoint_left]; intro a ha
      simp only [List.mem_singleton]; rintro rfl; exact htl₁ ha
    · rw [List.disjoint_left]; intro a ha
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact List.disjoint_left.mp hdl ha
      · exact htl₂

/-! ## A single tetrahedron is a ball -/

/-- A single tetrahedron `t` is a shelling-certified ball whose boundary is
the tetrahedron-boundary sphere. -/
theorem isBall_singleton {t : Finset V} (ht : t.card = 4) :
    IsBall {t} (tetFaces t) := by
  refine ⟨[t], by simp, by simp, ?_⟩
  simp only [IsShelling, ShellFrom]
  exact ⟨ht, trivial⟩

/-- A single tetrahedron is freely shellable. -/
theorem freelyShellable_singleton {t : Finset V} (ht : t.card = 4) :
    FreelyShellable {t} (tetFaces t) := by
  intro t' ht'
  rw [Finset.mem_singleton] at ht'
  subst t'
  refine ⟨[t], by simp, by simp, by simp, ?_⟩
  simp only [IsShelling, ShellFrom]
  exact ⟨ht, trivial⟩

end Taut
