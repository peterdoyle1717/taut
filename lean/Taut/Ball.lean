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
quantifies over the first element.  `IsSphere2` of every intermediate
boundary is **baked into** the gluing step, so the induction has sphere-hood
available at every stage.

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
  sphere as its boundary (`isBall_singleton`, `freelyShellable_singleton`);
* the boundary of a shelling-certified ball is a combinatorial 2-sphere
  (`IsBall.isSphere2`) — the structural invariant carried by the certificate.
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

/-- The four triangular faces of a tetrahedron `t` (the card-3 subsets). -/
abbrev tetFaces (t : Finset V) : Finset (Finset V) := t.powersetCard 3

/-- One gluing step of a shelling: tet `t` is glued onto a ball whose
boundary 2-sphere is `B`, producing the ball with boundary `B'`.

* `card4` — `t` is a tetrahedron (4 vertices);
* `shared` — `t` meets the current boundary in **one or two** of its faces
  (type 1 or 2; type 3 is excluded, as it would create an interior vertex);
* `newBdry` — the new boundary is the symmetric difference of `B` and the
  faces of `t`: shared faces become interior, the rest are exposed;
* `sphere` — the new boundary is again a combinatorial 2-sphere (the
  invariant baked into the certificate).
-/
structure GlueStep (t : Finset V) (B B' : Finset (Finset V)) : Prop where
  card4 : t.card = 4
  shared : (tetFaces t ∩ B).card = 1 ∨ (tetFaces t ∩ B).card = 2
  newBdry : B' = (B \ tetFaces t) ∪ (tetFaces t \ B)
  sphere : IsSphere2 B'

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

/-! ## The boundary of a ball is a sphere -/

/-- Gluing preserves sphere-hood of the boundary: if the starting boundary
`B₀` is a sphere, so is the final boundary `B`. -/
lemma ShellFrom.isSphere2 {l : List (Finset V)} :
    ∀ {B₀ B : Finset (Finset V)}, ShellFrom B₀ l B → IsSphere2 B₀ → IsSphere2 B := by
  induction l with
  | nil =>
      intro B₀ B h h0
      simp only [ShellFrom] at h
      exact h ▸ h0
  | cons t l ih =>
      intro B₀ B h _
      simp only [ShellFrom] at h
      obtain ⟨B₁, hg, hrest⟩ := h
      exact ih hrest hg.sphere

/-- The final boundary of a shelling is a combinatorial 2-sphere. -/
lemma IsShelling.isSphere2 {l : List (Finset V)} {B : Finset (Finset V)}
    (h : IsShelling l B) : IsSphere2 B := by
  cases l with
  | nil => simp only [IsShelling] at h
  | cons t l =>
      simp only [IsShelling] at h
      exact h.2.isSphere2 (isSphere2_powersetCard3 h.1)

/-- The boundary of a shelling-certified ball is a combinatorial 2-sphere. -/
theorem IsBall.isSphere2 {τ B : Finset (Finset V)} (h : IsBall τ B) :
    IsSphere2 B := by
  obtain ⟨_, _, _, hsh⟩ := h
  exact hsh.isSphere2

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
