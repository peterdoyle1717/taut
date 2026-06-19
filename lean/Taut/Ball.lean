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

/-- **Ambient transport of one glue step.** A glue step commutes with adjoining a
piece `K` of boundary disjoint from the tet's faces: the shared count is unchanged
(the tet's faces avoid `K`) and the new boundary just carries `K` along.  This is
the combinatorial core of the case-2 bridge — sticking the second ball's tets while
the first ball + bridge sit in the ambient `K`. -/
lemma GlueStep.union_disjoint {t : Finset V} {B B' K : Finset (Finset V)}
    (hg : GlueStep t B B') (hdisj : Disjoint (tetFaces t) K) :
    GlueStep t (B ∪ K) (B' ∪ K) where
  card4 := hg.card4
  shared := by
    have heq : tetFaces t ∩ (B ∪ K) = tetFaces t ∩ B := by
      ext s
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hsT, hsB | hsK⟩
        · exact ⟨hsT, hsB⟩
        · exact absurd hsK (fun h => (Finset.disjoint_left.mp hdisj) hsT h)
      · rintro ⟨hsT, hsB⟩; exact ⟨hsT, Or.inl hsB⟩
    rw [heq]; exact hg.shared
  newBdry := by
    rw [hg.newBdry]
    ext s
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hsK : s ∈ K
    · have hsT : s ∉ tetFaces t := fun h => (Finset.disjoint_left.mp hdisj) h hsK
      tauto
    · tauto

/-- **Ambient transport of a whole relative shelling.** Gluing the tets of `l` onto
`B₀` transports to gluing them onto `B₀ ∪ K`, provided every tet's faces avoid `K`. -/
lemma ShellFrom_union_disjoint {K : Finset (Finset V)} {l : List (Finset V)} :
    ∀ {B₀ B : Finset (Finset V)}, ShellFrom B₀ l B →
      (∀ t ∈ l, Disjoint (tetFaces t) K) → ShellFrom (B₀ ∪ K) l (B ∪ K) := by
  induction l with
  | nil =>
      intro B₀ B h _
      simp only [ShellFrom] at h ⊢
      rw [h]
  | cons t l ih =>
      intro B₀ B h hd
      simp only [ShellFrom] at h ⊢
      obtain ⟨B₁, hg, hrest⟩ := h
      exact ⟨B₁ ∪ K, hg.union_disjoint (hd t (List.mem_cons.mpr (Or.inl rfl))),
        ih hrest (fun u hu => hd u (List.mem_cons.mpr (Or.inr hu)))⟩

/-- One glue step, transported by erasing the interface face `γ` and adjoining the
disjoint piece `K`, when the tet avoids both. -/
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

/-- **Boundary-piece transport.** If none of the tets in a relative shelling touches
`γ` or the ambient piece `K`, then the shelling is unchanged after replacing the
carried boundary face `γ` by `K`.

This is the degree-3 star-start transport target: after the first remainder tet
uses the interface triangle `γ`, the rest of the remainder shelling carries the
three exposed star faces `K` instead, while `γ` is final on the remainder side and
is therefore absent from all later glue steps. -/
lemma ShellFrom_erase_union_disjoint {γ : Finset V} {K : Finset (Finset V)}
    {l : List (Finset V)} :
    ∀ {B₀ B : Finset (Finset V)}, ShellFrom B₀ l B →
      (∀ t ∈ l, Disjoint (tetFaces t) (insert γ K)) →
      ShellFrom (B₀.erase γ ∪ K) l (B.erase γ ∪ K) := by
  induction l with
  | nil =>
      intro B₀ B h _
      simp only [ShellFrom] at h ⊢
      rw [h]
  | cons t l ih =>
      intro B₀ B h hd
      simp only [ShellFrom] at h ⊢
      obtain ⟨B₁, hg, hrest⟩ := h
      exact ⟨B₁.erase γ ∪ K, hg.erase_union_disjoint (hd t (List.mem_cons.mpr (Or.inl rfl))),
        ih hrest (fun u hu => hd u (List.mem_cons.mpr (Or.inr hu)))⟩

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

/-- **Relative shelling over an inserted boundary face.** A freely shellable ball
`τ` (boundary `B`) which has a *unique* tet `head` containing a given triangle
`γ` (and whose tets are otherwise disjoint from an ambient piece `K`) admits a
relative shelling onto the ambient boundary `insert γ K`, ending at `B.erase γ ∪ K`.

This is the case-2 bridge engine: the bridge tet `e` exposes `γ` on the second
side's boundary; gluing `e` first consumes `head` (sharing the single face `γ`),
exposing the three other faces of `head` while carrying `K` along, and the
remaining tets glue on disjointly from `K`. -/
lemma FreelyShellable.relShelling_over_insert_boundary_face
    {τ B K : Finset (Finset V)} {γ : Finset V} {σ : Finset (Finset V)}
    (hfree : FreelyShellable τ B)
    (hγ3 : γ.card = 3)
    (huniq : ∃! t, t ∈ τ ∧ γ ⊆ t)
    (hKdisj : ∀ t ∈ τ, Disjoint (tetFaces t) K)
    (hσ : σ = B.erase γ ∪ K) :
    RelShelling τ (insert γ K) σ := by
  classical
  obtain ⟨head, ⟨hheadτ, hγhead⟩, huniq'⟩ := huniq
  -- `γ` is a face of `head`.
  have hγhd : γ ∈ tetFaces head :=
    Finset.mem_powersetCard.mpr ⟨hγhead, hγ3⟩
  -- The shelling list starting at `head`.
  obtain ⟨l, hlhead, hlτ, hlnodup, hlshell⟩ := hfree head hheadτ
  -- Destruct the list: it is nonempty with head `head`.
  cases l with
  | nil => simp at hlhead
  | cons hd tail =>
    have hhd : hd = head := by
      simpa only [List.head?_cons, Option.some.injEq] using hlhead
    subst hhd
    simp only [IsShelling] at hlshell
    obtain ⟨hcard4, hshellfrom⟩ := hlshell
    -- Disjointness of `hd` from `K`, hence `tetFaces hd ∩ insert γ K = {γ}`.
    have hheadK : Disjoint (tetFaces hd) K := hKdisj hd hheadτ
    have hinter : tetFaces hd ∩ insert γ K = {γ} := by
      ext s
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hsT, hsγ | hsK⟩
        · exact hsγ
        · exact absurd hsK (fun h => (Finset.disjoint_left.mp hheadK) hsT h)
      · rintro rfl; exact ⟨hγhd, Or.inl rfl⟩
    -- The first glue step: glue `hd` onto `insert γ K`.
    have hfirstGlue : GlueStep hd (insert γ K) ((tetFaces hd).erase γ ∪ K) := by
      refine ⟨hcard4, ?_, ?_⟩
      · rw [hinter, Finset.card_singleton]; exact Or.inl rfl
      · -- newBdry: (insert γ K \ tetFaces hd) ∪ (tetFaces hd \ insert γ K)
        --        = (tetFaces hd).erase γ ∪ K
        ext s
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_erase]
        by_cases hsK : s ∈ K
        · have hsT : s ∉ tetFaces hd :=
            fun h => (Finset.disjoint_left.mp hheadK) h hsK
          tauto
        · by_cases hsT : s ∈ tetFaces hd
          · by_cases hsγ : s = γ
            · subst hsγ; tauto
            · tauto
          · -- s ∉ tetFaces hd and s ∉ K; in particular s ≠ γ since γ ∈ tetFaces hd
            have hsγ : s ≠ γ := fun h => hsT (h ▸ hγhd)
            tauto
    -- The tail tets all avoid `insert γ K`: disjoint from `K` (hKdisj) and do not
    -- contain `γ` (uniqueness of `head`).
    have htailDisj : ∀ t ∈ tail, Disjoint (tetFaces t) (insert γ K) := by
      intro t ht
      have htτ : t ∈ τ := by
        rw [← hlτ]; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ ht)
      have htK : Disjoint (tetFaces t) K := hKdisj t htτ
      have hγnt : ¬ γ ⊆ t := by
        intro hγt
        have : t = hd := huniq' t ⟨htτ, hγt⟩
        subst this
        exact (List.nodup_cons.mp hlnodup).1 ht
      have hγnT : γ ∉ tetFaces t := fun h => hγnt (Finset.mem_powersetCard.mp h).1
      rw [Finset.disjoint_left]
      intro x hxT hxins
      rcases Finset.mem_insert.mp hxins with hxγ | hxK
      · exact hγnT (hxγ ▸ hxT)
      · exact (Finset.disjoint_left.mp htK) hxT hxK
    -- Transport the tail shelling onto the erased/adjoined boundary.
    have htailShell :
        ShellFrom ((tetFaces hd).erase γ ∪ K) tail (B.erase γ ∪ K) :=
      ShellFrom_erase_union_disjoint hshellfrom htailDisj
    refine ⟨hd :: tail, hlτ, hlnodup, ?_⟩
    rw [hσ]
    exact ⟨(tetFaces hd).erase γ ∪ K, hfirstGlue, htailShell⟩

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

/-! ## Boundary (weak) shelling — demoted names

The predicates above are *boundary traces*: a `GlueStep` only constrains the new
tet against the current boundary `B` (its shared card-3 faces, symmetric-
difference update); it never sees the accumulated tet-set, so it cannot detect a
rogue lower-dimensional intersection with an already-built tet.  The clean,
public predicates (`CleanGlueStep`, `IsCleanShelling`, `FreelyCleanShellable`, …)
live in `Taut.CleanShelling` and project down to these via `.toBoundary…`, so the
banked reassembly lemmas keep firing on the projected boundary trace.  These
aliases mark the weak layer; avoid the bare names in final theorem statements. -/

/-- Boundary (weak) glue step — alias for `GlueStep`. -/
abbrev BoundaryGlueStep (t : Finset V) (B B' : Finset (Finset V)) : Prop :=
  GlueStep t B B'
/-- Boundary (weak) shelling-from — alias for `ShellFrom`. -/
abbrev BoundaryShellFrom (B₀ : Finset (Finset V)) (l : List (Finset V))
    (B : Finset (Finset V)) : Prop := ShellFrom B₀ l B
/-- Boundary (weak) shelling — alias for `IsShelling`. -/
abbrev BoundaryIsShelling (l : List (Finset V)) (B : Finset (Finset V)) : Prop :=
  IsShelling l B
/-- Boundary (weak) ball — alias for `IsBall`. -/
abbrev BoundaryIsBall (τ B : Finset (Finset V)) : Prop := IsBall τ B
/-- Boundary (weak) free shellability — alias for `FreelyShellable`. -/
abbrev BoundaryFreelyShellable (τ B : Finset (Finset V)) : Prop := FreelyShellable τ B
/-- Boundary (weak) relative shelling — alias for `RelShelling`. -/
abbrev RelBoundaryShelling (τ B₀ B : Finset (Finset V)) : Prop := RelShelling τ B₀ B

end Taut
