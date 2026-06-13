# G1 design spec: linkConn for the cut pieces (the v∈γ cycle-arc)

Target: complete `linkConn` for the capped sides `insert γ (cutSet σ W)` of the
separation, then assemble `IsSphere2` for the pieces. This is the last hard
field of "the cut pieces are spheres". Resuming the protocol with codex on
architecture; M9–M16 are committed (tag `fable-axed`) and G1-APPROVED.

## 0. Context — what is already built (Separation.lean, all building)

For a sphere `σ : Finset (Finset V)` (`IsSphere2`), a non-face triangle `γ`
(`γ.card = 3`, `γ.powersetCard 2 ⊆ edgesOf σ`, `γ ∉ σ`), and a cut
`W : ↥σ → ZMod 2` with `bd2 σ W = gammaChain σ γ` (`exists_cut`):
- `cutSet σ W` = the faces with `W = 1` (one side σ₁); `σ₂ = cutSet σ (W+𝟙)`.
- `edge_cut_parity`: across each edge `e` with faces `f₁,f₂`,
  `W f₁ + W f₂ = if e ⊆ γ then 1 else 0`. So **non-γ edges don't cross the
  cut; the three γ-edges do.**
- `closed_cut`: `insert γ (cutSet σ W)` is a closed pseudomanifold.
- `conn_cut`: its skeleton is connected.
- **v∉γ half of linkConn already done**: `W_eq_of_share_edge` (two faces
  sharing a non-γ edge are same-side), `W_eq_along_link` (W constant along a
  link walk at v∉γ), `W_const_at` (all faces through an off-γ vertex are
  same-side). Consequence (to be packaged): for `v ∉ γ`, all cut faces at `v`
  are uniformly σ₁ or σ₂, so `linkGraph (insert γ σ₁) v = linkGraph σ v` on the
  same `linkVerts`, and `linkConn` is inherited from `σ`.
- M8 facts available: `link_two_regular` (each `x ∈ linkVerts σ v` has exactly
  2 neighbours in `linkGraph σ v`), `linkConn σ` (links connected),
  `three_le_card_linkVerts`, `exists_two_faces`, `mem_linkVerts(_iff_edge)`.
- Mathlib (v4.29.1) has `SimpleGraph.IsCycles` (`Matching.lean`): a graph where
  every vertex has neighbour-set ncard 0 or 2, with `IsCycles.other_adj_of_adj`,
  `IsCycles.existsUnique_ne_adj`,
  `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`.

## 1. The remaining design: the v∈γ case of linkConn

Goal: for `v ∈ γ` (so `v ∈ vertsOf (insert γ σ₁)`),
`ConnOn (linkGraph (insert γ σ₁) v) (linkVerts (insert γ σ₁) v)`.

Geometry: `linkGraph σ v` is a single cycle `C` (2-regular + connected). Its
edges = σ-faces at `v`; its vertices = `linkVerts σ v`. Write `γ = {v,a,b}`.
The cut "side" of a face `{v,x,y}` is `W`; two faces sharing link-vertex `z`
(edge `{v,z}`) are same-side iff `{v,z}` is non-γ iff `z ∉ {a,b}`. So going
around `C` the side is **constant except it flips exactly at `a` and `b`** ⇒
`C` splits into two arcs between `a` and `b`: one all-σ₁, one all-σ₂.

The faces of `insert γ σ₁` at `v` = (σ₁-faces at `v`) ∪ {γ}; as link data
= (the σ₁-arc's edges) + the chord `{a,b}` (from γ). So
`linkGraph (insert γ σ₁) v` = "σ₁-arc + chord a–b" = a single cycle ⇒ connected;
`linkVerts (insert γ σ₁) v` = the σ₁-arc's vertices (with `a,b` its endpoints).

### Candidate proof routes (the audited question)
**Route A (IsCycles + traversal).** Show `linkGraph σ v` is `IsCycles` (from
`link_two_regular` + neighbours-lie-in-linkVerts). Show `linkGraph (insert γ σ₁) v`
is `IsCycles` too (every link-vertex has degree exactly 2: interior σ₁-arc
vertices keep their two σ₁ faces; `a,b` get one σ₁ face + the chord). Then
"connected 2-regular = one cycle" — but `IsCycles` alone gives a *disjoint
union* of cycles; connectivity needs that the side flips at exactly the two
points `a,b` (so one σ₁-arc, not several). Formalize via cycle traversal
(`other_adj_of_adj` to walk the σ₁-arc from `a` to `b`).

**Route B (reroute along `linkConn σ`).** For `y ∈ linkVerts (insert γ σ₁) v`,
build a path `y → a` in `linkGraph (insert γ σ₁) v`: take the `linkConn σ`
path `y → a` in `C`; where it would use a σ₂-face, reroute via the chord
`{a,b}`. Needs the same arc fact (a σ₂-excursion enters/leaves only at `a,b`).

**Route C (degree-2 + connected-skeleton transfer).** `linkGraph (insert γ σ₁) v`
is 2-regular on its link-verts (as above). Is there a cheaper connectivity
certificate than full arc traversal — e.g. counting (a connected 2-regular
graph on `linkVerts (insert γ σ₁) v` with the chord), or a parity/Euler
argument on the 1-dimensional link?

## 2. Conventions
Unoriented; the cut side is `W` over `ZMod 2`. `insert γ σ₁` is the capped
side. `linkVerts`/`linkGraph` as in Complex2. No new global convention; this is
proof machinery for one IsSphere2 field.

## 3. After linkConn: euler + assembly (sanity-check the rest of the packet)
- `euler` for the pieces: `χ(insert γ σ₁) = 2`. Plan: χ-additivity
  `χ(τ₁) + χ(τ₂) = χ(σ ∪ {γ}) + χ(shared)` with `σ∪{γ}` adding 1 face / 0 new
  edges-or-verts to σ (so χ = 3) and shared = the closed triangle γ (χ = 1),
  giving `χ(τ₁)+χ(τ₂) = 4`; with `χ(τᵢ) ≤ 2` (each is a connected closed
  surface, so `b₂=1` via the M10 dual-connectivity argument ⇒ χ = 2 − b₁ ≤ 2)
  forcing each `= 2`. OR direct vertex/edge/face counting. Which is cleaner?
- assemble `IsSphere2 (insert γ σᵢ)` for BOTH sides (σ₂ via `W + 𝟙`, which also
  satisfies `bd2 (W+𝟙) = gammaChain` since `bd2 𝟙 = 0`).

## 4. Validation invariants / failure modes
- The v∈γ link is a cycle and the cut gives exactly two arcs: cross-checks
  `link_two_regular` + `edge_cut_parity` against each other; a wrong arc count
  breaks connectivity. Smoke test: the tetrahedron-boundary sphere with a
  non-face triangle (if a cheap instance exists), else the build is the test.

## 5. Files and commands
`lean/Taut/Separation.lean` (extend). Build `cd lean && lake build`; greps +
`#print axioms` per the G2 gate.

## Questions for the auditor
Q1. Which route (A IsCycles-traversal / B reroute / C degree-2+cheaper-cert)
    is the least painful in Lean for the v∈γ linkConn? Is `SimpleGraph.IsCycles`
    the right tool, or does it add more friction than a hand-rolled cycle
    walk built from `link_two_regular`?
Q2. Is "the side flips at exactly `a,b` ⇒ the σ₁-faces form a single arc" best
    proved by cycle traversal, or is there a slicker invariant (e.g. an
    even/odd-crossing parity argument) that avoids constructing the arc?
Q3. Any hidden trap making the v∈γ case false or much harder than sketched —
    e.g. degenerate links (`linkVerts` small), or `a = b` impossible to rule
    out (γ.card = 3 gives a ≠ b)?
Q4. `euler` for the pieces: χ-additivity vs. direct counting — which is the
    lower-risk path, and does additivity need an inclusion–exclusion lemma I
    should state first?
Q5. Anything in assembling `IsSphere2 (insert γ σᵢ)` for the σ₂ side (via W+𝟙)
    that won't just mirror the σ₁ side?
