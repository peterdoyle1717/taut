# G1 design spec: combinatorial spheres and balls for Theorem 2

Target: Theorems 2–4 of taut/taut.tex. Theorem 2: any taut filling of (a
2-cycle orienting) a simplicial triangulation σ of S² arises from a
simplicial triangulation of B³. Theorem 3: freely shellable. Theorem 4:
flag. Status: Props 1–4 and Theorem 1 (both parts) are formalized and
committed (M2–M6); this spec opens the geometric half.

## 0. Why this packet is the expensive one (the "months" estimate)

Theorem 1 was cheap to state: its statement quantifies over chains, and
the chain encoding was 50 lines. Theorem 2 is expensive for four reasons,
none of them "the proof is deep":

1. **Statement debt.** "Simplicial triangulation of S²" and "triangulation
   of B³" must be REPLACED by combinatorial definitions before the theorem
   can even be stated. These definitions are load-bearing conventions:
   every later lemma builds on them, and an error (too weak: theorems
   become false; too strong: unprovable or vacuous) surfaces only deep in
   the Th2 induction. This is exactly the failure mode G1 exists for.

2. **The paper's one-line topology.** The 1.5-page proof of Th2 leans on
   facts asserted with zero proof because they are visually obvious:
   (a) removing an eligible tet performs an edge flip on σ, and the result
   is again a triangulated S² OR pinches into two triangulated S²'s
   sharing an edge (the flip dichotomy);
   (b) ball ∪_face tet = ball, ball ∪_triangle ball = ball (gluing);
   (c) for Th4, "an S³ cannot sit inside B³" (replaceable by a pure chain
   argument — tautness — as recorded in the M1-era assessment).
   Fact (a)'s pinching case needs χ ≤ 2 for connected closed surface
   complexes — a real theorem (tree–cotree: spanning tree of the
   1-skeleton plus dual spanning tree; "the edge-boundary of a face-set is
   an even subgraph because vertex links are cycles"). Mathlib has NO
   surface combinatorics, no planar Euler formula, no shellability, no
   pseudomanifolds; only `SimpleGraph` and spanning-tree existence
   (`Connected.exists_isTree_le`). The substrate must be built.

3. **Induction design.** The paper proves Th2 by minimal counterexample
   and says Th3 is "a corollary of the proof". Formally that means ONE
   merged strong induction on nrm M whose conclusion packages:
   simpliciality of M, support-is-a-ball, boundary = σ, and free
   shellability (the gluing lemmas in the reassembly steps need the free
   shellability of the sub-balls, so it must ride the induction).
   Getting this statement wrong means redoing the skeleton.

4. **Micro-lemma volume.** ~30–50 half-day facts ("the only edge that
   disappears is the flipped one", "at most 2 of the K₄ faces are on the
   boundary", "all degrees 4 ⟹ octahedron", base case "taut fillings of
   ∂Δ³ are single tets", link-connectivity preserved by flips). None
   deep; collectively the bulk.

Calibration: the original months figure was human-FTE. Given that M2–M6
(estimated 5–9 human-weeks) landed in one session, the realistic forecast
for Th2+Th3 is a few hard sessions IF the definitional layer survives
audit — the months-scale tail risk is definitional rework and the χ ≤ 2
lemma, not any single proof.

## 1. Proposed definitions (the audited artifact)

Vertex type `V`, `[LinearOrder V]`. A pure 2-complex is identified with
its facet set `σ : Finset (Finset V)` (members = 2-simplices, card 3),
as in the paper's "confound a pure complex with the set of its
n-simplices".

    edgesOf σ  := σ.biUnion (·.powersetCard 2)
    vertsOf σ  := σ.biUnion id
    edgeDeg σ e := #{f ∈ σ | e ⊆ f}
    skel σ      : SimpleGraph V := ⟨fun a b => a ≠ b ∧ {a,b} ∈ edgesOf σ, …⟩
    linkGraph σ v : SimpleGraph V := ⟨fun a b => a ≠ b ∧ {v,a,b} ∈ σ, …⟩
    linkVerts σ v := (vertsOf (σ.filter (v ∈ ·))).erase v
    ConnOn G s  := ∀ a ∈ s, ∀ b ∈ s, G.Reachable a b

    structure IsSphere2 (σ : Finset (Finset V)) : Prop where
      pure     : ∀ f ∈ σ, f.card = 3
      closed   : ∀ e ∈ edgesOf σ, edgeDeg σ e = 2          -- closed pm
      linkConn : ∀ v ∈ vertsOf σ, ConnOn (linkGraph σ v) (linkVerts σ v)
      conn     : ConnOn (skel σ) (vertsOf σ)
      euler    : (vertsOf σ).card + σ.card = (edgesOf σ).card + 2

Notes: χ = 2 is in the DEFINITION (so Euler relations 3f = 2e,
3v = e + 6, 2v = f + 4 are free arithmetic); "links are single cycles"
is NOT assumed — it follows: closed pm makes each link graph 2-regular,
and 2-regular + connected = one cycle (derived lemma, used for the
even-subgraph step of χ ≤ 2 and for mindeg ≥ 3).

Balls, via explicit shelling certificates (Lists, not an inductive Prop,
because the Th2 reassembly grafts shellings by list concatenation and
free shellability quantifies over the first element):

    IsShelling : List (Finset V) → Finset (Finset V) → Prop
    -- IsShelling l ∂ : the tets of l, glued in order, form a ball with
    -- boundary ∂.  [t] is a ball with ∂ = t.powersetCard 3 (t.card = 4);
    -- gluing t onto (τ, ∂) requires: t.card = 4, t ∉ τ,
    -- F := t.powersetCard 3 ∩ ∂ has card 1 or 2 (type-3 never needed),
    -- new boundary ∂' := (∂ \ F) ∪ (t.powersetCard 3 \ F),
    -- side condition: IsSphere2 ∂' (sphere-hood BAKED INTO the
    -- certificate, not derived — the Th2 induction has it available at
    -- every gluing step, and this keeps the definition's invariant
    -- self-evident).
    IsBall τ ∂        := ∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsShelling l ∂
    FreelyShellable τ ∂ := ∀ t ∈ τ, ∃ l, l.head? = some t ∧ …

Theorem 2+3 statement (merged conclusion, chain-first to dodge
orientability): for X a closed chain with coefficients in {−1,1} exactly
on σ := X.support, IsSphere2 σ, and M taut with bdry M = X:
∀ t, M t ∈ {−1,0,1}, and IsBall M.support σ, freely shellable.
Orientability of IsSphere2 (existence of such X) is NOT needed for
Th2–Th4 and is not claimed; X is input data, as in the paper ("let X(σ)
be either one of the 2-cycles").

## 2. Conventions

Unoriented complexes only; orientations stay in the chain layer (M2).
The bridge: `X.support = σ`, coefficients ±1; faces/edges of complexes
are bare Finsets. No geometric realization, no topology anywhere.

## 3. Validation invariants (build-checked)

(a) Counting: IsSphere2 σ → 3·σ.card = 2·(edgesOf σ).card,
    3·(vertsOf σ).card = (edgesOf σ).card + 6,
    2·(vertsOf σ).card = σ.card + 4.
(b) Instance: the boundary of a tetrahedron on any 4 distinct vertices
    satisfies IsSphere2 (semantic smoke test against a vacuous or
    over-strong definition; its links are triangles, so ConnOn is proved
    by single edges).
(c) Later, same file family: links are 2-regular; 2-regular + connected
    = single cycle; mindeg ≥ 3.

## 4. Failure modes caught

(a) catches a wrong edgesOf/edgeDeg (double counting breaks); (b)
catches over-strong definitions (unsatisfiable IsSphere2 would make
Th2 vacuous) and wrong link/connectivity encodings; the derived
links-are-cycles lemma cross-validates `closed` against `linkConn`.

## 5. Files and commands

    lean/Taut/Complex2.lean — definitions + (a),(b) now; link-cycle
                              lemmas next; flip dichotomy + χ ≤ 2 after.
    lean/Taut/Ball.lean     — IsShelling/IsBall/FreelyShellable (after
                              this audit settles Q2/Q3).
    Build: cd ~/Dropbox/taut/lean && lake build. Greps + #print axioms
    per commit gate, as in M2–M6.

## Questions for the auditor

Q1. IsSphere2: χ-in-the-definition + link-connectivity (deriving
    links-are-cycles), versus assuming links-are-cycles outright,
    versus an inductive (flip-reachable from ∂Δ³) definition — the
    last makes the splitting case of the flip dichotomy essentially
    unstatable, which is why it was rejected. Agree with the χ-based
    structure? Anything missing (e.g. is global `conn` redundant given
    `linkConn` + χ? — we believe NOT redundant and keep it)?
Q2. Balls as List shelling certificates with IsSphere2 of every
    intermediate boundary baked into the gluing condition: sound for the
    Th2 induction (tear down eligible tet / recurse / reassemble by
    concatenation)? Or is an inductive Prop with the same side
    conditions preferable despite harder grafting?
Q3. Free shellability as ∀ t ∈ τ, ∃ shelling with t FIRST (building up
    from t), matching the paper's shucking-in-reverse. The Th2 gluing
    lemmas (ball ∪_triangle ball, ball+tet+ball sandwich) consume it.
    Right primitive?
Q4. χ ≤ 2 for connected closed normal pseudo-surfaces via tree–cotree
    (Mathlib `Connected.exists_isTree_le` + even-subgraph-in-tree-is-
    empty + links-are-cycles): endorse this as the planned route for the
    flip dichotomy's splitting case, or propose simpler?
Q5. The chain↔complex bridge (σ := X.support, coefficients ±1, no
    orientability claim): any trap for Th2's induction, where sub-balls'
    boundary cycles must be re-derived after splitting along an edge?
