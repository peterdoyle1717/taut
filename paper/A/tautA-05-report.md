# tautA-05 report (stabilization of A-04; Claude + Codex agreed)

**Base file:** `text/tautxy/tautA-04.tex`. Output: `tautA-05.tex`, `tautA-05.pdf`, this report.
Paper-style throughout: no Lean names, no endpoint names, no formalization-status commentary
(Codex independently confirmed none leaked). No commit.

## Mechanical fixes

1. Date line changed from "Version A-03 (GPT revision of joint 02)" to `\date{Version A-05, dated 2026-06-27}`.
2. The corrupted `\tau` in the old octahedron sentence (a literal TAB had replaced `\t`, rendering as
   "au") is gone — that sentence was removed in the flag rewrite below.
3. Rebuilt with the full cycle from `text/tautxy/`: `pdflatex → bibtex → pdflatex → pdflatex`. **15 pages,
   0 errors, 0 undefined references, 0 undefined citations.**

## How the octahedral / maxdeg = 4 issue was handled

**Eliminated, not deferred.** The A-04 flag proof reached the octahedral boundary as an unsatisfying
"finite list checked directly" placeholder, because its Configuration-2 argument needed `maxdeg ≥ 5`.
A-05 replaces that whole argument with a **persistence** argument that needs no degree bound:

> Once empty triangles are ruled out, the four faces `ABC, ABD, ACD, BCD` of a would-be empty `K_4` are
> all simplices. Removing **any** eligible tetrahedron `t` leaves the empty `K_4` intact: for each edge,
> say `AB`, at least one of the triangles `ABC, ABD` is not contained in `t` (containing both would make
> `t = {A,B,C,D}`, not a tetrahedron), and that triangle, being a simplex, lies in some tetrahedron
> `u ≠ t`, so `AB` survives. Hence any single eligible removal yields a smaller counterexample.

With no `maxdeg` threshold there is no exceptional case, so the octahedron never arises. This mirrors the
topology-free Lean argument (`hasEmptyK4_removeTet_of_eligible`).

## Is the flag proof complete?

**Yes — complete, with no finite-case placeholder.** The three configurations are now ruled out by:
- **Config 1 (empty `K_3`):** flip count — at least `maxdeg(σ) ≥ 4` eligible tets with *distinct* flip
  edges versus only three forbidden edges, so some removal preserves the triangle.
- **Config 2 (empty `K_4`):** the persistence argument above (any eligible removal preserves it).
- **Config 3 (`K_5`):** replaced the topological "`S^3` cannot embed in `B^3`" step with a one-line
  consequence of Proposition 1. A new **Corollary** ("a taut chain contains no nonzero closed subchain")
  is added after Proposition 1; the five tetrahedra on the `K_5` vertices form a subchain `U` whose every
  boundary triangle is interior (hence has coefficient 0 in `∂M = X(σ)`), so `∂U = 0` and the corollary
  forces `U = 0`, contradicting that `U` has five tetrahedra. No topology.

Codex reviewed all of these and returned **PASS**, "sound, complete paper-style version A," no blockers.

## Other substantive/prose revisions (per the A-05 request)

- **Theorem 2 local-witness paragraph (directive D):** the risky "remove an eligible tet whose two
  boundary faces are disjoint from the boundary faces involved in that witness" is replaced by "choose an
  eligible tet whose two boundary faces are disjoint from the *finitely many boundary faces needed to
  change* that local witness," with the three concrete instances (repeated tetrahedron / over-incident
  triangle / disconnected link) spelled out. No longer implies every witness literally has boundary faces.
- **K₅ topological shortcut removed** (see Config 3 above).
- **Abstract:** "it has no repeated tetrahedron" (not "repeats no tetrahedron"); "This support complex is
  shellable and flag:" (no scare quotes around flag).
- **Overview:** "Theorem 2 states that any taut filling of `X(σ)` is clean and that its support complex
  `K(M)` triangulates `B^3`." (no doubled "clean").
- **Theorems 3 & 4 proofs:** "By Theorem 2, `K(M)` is a triangulated ball; write `τ = K(M)`." / "Let
  `τ = K(M)`."
- Structure preserved: Triangulations section active; clean complex defined intrinsically; `M` clean iff
  simplicial (no repeated tetrahedra) and `K(M)` clean; Theorem 2 gives `M` clean and `K(M)` triangulating
  `B^3`; Theorems 3, 4 stated for `K(M)`.

## Remaining author-level review items (none blocking)

- The Config-1 step uses "removing an eligible tet deletes from `τ` only the flipped edge" — the standard
  property of a `2`–`2` bistellar flip, stated but not re-derived.
- The conjoined-split localization ("a forbidden `K_3`/`K_4` lies on one side") is stated at paper level;
  it rests on the taboo's vertices being mutually joined by edges, so they cannot straddle the single
  shared edge.
- Theorem 2's clean-complex "persistence" paragraph remains paper-level; the underlying avoidance is the
  eligible-tet count (more eligible tets than the bounded witness touches).

## Status

Build: 15 pages, citations and references resolve. Claude and Codex agree this is a sound, complete
paper-style version A; the flag proof is complete and the octahedron case is gone. No commit.
