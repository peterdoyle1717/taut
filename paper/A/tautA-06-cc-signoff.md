# tautA-06 — Claude + Codex sign-off

**PASS: tautA-06 is safe as the current final Version A candidate.**

Both reviewers (Claude and Codex) independently checked `text/tautxy/tautA-06.tex` and agree.

## Delta from A-05 (verified by diff)

The only changes from `tautA-05.tex` are exactly the two intended ones:
- the version line `Version A-05, …` → `Version A-06, dated 2026-06-27`;
- in the flag proof's K5 step, "by triangle-boundedness (Theorem 2)" → "by the pseudomanifold condition
  from Theorem 2" (with a one-sentence prose tidy in the same sentence).

No other mathematical content changed.

## Checks (all pass)

1. **Build** — full cycle from `text/tautxy/` (`pdflatex; bibtex; pdflatex; pdflatex`): **15 pages, 0
   errors, 0 undefined references, 0 undefined citations.**
2. **Version line** — `\date{Version A-06, dated 2026-06-27}`.
3. **Theorem statements** —
   - Th 2: "$M$ is clean and $K(M)$ is a simplicial triangulation of $B^3$";
   - Th 3: "$K(M)$ is a freely shellable simplicial triangulation of $B^3$";
   - Th 4: "$K(M)$ is a flag complex".
4. **K5 argument sound (new wording).** The five $K_4$ tetrahedra form a nonzero subchain $U$; each of the
   ten triangles is incident to exactly two of them; by the pseudomanifold condition supplied by
   Theorem 2 (a clean complex is a pseudomanifold, so each triangle lies in at most two tetrahedra) these
   two are the only tetrahedra of $M$ containing it; hence the triangle is interior, not a face of
   $\sigma$, with coefficient $0$ in $\partial M = X(\sigma)$; so $\partial U = 0$; by the Corollary (a
   taut chain has no nonzero closed subchain) $U = 0$, contradiction. The "pseudomanifold condition from
   Theorem 2" citation is accurate and is in fact more precise than the former "triangle-boundedness".
5. **K4 argument sound.** With Configuration 1 ruled out, all four $K_4$ triangles are simplices; removing
   any eligible tet preserves each $K_4$ edge (each edge lies in two $K_4$ triangles, and the removed tet
   cannot contain both without being the absent $K_4$ tetrahedron); removal creates no tetrahedron; so the
   empty $K_4$ persists, giving a smaller counterexample. **No `maxdeg = 4` / octahedron special case
   remains.**
6. **Theorem 2 cleanness paragraph** (repeated tetrahedron / over-incident triangle / disconnected edge
   link / disconnected vertex link) is acceptable at paper level; no actual false statement found.
7. **No Lean names or formalization-status commentary** leaked into the text.
8. **No unresolved placeholders** ("finite check", "octahedron case remains", "to be checked", "TODO",
   "sorry", "Lean", "formal endpoint"). The single "octahedral" occurrence is the closing sentence stating
   that no octahedral special case is needed.

## Verdicts

- **Claude:** PASS.
- **Codex:** PASS — "tautA-06 is safe as the current final Version A candidate." Blockers: none. (Consult
  log: `notes/codex-consults/2026-06-27-…-g3-tautA06-signoff-*`.)

No commit.
