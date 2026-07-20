# tautA-04 explanation (joint Claude + Codex)

Base: `tautA-03.tex`. Both Claude and Codex reviewed tautA-03 and agreed it is a sound base for a
near-final version, needing a few substantive alignment fixes. Still paper-style prose: no Lean/
formalization terminology. We are striving for closure, so the remaining genuinely-hard items are flagged
for the authors rather than forced.

## What tautA-03 actually contributed (kept in 04)

The real, valuable change in tautA-03 was an **expanded Theorem-2 cleanness proof**: a "persistence
principle" (an obstruction to cleanness is *local* — one repeated tet, one over-incident triangle, or one
disconnected link — and removing an eligible tet disjoint from that witness makes it persist in the smaller
filling, contradicting minimality), together with an explicit first condition **"M has no repeated
tetrahedron"**, then the pseudomanifold, edge-link, and vertex-link conditions. Both reviewers judged this
correct and an improvement over v02; tautA-04 keeps it verbatim.

## Correction to the tautA-03 explanation

The tautA-03 explanation claimed four further changes that were **not actually present** in `tautA-03.tex`
(both reviewers verified this against the file):
- the abstract did not mention cleanness;
- the Overview did not say Theorem 2 gives a clean support complex;
- Theorem 3 was still phrased for "the taut filling", not for `K(M)`;
- Theorem 4 was still phrased for "the taut filling", not for `K(M)`.

tautA-04 **actually applies** these (they are genuine precision improvements):
1. Abstract: adds "The filling is clean: it repeats no tetrahedron, and its support complex is a clean
   simplicial complex."
2. Overview: Theorem 2 now stated as giving a clean filling with clean support `K(M)`.
3. Theorem 3: "If `M` is a taut filling of `X(σ)`, then `K(M)` is a freely shellable simplicial
   triangulation of `B^3`."
4. Theorem 4: "… then `K(M)` is a flag complex." (now labelled `th4`.)

## Build fix

tautA-03 was built without BibTeX, so its citations were unresolved. tautA-04 was built with the full
`pdflatex -> bibtex -> pdflatex -> pdflatex` cycle from `text/tautxy/` (where `taut.bib` lives). Result:
**15 pages, no errors, no undefined references, no undefined citations.**

## Remaining items deferred to the authors (closure, not solved)

Both reviewers agree these are the only non-trivial gaps left, and that they are author-level finite/topology
choices rather than blockers:
1. **Octahedral boundary (maxdeg = 4).** The text correctly shows that, with no degree-3 vertex,
   `maxdeg = 4` forces the octahedron (`v=6`); the finite check of its taut fillings is asserted, not
   written out. The single biggest non-expanded claim.
2. **K_5 step in the flag proof.** Relies on the standard topological fact that a triangulated `S^3`
   (the boundary of a 4-simplex) cannot sit as a subcomplex of a triangulated `B^3`. Acceptable paper
   topology; could be replaced by a purely combinatorial argument if desired.
3. **Eligible-tet avoidance lemma.** The persistence principle uses "enough eligible tets remain to avoid
   the witness", including the repeated-tet witness and the borderline `maxdeg = 4`. Sound as stated for a
   paper draft, but Codex suggests naming it as an explicit lemma; we left it inline for now.

## Status

Joint review: Claude and Codex independently examined tautA-03 and converged on exactly the four fixes above
plus the build fix. `tautA-04.tex` / `tautA-04.pdf` (15 pages) is the resulting joint near-final draft.
No commit.
