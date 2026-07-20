# tautA-codex-01 report

## Base and sources

- Base file used: `drafts_by_date/taut_2026-02-20_2b2e846.tex`.
- Later drafts consulted selectively: `text/tautxy/tautx.tex` and `text/tautxy/tautx_pass1_minimal.tex`.
- Independence constraint observed: I did not open or read `text/tautxy/tautA-claude-01.tex`, its report/PDF, or `text/tautxy/tautA2.tex`/PDF.

## Major changes made

- Preserved the active Triangulations section and rewrote it as paper terminology:
  clean complexes are defined intrinsically; an abstract triangulated manifold is named `W`; a filling is named `M`; and `K(M)` is defined as the support complex.
- Standardized filling notation in the repaired parts: fillings use `M`, the ambient vertex set remains `\Omega`, and the almost-disjoint-union summand `Y` in `X+Y` was left unchanged.
- Repaired Theorem 2 to state that a taut filling `M` is clean and that `K(M)` is a simplicial triangulation of `B^3`.
- Imported and tightened the later eligible-tet count using support tetrahedra of a coefficiented chain, with boundary faces counted only when they occur with the correct orientation.
- Reframed the Theorem 2 proof using minimal bad filling pairs.  Both eligible-tet cases are included: the flipped boundary remains one sphere, or it becomes two spheres conjoined along an edge.
- In the conjoined case, explicitly noted that `K(M-t)` need not be clean as one complex, while it splits into clean pieces `K(M_1)` and `K(M_2)` by induction.
- Replaced the rough shelling paragraph with the shucking/dismantling proof, phrased as an ordinary shelling argument.
- Reworked the flag section to use “flag complex” (with “clique complex” parenthetically), corrected Configuration 2 as the `K_4` on `{A,B,C,D}`, and removed informal prose.
- Fixed typos and incomplete/provisional wording, including the triangulation carrier typo and the `CV = A \cap B` typo in Theorem 1's proof.

## Remaining proof-sketch areas

- The final clean-complex verification in Theorem 2 still uses compressed minimality arguments for pseudomanifoldness and connected links.  It is paper-style, but a human may want to expand the persistence argument in the conjoined case.
- The shelling proof is still recursive and concise.  It states the shucking procedure and its reversal but does not spell out every topological verification after each removal.
- The flag proof still contains a direct-check placeholder for the octahedral boundary case when `\maxdeg(\sigma)=4`.
- The exclusion of the `K_5` configuration uses the topological fact that the boundary of a 4-simplex cannot occur as a subcomplex of a triangulated 3-ball; this may deserve a cited lemma or a short justification.

## Theorem statements needing possible human review

- Theorem 2: wording is now `If \sigma is a simplicial triangulation of S^2 and M is a taut filling of X(\sigma), then M is clean and K(M) is a simplicial triangulation of B^3.`  This matches the requested convention, but the phrase “taut filling of `X(\sigma)`” should be checked against the authors' preferred shorthand “taut filling of `\sigma`.”
- Theorem 3: “freely shellable” is used for the shellings produced by shucking, with the text noting that three-face moves do not occur.  If the authors want the older “freely monotone shellable” term retained, the statement can be renamed.
- The flag theorem states that any taut filling of `X(\sigma)` is a flag complex, relying on the identification with `K(M)` after Theorem 2.  A more explicit statement could say `K(M)` is flag.

## Build status

- PDF build: succeeded.
- Build command cycle run from `text/tautxy/`:
  `pdflatex -interaction=nonstopmode tautA-codex-01.tex`,
  `bibtex tautA-codex-01`,
  `pdflatex -interaction=nonstopmode tautA-codex-01.tex`,
  `pdflatex -interaction=nonstopmode tautA-codex-01.tex`.
- Final log status: no unresolved references or undefined citations found.  The log reports only overfull hbox warnings.
