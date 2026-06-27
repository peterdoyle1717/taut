# tautA-claude-01 — report

Independent paper-style draft A produced by Claude. **Worked solo:** to honor the independence rule I
did not consult Codex and did not read `tautA-codex-01.tex` (it does not yet exist) or the pre-existing
`tautA2.tex`. No commits.

## Base file used

`drafts_by_date/taut_2026-02-20_2b2e846.tex` (the Feb-20 pre-break draft) — verbatim starting point.
It already had: Ω for the ambient vertex set, `M` for fillings in the front matter, a **live**
`\section{Triangulations}` with the clean-complex infrastructure, and the conjoined-case observation in
Theorem 2. It still used **`Y`** for the filling in the clean convention and in Theorem 2, had a terse
eligible-tet count, a placeholder (jokey) Theorem 3, and the short Configuration-2 flag argument.

## Later drafts consulted (for selective import only)

`drafts_by_date/taut_2026-WORKINGTREE_uncommitted.tex` (= "tautx"). I imported, where genuinely better:
the refined eligible-tet count (assign each boundary 2-simplex a properly-oriented support tet; at most
2-to-1); the explicit edge-flip / "conjoined" case split; the **shucking** proof of Theorem 3; and the
fuller flag Configuration-2 (octahedron special case, `maxdeg ≥ 5`, interior edge AD). I did **not**
import tautx's damage: I kept the Triangulations section live, kept Theorem 2's cleanness conclusion and
its explicit pseudomanifold/edge-link/vertex-link verification, and kept the conjoined-pieces remark.
I did not consult `pass1_minimal` (the Feb-20 base plus tautx covered every requested improvement).

## Major changes made

1. **Notation.** Filling `Y → M` throughout the clean convention and all of Theorem 2 (scoped: `Y`
   remains the second summand *cycle* in §Almost disjoint unions, where it is correct). Introduced
   `K(M)` for the support complex of a simplicial filling. Renamed the abstract manifold in the
   triangulation definition from `M` to `W` to avoid clashing with the filling `M`.
2. **Triangulations typo.** "a simplicial triangulation of `M` if the geometric carrier of `σ` is
   homeomorphic to `S^2`" → "...of `W` ... homeomorphic to `W`."
3. **Clean convention** stated as required: `M` is *simplicial* if no simplex is repeated; `K(M)` is its
   support; `M` is *clean* if simplicial and `K(M)` is clean. Specialized to fillings (tetrahedra).
4. **Theorem 2** restated: "`M` is clean, and its support `K(M)` is a simplicial triangulation of `B^3`."
   Kept the minimal-counterexample proof, refined the eligible-tet count to use **support tets and
   correct boundary signs** (not coefficient copies or cancelled appearances), made the edge-flip
   explicit, kept **both** cases (one sphere; two spheres *conjoined* along an edge), kept the remark
   that `M-t` need not be clean as one complex though it splits into clean pieces, kept the
   disjoint-eligible-tet argument ruling out multiplicity 2, and kept the explicit
   pseudomanifold/edge-link/vertex-link verification of cleanness.
5. **Shelling** rewritten around the **shucking** recursion (replacing the placeholder proof). Theorem 3
   states *freely shellable*; "monotone" is mentioned once (every shelling here is monotone, since
   type-3 gluing would bury an interior vertex) without proliferating terminology.
6. **Flag complex.** "flag complex" is the main term, "clique complex" parenthetical. Imported the
   fuller Configuration-2 (octahedron special case, `maxdeg ≥ 5`, interior edge AD, K₄ throughout —
   fixing the K₄/K₅ confusion). Fixed typos ("we would **have** the five...", "Since `σ` has no vertex
   of degree 3**,**", `K_3` vs "triangle").
7. **De-jokification** (paper register): removed "let's drag it out", "long-winded way of saying",
   "insists on being called a separate theorem", "through gritted teeth".

## Places where the proof is still sketched rather than complete

- **Flag, Configuration 2 — octahedron special case.** "Treating the octahedron separately as a special
  case, we may assume `maxdeg ≥ 5`." The octahedron (the unique min-degree case, all degrees 4) is named
  but not worked out. This is inherited from tautx; it needs a short separate argument or a citation.
- **Flag, taboo 3 ⇒ S³.** "the five associated 3-simplices ... would form an `S^3`, not possible as a
  subcomplex of the 3-ball `τ`." A correct but compact topological appeal (S³ ⊄ B³); a referee may want
  it expanded or attributed.
- **Theorem 1 proof** is carried out on the representative case `n=2`, `|C|=3` ("we might as well take
  n=2 ... this case illustrates all the issues"), as in the source. Faithful, but the general-`n`
  bookkeeping is by analogy, not written out.
- **Flag, Configuration 1** says "four choices of the edge to flip"; strictly there are at least `maxdeg`
  ≥ 4. Harmless, but slightly loose.

## Theorem statements whose wording may need human review

- **Theorem 2:** "Then `M` is clean, and its support `K(M)` is a simplicial triangulation of `B^3`."
  (This is the requested form; please confirm "simplicial triangulation of `B^3`" reads as intended —
  carrier homeomorphic to `B^3`.)
- **Theorem 3:** phrased as "`M` is freely shellable: its support `τ=K(M)` is a ... triangulation of
  `B^3` admitting a shelling that begins with any prescribed tet." Confirm you are happy dropping the
  named property "freely *monotone* shellable" in favor of "freely shellable" + the monotone remark.
- **Flag theorem** is unlabeled (no `\label`) in the source; left as is.

## Does the PDF build?

**Yes.** `pdflatex → bibtex → pdflatex → pdflatex` (TeX Live 2010 x86_64 under Rosetta; `taut.bib` is in
the directory). Final pass: **0 errors, 0 undefined references, 0 undefined citations.**
`tautA-claude-01.pdf` = **14 pages**.

## Deliverables

- `text/tautxy/tautA-claude-01.tex`
- `text/tautxy/tautA-claude-01.pdf`
- `text/tautxy/tautA-claude-01-report.md`
