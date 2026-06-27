# tautA-03 explanation

Base: `tautA-02.tex`, the Claude+Codex joint version 02.

Purpose: produce a next A-line draft for review by C/C.  This is still paper-style prose: no Lean endpoint names and no formalization-status language.

## Main changes from tautA-02

1. **Abstract now mentions cleanness explicitly.**
   Version 02 said any taut filling arises from a ball extension and that the complex is shellable/flag.  Version 03 also says the filling is clean: no repeated tetrahedra, and clean support complex.

2. **Overview now says Theorem 2 gives clean support complex.**
   This keeps the paper goal visible from the start, instead of letting cleanness first appear in the proof.

3. **Theorem 3 is stated literally for `K(M)`.**
   Version 02 said a taut filling is a freely shellable simplicial triangulation.  Since the filling is a chain, version 03 says: if `M` is a taut filling, then `K(M)` is freely shellable.

4. **Theorem 4 is stated literally for `K(M)`.**
   Version 02 said a taut filling is a flag complex.  Version 03 says `K(M)` is a flag complex.

5. **The final cleanness check in Theorem 2 is expanded.**
   Version 02 had three bullets for pseudomanifold, edge links, and vertex links, after a sentence saying the remaining clean conditions follow by the same minimality argument.  Version 03 inserts a persistence principle and adds the missing condition that `M` has no repeated tetrahedron.

6. **The conjoined-case exception is kept explicit.**
   Version 03 preserves the point that `K(M-u)` may fail to be clean as a single complex because the new common edge can have disconnected link; this is why the proof splits into two summands before applying induction.

7. **The octahedron line is softened but not solved.**
   Version 02 said the octahedral boundary case is handled by a finite check using the same flip alternatives.  Version 03 makes this a little more explicit, but it remains a review item.

## Remaining review items

1. **Eligible-tet avoidance in the cleanness proof.**
   Version 03 says local obstructions can be preserved by removing a suitable eligible tet whose boundary faces avoid the witness.  This is the intended minimality argument, but C/C should check whether the eligible-tet count as stated is strong enough in every borderline case, or whether the proof needs a separate lemma.

2. **Repeated tetrahedron argument.**
   Version 03 adds the missing “no repeated tetrahedron” bullet.  C/C should check whether the choice of an eligible tet avoiding a repeated support tet is fully justified, especially when `maxdeg = 4`.

3. **Edge-link connectedness.**
   The version 03 paragraph is more explicit than version 02 but still compressed.  C/C should check the isolated-edge-component exception and the conjoined split localization.

4. **Flag theorem, `K_5` shortcut.**
   The topological statement that a triangulated `S^3` cannot occur as a subcomplex of a triangulated `B^3` is acceptable paper topology if we want it, but it should be verified or replaced in B/C.

5. **Flag theorem, octahedral boundary.**
   The finite-check line is still a placeholder unless the direct check is supplied elsewhere.  This is probably the biggest remaining non-expanded claim in A.

## Build

`pdflatex` was run twice.  The PDF builds as 14 pages.  The usual bibliography citations are unresolved in this standalone environment because no `.bib/.bbl` file was supplied here.
