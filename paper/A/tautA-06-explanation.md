# tautA-06 explanation

Base file: `tautA-05.tex`.

Purpose: produce a minimal cleanup version for Claude/Codex sign-off, without reopening the proof or changing the new A05 strategy.

## Changes from A05

1. Version line updated:

   `Version A-05, dated 2026-06-27`

   became

   `Version A-06, dated 2026-06-27`.

2. In the proof of Theorem 4, Configuration 3 / K5, the phrase

   `by triangle-boundedness (Theorem 2)`

   was replaced by

   `by the pseudomanifold condition from Theorem 2`.

   Reason: A05's argument is correct, but `triangle-boundedness` is a new informal term. The proof should cite the actual property supplied by Theorem 2: the support complex is clean, hence pseudomanifold, so a triangle incident to the two K5 tetrahedra is incident to no other tetrahedron of M.

3. No other mathematical content was changed.

## What was intentionally left unchanged

- The new A05 K5 closed-subchain argument was kept.
- The new A05 K4 persistence argument was kept.
- The octahedral / maxdeg=4 case remains eliminated rather than treated separately.
- Theorem 2's cleanness persistence paragraph was left as paper-level prose.
- Corollary numbering was left as in A05: the new closed-subchain corollary is Corollary 1, and the old Qvol corollary is Corollary 2.

## Build status here

I built `tautA-06.pdf` locally from the TeX in `/mnt/data` using two `pdflatex` runs. The PDF renders correctly and is 15 pages.

Caveat: this sandbox does not have the project bibliography file `taut.bib`, so bibliography citations remain unresolved in my local build. In the project directory, run the full cycle:

    pdflatex tautA-06
    bibtex tautA-06
    pdflatex tautA-06
    pdflatex tautA-06

## Requested C/C check

Please check only the small delta from A05:

1. Confirm that replacing `triangle-boundedness` by `the pseudomanifold condition from Theorem 2` is the right wording.
2. Confirm that no hidden dependency on the old octahedron/maxdeg case has been reintroduced.
3. Confirm that the Corollary 1 / Corollary 2 numbering is intentional and acceptable.
4. Confirm that the PDF builds with resolved citations in `text/tautxy`.

If all four pass, `tautA-06` should be treated as the current signed-off A candidate.
