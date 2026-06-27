# tautA-gpt-01 report

Base file used:

- `taut-history-export/drafts_by_date/taut_2026-02-20_2b2e846.tex`

Later drafts consulted:

- `current_named_files/tautx.tex` for the later Theorem 1 wording, ordinary shelling/shucking section, and fuller flag-complex proof.
- `current_named_files/tauty.tex` and the history report for identifying which material was lost after the 2026-02-20 draft.

Major changes made:

- Kept the pre-break Triangulations section active, but rewrote it to be less jokey and more precise.
- Fixed the triangulation definition: a triangulation of a manifold `N` has carrier homeomorphic to `N`, not always to `S^2`.
- Standardized the filling variable in the 3-dimensional part to `M` rather than `Y`.
- Defined `K(M)` as the support complex of a simplicial chain.
- Defined a clean filling as a simplicial chain with clean support complex.
- Strengthened Theorem 2 to say that `M` is clean and `K(M)` triangulates `B^3`.
- Reworked Theorem 2 proof using the minimal-bad-pair induction, including the one-sphere and conjoined-spheres cases after removing an eligible tet.
- Imported the coefficient-aware eligible-tet count: use support tets and correctly oriented boundary faces, not coefficient copies.
- Replaced the old monotone-shelling stub with a shucking proof of free shellability.
- Used standard flag-complex terminology and the fuller later taboo-configuration argument.
- Removed the external BibTeX dependency and included a short inline bibliography so the file builds standalone.

Places where proof may still be sketched rather than complete:

- The final paragraph of Theorem 2, explaining why the reassembly preserves cleanness, is still compressed. It states the local link/face-incidence reason and the persistent-obstruction/minimality reason, but a fully definitive paper proof may want a separate lemma for clean gluing.
- The flag proof still uses the statement that a forced `K_5` would form the boundary of a 4-simplex and cannot occur in a triangulated 3-ball. This is fine as paper topology, but a purely combinatorial version might be preferable later.
- The octahedral exception in the flag proof is mentioned but not expanded.

Theorem statements needing human review:

- Theorem 2: currently states `M` is clean and `K(M)` triangulates `B^3`. This matches our current convention, but the exact wording of “clean” should be checked against the final desired terminology.
- Theorem 3: currently says freely shellable, not freely monotone shellable. This follows the later tautx terminology rather than the older tauty monotone formulation.

Build status:

- `pdflatex` ran successfully twice.
- Output: `tautA-gpt-01.pdf`, 14 pages.
- No Lean/formalization terminology is used.
