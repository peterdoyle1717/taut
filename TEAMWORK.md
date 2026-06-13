# TEAMWORK baton — taut fillings formalization

## Goal

Formalize the results of `taut/taut.tex` (Doyle–Ellison–Wang, "Taut
fillings") in Lean 4 + Mathlib, combinatorially (no topology): Props 1–4,
Theorem 1 (Zvol additivity + taut splitting for n ≥ 2), Corollary 1, then
(stretch, later sessions) the S²/B³ results Th2–Th4 via combinatorial
sphere/ball definitions.

## Live state (update on every milestone)

- Lean project: `lean/` (Mathlib v4.29.1, packages cached at
  `~/.cache/taut-lean/packages`, APFS-cloned from glove). Builds:
  `cd lean && lake build`.
- G1 design audit of the chain encoding:
  spec `notes/codex-consults/2026-06-11-g1-chain-encoding-spec.md`,
  output `...-output.txt` — verdict: APPROVED
  (codex session 019eb8d8-8926-75c2-b3cd-608c743bd5a4).
- Files: `Taut/Chains.lean` — COMPLETE and building: cnt/sgn sign library
  (incl. the two cancellation lemmas the auditor asked for), bdry, cone,
  lk, nbhd, vert, nrm, deg; proven invariants: ∂∂=0
  (`bdry_bdry`), exact global homotopy (`bdry_cone_add_cone_bdry`),
  `cone_lk`, localization (`nbhd_bdry_nbhd`), cone injectivity
  (`eq_nbhd_of_cone_eq_zero`), norm accounting (`nrm_cone_add_deg`).
  Axioms of all of the above: propext, Classical.choice, Quot.sound.
- `Taut/Zvol.lean` — COMPLETE and building: SubChain (+ support/norm-split
  lemmas), Zvol, IsTaut; Props 1–4 proven: `IsTaut.subChain`,
  `Zvol_add_deg_le`, `not_taut_complete_cone`,
  `IsTaut.no_internal_vertex` (with the 2 ≤ card dimension guard).
  Axioms: standard three.
- `Taut/Projection.lean` — COMPLETE and building: Kkills/KGen/Kmap,
  chain-map property `bdry_Kmap` (∂∘K=K∘∂), norm accounting
  `nrm_Kmap_add_killed_le`, triviality `eq_zero_of_supp_card_lt` /
  `eq_zero_of_closed_supp_card_eq`. Axioms: standard three.
- `Taut/Theorem1.lean` — COMPLETE and building: dimPart + grading
  (`dimPart_bdry`), purity of taut chains (`IsTaut.dim_pure`),
  `IsTaut.vert_subset`, `Kmap_eq_self`, recovery
  (`Kmap_eq_zero_of_closed`), kill lemma (`Kkills_or_Kkills`, general n),
  and THEOREM 1 PART 1: `Zvol_add_of_almost_disjoint` (general n ≥ 1,
  under p ≠ q ∈ A∩B; the |A∩B| ≤ 1 cases are open targets, NOT assumed).
  Axioms: standard three.
- `Taut/Splitting.lean` — COMPLETE and building: kill certificates,
  strengthened mass bound, `no_double_kill`, `hybrid_structure`,
  `no_extreme_hybrid` (the complete-cone argument, coefficient-level),
  and THEOREM 1 PART 2: `IsTaut.splits` (n ≥ 2, general dimension,
  constructive split by filtering along `· ⊆ A`). Axioms: standard three.
  PAPER STATUS: Props 1-4 and Theorem 1 (both parts) fully formalized.
- G1 audit #2 (sphere/ball layer for Th2-Th4): spec
  notes/codex-consults/2026-06-12-g1-sphere-ball-spec.md — APPROVED.
  Notes of record: keep `conn` in IsSphere2 (χ alone admits torus
  components); balls = List shelling certificates, documented as
  "shelling-certified balls"; free shellability = ∀ t, ∃ shelling with t
  first; χ ≤ 2 via tree-cotree (even-boundary-in-tree + dual-graph
  connectedness are first-class milestones); after any split, repackage
  component boundaries as closed ±1-support sphere cycles before
  recursing; Th4's S³⊄B³ replacement = first-class chain obligation.
- `Taut/Complex2.lean` — COMPLETE and building: edgesOf/vertsOf/edgeDeg,
  skel, linkGraph, linkVerts, ConnOn, IsSphere2; Euler counting
  (3f = 2e, 3v = e+6, 2v = f+4); validation instance isSphere2_tetraBdry
  (generic 4 vertices). Axioms: standard three.
- Sphere local structure (M8) — COMPLETE: exists_third,
  exists_two_faces, inter_eq_edge_of_two_faces, mem_linkVerts(_iff_edge),
  link_two_regular, three_le_card_linkVerts, Decidable adjacencies.
- `Taut/Ball.lean` (M9) — COMPLETE and building: the audited Q2/Q3
  shelling-certificate layer. `tetFaces`, `GlueStep` (type 1/2 glue,
  symmetric-difference boundary, IsSphere2 baked in), `ShellFrom`
  accumulator, `IsShelling`, `IsBall` (shelling-certified ball),
  `FreelyShellable`. Validation: `IsBall.isSphere2` (boundary of a ball
  is a sphere), `isBall_singleton`/`freelyShellable_singleton` (a single
  tet is a freely shellable ball). Plus `isSphere2_powersetCard3` in
  Complex2 (base-case sphere = boundary of any 4-set). Axioms: standard
  three. NOTE: GlueStep's sym-diff formula is exercised structurally but
  not yet on a worked multi-tet sphere (e.g. bipyramid) — that lands for
  free with the flip dichotomy / induction, or as a later smoke test.
- Next (the watershed): the χ ≤ 2 packet — needs its OWN G1 audit (new
  encodings: closed-surface predicate sans χ; dual graph on faces;
  boundary ∂S of a face-set; even-subgraph; tree-cotree). Planned route
  (elementary, avoids 𝔽₂ linear algebra): edge-DISJOINT spanning trees of
  skeleton (V−1 edges) and dual graph (F−1 edges) ⟹ E ≥ V+F−2 ⟹ χ ≤ 2.
  Three lemmas: (L1) dual connectivity from conn+linkConn+closed; (L2)
  ∂S even subgraph from links-are-cycles; (L3) even subgraph in a forest
  is empty. Technical wrinkle to audit: complexes live in arbitrary `V`
  (infinite); spanning-tree API wants the graph on the vertex subtype/
  Fintype `{x // x ∈ vertsOf σ}`. Then flip dichotomy, then merged
  Th2+Th3 induction (assembly).
- Open targets (not assumed anywhere): Corollary 1 (ℚ-fillings, via
  clearing denominators); |A∩B| ≤ 1 cases of Th1; Th2-Th4 remainder.

## Design decisions of record (G1-audited)

- Chains: `Chain V := Finset V →₀ ℤ`, dimension-mixed, AUGMENTED (∅ is a
  generator). Canonical orientation = increasing vertex order.
- Signs: `cnt x s = #{y ∈ s | y < x}`, `sgn x s = (-1)^cnt`. ∂, cone, lk,
  K_{A,p} per the G1 spec. Validation invariants: ∂∘∂ = 0; exact global
  homotopy ∂(cone x M) + cone x (∂M) = M; cone x (lk x M) = nbhd x M;
  ∂ ∘ K = K ∘ ∂; norm accounting (no silent cancellation).
- Norm `nrm` into ℕ; `SubChain U M := ∀ s, |U s| + |M s − U s| = |M s|`;
  `Zvol X := sInf {nrm M | ∂M = X}`; `IsTaut M := nrm M = Zvol (∂M)`.
- Zvol-existence lemmas carry an explicit vertex `x : V` (V may be empty).
- Prop "nocone" needs the cone apex x with `deg x W = 0` AND a witness
  vertex `x'` with `deg x' W ≠ 0` (excludes the (−1)-dim cone, where the
  statement is false — found during design).

## History

- 2026-06-11: repo init (45ada4e: paper sources). Assessment written
  (conversation). Lean scaffold + Mathlib cache clone. G1 spec written,
  codex audit launched.

- 2026-06-11 (cont): G1 verdict APPROVED. Chains.lean complete and building:
  sign library, bdry/cone/lk/nbhd/vert/nrm/deg, ∂∂=0, homotopy identity,
  cone_lk, localization, cone injectivity, norm accounting. Axioms:
  standard three only. → M2 committed.

- 2026-06-12: M9 — Ball.lean, the shelling-certificate layer (audited
  Q2/Q3). Shelling-certified balls as List certificates with IsSphere2
  baked into each glue; boundary-of-ball-is-sphere; single tet is a
  freely shellable ball. Base-case sphere isSphere2_powersetCard3 added
  to Complex2. Build green, standard three axioms. → M9 committed.
