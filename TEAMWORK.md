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
- ROUTE CHANGE (PI, in session): tree–cotree for χ ≤ 2 is DROPPED — it was
  re-deriving a hypothesis we already have. χ = 2 is in IsSphere2, and the
  Euler–Poincaré identity χ = b₀ − b₁ + b₂ is pure linear algebra, so
  b₀ = 1 (conn) + b₂ = 1 (Doyle's "a 2-cycle has equal weight across every
  edge, hence constant") + the given χ = 2 force **b₁ = 0** (H₁ = 0,
  every 1-cycle bounds). The separation then falls out as a chain split
  feeding `IsTaut.splits`. Far cheaper, reuses the chain layer.
- `Taut/Homology2.lean` (M10) — COMPLETE and building: the 𝔽₂ chain
  complex (C0/C1/C2 as ↥Finset→ZMod 2, bd1/bd2 as LinearMaps),
  `bd1_comp_bd2` (∂∂=0, via "each vertex in exactly two of a triangle's
  edges"), `bd2_one` (all-faces fundamental cycle), `bd2_at_edge` (∂₂ at
  an edge = sum of its two faces), the dual graph + FULL dual connectivity
  (`dualGraph_preconnected`, from conn+linkConn+closed via two Walk
  inductions — the hard derived lemma), and **b₂ = 1**
  (`finrank_ker_bd2`: ker ∂₂ = span of the fundamental class). Axioms:
  standard three.
- G1 VERDICT (M10-M14, post-implementation): **APPROVED** — codex session
  019ec1fd-f620-7871-92f7-16fb7e06b717, output
  notes/codex-consults/2026-06-13-g1-homology-postimpl-output.txt. "No math
  blocker in the b₁=0 route; uses only IsSphere2.euler/conn/linkConn/closed
  + 𝔽₂ linear algebra; no hidden tree-cotree." Endorsed: LinearMap+Submodule
  encoding (Q1), const_of_adj_of_reachable/accumulate (Q2), 𝔽₂-then-reorient
  (Q3), two-layer separates (Q4). codex re-ran the build + #print axioms.
  Forward guidance: (i) the X=X₁+X₂ step needs an "orientation coherence"
  lemma (∂ of X restricted to a side = ±γ-boundary, from bdry X=0 + ±1
  coeffs + edge_cut_parity); (ii) linkConn for the pieces has NO obstruction
  (from original linkConn + cut boundary = exactly the two γ-edges at each
  γ-vertex, empty off γ); euler via additivity or direct counting.
- PROCESS FIX (root cause of the earlier "hangs"): the prior G1 attempts
  were mis-invoked — `codex exec "$PROMPT"` reads stdin (appends a <stdin>
  block) and BLOCKS until EOF; backgrounded with no redirect, stdin never
  closes, so codex sat at "Reading additional input from stdin..." forever.
  G2 worked only because it pipes a bundle (`< file`). FIX: always redirect
  stdin — `codex exec "$PROMPT" < /dev/null` for audits, or pipe a file.
  Verified: `codex exec "..." < /dev/null` returns in ~6s. NOT an infra
  problem; codex is reliable when stdin is given EOF.
- Homology2.lean (M11) — COMPLETE and building: the b₀=1/r₁ side and the
  watershed. `aug` (augmentation ε), `finrank_ker_aug` (= V−1),
  `bd1_single_pair` (∂₁ of an edge basis vector = its endpoint-indicator),
  `accumulate` (skeleton-walk accumulation: δ_u+δ_w ∈ range ∂₁), the two
  directions giving **`finrank_range_bd1` = V−1**, and **H₁ = 0**
  (`range_bd2_eq_ker_bd1`: range ∂₂ = ker ∂₁, from ∂∂=0 + equal finrank
  F−1 using the given χ=2). THE WATERSHED IS DONE — every 1-cycle on a
  combinatorial 2-sphere bounds. Axioms: standard three. (577 lines total.)
- `Taut/Separation.lean` (M12) — IN PROGRESS, building. `gammaChain` (the
  γ-edge 1-chain), `bd1_gammaChain` (it's a cycle), **`exists_cut`** (H₁=0
  ⟹ ∃ W, ∂₂W = γ-cycle — this is where the watershed is spent), `cutSet`
  (= W's support = one side σ₁), `edge_cut_parity` (across each edge the
  two faces' W-values sum to [e⊆γ] — the geometric cut), and **`closed_cut`**
  (each capped side `insert γ σ₁` is a closed pseudomanifold — the second
  IsSphere2 field). Axioms: standard three.
- M13 (in Separation.lean, building): `bd1_eval_two` (∂₁ at a vertex on
  exactly two support-edges = their coefficient sum) and **`gammaCycle_dichotomy`**
  (a 1-cycle supported on γ's edges is 0 or vγ — the load-bearing fact for
  both `conn` and the final piece-decomposition; ∂₁=0 forces the three
  triangle-edge coefficients equal). Axioms: standard three.
- M14 (in Separation.lean, building): **σ₁ is dual-connected**. `dualOn`
  (dual graph restricted to a side), `reachChain` (indicator of faces
  dual-reachable from a base face inside the side) + `reachChain_self`/
  `_closed`/`_mem`/`_zero`/`dualOn_walk_mem`, `bd2_reachChain_supp` (∂₂ of
  the reach-chain vanishes off γ-edges, by dual-closedness + the cut
  parity), and **`cutSet_dualConn`** (`reachChain = W`: every cut-face is
  dual-reachable from f₀ — via gammaCycle_dichotomy + ker ∂₂={0,𝟙}). The
  hard core of `conn`. Axioms: standard three.
- Next, to finish `separates`: (a) dual-conn ⟹ skeleton-`conn` for the
  pieces (a dual-walk → vertex-walk transport, ~50 lines); (b) **`linkConn`**
  (the genuinely hard field — at a γ-vertex the σ₁-faces form a connected
  arc of the link cycle, closed by γ; subgraph-of-a-cycle-with-2-odd-
  vertices-is-an-arc); (c) `euler` (χ-additivity + χ≤2 from b₂=1); (d)
  assemble `IsSphere2 (insert γ σᵢ)` (both sides: σ₂ = cutSet of W+𝟙);
  (e) reorient via the integral X to get X = X₁+X₂ feeding `IsTaut.splits`.
  Then the merged Th2+Th3 induction (eligible tets, flip, base case,
  shelling reassembly). NB: this is genuinely multi-session work — the
  watershed (M11) and the cut/closed/dual-conn (M12-14) are done; the
  remaining pieces-are-spheres (esp. linkConn) + induction are the bulk.
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

- 2026-06-12 (cont): PI redirected the watershed — dropped tree–cotree
  for the b₁=0 / Euler–Poincaré route (use the given χ=2 + b₂=1). M10 —
  Homology2.lean: 𝔽₂ chain complex, ∂∂=0, fundamental cycle, dual graph
  + full dual connectivity (two Walk inductions), and b₂=1. Build green,
  standard three axioms. G1 audit infra hung twice; proceeded per the
  process-friction clause (PI design + spec + pre-validated primitives +
  G2 backstop). → M10 committed.

- 2026-06-12 (cont): M11 — the r₁ side and the watershed itself. aug +
  finrank_ker_aug (V−1), bd1_single_pair, accumulate (skeleton-walk),
  finrank_range_bd1 (= V−1), and H₁ = 0 (range_bd2_eq_ker_bd1: every
  1-cycle on a sphere bounds). Build green, standard three axioms.
  → M11 commit pending G2.
