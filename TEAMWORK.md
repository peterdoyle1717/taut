# TEAMWORK baton — taut fillings formalization

> ## ⟲ RECOVERY CHECKPOINT — `fable-axed` (commit `a8a8954`, branch `main`)
> The canonical "where we were when Fable was removed" state. To return to it
> exactly: `git checkout fable-axed`. Full details + recovery commands +
> what-remains in **`RECOVERY.md`**. State: M9–M16 (watershed H₁=0 + most of
> the separation), G1-APPROVED, build green, no sorry/admit, standard axioms.
>
> **Protocol (Fable removed):** back to codex doing the architecture — G1
> design audit before new load-bearing code, G2 gate on every commit.
> Run codex with `< /dev/null` (no stdin redirect ⇒ it hangs; not infra).

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
- M15 (in Separation.lean, building): **`conn` for the capped side**. Generic
  `skel_reach_within`, `dualwalk_skel`, `skelConn_of_dualPreconn` (dual-
  preconnected ⟹ skeleton-connected, reusable), `dualOn_skel_insert` (a
  dualOn walk among cut-faces → skeleton walk in `insert γ σ₁`), and
  **`conn_cut`** (skel of `insert γ (cutSet σ W)` connected — every vertex
  reaches a base cut-face vertex; cut-faces via the transport, γ via its
  shared edge with a cut-face). So pieces now have pure+closed+conn.
- M16 (in Separation.lean, building): **`linkConn` infrastructure + the v∉γ
  half**. `W_eq_of_share_edge` (two faces sharing a non-γ edge are same-side,
  from edge_cut_parity), `W_eq_along_link` (W constant along a link walk at
  v∉γ), `W_const_at` (all faces through an off-γ vertex are same-side, via
  linkConn σ). So for v ∉ γ, the cut faces at v are all-σ₁-or-all-σ₂ ⟹
  linkGraph of the piece at v = linkGraph σ at v ⟹ linkConn inherited.
- G1 VERDICT (linkConn v∈γ packet): **APPROVED** — codex session
  019ec22b-9f84-7ea2-8bcd-09da5de864c7, output
  notes/codex-consults/2026-06-13-g1-linkconn-output.txt. KEY RULING: **avoid
  `IsCycles` and any explicit "single-arc" theorem** — they drag in Set
  neighbor-sets and only give per-component cycles. Instead use a local-
  closure + walk-reroute proof (mirrors `W_eq_along_link`):
  1. `gamma_endpoints_at` — γ = {v,a,b}, a≠b, a≠v, b≠v (the flip vertices are
     the OTHER two, not all 3);
  2. `gamma_chord_adj` — `(linkGraph τ v).Adj a b` (γ ∈ τ);
  3. `cut_link_closure_nonendpoint` — x ∈ linkVerts τ v, x ∉ γ,
     `(linkGraph σ v).Adj x y` ⟹ `(linkGraph τ v).Adj x y` (x∉γ ⟹ {v,x}
     non-γ ⟹ W_eq_of_share_edge forces every σ-face thru {v,x} same-side,
     so {v,x,y} ∈ cutSet ⊆ τ);
  4. `reroute_to_gamma_endpoint` — induct a σ-link walk x→a to a τ-link
     reach: at a stop; at b use chord; else lift via (3);
  5. `linkConn_cut_at_gamma` + combine with the v∉γ case ⟹ full `linkConn_cut`.
  Trap: for x∈linkVerts τ v with x∉γ the witness face can't be γ (the bridge
  to a cut face). euler: χ-additivity (state vertsOf/edgesOf/τ₁∩τ₂ set lemmas
  first; χτ₁+χτ₂=4) — but needs a **generalized χ≤2 lemma for connected closed
  pure 2-complexes with connected links** (small refactor of the M10 dual-conn/
  rank machinery off `IsSphere2`). σ₂ side mirrors via `bd2 (W+𝟙)=gammaChain`.
- M17 (DONE, Separation.lean, building): **`linkConn_cut` — both cases**, via
  the codex-approved local-closure + reroute route (NO IsCycles). New lemmas:
  `face_two_ne`, `gamma_endpoints_at`, `gamma_chord_adj`,
  `cut_link_closure_nonendpoint` (at a non-γ link vertex every σ-link edge is a
  τ-link edge), `reroute_to_gamma_endpoint` (a walk to any γ-vertex lifts to a
  τ-reach of `a`; endpoint kept generic to avoid pinning the induction),
  `linkConn_cut_at_gamma` (v∈γ), `linkGraph_le_cut_nonendpoint` +
  `linkConn_cut_off_gamma` (v∉γ, via `Reachable.mono` on the subgraph), and
  `linkConn_cut`. Build green (8258 jobs), no sorry, standard three axioms.
- NEXT (approved): `euler` for the pieces. Plan (codex Q4): χ-additivity with
  explicit set lemmas (vertsOf τ₁∪τ₂=vertsOf σ, ∩=γ; edgesOf likewise;
  τ₁∩τ₂={γ}) ⟹ χτ₁+χτ₂=4; needs a **generalized χ≤2** for connected closed
  pure 2-complexes with connected links (refactor the M10 dual-conn/rank
  machinery off `IsSphere2`). Then assemble `IsSphere2 (insert γ σᵢ)` both
  sides (σ₂ via `bd2 (W+𝟙)=gammaChain`), then X=X₁+X₂ → `IsTaut.splits`, then
  the Th2+Th3 induction (own G1 audit).
- G1 VERDICT (euler packet): **APPROVED** — codex session
  019ec247-f4dc-7eb0-8f2c-70cdf163ff64, output
  notes/codex-consults/2026-06-13-g1-euler-output.txt. Rulings:
  • **Option C**: add `structure IsClosedSurface` (pure+closed+linkConn+conn)
    BEFORE IsSphere2, keep IsSphere2 unchanged, add forgetful
    `IsSphere2.toClosedSurface`. NOT `extends` (would churn every constructor).
  • **χ≤2** (no euler): b₂=1 + r₁=V−1 + `range bd2 ≤ ker bd1`
    (`LinearMap.range_le_ker_iff.mpr (bd1_comp_bd2 σ h.pure)`, then
    `Submodule.finrank_mono`) ⟹ (F−1) ≤ (E−(V−1)) ⟹ V−E+F ≤ 2. Carry
    `(vertsOf σ).Nonempty` explicitly (IsClosedSurface vacuous on ∅; recover
    σ.Nonempty via mem_vertsOf for finrank_ker_bd2).
  • Generalize {dualGraph_preconnected, finrank_ker_bd2 (+ker_bd2_eq_span),
    finrank_ker_aug, bd1_single_pair, accumulate, finrank_range_bd1} to take
    IsClosedSurface+nonempty; watershed passes toClosedSurface+vertsOf_nonempty.
    finrank_range_bd1 does NOT smuggle euler (only conn + vertex nonemptiness).
  • **Additivity** χτ₁+χτ₂=4, via counts V₁+V₂=Vσ+3, E₁+E₂=Eσ+3, F₁+F₂=Fσ+2
    (incl-excl: vertsOf τ₁∪τ₂=vertsOf σ & ∩=γ; edgesOf likewise & ∩=γ.pwsCard2;
    τ₁∪τ₂=σ∪{γ} & ∩={γ}). Lemmas: `Finset.card_union_add_card_inter`,
    `card_insert_of_notMem`, `card_powersetCard`. Then with σ.euler + χ≤2 each,
    `omega` ⟹ both euler. Every γ-edge in BOTH pieces (γ inserted in both);
    excluding non-γ edges from the ∩ uses cut parity (edge_cut_parity).
  • σ₂ side mirrors: `bd2 (W+𝟙)=gammaChain` (map_add+hW+bd2_one); optional
    `cutSet σ (W+𝟙) = σ \ cutSet σ W`. Show γ's verts/edges ⊆ σ via hγe first.
- M18 (DONE, building): **IsClosedSurface + generalized homology + chi_le_two.**
  `structure IsClosedSurface` (pure+closed+linkConn+conn) + `IsSphere2.toClosedSurface`
  in Complex2. Generalized {exists_two_faces, dualGraph_ker_const, linkwalk_dual,
  dual_reach_shared_vertex, skelwalk_dual, dualGraph_preconnected, bd2_ker_constant,
  ker_bd2_eq_span, finrank_ker_bd2, finrank_ker_aug, ker_aug_le_range_bd1,
  finrank_range_bd1} to IsClosedSurface (+ explicit nonemptiness where used);
  watershed + Separation:380 pass `.toClosedSurface`. New `chi_le_two`
  (V+F ≤ E+2 from b₂=1, r₁=V−1, range∂₂≤ker∂₁, additive rank-nullity — no euler).
  Build green (8258 jobs), no sorry, watershed still standard-three-axioms.
- M19 (DONE, building): **`separates` — THE SEPARATION THEOREM.** A non-face
  triangle γ of a combinatorial 2-sphere splits it into two sides, each capping
  with γ to a combinatorial 2-sphere. New lemmas: `bd2_W_add_one`,
  `mem_cutSet_add_one`/`cutSet_add_one_eq_sdiff` (the two sides partition σ),
  `pure_cut`, `card_faces_cut_add` (Fτ₁+Fτ₂=Fσ+2), `gamma_vert_mem_verts`,
  `vertsOf_cut_union`/`vertsOf_cut_inter` (=γ), `edgesOf_cut_union`/
  `edgesOf_cut_inter` (=γ.pwsCard2), `euler_cut` (χ≤2 each + additivity ⟹
  both χ=2), `isSphere2_cut` (all 5 fields), `separates`. Build green
  (8258 jobs), no sorry, `separates`/`isSphere2_cut`/`euler_cut` on the
  standard three axioms. **Theorem 2's geometric core (the cut) is complete.**
- G1 VERDICT (Theorem 2+3 induction, the central theorem): **APPROVED** — codex
  session 019ec265-480d-7ce0-841b-a0f0c80595b3, output
  notes/codex-consults/2026-06-13-g1-theorem2-output.txt. Rulings:
  • Q1 "good" = a **Prop** conclusion (NOT a data-carrying structure). Target:
    `IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M →
     SimplicialChain M ∧ IsBall M.support σ ∧ FreelyShellable M.support σ`.
    For Th3, prove a stronger internal theorem parameterized by a chosen first
    tet; extract List shelling witnesses only at reassembly points.
  • Q2 add a small **tet/flip primitive layer** (tetChain, FlipBoundary,
    `bdry_remove_tet`, `support_flipBoundary_of_eligible`); define eligibility
    via coefficients of `bdry (Finsupp.single t (M t))`, not just set membership.
  • Q3 **strong induction on `nrm M`** (`Nat.strong_induction_on`). The prime/
    no-deg-3 preprocessing is NOT avoidable — make it a first-class branch
    (connected-sum/deg-3 split via IsTaut.splits) before the eligible-tet branch.
  • Q4 `separates` is NOT enough alone (𝔽₂, sphere facet sets only). Need an
    **orientation-packaging bridge** `oriented_split_chains_of_separates`
    (consume the actual `cutSet σ W` partition) producing integral closed X₁,X₂
    with supports in A,B, then call `IsTaut.splits` (n:=2). Not a stronger
    separates — a packaging lemma between separates/cutSet and IsTaut.splits.
  • Q5 BIGGEST RISK = **eligible-tet existence** (2-to-1/maxdeg count + disjoint
    extraction + "3 boundary faces ⟹ deg-3 vertex"); 2nd = the multiplicity-2
    argument (link "not simplicial" to SimplicialChain/IsBall though support
    erases multiplicity). Tractable only if staged.
  • Q6 MILESTONE DECOMPOSITION (do #4 and #6 — the bridge and the count —
    BEFORE the main induction):
    M20 = chain/facet bridge (UnitOn, SimplicialChain, nrm_eq_support_card_of_simplicial);
    M21 = tet removal + flip API (tetChain, eligible, bdry_remove_tet, support_flipBoundary_of_eligible);
    M22 = Ball reassembly (append type-2 tet; concat two shellings thru a bridge tet; preserve FreelyShellable);
    M23 = oriented separation bridge (oriented_split_chains_of_separates → IsTaut.splits);
    M24 = connected-sum/deg-3 reduction via IsTaut.splits;
    M25 = eligible-tet existence + disjoint-pair count (the risk);
    M26 = main strong induction + public Theorem 2+3 wrapper.
- M20 (DONE, Theorem2.lean, building): **the chain/facet bridge.** New file
  `Taut/Theorem2.lean`: `UnitOn` (±1-chain supported on σ), `SimplicialChain`
  (coeffs in {-1,0,1}), `SimplicialChain.natAbs_eq_one`,
  `nrm_eq_support_card_of_simplicial` (|M| = #support when simplicial — links
  the nrm-induction to the ball's facet count), `UnitOn.simplicialChain`,
  `UnitOn.nrm_eq` (nrm = #σ). Build green (8259 jobs), no sorry, standard three.
- NEXT: M21 (tet removal + flip API) — then M22-M26 per the decomposition.
- Open: Corollary 1, |A∩B|≤1 Th1 cases, Th4.
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

- 2026-06-13: M12–M16 (Separation.lean) — exists_cut (the cut from H₁=0),
  edge_cut_parity, closed_cut, gammaCycle_dichotomy, cutSet_dualConn
  (σ₁ dual-connected), conn_cut (conn for the pieces), and the v∉γ half of
  linkConn (W_eq_of_share_edge/W_eq_along_link/W_const_at). Diagnosed +
  fixed codex: `codex exec` blocks until stdin EOF — the earlier G1 "hangs"
  were a missing stdin redirect, not infra; `< /dev/null` fixes it. Re-ran
  the G1 audit → APPROVED (session 019ec1fd, cf807d1). Added a permission
  for the .git evidence-file write; gitignored settings.local.json.

- 2026-06-13 (checkpoint): **Fable removed from the workflow.** Tagged the
  exact state `fable-axed` (commit a8a8954) and wrote RECOVERY.md (prominent
  recovery instructions). Resuming the full protocol with codex doing the
  architecture (G1 audits, run with `< /dev/null`). Next packet to G1-audit:
  the v∈γ linkConn cycle-arc.

- 2026-06-13: G1 audit of the v∈γ linkConn packet → **APPROVED** (codex
  019ec22b), with a key redirect: avoid `IsCycles`, use local-closure +
  walk-reroute. M17 — implemented exactly that: `linkConn_cut` (both v∈γ and
  v∉γ) is proved, the last hard field of "the cut pieces are spheres". The v∈γ
  reroute decouples the walk endpoint from the reach-target `a` so the walk
  induction doesn't pin the target (the trap that bit the earlier attempts).
  Build green (8258 jobs), no sorry, standard three axioms. → M17 committed (c2c6cc7).

- 2026-06-13: G1 audit of the euler packet → **APPROVED** (codex 019ec247).
  Rulings: Option C (new IsClosedSurface, no IsSphere2 redefinition, forgetful
  map); χ≤2 via b₂=1 + r₁=V−1 + range∂₂≤ker∂₁ (no euler); additivity counts
  V₁+V₂=Vσ+3, E₁+E₂=Eσ+3, F₁+F₂=Fσ+2. M18 — implemented the refactor + chi_le_two
  (the key euler-free lemma). The b₂/r₁ machinery only ever used euler for
  nonemptiness, so the generalization is clean. Build green, no sorry, watershed
  still standard-three-axioms. → M18 committed (0c75083). (G2 commit was first
  blocked by the pre-commit hook on TRAILING WHITESPACE in the codex output log
  — `**Q1**  ` markdown line-breaks; codex found no substantive issue. Fixed by
  stripping trailing whitespace from the consult logs. Lesson: strip trailing
  whitespace from codex-output files before staging.)

- 2026-06-13: M19 — **`separates`, the separation theorem, is PROVED.** A
  non-face triangle of a combinatorial 2-sphere cuts it into two combinatorial
  2-spheres (both pieces get all 5 IsSphere2 fields; euler via chi_le_two +
  the V/E/F additivity counts). This completes the geometric core of Theorem 2.
  Build green (8258 jobs), no sorry, separates on the standard three axioms.
  → M19 committed (312750b).

- 2026-06-13: G1 audit of the CENTRAL theorem (Theorem 2+3 induction) →
  **APPROVED** (codex 019ec265) with a 7-milestone decomposition (M20-M26) and
  two pieces flagged to isolate first (the eligible-tet count M25, the oriented
  separation bridge M23). M20 — implemented the chain/facet bridge (UnitOn,
  SimplicialChain, nrm_eq_support_card_of_simplicial). Build green (8259 jobs),
  no sorry, standard three axioms. → M20 commit pending G2.
