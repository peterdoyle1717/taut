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
- Next: `Taut/Projection.lean` — K_{A,p}, chain-map property, kill lemmas,
  small-support triviality; then Theorem 1.

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
