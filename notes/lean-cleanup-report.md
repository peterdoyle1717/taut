# Lean cleanup report (clean-anyrooted-stickerball)

## 1. Branch
`clean-anyrooted-stickerball` — created from the completed-and-green cleanup state.  The cleanup
(Phases 0–3 + 5) was carried out on the sibling branch `clean-anyrooted-stickerballs` and inherited here
verbatim; this branch is the requested-named home, re-validated below.

## 2. Commit trail (inherited; each builds green)
- `50b7d22` Phase 0: baseline inventory + future-projects note
- `47cd9a3` Phase 1: clean predicate hierarchy (IsClean3Complex / IsStickerball / IsAnyrootedStickerball)
- `1d08558` Phase 2/3: mathematically-named public endpoints; remove weak theorem2/theorem3
- `983f44d` Phase 5: validation report
- (this commit) Phase 5 refresh: re-validated on `clean-anyrooted-stickerball`.

## 3. Build status
`cd lean && lake build` → **Build completed successfully (8274 jobs).**

## 4. no-sorry/admit status
`grep -rnE "sorry|admit" lean/Taut` (excluding "admits"/"admitting" in docstrings) → **ZERO**.

## 5. Final public theorem endpoint inventory (all `#print axioms = [propext, Classical.choice, Quot.sound]`)

| paper result | primary endpoint (mathematical name) | conclusion |
|---|---|---|
| Theorems 2+3 (unified) | **`taut_filling_is_anyrootedStickerball`** | `IsAnyrootedStickerball M.support σ` |
| Theorem 2 | `taut_filling_is_stickerball` | `IsStickerball M.support σ` |
| Theorem 2 (normality) | `taut_filling_is_clean3Complex` | `IsClean3Complex M.support` |
| Theorem 2 (shelling) | `taut_filling_is_shellable` | `IsCleanBall M.support σ` |
| Theorem 4 | `taut_filling_is_flagComplex` | `IsFlagComplex M.support` |
| Theorem 1 (additivity) | `Zvol_add_of_almost_disjoint_full` (already mathematical) | `Zvol (X+Y) = Zvol X + Zvol Y` |
| Theorem 1 (splitting) | `IsTaut.splits_full` (already mathematical) | taut split |
| Corollary 1 (additivity) | `Qvol_add_of_almost_disjoint_full` (already mathematical) | `Qvol (X+Y) = Qvol X + Qvol Y` |
| Corollary 1 (splitting) | `IsQTaut.splits_full` (already mathematical) | rational taut split |

Underlying / compatibility lemmas retained (not the primary architecture): `theorem2_clean`,
`theorem3_clean`, `taut_clean3Complex`, `theorem4_flag`.  Theorem 1 / Corollary 1 had **no**
`theorem1`/`corollary1` paper-number names to begin with — already mathematically named.

## 6. Exact statement of the main theorem
```
theorem taut_filling_is_anyrootedStickerball :
  ∀ {V} [LinearOrder V] {σ : Finset (Finset V)} {X M : Chain V},
    IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
    IsAnyrootedStickerball M.support σ
```

## 7. Exact definition expansion (`#print`)
```
IsClean3Complex τ          := Clean3Complex τ            -- = Pure3 τ ∧ TriangleBounded3 τ ∧ Normal3 τ
                                                          --   Normal3 τ = EdgeLinkConnected τ ∧ VertexLinkConnected τ
IsStickerball τ B          := IsCleanBall τ B ∧ B.Nonempty
IsAnyrootedStickerball τ B := IsStickerball τ B ∧ FreelyCleanShellable τ B
```

## 8. Does `IsStickerball` include vertex-link connectedness? — **YES (provably).**
`IsStickerball τ B := IsCleanBall τ B ∧ B.Nonempty`, and `IsCleanBall.clean3Complex` (CHECKED, std-3)
gives `IsCleanBall τ B → Clean3Complex τ = IsClean3Complex τ`, whose `Normal3` component is
`EdgeLinkConnected ∧ VertexLinkConnected`.  Exposed directly as `IsStickerball.isClean3Complex`.  So
`taut_filling_is_clean3Complex … : IsClean3Complex M.support`, and `(… ).2.2.2 : VertexLinkConnected
M.support`.  (Vertex-link connectivity is certified per-glue by `CleanGlueStep.hvlc` →
`vertexLinkConnected_insert` → `IsCleanShelling.clean3Complex`; not handwaved.)

## 9. Does the main theorem prove anyrooted shellability? — **YES.**
`taut_filling_is_anyrootedStickerball … : IsAnyrootedStickerball M.support σ`, whose second component is
`FreelyCleanShellable M.support σ` (a clean shelling beginning with *any* prescribed tet).  This is the
actual content of the minimal-counterexample induction (`theorem3_core_clean` carries
`FreelyCleanShellable` through base/deg-3/prime); `IsStickerball` (one shelling) is the weakening.

## 10. Weak endpoints removed / renamed / internalized
- **Removed:** `theorem2` (`IsBall`) and `theorem3` (`FreelyShellable`) — weak boundary-trace endpoints
  (PrimeStep.lean), superseded by the clean endpoints.  Replaced by an in-file comment noting the removal.
- **Removed:** the dead legacy `IsStickerball := FreelyShellable ∧ IsPseudomanifold ∧ EdgeLinkConnected`
  + its two unused helper lemmas (`isStickerball_singleton`/`isStickerball_insert`) — mis-bundled
  `FreelyShellable`, omitted `VertexLinkConnected`.  `IsStickerball` redefined correctly in CleanShelling.lean.
- **Retained (load-bearing):** the weak *predicates* `IsBall`/`IsShelling`/`FreelyShellable`/`GlueStep`
  (Ball.lean) — the clean route projects onto them via `IsCleanBall.toBoundaryIsBall` etc.

## 11. Remaining non-mathlib-style cruft
- **Orphaned weak induction machinery — REMOVED (commit `69705ab`).**  `theorem3_core`,
  `base_free`, `degree3_star_start_shellFrom`, `deg3_step_free`, `prime_flipEdge_split_free_package`,
  `exists_shelling_prime_case1`/`2`, `prime_step_free`, and the dead adapter
  `FreelyShellable.isBall_of_mem` are deleted (≈537 net lines).  Each was verified dead by
  `git grep -wn` (sole code consumers were each other and the already-removed weak
  `theorem2`/`theorem3`).  Build green (8274); five public endpoints still std-3 axioms.  Retained:
  the PM skeletons `base_isPM`/`deg3_isPM`/`theorem2_core` and the weak *predicates*
  `IsBall`/`IsShelling`/`FreelyShellable`/`GlueStep` (the clean route projects onto them).
- **Dead weak side-split / relative-shelling cluster — REMOVED (second cleanup commit, follows `69705ab`).**  After the
  induction removal above, a connected 7-decl cluster was left with no live consumer; measured against
  the clean route (`git grep -wn`) and deleted: `flipEdgePresent_side_data`, `flipEdgePresent_side_bridge`,
  the struct `PrimeFlipEdgeSplitFreePackage` (PrimeStep.lean), and `RelShelling`,
  `relShelling_over_insert_boundary_face`, `IsBall.bridge_of_relShelling`, `RelBoundaryShelling`
  (Ball.lean).  **Retained because the clean route genuinely consumes them** (it re-derives the case-2
  split directly, *not* via `flipEdgePresent_side_data`): `flipEdgePresent_side_sets`,
  `flipEdgePresent_side_algebra`, `flipEdgePresent_side_reconstruct`(`_left`), `glueStep_bridge_left`/`_right`,
  and the core weak predicates `IsBall`/`IsShelling`/`FreelyShellable`/`GlueStep`/`ShellFrom`.  Build
  green (8274); five endpoints still std-3.  (Note: my earlier draft of this bullet wrongly flagged
  `flipEdgePresent_side_sets` as possibly-dead — it is live, used by `Theorem3Clean.lean`.)
- **Minor residual (not chased):** `freelyShellable_singleton` (Ball.lean) is now dead collateral of the
  `base_free` removal (only comment refs remain); a few docstrings in `Ball.lean`/`FlipGeom.lean`/
  `Theorem3Clean.lean`/`CleanShelling.lean` still name removed decls historically.  Harmless.
- **Paper-number underlying lemmas:** `theorem2_clean`/`theorem3_clean`/`taut_clean3Complex`/`theorem4_flag`
  remain as the proof-bearing lemmas under the new public endpoints.  They are no longer the primary
  API; could be renamed (e.g. to `*_aux`/private) in a follow-up, but that is churn with little gain.
- **Phase 4 (broad mathlib restyle) NOT done:** internal lemma names with paper numbers / `_aux` /
  `_clean` suffixes, and a few giant tactic blocks, remain across `PrimeStep.lean`, `Theorem3Clean.lean`,
  `Theorem2Aleph.lean`.  A full restyle is out of scope for a single safe pass; flagged for later.

## 12. Anything that still claims more than Lean proves
- **None in the theorem statements.**  The one external claim — that a stickerball is homeomorphic to
  `B³` — is **not** in any endpoint; it is documented in the `IsStickerball` docstring and
  `notes/future-projects.md` as the Danaraj–Klee/Björner route, explicitly *not formalized*.  The Lean
  result is the combinatorial certificate (shellable clean 3-complex, nonempty boundary), nothing more.

## Status / next
Phases 0–3 + 5 complete; orphaned-weak-machinery removal done (commit `69705ab`).  Build green, no
sorries, std axioms.  Deferred bounded follow-ups: the residual dead flip-edge side-split support
(§ 11), stale comment references (§ 11), and Phase 4 (broad mathlib restyle).  Branch not merged to main.
