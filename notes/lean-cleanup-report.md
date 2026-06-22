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

## 11. Remaining non-mathlib-style cruft (deferred, to avoid sprawl)
- **Orphaned weak induction machinery:** `theorem3_core`, `base_free`, `deg3_step_free`,
  `prime_step_free` (and their supporting weak-route lemmas) are now referenced **only in comments**
  (confirmed by `git grep`: the sole code consumers were the deleted weak `theorem2`/`theorem3`).  But
  the web spans **five files** (`Theorem3.lean`, `Theorem23.lean`, `PrimeStep.lean`, `FlipGeom.lean`,
  `Ball.lean`) and interleaves with the weak *predicates* `IsBall`/`IsShelling`/`FreelyShellable` that
  the clean route still projects onto.  Removing it cleanly is a dedicated multi-file pass (≈ hundreds of
  lines) — a **bounded follow-up**, deferred here per the "stop if sprawl" rule.  Needs Peter's go-ahead.
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
Phases 0–3 + 5 complete on this branch; build green, no sorries, std axioms.  Phase 4 (broad restyle)
and the orphaned-weak-machinery removal are deferred as bounded follow-ups.  Branch not merged to main.
