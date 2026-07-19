# Simpliciality-hypothesis repair — investigation report

Branch `clean-anyrooted-stickerball`, commit `b5a2428`, build green. This is the report requested
before any rewrite (task E). **No edits made to the proof yet.**

## 0. Verdict (read first)

`SimplicialChain M` is **not** an inert surface hypothesis that is threaded through unused. It is
**used**, at foundational points, to establish the ±1-coefficient facts the entire stickerball
reduction relies on. There is **no** lemma in the development that derives `SimplicialChain M` from
`IsTaut M` (or any coefficient-magnitude bound from tautness), and every existing coefficient-±1
result **assumes** simpliciality (circular for this purpose).

Consequently: removing `SimplicialChain M` from the public endpoint needs a **new** bridge theorem
`taut_filling_is_simplicialChain`. The endpoint composition *given* the bridge is a ~5-line, zero-risk
change. The bridge itself is the entire cost, is not in the API, and its difficulty turns on a
question the Lean cannot answer (is the paper's unit-coefficient argument independent of the shelling
structure?). I have **not** attempted the bridge and do not claim it is short.

`UnitOn X σ`, `bdry X = 0`, `bdry M = X` are **not** extra: together they are the paper statement
"`M` is a taut filling of the simplicial 2-sphere `σ`" (they pin `X` to the fundamental ±1 cycle of
`σ`; there is no canonical `X σ` function in the API, so the desired `bdry M = X σ` shape is not
directly expressible). Only `SimplicialChain M` is the spurious hypothesis.

## 1. Current final theorem statements (exact `#check`)

```
taut_filling_is_anyrootedStickerball :
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
    IsAnyrootedStickerball M.support σ
taut_filling_is_stickerball :
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
    IsStickerball M.support σ
taut_filling_is_clean3Complex :
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
    IsClean3Complex M.support
taut_filling_is_shellable :
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
    IsCleanBall M.support σ
theorem3_clean :
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
    FreelyCleanShellable M.support σ
taut_isPseudomanifold :
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
    IsPseudomanifold M.support
```
`theorem3_core_clean` carries `SimplicialChain M` in its main hypotheses **and** `SimplicialChain M'`
in the inductive-hypothesis function for every smaller filling (so simpliciality is an *invariant of
the whole induction*, not just a top-level input).

`SimplicialChain M := ∀ t, M t = -1 ∨ M t = 0 ∨ M t = 1` (`Theorem2.lean:27`).

## 2. Where `SimplicialChain` enters (task B)

- **Directly** in the public endpoint `taut_filling_is_anyrootedStickerball` (`Theorem3Clean.lean`),
  passed verbatim to `theorem2_clean` and `theorem3_clean`.
- **Threaded through the entire induction**: `theorem3_core_clean` requires it and carries
  `SimplicialChain M'` in its IH; the three case lemmas `base_free_clean`, `deg3_step_clean`,
  `prime_step_clean` all require it; `taut_isPseudomanifold` (`PrimeStep.lean:1536`) requires it.
- **Genuinely used (not merely passed)** — the first load-bearing consumers:
  - `tet_coeff_eq_pm_one_of_eligible` (`Theorem2.lean:250`): proof is literally `rcases hS t` — it
    *is* simpliciality applied to an eligible tet, giving `M t = ±1`.
  - the `faceCount = 1` lemma in `Stickerball.lean:70` (`rcases hS t`) — needs `M t = ±1`.
  - `unitOn_flipBoundary_of_eligible` (`Theorem2.lean`) — uses the former; the prime-step flip needs it.
  - `nrm_eq_support_card_of_simplicial`, `simplicialChain_removeTet` (preservation under `removeTet`).
- So the first downstream requirement is the endpoint itself; the deepest *use* is the eligible-tet
  ±1 coefficient and the `faceCount = 1` boundary lemma.

## 3. Existing lemmas relevant to "taut → simplicial" (task C)

Take `SimplicialChain` / `UnitOn` as **input** (cannot supply the bridge — circular):
- `SimplicialChain.natAbs_eq_one`, `tet_coeff_eq_pm_one_of_eligible`, `Stickerball` faceCount lemma.
- `UnitOn.simplicialChain` (`Theorem2.lean:47`) — proves the **boundary** `X` is simplicial, not `M`.
- `simplicialChain_removeTet` (`Theorem2.lean:141`) — preservation, needs `hS`.

Tautness corollaries that exist but **do not bound coefficient magnitude**:
- `IsTaut.dim_pure` (`Theorem1.lean:139`) — generators have card `k+1` (dimension, not coefficient).
- `IsTaut.vert_subset` / `IsTaut.no_internal_vertex` (`Theorem1.lean:157`, `Zvol.lean:134`) — vertices on boundary.
- `not_taut_complete_cone` (`Zvol.lean:122`) — no nontrivial complete cone.
- `IsTaut.subChain`, `exists_fill_eq_Zvol`, `Zvol_le`, `nrm_add_le` — norm/filling bookkeeping.

**There is no lemma bounding `(M t).natAbs` from `IsTaut`, and no `IsTaut M → SimplicialChain M`.**
(Confirmed: `git grep` for any conclusion `SimplicialChain M` on a filling returns nothing.)

## 4. Proposed bridge theorem (task C/4)

```lean
theorem taut_filling_is_simplicialChain
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0)
    (hMX : bdry M = X) (hT : IsTaut M) : SimplicialChain M
```
Type-correct in the current API. The hypotheses are exactly the paper's "`M` is a taut filling of
`σ`," minus `SimplicialChain`.

## 5. Status of the bridge: **new work** (task C/5)

- **Not present, not nearly-present.** There is no partial coefficient bound from tautness to extend.
- The natural argument (the one in the task: `|M t| ≥ 2` ⟹ reduce `nrm` while preserving `bdry M`)
  is **not formalized**. It requires a concrete norm-lowering operation localized at a high-coefficient
  tet that keeps the boundary fixed — new machinery, not in the API.
- It **cannot reuse** the existing ±1 machinery (`tet_coeff_eq_pm_one_of_eligible` etc.), which assumes
  simpliciality.

## 6. Patch plan (task D/6)

If/when the bridge is proved, the endpoint change is mechanical and **does not touch** `theorem3_clean`,
`theorem3_core_clean`, or any shelling/induction machinery (they keep `SimplicialChain` internally):

```lean
theorem taut_filling_is_anyrootedStickerball
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M) :
    IsAnyrootedStickerball M.support σ :=
  _root_.Taut.taut_filling_is_anyrootedStickerball hσ hU hXc hMX hT
    (taut_filling_is_simplicialChain hσ hU hXc hMX hT)
```
(rename the current 6-hypothesis lemma to an internal `*_of_simplicial` and expose this 5-hypothesis
wrapper; likewise for `_stickerball`, `_clean3Complex`, `_shellable`, and the public face of
`taut_isPseudomanifold` if a hypothesis-free version is wanted). Keep `UnitOn`/`bdry X = 0`/`bdry M = X`.

## 7. Estimated difficulty (task 7)

- Endpoint composition: **trivial** (minutes), zero risk, build stays green.
- The bridge `taut_filling_is_simplicialChain`: **the entire cost; HIGH / uncertain.** No supporting
  lemma exists; it is a new minimality theorem. I cannot, from the Lean alone, confirm it is a short
  proof, and I have not attempted it.

## 8. Risks (task 8)

1. **Circularity.** Every unit-coefficient result in the codebase assumes `SimplicialChain`. The bridge
   must be proved by a route **independent** of the eligible-tet / flip / faceCount machinery.
2. **Depth / possible entanglement with Theorem 3.** It is plausible that the only available proof of
   unit coefficients runs *through* the stickerball structure. If so, removing the hypothesis is not a
   small bridge but a reproof of the structure theorem without assuming simpliciality — a broad
   refactor (explicitly out of scope here). The formalization may have assumed `SimplicialChain`
   precisely because the clean route does not independently establish it.
3. **Missing norm-reduction primitive.** The "`|M t| ≥ 2` ⟹ reduce `nrm`" step needs a boundary-
   preserving local replacement that is not in the API; building it is non-trivial.

### Recommended next step (not yet taken)
Before committing to the bridge: extract the paper's exact unit-coefficient argument and check whether
it is **structure-independent** (uses only `bdry M = X`, `IsTaut`, `IsSphere2`-level facts) or whether
it presupposes the shelling. That single determination decides whether this is a ~1-lemma repair or a
major effort. The Lean side is unambiguous: the bridge is currently missing and unsupported.
