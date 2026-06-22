# Lean cleanup audit (Stage 1) — clean/normality package & stickerball-vs-freely-shellable

Stage 1 = **Lean only**. No paper edits (`taut/text/*` untouched). This note is the only written artifact.
All `#check` / `#print axioms` output below is machine-verified against the current tree; every endpoint
`#print axioms = [propext, Classical.choice, Quot.sound]` (genuinely proven, no `sorry`/`admit`).

## Endpoint inventory (exact `#check`)

**Theorem 1** (`Theorem1.lean`, `Splitting.lean`):
- `Zvol_add_of_almost_disjoint_full : {V} [LinearOrder V] [Infinite V] {A B n} → 1 ≤ n → (A∩B).card ≤ n+1
  → {X Y : Chain V} → (∀ s ∈ X.support, s⊆A ∧ s.card=n+1) → (∀ s ∈ Y.support, s⊆B ∧ s.card=n+1)
  → bdry X = 0 → bdry Y = 0 → Zvol (X+Y) = Zvol X + Zvol Y`
- `IsTaut.splits_full : … [Infinite V] … → 2 ≤ n → … → {M} → IsTaut M → bdry M = X+Y →
  bdry (M.filter (·⊆A)) = X ∧ bdry (M.filter ¬(·⊆A)) = Y ∧ IsTaut (M.filter (·⊆A)) ∧
  IsTaut (M.filter ¬(·⊆A)) ∧ M.filter (·⊆A) + M.filter ¬(·⊆A) = M`

**Corollary 1** (`Corollary1.lean`):
- `Qvol_add_of_almost_disjoint_full : … [Infinite V] … {X Y : QChain V} … → Qvol (X+Y) = Qvol X + Qvol Y`
- `IsQTaut.splits_full : … [Infinite V] … {M : QChain V} → IsQTaut M → Qbdry M = X+Y → <Qbdry/IsQTaut 5-way split>`

**Theorem 2** (clean = canonical; weak = legacy):
- `theorem2_clean : {V} [LinearOrder V] {σ X M} → IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X →
  IsTaut M → SimplicialChain M → IsCleanBall M.support σ`   [Theorem3Clean.lean]
- `theorem2 : … → IsBall M.support σ`   [PrimeStep.lean — weak boundary-trace route, superseded]
- **NEW (this patch)** `taut_clean3Complex : … → Clean3Complex M.support`   [Theorem3Clean.lean]

**Theorem 3** (clean = canonical; weak = legacy):
- `theorem3_clean : … → FreelyCleanShellable M.support σ`   [Theorem3Clean.lean]
- `theorem3 : … → FreelyShellable M.support σ`   [PrimeStep.lean — weak route]

**Theorem 4** (`Theorem4.lean`):
- `theorem4_flag : … → IsFlagComplex M.support`

## `#print axioms` (all endpoints)
Every one of `Zvol_add_of_almost_disjoint_full`, `IsTaut.splits_full`, `Qvol_add_of_almost_disjoint_full`,
`IsQTaut.splits_full`, `theorem2_clean`, `theorem2`, `theorem3_clean`, `theorem3`, `theorem4_flag`,
`taut_clean3Complex`, `IsCleanBall.clean3Complex`, `FreelyCleanShellable.clean3Complex`
→ `[propext, Classical.choice, Quot.sound]`.

## Predicate expansion (exact defs)

| predicate | def | file:line |
|---|---|---|
| `IsBall τ B` | `∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B` | Ball.lean:83 |
| `IsShelling (t::l) B` | `t.card = 4 ∧ ShellFrom (tetFaces t) l B` (weak `GlueStep`/`ShellFrom`; boundary trace, no τ threading) | Ball.lean:77 |
| `FreelyShellable τ B` | `∀ t ∈ τ, ∃ l, l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B` | Ball.lean:89 |
| `IsCleanBall τ B` | `∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B` | CleanShelling.lean:80 |
| `IsCleanShelling (t::l) B` | `t.card = 4 ∧ CleanShellFrom {t} (tetFaces t) l B` (threads τ; `CleanGlueStep` has clean fields) | CleanShelling.lean:74 |
| `FreelyCleanShellable τ B` | `∀ t ∈ τ, ∃ l, l.head? = some t ∧ … ∧ IsCleanShelling l B` | CleanShelling.lean:85 |
| `CleanGlueStep t τ B B'` | `weak ∧ clean ∧ newTet ∧ hpmc ∧ helc ∧ **hvlc**` (hvlc = per-vertex link compatibility) | CleanShelling.lean:48 |
| `IsPseudomanifold τ` (= `TriangleBounded3`) | `∀ f, f.card = 3 → faceCount τ f ≤ 2` | Pseudomanifold.lean:28 |
| `EdgeLinkConnected τ` | `∀ e, e.card = 2 → ConnOn (edgeLinkGraph τ e) (edgeLinkVerts τ e)` | Pseudomanifold.lean:105 |
| `VertexLinkConnected τ` | `∀ v, ConnOn (vertexLinkGraph τ v) (vertexLinkVerts τ v)` | Pseudomanifold.lean:333 |
| `Pure3 τ` | `∀ t ∈ τ, t.card = 4` | Pseudomanifold.lean:467 |
| `Normal3 τ` | `EdgeLinkConnected τ ∧ VertexLinkConnected τ` | Pseudomanifold.lean:471 |
| `Clean3Complex τ` | `Pure3 τ ∧ TriangleBounded3 τ ∧ Normal3 τ` | Pseudomanifold.lean:477 |
| `IsStickerball τ B` | `FreelyShellable τ B ∧ IsPseudomanifold τ ∧ EdgeLinkConnected τ` — **LEGACY, unused** | Pseudomanifold.lean:244 |

## Issue A — clean/normality incl. connected vertex links

**VERDICT: PASS** (clean route), via an exact named theorem path.

- The canonical Theorem-2 endpoint `theorem2_clean` concludes `IsCleanBall M.support σ`.  `IsCleanBall`'s
  *type* does not list `VertexLinkConnected`, but it provably entails the full normality package:
  `IsCleanBall.clean3Complex` (CleanShelling.lean:184) : `IsCleanBall τ B → Clean3Complex τ`.
- Chain (all std-3): `CleanGlueStep.hvlc` (CleanShelling.lean:60) → `clean3Complex_insert`
  (Pseudomanifold.lean:499, via the proven `vertexLinkConnected_insert`, Pseudomanifold.lean:410) →
  `IsCleanShelling.clean3Complex` (CleanShelling.lean:173) → `IsCleanBall.clean3Complex` (:184).
- `Clean3Complex = Pure3 ∧ TriangleBounded3 ∧ Normal3`, `Normal3 = EdgeLinkConnected ∧ VertexLinkConnected`,
  so connected vertex links **and** edge links are delivered — matching the paper's "normal" (dim 0,…,n−2
  links connected ⇒ for n=3, vertex + edge links).
- **Patch (this pass):** added `taut_clean3Complex : … → Clean3Complex M.support`, so connected vertex
  links are now a first-class *named endpoint* (`(taut_clean3Complex …).2.2.2 : VertexLinkConnected`),
  not something a consumer must unpack.  `theorem2_clean` docstring updated to point at it.
- Caveat (honest): the *weak* `theorem2 → IsBall` carries **no** manifold invariants; the legacy
  `IsStickerball` carries `EdgeLinkConnected` but **omits** `VertexLinkConnected`.  Neither is the
  canonical endpoint; both are superseded by the clean route.

## Issue B — stickerball vs freely shellable

**VERDICT: STRONGER** (and the public hierarchy is correct; only one dead-code naming infelicity).

- The live predicates are already **distinct**: `IsCleanBall` (= stickerball = shellable clean ball,
  *one* shelling) vs `FreelyCleanShellable` (= free-start, *any* prescribed head).  Lean does **not**
  conflate them at the endpoint level.
- The minimal-counterexample induction (`theorem3_core_clean`) carries `FreelyCleanShellable` through
  **every** step (base/deg-3/prime), so it proves the **stronger free-start** statement; `theorem2_clean`
  is literally a one-line weakening (`obtain … := theorem3_clean … t ht`, dropping the `head? = some t`).
  So Theorem 2 *as proven* already gives free shellability, and Theorem 3 (Lean) carries **no extra
  mathematical content** — it is the actual inductive statement, of which Theorem 2 is a corollary.
- **Patch (this pass):** `theorem2_clean` docstring now states this explicitly (the proof proves
  free-start; `IsCleanBall` vs `FreelyCleanShellable` kept distinct on purpose — "stickerball" not
  redefined to "freely shellable").
- **One dead-code naming issue (documented, not yet removed):** the legacy `IsStickerball`
  (Pseudomanifold.lean:244) `:= FreelyShellable ∧ IsPseudomanifold ∧ EdgeLinkConnected` *does* mis-bundle
  `FreelyShellable` (contrary to intent) and omit `VertexLinkConnected`.  It is **unused** (its only
  lemmas `isStickerball_singleton`/`isStickerball_insert` are referenced nowhere).  Marked `LEGACY /
  superseded` in its docstring this pass; recommend retiring it (delete or rename-with-alias) in a
  follow-up bounded pass — left in place now to avoid churning the committed migration bridge.

## Lean changes made this pass (additive, endpoint-preserving)
1. `taut_clean3Complex` — new named normality endpoint (Issue A); derived from `theorem2_clean` +
   `IsCleanBall.clean3Complex`.
2. `theorem2_clean` docstring — records (a) `IsCleanBall` = stickerball, (b) it entails `Clean3Complex`
   incl. connected vertex links, (c) the proof proves the stronger `FreelyCleanShellable`.
3. `IsStickerball` docstring — marked LEGACY/superseded; documents the `FreelyShellable`-bundling and the
   missing `VertexLinkConnected`.
No theorem **signatures** changed; no endpoint weakened; no proof deleted.

## Recommended (NOT done this pass — future bounded items)
- Retire `IsStickerball` + `isStickerball_singleton`/`isStickerball_insert` (dead) — delete or alias.
- Optionally retire the weak `theorem2`/`theorem3` (`IsBall`/`FreelyShellable`) if the clean route fully
  supersedes them downstream (verify no consumer first).
- Optional: a tiny `taut_vertexLinkConnected` / `taut_edgeLinkConnected` convenience corollary if a
  consumer wants the links directly (currently `taut_clean3Complex` suffices).

## What remains before Stage 2 (paper revision)
- Confirm with Peter whether to retire `IsStickerball` / the weak endpoints now or after Stage 2.
- Settle final public vocabulary: `IsCleanBall` (stickerball), `FreelyCleanShellable` (free-start),
  `Clean3Complex`/`Normal3` (normality) — these are the names the paper revision should mirror.
- The paper's separate "shucking" proof of Theorem 3 is redundant with the Lean approach (single
  induction proves free-start); this is a Stage-2 expository note, not a Lean change.
