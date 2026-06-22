# Phase 0 — baseline audit (clean-anyrooted-stickerballs)

Exact pre-refactor state. No predicate changes yet. (`#check`/`#print axioms` copied verbatim from
`lake env lean` on this branch; predicate bodies copied from source.)

## 1. Branch / commit
- Branch: `clean-anyrooted-stickerballs` (forked from `claude/clean-shelling`).
- Base commit: `d52be46` ("Stage1 cleanup: taut_clean3Complex endpoint + stickerball/free-start docstrings").

## 2. Build status
- `cd lean && lake build` → **Build completed successfully (8274 jobs).**

## 3. sorry/admit
- `grep -rnE "sorry|admit" lean/Taut` (excluding "admits"/"admitting" in docstrings) → **ZERO**.

## 4–6. Public theorem endpoints — exact `#check` + `#print axioms`
All `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**Theorem 1:**
```
@Zvol_add_of_almost_disjoint_full : ∀ {V} [LinearOrder V] [Infinite V] {A B : Finset V} {n : ℕ},
  1 ≤ n → (A ∩ B).card ≤ n + 1 → ∀ {X Y : Chain V},
    (∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1) → (∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1) →
    bdry X = 0 → bdry Y = 0 → Zvol (X + Y) = Zvol X + Zvol Y
@IsTaut.splits_full : ∀ {V} [LinearOrder V] [Infinite V] {A B} {n}, 2 ≤ n → (A∩B).card ≤ n+1 → ∀ {X Y},
  … → ∀ {M}, IsTaut M → bdry M = X + Y →
    bdry (M.filter (·⊆A)) = X ∧ bdry (M.filter ¬(·⊆A)) = Y ∧
    IsTaut (M.filter (·⊆A)) ∧ IsTaut (M.filter ¬(·⊆A)) ∧ M.filter (·⊆A) + M.filter ¬(·⊆A) = M
```

**Corollary 1:**
```
@Qvol_add_of_almost_disjoint_full : ∀ {V} [LinearOrder V] [Infinite V] … {X Y : QChain V} … →
  Qvol (X + Y) = Qvol X + Qvol Y
@IsQTaut.splits_full : ∀ {V} [LinearOrder V] [Infinite V] … {M : QChain V} → IsQTaut M → Qbdry M = X+Y →
  <Qbdry/IsQTaut 5-way split, same shape as IsTaut.splits_full>
```

**Theorem 2 (clean = canonical; weak = legacy):**
```
@theorem2_clean : ∀ {V} [LinearOrder V] {σ X M}, IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X →
  IsTaut M → SimplicialChain M → IsCleanBall M.support σ
@theorem2     : … → IsBall M.support σ          -- WEAK boundary-trace route (PrimeStep.lean)
@taut_clean3Complex : … → Clean3Complex M.support   -- normality endpoint (added Stage 1)
```

**Theorem 3 (clean = canonical; weak = legacy):**
```
@theorem3_clean : … → FreelyCleanShellable M.support σ
@theorem3       : … → FreelyShellable M.support σ      -- WEAK route (PrimeStep.lean)
```

**Theorem 4:**
```
@theorem4_flag : … → IsFlagComplex M.support
```

## 7. Predicate expansion (exact source bodies)

```
-- WEAK incidence / boundary-trace layer (Ball.lean / Pseudomanifold.lean)
IsPseudomanifold τ          := ∀ f, f.card = 3 → faceCount τ f ≤ 2          -- triangle incidence only
abbrev TriangleBounded3 τ   := IsPseudomanifold τ
structure GlueStep t B B'   := card4 (t.card=4) ; shared ((tetFaces t ∩ B).card ∈ {1,2}) ;
                               newBdry (B' = (B \ tetFaces t) ∪ (tetFaces t \ B))   -- boundary trace, no τ
abbrev BoundaryGlueStep t B B' := GlueStep t B B'
ShellFrom B₀ (t::l) B       := ∃ B₁, GlueStep t B₀ B₁ ∧ ShellFrom B₁ l B
IsShelling (t::l) B         := t.card = 4 ∧ ShellFrom (tetFaces t) l B
IsBall τ B                  := ∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B
FreelyShellable τ B         := ∀ t ∈ τ, ∃ l, l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B
IsStickerball τ B           := FreelyShellable τ B ∧ IsPseudomanifold τ ∧ EdgeLinkConnected τ
                               -- LEGACY/UNUSED: mis-bundles FreelyShellable; omits VertexLinkConnected

-- CLEAN layer (Pseudomanifold.lean / CleanShelling.lean) — the live architecture
EdgeLinkConnected τ         := ∀ e, e.card = 2 → ConnOn (edgeLinkGraph τ e) (edgeLinkVerts τ e)
VertexLinkConnected τ       := ∀ v, ConnOn (vertexLinkGraph τ v) (vertexLinkVerts τ v)   -- PRESENT
Pure3 τ                     := ∀ t ∈ τ, t.card = 4
Normal3 τ                   := EdgeLinkConnected τ ∧ VertexLinkConnected τ
Clean3Complex τ             := Pure3 τ ∧ TriangleBounded3 τ ∧ Normal3 τ                   -- the real clean cond
structure CleanGlueStep t τ B B' := weak (BoundaryGlueStep) ; clean (no rogue old face) ; newTet (t∉τ) ;
                               hpmc (triangle ≤1 old tet) ; helc (edge-link compat) ; hvlc (vertex-link compat)
CleanShellFrom τ B₀ (t::l) B := ∃ B₁, CleanGlueStep t τ B₀ B₁ ∧ CleanShellFrom (insert t τ) B₁ l B
IsCleanShelling (t::l) B    := t.card = 4 ∧ CleanShellFrom {t} (tetFaces t) l B
IsCleanBall τ B             := ∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B        -- shellable clean ball
FreelyCleanShellable τ B    := ∀ t ∈ τ, ∃ l, l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B
```

Self-certification (all std-3): `IsCleanShelling.clean3Complex` (CleanShelling.lean:173) :
`IsCleanShelling l B → Clean3Complex l.toFinset`; `IsCleanBall.clean3Complex` (:184) :
`IsCleanBall τ B → Clean3Complex τ`; `FreelyCleanShellable.clean3Complex` (:189).

## Target name mapping (Phase 1+, planned)
| current | role | target |
|---|---|---|
| `IsPseudomanifold`/`TriangleBounded3` | triangle incidence (weak) | keep; clarify docstring (already wrapped as `TriangleBounded3`) |
| `Clean3Complex` | pure + triangle-bdd + connected vertex & edge links | `IsClean3Complex` (rename; alias `Clean3Complex`) |
| `IsCleanBall` | shellable clean ball | basis for `IsStickerball` |
| `FreelyCleanShellable` | anyrooted | `IsAnyrootedStickerball` |
| `theorem3_clean` (FreelyCleanShellable) | MAIN content | `taut_filling_is_anyrootedStickerball` |
| `theorem2_clean` (IsCleanBall) | corollary | `taut_filling_is_stickerball` |
| `taut_clean3Complex` | corollary | `taut_filling_is_clean3Complex` |
| `theorem2` (IsBall), `theorem3` (FreelyShellable) | WEAK, terminal, unused | internalize/remove |
| `IsStickerball` (legacy) | dead, mis-defined | redefine to `IsClean3Complex ∧ shellable ∧ bdry≠∅`, or retire |
| `theorem4_flag` | flag complex | `taut_filling_is_flagComplex` (alias `theorem4_flag`) |

Verdict carried from the Stage-1 audit (notes/lean-cleanup-audit.md): VertexLinkConnected IS present and IS
implied by the clean Theorem 2 (PASS); the proof already gives the anyrooted (free-start) property
(STRONGER). Phase 1+ make this the primary, mathematically-named architecture.
