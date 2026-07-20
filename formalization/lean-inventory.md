# Taut Fillings — Lean-side inventory (raw, for the formalization certificate)

Inventory mapping the paper-style statements in `paper/tautA/taut.tex` to the Lean development. Exact
names and paths; no paraphrase of theorem names. This is source data for the certificate, not the
certificate.

---

## 1. Build anchor

| field | value |
|---|---|
| repo path | `/Users/doyle/Dropbox/taut` |
| current branch | `clean-anyrooted-stickerball` |
| current commit | `77df0ba5a4885898560d4e65819867d598de05c3` |
| Lean toolchain | `leanprover/lean4:v4.29.1` (`lean/lean-toolchain`) |
| Mathlib version | `v4.29.1`, rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (`lean/lake-manifest.json`) |
| build command | `cd lean && lake build` |
| build result | `Build completed successfully (8273 jobs).` |
| `sorry` / `admit` count | **0** in `lean/Taut` (`grep -RnE "\bsorry\b\|\badmit\b\|^\s*axiom \|native_decide" lean/Taut` → empty) |
| files excluded from build | none |

Note: `lean/` is unchanged by the recent paper commits (`git diff fc1b394 HEAD -- lean/` empty); the build
state is that of commit `fc1b394`. Endpoint axioms (verified earlier this session via `#print axioms`):
`[propext, Classical.choice, Quot.sound]` only.

---

## 2. Paper theorem inventory

Paper numbering is by appearance order in `paper/tautA/taut.tex` (`\newtheorem` independent counters).

### Proposition 1  (`\label{subtaut}`, taut.tex:343)
- Paper statement summary: If `M` is taut and `U ⊂ M` then `U` is taut.
- Lean theorem name(s): `IsTaut.subChain`
- Lean file path(s): `lean/Taut/Zvol.lean:98`
- Lean statement summary: `IsTaut M → SubChain U M → IsTaut U`.
- Status: **PROVEN**
- Notes: `SubChain U M` (`Zvol.lean:27`) is the Lean form of `U ⊂ M` (sub-multiset).

### Corollary 1  (`\label{nosubcycle}`, taut.tex:365)
- Paper statement summary: A taut chain has no nonzero closed subchain: `M` taut, `U ⊂ M`, `∂U = 0` ⇒ `U = 0`.
- Lean theorem name(s): none standalone; realized inline as `IsTaut.subChain` + `nrm U = Zvol (bdry U) = Zvol 0 = 0` + `nrm_eq_zero_iff`.
- Lean file path(s): used inside `no_k5Clique_of_no_emptyK4_taut` (`lean/Taut/Theorem4.lean:287`, lines ~300–307).
- Lean statement summary: from `IsTaut U` and `bdry U = 0`, `nrm U = Zvol 0 = 0`, so `U = 0`.
- Status: **DERIVED**
- Notes: immediate from Proposition 1 + `IsTaut` (`nrm = Zvol(bdry)`); not packaged as its own Lean theorem.

### Proposition 2  (`\label{maxdeg}`, taut.tex:405)
- Paper statement summary: For `X ∈ Z_n`, `Zvol(X) ≤ |X| − maxdeg(X)`.
- Lean theorem name(s): `Zvol_add_deg_le`
- Lean file path(s): `lean/Taut/Zvol.lean:113`
- Lean statement summary: for any vertex `x`, `bdry X = 0 → Zvol X + deg x X ≤ nrm X`.
- Status: **PROVEN**
- Notes: Lean form is per-vertex (`deg x X`); the paper's `maxdeg(X)` is the max over `x`, giving `Zvol X ≤ |X| − maxdeg(X)` immediately. `nrm = |·|`.

### Proposition 3  (`\label{nocone}`, taut.tex:421)
- Paper statement summary: If `M` is taut it contains no non-trivial complete cone.
- Lean theorem name(s): `not_taut_complete_cone`
- Lean file path(s): `lean/Taut/Zvol.lean:122`
- Lean statement summary: a taut `M` has no subchain that is a non-trivial complete cone `cone x W` (`W` closed, `deg_x W = 0`, some `deg_{x'} W ≠ 0`).
- Status: **PROVEN**

### Proposition 4  (`\label{nointernal}`, taut.tex:429)
- Paper statement summary: If `M` is taut then it has no internal vertices.
- Lean theorem name(s): `IsTaut.no_internal_vertex` (and the consequence `IsTaut.vert_subset`)
- Lean file path(s): `lean/Taut/Zvol.lean:134` (`IsTaut.vert_subset` at `lean/Taut/Theorem1.lean:157`)
- Lean statement summary: a vertex of `M` not on `bdry M` cannot occur, i.e. `vertices(M) ⊆ vertices(∂M)`.
- Status: **PROVEN**

### Proposition 5  (`\label{recover}`, taut.tex:498)
- Paper statement summary: `(X,Y)` is recoverable from `X+Y` when `|A∩B| ≤ n` (chains) or `= n+1` (cycles), via `g_n(p,q)`.
- Lean theorem name(s): none standalone; realized via `Kmap_eq_self` + `Kmap_eq_zero_of_closed`.
- Lean file path(s): `lean/Taut/Theorem1.lean:167` (`Kmap_eq_self`), `lean/Taut/Theorem1.lean:231` (`Kmap_eq_zero_of_closed`).
- Lean statement summary: the projection `K_*(A,p)` fixes chains on `A` and kills closed cycles confined to the overlap.
- Status: **DERIVED**
- Notes: the paper's `recover` is an intermediate step; Lean uses the two `Kmap` lemmas directly inside the splitting proof rather than a packaged `recover`.

### Theorem 1  (`\label{th1}`, taut.tex:528)
- Paper statement summary: For `|A∩B| ≤ n+1`, `Zvol(X+Y) = Zvol X + Zvol Y`; and for `n ≥ 2`, any taut `M` of `X+Y` splits `M = M_X + M_Y` with `M_X,M_Y` taut.
- Lean theorem name(s): `Zvol_add_of_almost_disjoint_full` (additivity); `IsTaut.splits_full` (splitting)
- Lean file path(s): `lean/Taut/Theorem1.lean:430`; `lean/Taut/Splitting.lean:510`
- Lean statement summary: additivity at `1 ≤ n`, `(A∩B).card ≤ n+1`; splitting at `2 ≤ n` returns the filter-by-`⊆A` decomposition with both pieces taut.
- Status: **PROVEN**
- Notes: requires `[Infinite V]`. `IsTaut.splits` (`Splitting.lean:412`) is the size-2-cut core; `_full` adds the fresh-vertex WLOG.

### Corollary 2  (`\label{cor1}`, taut.tex:684)
- Paper statement summary: `Qvol` adds under almost disjoint union, and for `n ≥ 2` taut `ℚ`-fillings split.
- Lean theorem name(s): `Qvol_add_of_almost_disjoint_full`; `IsQTaut.splits_full`
- Lean file path(s): `lean/Taut/Corollary1.lean:596`; `lean/Taut/Corollary1.lean:347`
- Lean statement summary: rational additivity (`n ≥ 1`) and splitting (`n ≥ 2`) over `QChain`, via clearing denominators to Theorem 1.
- Status: **PROVEN**
- Notes: `IsQTaut M := ∀ N, Qbdry N = Qbdry M → Qnrm M ≤ Qnrm N` (order-optimal), not "`Qnrm = Qvol` attained" (see mismatch ledger).

### Theorem 2  (`\label{th2}`, taut.tex:778)
- Paper statement summary: For a simplicial triangulation `σ` of `S²` and a taut filling `M` of `X(σ)`, `M` is clean and `K(M)` is a simplicial triangulation of `B³`.
- Lean theorem name(s): cleanness — `taut_filling_is_clean3Complex` (with simpliciality `taut_filling_is_simplicialChain`, triangle-bound `taut_isPseudomanifold`); combinatorial-ball surrogate — `taut_filling_is_stickerball` / `taut_filling_is_anyrootedStickerball`
- Lean file path(s): `lean/Taut/Theorem3Clean.lean:3651` (clean3Complex); `:3462` (simplicialChain); `:3644` (stickerball); `:3636` (anyrootedStickerball); `lean/Taut/PrimeStep.lean:1646` (pseudomanifold)
- Lean statement summary: `IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → IsClean3Complex M.support` (and `IsStickerball M.support σ`); `IsClean3Complex = Pure3 ∧ IsPseudomanifold ∧ Normal3`.
- Status: **BRIDGED**
- Notes: "M is clean" = `IsClean3Complex M.support` (PROVEN, with `M.support` for `K(M)`; simpliciality derived by `taut_filling_is_simplicialChain`). "`K(M)` is a simplicial triangulation of `B³`" (topological/PL ball) is **NOT formalized**; the Lean conclusion is the combinatorial surrogate `IsStickerball`/`IsAnyrootedStickerball`. (`IsCleanBall` (`CleanShelling.lean:65`) is the clean-shelling predicate proper, `∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B`; `IsStickerball` (`:87`) `= IsCleanBall τ B ∧ B.Nonempty` adds the nonempty boundary, and `IsAnyrootedStickerball` (`:93`) inherits it — these are the combinatorial ball certificates.) The "stickerball ⇒ PL `B³`" step (Danaraj–Klee) is not in Lean. See mismatch ledger items M1–M3.

### Theorem 3  (`\label{th3}`, taut.tex:944)
- Paper statement summary: `K(M)` is a freely shellable simplicial triangulation of `B³`.
- Lean theorem name(s): `theorem3_clean`
- Lean file path(s): `lean/Taut/Theorem3Clean.lean:3379`
- Lean statement summary: `… → IsTaut M → SimplicialChain M → FreelyCleanShellable M.support σ`.
- Status: **BRIDGED**
- Notes: "freely shellable" = `FreelyCleanShellable` (`CleanShelling.lean:70`), a clean shelling carrying link certificates — stronger packaging than a boundary-only shelling. "simplicial triangulation of `B³`" is the same combinatorial surrogate as Theorem 2 (topological `B³` not formalized). `SimplicialChain M` discharged at the public level by `taut_filling_is_simplicialChain`.

### Theorem 4  (`\label{th4}`, taut.tex:1000)
- Paper statement summary: `K(M)` is a flag complex.
- Lean theorem name(s): `taut_filling_is_flagComplex` (internal hS-taking form `theorem4_flag`)
- Lean file path(s): `lean/Taut/Theorem4.lean:1514` (`theorem4_flag` at `:1503`)
- Lean statement summary: `IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → IsFlagComplex M.support`.
- Status: **PROVEN**
- Notes: `IsFlagComplex M.support` (`Theorem4.lean:35`) is the genuine clique-spans-simplex predicate; public endpoint hS-free (derives simpliciality via the bridge).

---

## 3. Definition dictionary

| Paper concept | Lean name(s) | Lean file path | Exact role | Equivalence / mismatch notes |
|---|---|---|---|---|
| Chain `C_n` | `Chain` | `Taut/Chains.lean:37` | `abbrev Chain V := Finset V →₀ ℤ` | finitely-supported ℤ-chain on `Finset V` |
| boundary `∂` | `bdry` | `Taut/Chains.lean` | `def bdry : Chain V →ₗ[ℤ] Chain V` | signed face operator |
| `L¹` norm / size `|M|` | `nrm` | `Taut/Chains.lean` | `def nrm M := ∑_{s∈supp} |M s|` | `ℕ`-valued |
| `Zvol` | `Zvol` | `Taut/Zvol.lean` | `def Zvol X := inf …` | filling volume, `ℕ`-valued |
| taut filling | `IsTaut` | `Taut/Zvol.lean` | `def IsTaut M := nrm M = Zvol (bdry M)` | combinatorial ℓ¹-minimality |
| support complex `K(M)` | `M.support` | (Finsupp) | the `Finset (Finset V)` of generators, read as a pure complex | **no explicit `K` function**; `K(M)` ↔ `M.support` for simplicial `M` |
| simplicial chain | `SimplicialChain` | `Taut/Theorem2.lean` | `def SimplicialChain M := ∀ t, M t ∈ {-1,0,1}` | "no repeated tetrahedra" |
| clean complex | `Clean3Complex` (`IsClean3Complex`) | `Taut/Pseudomanifold.lean` | `Pure3 ∧ IsPseudomanifold ∧ Normal3` | dimension-3 specialization |
| pseudomanifold | `IsPseudomanifold` | `Taut/Pseudomanifold.lean` | `∀ f, f.card=3 → faceCount τ f ≤ 2` | **triangle-bounded only**, not full classical pseudomanifold |
| edge-link connected | `EdgeLinkConnected` | `Taut/Pseudomanifold.lean:100` | normality on edges | part of `Normal3` |
| vertex-link connected | `VertexLinkConnected` | `Taut/Pseudomanifold.lean:278` | normality on vertices | part of `Normal3` (`Normal3` at `Pseudomanifold.lean`) |
| triangulated ball / stickerball / ball surrogate | `IsCleanBall`, `IsStickerball`, `IsAnyrootedStickerball` | `Taut/CleanShelling.lean` (`IsStickerball`, `IsAnyrootedStickerball`; `IsCleanBall` same file) | combinatorial `B³` certificate | **surrogate for "triangulation of `B³`"**; topological/PL ball not formalized |
| freely shellable | `FreelyCleanShellable` (`IsCleanShelling`) | `Taut/CleanShelling.lean:70` (`IsCleanShelling` same file) | clean shelling from any tet, with link certificates | stronger than boundary-only shelling |
| flag complex | `IsFlagComplex` (`SimplexOf`, `CliqueInOneSkeleton`) | `Taut/Theorem4.lean:35` (`SimplexOf:26`, `CliqueInOneSkeleton:31`) | every 1-skeleton clique spans a simplex | matches paper |
| empty K3 | `HasEmptyK3` | `Taut/Theorem4.lean` | 3 vertices, all edges simplices, set not a simplex | matches |
| empty K4 | `HasEmptyK4` | `Taut/Theorem4.lean` | 4 vertices, all edges simplices, set not a simplex | matches; (`HasK5Clique`, `NoTaboo` same file) |
| almost disjoint union | (hypothesis bundle) | `Taut/Theorem1.lean:430`, `Splitting.lean:510` | `(A∩B).card ≤ n+1` + supports `⊆A`/`⊆B`, card `n+1`, closed | informal name; no single predicate |
| splitting | `IsTaut.splits_full` (`IsTaut.splits`) | `Taut/Splitting.lean:510` (`:412`) | filter-by-`⊆A` taut decomposition | — |
| eligible tetrahedron | `EligibleTet` (geom: `GeomEligible`) | `Taut/Theorem2.lean` (`GeomEligible` `Taut/Eligible.lean`) | tet sharing two oriented faces with `σ` | `EligibleTet` includes orientation; `GeomEligible` does not |
| one-sphere flip case | `isSphere2_flipBoundary_of_eligible` | `Taut/FlipGeom.lean:1546` | removed tet leaves one `S²` | — |
| conjoined-spheres flip case | `flipEdgePresent_side_sets`, `flipEdgePresent_side_algebra`; predicate `FlipEdgePresent` | `Taut/PrimeStep.lean:1084`, `:1315`; `Taut/Theorem2.lean:89` | flip edge already present ⇒ split into two sides | — |
| no nonzero closed subchain of a taut chain | (Corollary 1; DERIVED) | via `IsTaut.subChain` `Taut/Zvol.lean:98` | closed subchain of taut is zero | not separately named (§2 Cor 1) |
| (boundary sphere `σ`) | `IsSphere2` | `Taut/Complex2.lean` | structure: pure, edge-deg 2, links connected, conn, Euler | includes `V+F=E+2` as a field |
| (unit boundary cycle) | `UnitOn` | `Taut/Theorem2.lean` | `X.support = σ ∧ ∀ s∈σ, X s = ±1` | pins `X` to `X(σ)` |
| (rational layer) | `QChain`, `IsQTaut`, `Qbdry`, `Qvol`, `Qnrm` | `Taut/Corollary1.lean` | ℚ-chains, order-optimal tautness, real `Qvol/Qnrm` | `IsQTaut` order-optimal |

---

## 4. Proof-dependency graph

### Theorem 1
- Lean endpoint: `IsTaut.splits_full` (`Splitting.lean:510`) and `Zvol_add_of_almost_disjoint_full` (`Theorem1.lean:430`).
- Depends on:
  - `IsTaut.dim_pure` — `Theorem1.lean:139` — taut generators are pure `(n+1)`-simplices.
  - `IsTaut.vert_subset` — `Theorem1.lean:157` — vertices of `M` lie on `∂M`.
  - `Kmap_eq_self` — `Theorem1.lean:167` — projection fixes the `A`-part (recover).
  - `Kmap_eq_zero_of_closed` — `Theorem1.lean:231` — projection kills the closed `B`-part (recover).
  - `not_taut_complete_cone` — `Zvol.lean:122` — no-cone (rules out straddling hybrids, needs `n ≥ 2`).
  - `IsTaut.splits` — `Splitting.lean:412` — size-2-cut core that `_full` wraps via fresh vertices.

### Theorem 2
- Lean endpoint: `taut_filling_is_clean3Complex` (`Theorem3Clean.lean:3651`); combinatorial ball `taut_filling_is_anyrootedStickerball` (`:3636`).
- Depends on:
  - minimal bad pair / induction setup — `theorem3_core_clean` — `Theorem3Clean.lean:8` — strong induction on `nrm M`, cases base/deg-3/prime; and the parallel induction in `taut_filling_is_simplicialChain` (`:3462`) and `taut_isPseudomanifold` (`PrimeStep.lean:1646`).
  - eligible tet existence — `exists_eligibleTet` (`Eligible.lean:90`), `exists_disjoint_eligible_family_noS` (`Eligible.lean:643`), `aleph_disjoint_eligible_pair` (`Theorem2Aleph.lean:1215`).
  - one-sphere case — `isSphere2_flipBoundary_of_eligible` — `FlipGeom.lean:1546`.
  - conjoined-spheres case — `flipEdgePresent_side_sets` (`PrimeStep.lean:1084`), `flipEdgePresent_side_algebra` (`PrimeStep.lean:1315`).
  - no repeated tetrahedra — `taut_filling_is_simplicialChain` — `Theorem3Clean.lean:3462`.
  - pseudomanifold condition — `taut_isPseudomanifold` — `PrimeStep.lean:1646`.
  - edge-link connectedness — `taut_edgeLinkConnected` — `Theorem3Clean.lean:2953`; also `edgeLinkConnected_insert` via the clean shelling.
  - vertex-link connectedness — `vertexLinkConnected_insert` (`Pseudomanifold.lean:347`), assembled by `IsStickerball.isClean3Complex` (`CleanShelling.lean:194`).
  - final clean/stickerball/ball conclusion — `taut_filling_is_clean3Complex` (`:3651`), `taut_filling_is_stickerball` (`:3644`), `taut_filling_is_anyrootedStickerball` (`:3636`); `theorem2_clean` (`:3607`).

### Theorem 3
- Lean endpoint: `theorem3_clean` (`Theorem3Clean.lean:3379`).
- Depends on:
  - `theorem3_core_clean` — `Theorem3Clean.lean:8` — induction skeleton.
  - `base_free_clean` — `Theorem3Clean.lean:52` — base case (`σ` ≤ 4 vertices).
  - `deg3_step_clean` — `Theorem3Clean.lean:641` — degree-3 cut, via `IsTaut.splits`.
  - `prime_step_clean` — `Theorem3Clean.lean:3348` — no-degree-3 (flip) case.

### Theorem 4
- Lean endpoint: `taut_filling_is_flagComplex` (`Theorem4.lean:1514`); internal `theorem4_flag` (`:1503`).
- Depends on:
  - no empty K3 / no empty K4 — `no_emptyK3K4_of_taut` — `Theorem4.lean:1476` — minimal-counterexample induction.
  - empty-K4 persistence — `hasEmptyK4_removeTet_of_eligible` — `Theorem4.lean:1020` — removing any eligible tet preserves an empty K4 (no octahedron/maxdeg case).
  - K5 ruled out by closed subchain — `no_k5Clique_of_no_emptyK4_taut` — `Theorem4.lean:287` — uses `bdry_filter_subset_eq_zero` (`Theorem4.lean:215`, `∂U = 0`) + `IsTaut.subChain` (`Zvol.lean:98`, `U` taut) ⇒ `U = 0`.
  - flag conclusion — `theorem4_flag_from_no_emptyK3K4` (`Theorem4.lean:316`) ← `NoTaboo.to_flag` (`Theorem4.lean:59`, no taboo ⇒ flag).

---

## 5. Mismatch ledger

**M1 — topological/PL ball.**
- Paper says: `K(M)` is a *simplicial triangulation of `B³`* (Theorems 2, 3) — i.e. carrier homeomorphic to `B³`.
- Lean proves: `IsStickerball M.support σ` / `IsAnyrootedStickerball` (`CleanShelling.lean`) — a clean-shellable normal `3`-complex with nonempty boundary (combinatorial). The shelling proper is `IsCleanBall` (`:65`); `IsStickerball` (`:87`) `= IsCleanBall ∧ B.Nonempty` adds the nonempty-boundary clause, inherited by `IsAnyrootedStickerball` (`:93`).
- Bridge needed: "clean-shellable normal `3`-pseudomanifold with boundary ⇒ PL `B³`" (Danaraj–Klee / Björner).
- Status: **NOT FORMALIZED** (recorded only as a docstring remark).
- Notes: this is the central gap; the Lean conclusion is the combinatorial surrogate, not a space homeomorphic to `B³`.

**M2 — `K(M)` vs `M.support`.**
- Paper says: support complex `K(M)`.
- Lean proves: properties of `M.support` (a `Finset (Finset V)`), read as a pure complex.
- Bridge needed: identify `K(M) := M.support` for simplicial `M`.
- Status: **DERIVED / notational** — no explicit `K` operator; trivial under simpliciality (`SimplicialChain M`).

**M3 — pseudomanifold strength.**
- Paper says: clean complex is a normal *pseudomanifold*.
- Lean proves: `IsPseudomanifold τ := ∀ f, f.card=3 → faceCount τ f ≤ 2` (triangle-bounded only).
- Bridge needed: normality (link-connectedness) supplied separately via `Normal3` / the clean shelling.
- Status: **BRIDGED** — `Clean3Complex = Pure3 ∧ IsPseudomanifold ∧ Normal3` recovers the paper's clean complex; the bare `IsPseudomanifold` name is weaker than its classical namesake.

**M4 — "clean filling" is derived, not assumed.**
- Paper says: `M` is clean iff simplicial and `K(M)` clean.
- Lean proves: simpliciality (`SimplicialChain M`) is *derived* from tautness by `taut_filling_is_simplicialChain` (`Theorem3Clean.lean:3462`); internal lemmas (`theorem3_clean`, `taut_isPseudomanifold`, `theorem4_flag`) take `SimplicialChain M` as a hypothesis discharged by that bridge.
- Bridge needed: none beyond `taut_filling_is_simplicialChain`.
- Status: **PROVEN** (the public endpoints `taut_filling_is_*` are simpliciality-free).

**M5 — rational tautness packaging.**
- Paper says: a taut `ℚ`-filling is one of minimal `L¹`-norm.
- Lean proves: `IsQTaut M := ∀ N, Qbdry N = Qbdry M → Qnrm M ≤ Qnrm N` (order-optimal).
- Bridge needed: none (order-optimal = norm-minimal); avoids asserting a minimiser exists.
- Status: **PROVEN / definitional** — same content, different packaging.

**M6 — Corollary 1 and Proposition 5 not separately named.**
- Paper says: Corollary 1 (no nonzero closed subchain), Proposition 5 (recover `(X,Y)`).
- Lean proves: both as inline steps (`IsTaut.subChain`; `Kmap_eq_self`/`Kmap_eq_zero_of_closed`).
- Bridge needed: none.
- Status: **DERIVED** — no standalone Lean theorem with that exact statement.

---

## 6. Gaps

- **Item:** "`K(M)` is a simplicial triangulation of `B³`" (the topological/PL ball), Theorems 2 and 3.
  - Status: NOT FORMALIZED (combinatorial surrogate `IsStickerball`/`IsAnyrootedStickerball` proven instead; `IsCleanBall` is the underlying clean-shelling predicate).
  - What remains: formalize "clean-shellable normal `3`-pseudomanifold with boundary ⇒ PL `B³`" (Danaraj–Klee), or state the paper conclusion explicitly modulo this external theorem.

- **Item:** classical pseudomanifold (Theorem 2 cleanness), see M3.
  - Status: BRIDGED (triangle-bound `IsPseudomanifold` + `Normal3`).
  - What remains: nothing for the certificate beyond noting `IsPseudomanifold` is triangle-bounded-only.

- **Item:** Corollary 1 (`nosubcycle`), Proposition 5 (`recover`).
  - Status: DERIVED (not separately named).
  - What remains: optional — add named Lean lemmas if the certificate wants direct citations.

- **Item:** Figures / informal remarks in `paper/tautA/taut.tex` (`\fig` macros, background prose).
  - Status: not mathematical content; `\fig`/`\figsize` macros are defined but never invoked.
  - What remains: none.
