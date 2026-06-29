# Taut Fillings — Lean correspondence ledger (draft 01)

A structured verification ledger mapping the paper-style results in
`paper/tautA/taut.tex` to the Lean 4 formalization under `lean/`.
Purpose: let an independent reader (likely an AI) check exactly how each
paper item is — or is not — formalized. Exactness over elegance.

Every Lean name, path, and line number below was grep-verified against the
build anchor commit. Paper line numbers are into `paper/tautA/taut.tex`.

---

## 1. Build anchor

| field | value |
|---|---|
| repo path | `/Users/doyle/Dropbox/taut` |
| git branch | `clean-anyrooted-stickerball` |
| git commit | `77df0ba5a4885898560d4e65819867d598de05c3` |
| Lean toolchain | `leanprover/lean4:v4.29.1` (`lean/lean-toolchain`) |
| Mathlib version | `inputRev = v4.29.1`, pinned `rev = 5e932f97dd25535344f80f9dd8da3aab83df0fe6` (`lean/lake-manifest.json`) |
| build command | `cd lean && lake build` |
| build result | `Build completed successfully (8273 jobs).` — exit 0. One linter warning only (`Taut/Corollary1.lean:549:25: unused variable s`); no errors. |
| `sorry` / `admit` count | **0** over `lean/Taut` (`grep -rnE '\b(sorry\|admit)\b' lean/Taut` empty). Also 0 `native_decide`, 0 local `axiom`. |
| excluded Lean files | **none**. `lean/Taut.lean` imports all 24 files under `lean/Taut/`; `ls lean/Taut/*.lean` = 24 files, all imported. The library build covers the entire Lean development. |
| `#print axioms` (exported endpoints) | `[propext, Classical.choice, Quot.sound]` for the integer, rational, clean/stickerball, free-shelling, and flag endpoints (no extra axioms; recorded in the prior Codex audit). |

Note on hypotheses: the `taut_filling_is_*` public endpoints (stickerball,
clean3Complex, flagComplex) take only the geometric hypotheses
`IsSphere2 σ`, `UnitOn X σ`, `bdry X = 0`, `bdry M = X`, `IsTaut M`. The
internal core lemmas (`theorem2_clean`, `theorem3_clean`, `theorem4_flag`,
`taut_isPseudomanifold`, `taut_edgeLinkConnected`, `no_k5Clique_…`) carry an
extra `SimplicialChain M` hypothesis, discharged at the public level by
`taut_filling_is_simplicialChain` (Theorem3Clean.lean:3462).

---

## 2. Paper item inventory

Status legend: **PROVEN** (a sorry-free Lean theorem proves it directly) ·
**BRIDGED** (Lean proves a differently packaged statement; bridge explained)
· **DERIVED** (follows immediately from listed Lean theorems but is not a
named endpoint) · **NOT FORMALIZED**.

### Proposition 1 — `subtaut` (taut.tex:343)
- **Paper statement summary:** a subchain of a taut chain is taut.
- **Lean theorem name(s):** `IsTaut.subChain`
- **Lean file path(s):** `lean/Taut/Zvol.lean:98`
- **Lean statement summary:** `(hM : IsTaut M) (hU : SubChain U M) : IsTaut U`.
- **Status:** **PROVEN**
- **Notes:** the workhorse behind Corollary 1 and the K5 ruleout.

### Corollary 1 — `nosubcycle` (taut.tex:365)
- **Paper statement summary:** a taut chain contains no nonzero closed subchain (if `U ⊆ M`, `M` taut, `∂U = 0`, then `U = 0`).
- **Lean theorem name(s):** *(no standalone name)* — inlined from `IsTaut.subChain` + `Zvol 0 = 0` + `nrm_eq_zero_iff`.
- **Lean file path(s):** reconstructed inline at `lean/Taut/Theorem4.lean:296–303` (inside `no_k5Clique_of_no_emptyK4_taut`).
- **Lean statement summary:** `bdry U = 0 → SubChain U M → IsTaut U → nrm U = Zvol 0 = 0 → U = 0`.
- **Status:** **DERIVED**
- **Notes:** not imported from `Corollary1.lean` (that file is the *rational* development). The argument is rebuilt where needed.

### Proposition 2 — `maxdeg` (taut.tex:405)
- **Paper statement summary:** degree bound for a closed chain — `Zvol(X)` plus the degree of any vertex is at most the norm.
- **Lean theorem name(s):** `Zvol_add_deg_le`
- **Lean file path(s):** `lean/Taut/Zvol.lean:113`
- **Lean statement summary:** `(x : V) (hX : bdry X = 0) : Zvol X + deg x X ≤ nrm X`.
- **Status:** **PROVEN**
- **Notes:** the counting inequality used to produce eligible tetrahedra (feeds `exists_eligibleTet`, `aleph_card_gap_two`).

### Proposition 3 — `nocone` (taut.tex:421)
- **Paper statement summary:** a taut filling cannot contain a complete cone over a closed chain when an off-apex vertex has nonzero degree.
- **Lean theorem name(s):** `not_taut_complete_cone`
- **Lean file path(s):** `lean/Taut/Zvol.lean:122`
- **Lean statement summary:** `(hM : IsTaut M) (hU : SubChain (cone x W) M) (hW : bdry W = 0) (hx : deg x W = 0) (hx' : deg x' W ≠ 0) : False`.
- **Status:** **PROVEN**

### Proposition 4 — `nointernal` (taut.tex:429)
- **Paper statement summary:** a taut filling has no internal vertex; every vertex of `M` lies on `∂M`.
- **Lean theorem name(s):** `IsTaut.no_internal_vertex`
- **Lean file path(s):** `lean/Taut/Zvol.lean:134`
- **Lean statement summary:** `(hM : IsTaut M) (hdim : ∀ s ∈ M.support, 2 ≤ s.card) (hxM : x ∈ vert M) (hxB : x ∉ vert (bdry M)) : False`.
- **Status:** **PROVEN**
- **Notes:** consumed by `IsTaut.vert_subset` (Theorem1.lean:157).

### Proposition 5 — `recover` (taut.tex:498)
- **Paper statement summary:** the cone/`K`-operator recovery: a taut filling is recovered by `K_{A,p}`, which is the identity on the `A`-supported part and annihilates a closed `B`-supported part.
- **Lean theorem name(s):** `Kmap_eq_self`, `Kmap_eq_zero_of_closed`
- **Lean file path(s):** `lean/Taut/Theorem1.lean:167`, `lean/Taut/Theorem1.lean:231`
- **Lean statement summary:** `Kmap_eq_self : (∀ s ∈ M.support, s ⊆ A) → Kmap A p M = M`; `Kmap_eq_zero_of_closed : 1 ≤ n → p ∈ A∩B → (A∩B).card ≤ n+1 → (Y on B, card n+1) → bdry Y = 0 → Kmap A p Y = 0`.
- **Status:** **BRIDGED**
- **Notes:** one paper proposition ↔ two sorry-free Lean lemmas (identity + annihilation). Both individually PROVEN; the "recover" packaging is the bridge. They are the engine of Theorem 1's `≥` direction.

### Theorem 1 — `th1` (taut.tex:528)
- **Paper statement summary:** `Zvol` is additive on almost-disjoint unions, and a taut filling of `X+Y` splits into taut fillings of `X` and of `Y`.
- **Lean theorem name(s):** `Zvol_add_of_almost_disjoint_full` (additivity); `IsTaut.splits_full` (splitting)
- **Lean file path(s):** `lean/Taut/Theorem1.lean:430`; `lean/Taut/Splitting.lean:510`
- **Lean statement summary:** additivity — `1 ≤ n → (A∩B).card ≤ n+1 → X on A, Y on B (card n+1) → bdry X = bdry Y = 0 → Zvol (X+Y) = Zvol X + Zvol Y`. Splitting — same hyps with `2 ≤ n`, `IsTaut M`, `bdry M = X+Y` ⇒ the 5-part filter conjunction (`bdry` of each half is `X`/`Y`, each half `IsTaut`, halves sum to `M`).
- **Status:** **PROVEN**

### Corollary 2 — `cor1` (taut.tex:684)
- **Paper statement summary:** rational version of Theorem 1 — `Qvol` additivity and splitting of rational taut fillings.
- **Lean theorem name(s):** `Qvol_add_of_almost_disjoint_full`; `IsQTaut.splits_full`
- **Lean file path(s):** `lean/Taut/Corollary1.lean:596`; `lean/Taut/Corollary1.lean:347`
- **Lean statement summary:** the `QChain`/`Qvol`/`Qbdry`/`IsQTaut` analogues of the Theorem 1 pair, identical shape.
- **Status:** **PROVEN**
- **Notes:** the paper's second corollary; Lean label is `cor1` but it is the rational (order-optimal `IsQTaut`) result.

### Theorem 2 — `th2` (taut.tex:778)
- **Paper statement summary:** for a simplicial 2-sphere `σ` and a taut filling `M` of `X(σ)`, `M` is clean and `K(M)` is a simplicial triangulation of `B³`.
- **Lean theorem name(s):** cleanness — `taut_filling_is_clean3Complex` (with `taut_filling_is_simplicialChain`, `taut_isPseudomanifold`); ball surrogate — `taut_filling_is_stickerball` / `taut_filling_is_anyrootedStickerball`.
- **Lean file path(s):** `lean/Taut/Theorem3Clean.lean:3651` (clean3Complex), `:3462` (simplicialChain), `:3644` (stickerball), `:3636` (anyrootedStickerball); `lean/Taut/PrimeStep.lean:1646` (pseudomanifold).
- **Lean statement summary:** `IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → IsClean3Complex M.support` and `IsStickerball M.support σ`, where `IsClean3Complex = Pure3 ∧ TriangleBounded3 ∧ Normal3`.
- **Status:** **BRIDGED**
- **Notes:** "`M` is clean" is PROVEN (`IsClean3Complex M.support`). "`K(M)` is a simplicial triangulation of `B³`" (a topological/PL ball) is **NOT formalized**; Lean proves the combinatorial surrogate `IsStickerball`/`IsAnyrootedStickerball`. The "stickerball ⇒ PL `B³`" step (Danaraj–Klee) is external. See mismatch ledger M1–M3.

### Theorem 3 — `th3` (taut.tex:944)
- **Paper statement summary:** `K(M)` is a freely shellable simplicial triangulation of `B³`.
- **Lean theorem name(s):** `theorem3_clean`
- **Lean file path(s):** `lean/Taut/Theorem3Clean.lean:3379`
- **Lean statement summary:** `… → IsTaut M → SimplicialChain M → FreelyCleanShellable M.support σ`.
- **Status:** **BRIDGED**
- **Notes:** "freely shellable" = `FreelyCleanShellable` (CleanShelling.lean:70), a clean shelling that may start at any tet and carries link certificates. "triangulation of `B³`" is the same combinatorial surrogate as Theorem 2 (topological `B³` not formalized). `SimplicialChain M` discharged publicly via `taut_filling_is_simplicialChain`.

### Theorem 4 — `th4` (taut.tex:1000)
- **Paper statement summary:** `K(M)` is a flag complex (every clique in the 1-skeleton spans a simplex).
- **Lean theorem name(s):** `theorem4_flag`; public `taut_filling_is_flagComplex`
- **Lean file path(s):** `lean/Taut/Theorem4.lean:1503`; `lean/Taut/Theorem4.lean:1514`
- **Lean statement summary:** `… → IsTaut M → IsFlagComplex M.support` (`taut_filling_is_flagComplex` drops the explicit `SimplicialChain M`, deriving it internally).
- **Status:** **PROVEN**

---

## 3. Definition dictionary

| Paper concept | Lean name(s) | File path(s) | Exact role | Equivalence / mismatch notes |
|---|---|---|---|---|
| Chain | `Chain` | `Chains.lean:37` | `Finsupp` from oriented simplices to ℤ | `abbrev Chain V := Finset V →₀ ℤ` (an `abbrev`, not a `def`) |
| boundary | `bdry` | `Chains.lean:124` | `∂` operator on chains | direct |
| L¹ norm / size | `nrm` | `Chains.lean:423` | `‖·‖₁` = sum of `\|coeff\|` | direct |
| Zvol | `Zvol` | `Zvol.lean:75` | minimal filling norm `= inf{ nrm M : bdry M = X }` | `noncomputable def` |
| taut filling | `IsTaut` | `Zvol.lean:79` | `IsTaut M := nrm M = Zvol (bdry M)` | direct |
| support complex `K(M)` | `M.support` | (Finsupp `.support`) | the set of simplices with nonzero coeff, read as a pure complex | **no explicit `K` operator**; `K(M) := M.support` under simpliciality (M2) |
| simplicial chain | `SimplicialChain` | `Theorem2.lean:27` | all coeffs in `{−1,0,1}` | direct |
| clean complex | `Clean3Complex` / `IsClean3Complex` | `Pseudomanifold.lean:415` / `:421` | `Pure3 ∧ TriangleBounded3 ∧ Normal3` | `IsClean3Complex` is an `abbrev` for `Clean3Complex` |
| pseudomanifold | `IsPseudomanifold` ( = `TriangleBounded3`) | `Pseudomanifold.lean:28` (abbrev `:34`) | `∀ f, f.card = 3 → faceCount τ f ≤ 2` (triangle ≤ 2 tets) | **triangle-bounded only** — weaker than the classical pseudomanifold; normality added separately by `Normal3` (M3) |
| edge-link connected | `EdgeLinkConnected` | `Pseudomanifold.lean:100` | edge links are connected | direct |
| vertex-link connected | `VertexLinkConnected` | `Pseudomanifold.lean:278` | vertex links are connected | direct; together = `Normal3` (`:408`) |
| triangulated ball / stickerball / ball surrogate | `IsCleanBall`; `IsStickerball`; `IsAnyrootedStickerball` | `CleanShelling.lean:65`; `:87`; `:93` | combinatorial `B³` certificate | `IsCleanBall` = clean-shelling predicate (`∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B`); `IsStickerball = IsCleanBall ∧ B.Nonempty`; `IsAnyrootedStickerball = IsStickerball ∧ FreelyCleanShellable`. **Surrogate for "triangulation of `B³`"**; PL ball not formalized (M1) |
| freely shellable | `FreelyCleanShellable` | `CleanShelling.lean:70` | any tet can head a clean shelling | stronger than a boundary-only shelling |
| flag complex | `IsFlagComplex` | `Theorem4.lean:35` | every clique spans a simplex | direct |
| empty K3 | `HasEmptyK3` | `Theorem4.lean:39` | `∃ s, card 3 ∧ all edges simplices ∧ ¬ SimplexOf s` | direct |
| empty K4 | `HasEmptyK4` | `Theorem4.lean:43` | same, `card 4` | direct |
| no nonzero closed subchain of a taut chain | `IsTaut.subChain` (+ inline argument) | `Zvol.lean:98` | the primitive; `∂U=0 ⇒ U=0` reconstructed at `Theorem4.lean:296–303` | paper Corollary 1; not a standalone Lean theorem (M6) |
| almost disjoint union | *(no named `def`)* | hypothesis bundle on `Theorem1.lean:357` | `X` closed pure card `n+1` on `A`; `Y` likewise on `B`; `(A∩B).card ≤ n+1` | **no `AlmostDisjoint` predicate** — it is the conjunction of these hypotheses (M-A) |
| splitting of taut fillings | *(no named predicate)* | conclusion of `IsTaut.splits` / `splits_full`, `Splitting.lean:420–424` / `517–521` | inline 5-part conjunction (each half's `bdry`, each half `IsTaut`, halves sum to `M`) | the "splitting" is a theorem conclusion, not a defined relation |
| eligible tetrahedron | `EligibleTet`; `GeomEligible` | `Theorem2.lean:84`; `Eligible.lean:306` | `t.card=4 ∧ t∈support ∧ (sharedFaces M t).card=2 ∧ ∀ s∈sharedFaces, bdry M s = tetContribution M t s` | `GeomEligible` is the geometric variant |
| one-sphere flip case | `isSphere2_flipBoundary_of_eligible` | `FlipGeom.lean:1546` | flip edge **absent**: removing the eligible tet leaves a single 2-sphere | proved field-by-field (pure/closed/linkConn/conn/euler) |
| conjoined-spheres flip case | `flipEdgePresent_side_sets` (+ `flipEdgePresent_boundary_side_package`) | `PrimeStep.lean:1084` (+ `:1011`) | flip edge **present**: the boundary splits into two side-spheres joined along the new edge, with a tet partition | **no single "two spheres joined" lemma**; the role is the side-split here + the case-2 shelling `exists_clean_shelling_prime_case2` (Theorem3Clean.lean:3129) |

---

## 4. Proof spine

Each spine is ordered leaves → endpoint. All cited bodies are `sorry`/`admit`-free
(whole-repo grep empty). Status **PROVEN** = sorry-free named lemma;
**BRIDGED** = combinatorial surrogate for a topological claim.

### Theorem 1 — splitting / additivity
- **Paper theorem:** Theorem 1 (`th1`, taut.tex:528)
- **Lean endpoint:** `Zvol_add_of_almost_disjoint_full` (Theorem1.lean:430) + `IsTaut.splits_full` (Splitting.lean:510)
- **Proof spine:**
  - **Step purity** — paper role: optimal fillings carry no junk → `IsTaut.dim_pure` (Theorem1.lean:139) — PROVEN
  - **Step vertex-bound** — paper role: vertices of `M` lie on `∂M` → `IsTaut.vert_subset` (Theorem1.lean:157), via `IsTaut.no_internal_vertex` (Zvol.lean:134) — PROVEN
  - **Step recover-identity** — paper role: `K` fixes the `A`-part (Prop 5) → `Kmap_eq_self` (Theorem1.lean:167) — PROVEN
  - **Step recover-annihilate** — paper role: `K` kills a closed `B`-part (Prop 5) → `Kmap_eq_zero_of_closed` (Theorem1.lean:231) — PROVEN
  - **Step additivity (witnessed)** — paper role: the "kill" count → `Zvol_add_of_almost_disjoint` (Theorem1.lean:357) — PROVEN
  - **Step additivity (full)** — paper role: drop the witness-pair hypothesis by enlarging `A∩B` → `Zvol_add_of_almost_disjoint_full` (Theorem1.lean:430) — PROVEN
  - **Step splitting (witnessed)** — paper role: identify the two taut halves → `IsTaut.splits` (Splitting.lean:412) — PROVEN
  - **Step splitting (full)** — paper role: endpoint → `IsTaut.splits_full` (Splitting.lean:510) — PROVEN

### Theorem 2 — clean filling / triangulated ball (surrogate)
- **Paper theorem:** Theorem 2 (`th2`, taut.tex:778)
- **Lean endpoint:** `taut_filling_is_clean3Complex` (Theorem3Clean.lean:3651) + `taut_filling_is_stickerball` (Theorem3Clean.lean:3644)
- **Induction measure:** `Nat.strong_induction_on` on **`nrm M`** (number of tetrahedra counted with `±1` multiplicity), generalised over `σ, X, M`. The same `nrm M` strong-induction skeleton recurs in `theorem3_core_clean`, `taut_isPseudomanifold`, `taut_edgeLinkConnected`, `taut_filling_is_simplicialChain`. "Minimal bad pair" is realized as: assume failure at minimal `nrm`, delete an eligible tet → strictly smaller `nrm` → contradict IH.
- **Proof spine:**
  - **Step homology core** — paper role: `H₁(σ)=0` for a 2-sphere → `range_bd2_eq_ker_bd1` (Homology2.lean:536); Euler bound `chi_le_two` (Homology2.lean:562) — PROVEN
  - **Step eligible-tet existence (single)** — paper role: a removable tet exists → `exists_eligibleTet` (Eligible.lean:90), via pigeonhole on `Zvol_add_deg_le` — PROVEN
  - **Step eligible-tet existence (disjoint pair, no-deg-3)** — paper role: two removable tets with disjoint shared-face pairs → `aleph_disjoint_eligible_pair` (Theorem2Aleph.lean:1215), via card gap `aleph_card_gap_two` (Theorem2Aleph.lean:1098) — PROVEN
  - **Step one-sphere flip case** — paper role: removal keeps a single 2-sphere → `isSphere2_flipBoundary_of_eligible` (FlipGeom.lean:1546) — PROVEN
  - **Step conjoined-spheres flip case** — paper role: removal splits into two spheres joined along the new edge → `flipEdgePresent_side_sets` (PrimeStep.lean:1084), geometry in `flipEdgePresent_boundary_side_package` (PrimeStep.lean:1011) — PROVEN
  - **Step degree-3 cut** — paper role: connected-sum reduction at a degree-3 vertex → `separates` (Separation.lean:988) + `isSphere2_cut` (Separation.lean:979), assembled by `degree3_cut_setup` (Theorem2Aleph.lean:420) — PROVEN
  - **Step no repeated tetrahedra (simpliciality)** — paper role: `M` clean ⇒ no repeated tet → `taut_filling_is_simplicialChain` (Theorem3Clean.lean:3462) — PROVEN
  - **Step pseudomanifold (triangle ≤ 2 tets)** — paper role: `K(M)` is triangle-bounded → `taut_isPseudomanifold` (PrimeStep.lean:1646), induction step `removeTet_isPseudomanifold` (PrimeStep.lean:1491) — PROVEN
  - **Step edge-link connectedness** — paper role: links connected → `taut_edgeLinkConnected` (Theorem3Clean.lean:2953) — PROVEN
  - **Step vertex-link connectedness** — paper role: links connected (no pinch) → `vertexLinkConnected_insert` (Pseudomanifold.lean:347), carried into the endpoint via `clean3Complex_insert` (Pseudomanifold.lean:445; its proof at `:455` invokes `edgeLinkConnected_insert` and `vertexLinkConnected_insert`) inside `CleanGlueStep.clean3Complex` — PROVEN. **Note:** there is no standalone `taut_vertexLinkConnected`; vertex-link connectedness reaches the endpoint only through `Clean3Complex`/`Normal3` carried by the clean shelling, not as a separate `taut_…` theorem.
  - **Step final clean / stickerball assembly** — paper role: assemble clean + ball → `theorem2_clean` (Theorem3Clean.lean:3607, `IsCleanBall`) → `taut_filling_is_stickerball` (Theorem3Clean.lean:3644, adds `B.Nonempty`) → `taut_filling_is_clean3Complex` (Theorem3Clean.lean:3651) — PROVEN combinatorially; **BRIDGED** to the topological `B³` claim (M1).

### Theorem 3 — freely shellable (surrogate ball)
- **Paper theorem:** Theorem 3 (`th3`, taut.tex:944)
- **Lean endpoint:** `theorem3_clean` (Theorem3Clean.lean:3379)
- **Proof spine:**
  - **Step induction core** — paper role: shell the ball by induction → `theorem3_core_clean` (Theorem3Clean.lean:8); strong induction on `nrm M`; branches `(vertsOf σ).card ≤ 4` (base) / `HasDegree3Vertex σ` (deg3) / else (prime) — PROVEN
  - **Step base** — paper role: a single tetrahedron is shellable → `base_free_clean` (Theorem3Clean.lean:52) — PROVEN
  - **Step degree-3 reduction** — paper role: connected sum with a tetrahedral boundary at a degree-3 vertex; peel the star tet, recurse, glue → `deg3_step_clean` (Theorem3Clean.lean:641), cut datum `degree3_cut_setup` (Theorem2Aleph.lean:420) — PROVEN
  - **Step prime (no degree-3) reduction** — paper role: remove a disjoint-pair eligible tet, recurse, glue → `prime_step_clean` (Theorem3Clean.lean:3348) — PROVEN
    - **Sub-case flip edge absent** → `exists_clean_shelling_prime_case1` (Theorem3Clean.lean:2985), uses one-sphere flip `isSphere2_flipBoundary_of_eligible` — PROVEN
    - **Sub-case flip edge present** → `exists_clean_shelling_prime_case2` (Theorem3Clean.lean:3129), uses conjoined-spheres split `flipEdgePresent_side_sets`; assembly `clean_case2_sideA` (Theorem3Clean.lean:3065) — PROVEN
  - **Step endpoint** — `theorem3_clean` (Theorem3Clean.lean:3379) → `FreelyCleanShellable M.support σ` — PROVEN combinatorially; **BRIDGED** to topological `B³` (M1).

### Theorem 4 — flag complex
- **Paper theorem:** Theorem 4 (`th4`, taut.tex:1000)
- **Lean endpoint:** `theorem4_flag` (Theorem4.lean:1503); public `taut_filling_is_flagComplex` (Theorem4.lean:1514)
- **Proof spine:**
  - **Step no empty K3** — paper role: a triangle whose 3 edges are present is filled → left conjunct of `no_emptyK3K4_of_taut` (Theorem4.lean:1476); proven jointly with K4 by `nrm M` strong induction (`base_no_emptyK3K4` / `deg3_no_emptyK3K4` / `prime_no_emptyK3K4`) — PROVEN. *(Not a standalone lemma.)*
  - **Step no empty K4 (K4-persistence)** — paper role: eliminate the octahedron via persistence under eligible-tet removal → `hasEmptyK4_removeTet_of_eligible` (Theorem4.lean:1020): `¬HasEmptyK3 → (K4 on `s`, edges simplices, `¬SimplexOf s`) → EligibleTet M e → HasEmptyK4 (removeTet M e).support`. Each K4 edge keeps a witness tet `≠ e` (diagonal edge via `k4_edge_has_witness_ne_removed_of_no_emptyK3`, others via `edge_witness_ne_removed_of_not_sharedEdge`) — PROVEN. **This replaces the paper's maxdeg≥5 octahedron counting.**
  - **Step K5 ruled out by closed subchain** — paper role: Corollary 1 kills a 5-clique → `no_k5Clique_of_no_emptyK4_taut` (Theorem4.lean:287). The sub-chain `U := M.filter (· ⊆ s)` on the 5 vertices is **closed** (`bdry_filter_subset_eq_zero`, Theorem4.lean:215 — each of the 10 triangles is interior, coeff 0), hence taut (`IsTaut.subChain`, Zvol.lean:98), hence `nrm U = Zvol 0 = 0`, hence `U = 0`, contradicting a tet of `s` in `U`. Inline Corollary 1 at **Theorem4.lean:296–303**. — PROVEN
  - **Step flag conclusion** — paper role: no taboo ⇒ flag → `theorem4_flag_from_no_emptyK3K4` (Theorem4.lean:316) gets `¬HasK5Clique` from the K5 step, then `NoTaboo.to_flag` (Theorem4.lean:59) (clique card 3 ⇒ K3 contradiction L76–77, card 4 ⇒ K4 L78–79, card ≥5 ⇒ extract forbidden K5 L64–67) ⇒ `IsFlagComplex`. Assembled by `theorem4_flag` (Theorem4.lean:1503); public `taut_filling_is_flagComplex` (Theorem4.lean:1514) discharges `SimplicialChain M` via `taut_filling_is_simplicialChain`. — PROVEN

---

## 5. Mismatch ledger

Every place the paper statement and the Lean statement do not literally match.

### M1 — topological/PL ball
- **Paper says:** `K(M)` is a *simplicial triangulation of `B³`* (Theorems 2, 3) — carrier homeomorphic to `B³`.
- **Lean proves:** `IsStickerball M.support σ` / `IsAnyrootedStickerball` (CleanShelling.lean) — a clean-shellable normal 3-complex with nonempty boundary (combinatorial). The shelling proper is `IsCleanBall` (`:65`); `IsStickerball` (`:87`) `= IsCleanBall ∧ B.Nonempty`; `IsAnyrootedStickerball` (`:93`) inherits it.
- **Bridge needed:** "clean-shellable normal 3-pseudomanifold with boundary ⇒ PL `B³`" (Danaraj–Klee / Björner).
- **Status:** **NOT FORMALIZED** (recorded only as a docstring remark, CleanShelling.lean:83–86).
- **Notes:** the central gap; the Lean conclusion is a combinatorial certificate, not a space homeomorphic to `B³`.

### M2 — `K(M)` vs `M.support`
- **Paper says:** support complex `K(M)`.
- **Lean proves:** properties of `M.support` (a `Finset (Finset V)`), read as a pure complex.
- **Bridge needed:** identify `K(M) := M.support` for simplicial `M`.
- **Status:** **DERIVED / notational** — no explicit `K` operator; trivial under simpliciality (`SimplicialChain M`, derived by `taut_filling_is_simplicialChain`).
- **Notes:** harmless once simpliciality is in hand.

### M3 — pseudomanifold strength
- **Paper says:** the clean complex is a normal *pseudomanifold*.
- **Lean proves:** `IsPseudomanifold τ := ∀ f, f.card = 3 → faceCount τ f ≤ 2` (triangle-bounded only).
- **Bridge needed:** normality (link-connectedness) supplied separately via `Normal3` / the clean shelling.
- **Status:** **BRIDGED** — `Clean3Complex = Pure3 ∧ IsPseudomanifold ∧ Normal3` (Pseudomanifold.lean:415) recovers the paper's clean complex; the bare `IsPseudomanifold` name is weaker than its classical namesake.

### M4 — "clean filling" is derived, not assumed
- **Paper says:** `M` is clean iff simplicial and `K(M)` clean (a definition).
- **Lean proves:** simpliciality (`SimplicialChain M`) is *derived* from tautness by `taut_filling_is_simplicialChain` (Theorem3Clean.lean:3462); internal lemmas take `SimplicialChain M` as a hypothesis discharged by that bridge.
- **Bridge needed:** none — Lean proves *more* (cleanness is a theorem, not an assumption).
- **Status:** **OK / stronger in Lean**.

### M5 — order-optimality of the rational corollary
- **Paper says:** Corollary 2 is the rational analogue of Theorem 1.
- **Lean proves:** `IsQTaut` is an order-optimality predicate on `QChain`; the splitting/additivity are proved for it (Corollary1.lean:347, :596).
- **Bridge needed:** none — same shape as the integer case.
- **Status:** **OK** — noted only because the Lean label is `cor1` while the paper numbers it Corollary 2.

### M6 — Corollary 1 / Proposition 5 not standalone Lean theorems
- **Paper says:** Corollary 1 (`nosubcycle`) and Proposition 5 (`recover`) are named results.
- **Lean proves:** Corollary 1 is inlined at Theorem4.lean:296–303 (from `IsTaut.subChain` + `Zvol 0 = 0`); Proposition 5 is two K-map lemmas (`Kmap_eq_self`, `Kmap_eq_zero_of_closed`).
- **Bridge needed:** none — both are present, just not under a single name.
- **Status:** **DERIVED / repackaged**.

### M-A — "almost disjoint union" / "splitting" are not named definitions
- **Paper says:** "almost-disjoint union" and "splitting" read as defined notions.
- **Lean proves:** "almost disjoint" is the hypothesis bundle on `Zvol_add_of_almost_disjoint` (Theorem1.lean:357: `X,Y` closed pure card `n+1` on `A,B`; `(A∩B).card ≤ n+1`); "splitting" is the inline 5-part conjunction concluded by `IsTaut.splits`/`splits_full` (Splitting.lean:420–424 / 517–521).
- **Bridge needed:** none — they are unfolded hypotheses/conclusions, not `def`s.
- **Status:** **OK / notational**.

---

## 6. Gaps and uncertainty

### Gap 1 — topological/PL `B³` (central)
- **Item:** "`K(M)` is a simplicial triangulation of `B³`" (Theorems 2, 3).
- **Status:** **NOT FORMALIZED** (combinatorial surrogate `IsStickerball`/`IsAnyrootedStickerball` proven instead; `IsCleanBall` is the underlying clean-shelling predicate).
- **What remains:** formalize "clean-shellable normal 3-pseudomanifold with boundary ⇒ PL `B³`" (Danaraj–Klee), or state the paper conclusion explicitly modulo this external theorem.
- **Who/what should check it:** a topologist / PL-topology formalizer; cross-check against Mathlib's (currently absent) PL-ball API.

### Gap 2 — classical pseudomanifold naming
- **Item:** the bare `IsPseudomanifold` is triangle-bounded only (M3).
- **Status:** **BRIDGED** — normality added by `Normal3`.
- **What remains:** nothing for correctness; optionally rename to avoid the weaker-than-classical connotation.
- **Who/what should check it:** Lean-side reviewer; cosmetic.

### Gap 3 — vertex-link connectedness has no standalone endpoint
- **Item:** vertex-link connectedness reaches the endpoint only via `Clean3Complex`/`Normal3` carried by the clean shelling, not as a `taut_vertexLinkConnected` theorem (edge-link connectedness *does* have `taut_edgeLinkConnected`).
- **Status:** **OK but asymmetric** — present inside the shelling propagation (`vertexLinkConnected_insert` Pseudomanifold.lean:347; `clean3Complex_insert` Pseudomanifold.lean:445).
- **What remains:** optionally expose a standalone `taut_vertexLinkConnected` for symmetry/auditing ease.
- **Who/what should check it:** Lean-side reviewer.

### Gap 4 — `K(M) := M.support` identification
- **Item:** the paper's `K(M)` is identified with `M.support` (M2).
- **Status:** **DERIVED / notational**, sound under simpliciality.
- **What remains:** nothing; flagged for completeness.
- **Who/what should check it:** Codex / independent reader confirming the identification is used consistently.

---

## 7. Audit instructions for Codex

Audit this ledger independently against the Lean repo at commit
`77df0ba`. Check specifically:

1. **Theorem names exist** — every Lean name in Sections 2–4 resolves to a
   declaration at the stated path.
2. **File paths and line numbers are correct** — spot-check each `file:line`
   anchor; re-grep, do not trust the ledger.
3. **Statuses are not overclaimed** — no item marked PROVEN where the Lean
   statement is a surrogate or carries undischarged hypotheses; Theorems 2/3
   must be BRIDGED, not PROVEN.
4. **Every paper theorem has an entry** — Propositions 1–5, Corollaries 1–2,
   Theorems 1–4 all present in Section 2.
5. **No theorem using `sorry`/`admit` is marked PROVEN** — re-run the
   `sorry`/`admit`/`axiom`/`native_decide` scan over `lean/Taut`.
6. **Mismatch ledger is honest** — M1 (topological `B³`) is the central gap
   and is not hidden; M2–M6, M-A accurately describe the repackaging.
7. **Proof spines for Theorem 2 and Theorem 4 are complete enough to audit**
   — Theorem 2 covers induction measure, eligible-tet existence, both flip
   cases, no-repeat/pseudomanifold/edge-link/vertex-link, and the final
   clean/stickerball assembly; Theorem 4 covers no-K3, no-K4 (persistence),
   K5-via-closed-subchain, and the flag conclusion.

Write the audit verdict (first line `AUDIT: PASS` or
`AUDIT: CORRECTIONS NEEDED`) and findings to
`paper/lean-map-draft-codex-audit.md`. Cite `file:line` for every
correction. Do not modify the Lean tree or this ledger.
