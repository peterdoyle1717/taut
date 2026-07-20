# Lean data for the new writeup

Exact Lean output (`lake env lean` / `git` / `lake build`), captured at the commit in §6. Nothing is
paraphrased; build the natural-language writeup from these outputs, not from prose. The old prose draft
`notes/taut-lean-proof.tex` is frozen as scratch (copy: `notes/taut-lean-proof-claude-scratch.tex`) and
is NOT a source of truth.

**No endpoint names changed.** All ten names in §1 `#check` exactly as requested; no replacements.

---

## 1. `#check` output (theorem signatures, verbatim)

```
@Zvol_add_of_almost_disjoint_full : ∀ {V : Type u_1} [inst : LinearOrder V] [Infinite V] {A B : Finset V} {n : ℕ},
  1 ≤ n →
    (A ∩ B).card ≤ n + 1 →
      ∀ {X Y : Chain V},
        (∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1) →
          (∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1) → bdry X = 0 → bdry Y = 0 → Zvol (X + Y) = Zvol X + Zvol Y

@IsTaut.splits_full : ∀ {V : Type u_1} [inst : LinearOrder V] [Infinite V] {A B : Finset V} {n : ℕ},
  2 ≤ n →
    (A ∩ B).card ≤ n + 1 →
      ∀ {X Y : Chain V},
        (∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1) →
          (∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1) →
            bdry X = 0 →
              bdry Y = 0 →
                ∀ {M : Chain V},
                  IsTaut M →
                    bdry M = X + Y →
                      bdry (Finsupp.filter (fun t => t ⊆ A) M) = X ∧
                        bdry (Finsupp.filter (fun t => ¬t ⊆ A) M) = Y ∧
                          IsTaut (Finsupp.filter (fun t => t ⊆ A) M) ∧
                            IsTaut (Finsupp.filter (fun t => ¬t ⊆ A) M) ∧
                              Finsupp.filter (fun t => t ⊆ A) M + Finsupp.filter (fun t => ¬t ⊆ A) M = M

@range_bd2_eq_ker_bd1 : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)},
  IsSphere2 σ → (bd2 σ).range = (bd1 σ).ker

@exists_cut : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)},
  IsSphere2 σ → ∀ {γ : Finset V}, γ.card = 3 → Finset.powersetCard 2 γ ⊆ edgesOf σ → ∃ W, (bd2 σ) W = gammaChain σ γ

@taut_isPseudomanifold : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)} {X M : Chain V},
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M → IsPseudomanifold M.support

@theorem3_clean : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)} {X M : Chain V},
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M → FreelyCleanShellable M.support σ

@theorem3_core_clean : ∀ {V : Type u_1} [inst : LinearOrder V],
  (∀ (σ : Finset (Finset V)) (X M : Chain V),
      IsSphere2 σ → UnitOn X σ →
          bdry M = X → IsTaut M → SimplicialChain M → (vertsOf σ).card ≤ 4 → FreelyCleanShellable M.support σ) →
    (∀ (σ : Finset (Finset V)) (X M : Chain V),
        IsSphere2 σ → 4 < (vertsOf σ).card →
            UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M → HasDegree3Vertex σ →
              (∀ (σ' : Finset (Finset V)) (X' M' : Chain V),
                  nrm M' < nrm M → IsSphere2 σ' → UnitOn X' σ' → bdry X' = 0 → bdry M' = X' →
                    IsTaut M' → SimplicialChain M' → FreelyCleanShellable M'.support σ') →
                FreelyCleanShellable M.support σ) →
      (∀ (σ : Finset (Finset V)) (X M : Chain V),
          IsSphere2 σ → 4 < (vertsOf σ).card →
              UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M → NoDegree3Vertex σ →
                (∀ (σ' : Finset (Finset V)) (X' M' : Chain V),
                    nrm M' < nrm M → IsSphere2 σ' → UnitOn X' σ' → bdry X' = 0 → bdry M' = X' →
                      IsTaut M' → SimplicialChain M' → FreelyCleanShellable M'.support σ') →
                  FreelyCleanShellable M.support σ) →
        ∀ {σ : Finset (Finset V)} {X M : Chain V},
          IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
            FreelyCleanShellable M.support σ

@taut_filling_is_anyrootedStickerball : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)} {X M : Chain V},
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M → IsAnyrootedStickerball M.support σ

@taut_filling_is_clean3Complex : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)} {X M : Chain V},
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M → IsClean3Complex M.support

@taut_filling_is_shellable : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)} {X M : Chain V},
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M → IsCleanBall M.support σ
```

---

## 2. `#print` output (definitions / structures, verbatim)

```
structure Taut.IsSphere2 {V} [LinearOrder V] (σ : Finset (Finset V)) : Prop
fields:
  pure     : ∀ f ∈ σ, f.card = 3
  closed   : ∀ e ∈ edgesOf σ, edgeDeg σ e = 2
  linkConn : ∀ v ∈ vertsOf σ, ConnOn (linkGraph σ v) (linkVerts σ v)
  conn     : ConnOn (skel σ) (vertsOf σ)
  euler    : (vertsOf σ).card + σ.card = (edgesOf σ).card + 2

@[reducible] def Taut.IsClean3Complex : Finset (Finset V) → Prop :=
  fun τ => Clean3Complex τ
  -- where  Clean3Complex τ := Pure3 τ ∧ TriangleBounded3 τ ∧ Normal3 τ
  --        Pure3 τ         := ∀ t ∈ τ, t.card = 4
  --        TriangleBounded3 := IsPseudomanifold  (abbrev)

def Taut.Normal3 : Finset (Finset V) → Prop :=
  fun τ => EdgeLinkConnected τ ∧ VertexLinkConnected τ

def Taut.IsStickerball : Finset (Finset V) → Finset (Finset V) → Prop :=
  fun τ B => IsCleanBall τ B ∧ B.Nonempty
  -- where  IsCleanBall τ B := ∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B

def Taut.IsAnyrootedStickerball : Finset (Finset V) → Finset (Finset V) → Prop :=
  fun τ B => IsStickerball τ B ∧ FreelyCleanShellable τ B

structure Taut.CleanGlueStep {V} [LinearOrder V] (t : Finset V) (τ B B' : Finset (Finset V)) : Prop
fields:
  weak   : BoundaryGlueStep t B B'
  clean  : ∀ f ⊆ t, (∃ s ∈ τ, f ⊆ s) → ∃ g ∈ tetFaces t ∩ B, f ⊆ g
  newTet : t ∉ τ
  hpmc   : ∀ (f : Finset V), f.card = 3 → f ⊆ t → faceCount τ f ≤ 1
  helc   : ∀ e ⊆ t, e.card = 2 → edgeLinkVerts τ e = ∅ ∨ (t \ e ∩ edgeLinkVerts τ e).Nonempty
  hvlc   : ∀ v ∈ t, vertexLinkVerts τ v = ∅ ∨ (t \ {v} ∩ vertexLinkVerts τ v).Nonempty

def Taut.IsCleanShelling : List (Finset V) → Finset (Finset V) → Prop :=
  fun x x_1 => match x, x_1 with
    | [],     _ => False
    | t :: l, B => t.card = 4 ∧ CleanShellFrom {t} (tetFaces t) l B

def Taut.FreelyCleanShellable : Finset (Finset V) → Finset (Finset V) → Prop :=
  fun τ B => ∀ t ∈ τ, ∃ l, l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B

def Taut.IsPseudomanifold : Finset (Finset V) → Prop :=
  fun τ => ∀ (f : Finset V), f.card = 3 → faceCount τ f ≤ 2
```

### Weak / internal shelling predicates still present (`#print`)

```
structure Taut.GlueStep {V} [LinearOrder V] (t : Finset V) (B B' : Finset (Finset V)) : Prop
fields:
  card4   : t.card = 4
  shared  : (tetFaces t ∩ B).card = 1 ∨ (tetFaces t ∩ B).card = 2
  newBdry : B' = B \ tetFaces t ∪ tetFaces t \ B

@[reducible] def Taut.BoundaryGlueStep : Finset V → Finset (Finset V) → Finset (Finset V) → Prop :=
  fun t B B' => GlueStep t B B'
```

The other weak boundary-trace predicates — `IsShelling`, `IsBall`, `FreelyShellable`, `ShellFrom`
(and `RelShelling` and their reassembly lemmas) — are **deleted** (absent from the build; confirmed by
`grep`). Only `GlueStep`/`BoundaryGlueStep` survive, as the boundary-update primitive that
`CleanGlueStep.weak` wraps.

---

## 3. `#print axioms` output (verbatim)

```
'Taut.Zvol_add_of_almost_disjoint_full'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Taut.IsTaut.splits_full'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Taut.taut_isPseudomanifold'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Taut.theorem3_clean'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Taut.taut_filling_is_anyrootedStickerball' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. Dependency map (which named Lean results feed which)

Extracted by intersecting each proof body with the project's declaration-name set; dotted-method calls
(`hMt.dim_pure` ↦ `IsTaut.dim_pure`, etc.) added separately.

**Filling-volume additivity under AlmostDisjoint** — `Zvol_add_of_almost_disjoint(_full)`
← `exists_fill_eq_Zvol`, `bdry_cone_of_closed`, `Zvol_le`, `nrm_add_le` (the ≤ direction);
`IsTaut.dim_pure`, `IsTaut.vert_subset`, `Kkills_or_Kkills`, `Kmap_eq_self`, `Kmap_eq_zero_of_closed`,
`bdry_Kmap`, `nrm_Kmap_add_killed_le`, `nrm_le_killed_add_killed` (the ≥ direction);
and `Kmap_eq_zero_of_closed` ← `eq_zero_of_closed_supp_card_eq`, `eq_zero_of_supp_card_lt`.

**Taut splitting** — `IsTaut.splits(_full)`
← `IsTaut.dim_pure`, `IsTaut.vert_subset`, `hybrid_structure`, `no_extreme_hybrid`, `Kmap_eq_self`,
`Kmap_eq_zero_of_closed`, `nrm_filter_add_nrm_filter_neg`, `Zvol_add_of_almost_disjoint`, `Zvol_le`.
`hybrid_structure` ← `no_double_kill`, `kills_of_two_sdiff`, `kills_of_mem`.
`no_double_kill` ← `Kkills_or_Kkills`, `nrm_Kmap_add_killed_le`, `nrm_add_le_killed_add_killed`,
`Zvol_add_of_almost_disjoint`, `Zvol_le`.
`no_extreme_hybrid` ← `hybrid_structure`, `bdry_lk_eq_zero`, `not_taut_complete_cone`.
(Splitting does NOT use `exists_cut` / `range_bd2_eq_ker_bd1`.)

**H₁ / cut theorem** — `range_bd2_eq_ker_bd1` ← `finrank_ker_bd2` (b₂=1), `finrank_range_bd1`,
`bd1_comp_bd2`. `exists_cut` ← `range_bd2_eq_ker_bd1`, `bd1_gammaChain`.

**Clean local-structure (self-certification)** — `taut_filling_is_clean3Complex` ← `taut_clean3Complex`
← `IsStickerball.isClean3Complex` ← `IsCleanBall.clean3Complex` ← `IsCleanShelling.clean3Complex`
← `clean3Complex_insert` ← `isPseudomanifold_insert`, `edgeLinkConnected_insert`,
`vertexLinkConnected_insert` (driven by `CleanGlueStep` fields `hpmc`/`helc`/`hvlc`).
Triangle-bound only — `taut_isPseudomanifold` ← `base_isPM`, `deg3_isPM`, `prime_isPM` (induction on
`nrm M`); `prime_isPM` ← `aleph_disjoint_eligible_pair`, `removeTet_isPseudomanifold`,
`faceCount_removeTet_sharedFace_eq_zero`, `isPseudomanifold_insert`, `simplicialChain_removeTet`,
`unitOn_flipBoundary_of_eligible`.

**Degree-3 / eligible-tet step** —
`deg3_step_clean` ← `degree3_cut_setup`, `capped_cut_splits_unit`, `taut_splits_for_capped_cut`
(→ `IsTaut.splits`), `degree3_cut_star_side_glue`, `degree3_hanchor`,
`degree3_apex_notMem_left_verts_of_right_star`, `degree3_apex_notMem_right_verts_of_left_star`,
`degree3_star_start_cleanShellFrom`, `cleanGlueStep_firstStar`, `cleanGlueStep_star_of_remainder`,
`FreelyCleanShellable.insert_of_cleanGlueStep`, `starTet`, `removeTet`, `flipBoundary`.
`prime_step_clean` ← `aleph_disjoint_eligible_pair`, `EligibleTet`, `exposedFaces_eq_pair_of_eligible`,
`FlipEdgePresent`, `exists_clean_shelling_prime_case1`, `exists_clean_shelling_prime_case2`;
case-2 assembler ← `flipEdgePresent_side_sets`, `flipEdgePresent_side_algebra`,
`flipEdgePresent_side_reconstruct(_left)`, `glueStep_bridge_left`, `glueStep_bridge_right`, `exists_cut`.
(The degree-3 step is the one place that literally invokes the splitting theorem, via
`taut_splits_for_capped_cut` → `IsTaut.splits`. The prime step does not.)

**Final anyrooted stickerball theorem** — `taut_filling_is_anyrootedStickerball`
= `⟨⟨theorem2_clean …, IsSphere2.nonempty⟩, theorem3_clean …⟩`;
`theorem3_clean` = `theorem3_core_clean base_free_clean deg3_step_clean prime_step_clean`;
`theorem2_clean` ← `theorem3_clean`.

---

## 5. Weak / internal names — should NOT appear as paper-facing concepts

| name | one-line meaning | status |
|---|---|---|
| `GlueStep` | weak boundary-update glue: `t` a tet meeting boundary `B` in 1–2 faces; `B'` the symmetric-difference update. Asserts nothing about cleanness/links/ballness. | **retained**, internal |
| `BoundaryGlueStep` | reducible alias for `GlueStep` (the name `CleanGlueStep.weak` carries) | **retained**, internal alias |
| `IsPseudomanifold` | `∀ f, f.card=3 → faceCount τ f ≤ 2`, i.e. "every triangle in ≤ 2 tets" — **triangle-bounded only, NOT a classical pseudomanifold** | **retained**, but weak name: say "triangle-bounded," not "pseudomanifold" |
| `TriangleBounded3` | `abbrev` for `IsPseudomanifold` (same triangle bound) | **retained**, internal |
| `IsBall` | old weak shelling-certified ball (boundary-trace) | **obsolete (deleted)** |
| `IsShelling` | old weak boundary-trace shelling | **obsolete (deleted)** |
| `FreelyShellable` | old weak anyrooted boundary-trace shelling | **obsolete (deleted)** |
| `ShellFrom` | old weak boundary-trace shelling-from | **obsolete (deleted)** |
| `RelShelling`, `ShellFrom_*`, `IsShelling_*` | old weak reassembly lemmas | **obsolete (deleted)** |
| `CleanGlueStep`, `CleanShellFrom`, `IsCleanShelling` | the self-certifying clean-shelling machinery (paper concept is "clean shelling"/"stickerball"; the field names `weak/clean/newTet/hpmc/helc/hvlc` are certificate data) | **retained**, internal |
| `theorem3_core_clean`, `base_free_clean`, `deg3_step_clean`, `prime_step_clean`, `theorem2_clean` | induction-skeleton + case lemmas / existence wrapper | **retained**, internal |
| `taut_clean3Complex`, `base_isPM`, `deg3_isPM`, `prime_isPM` | clean3-complex wrapper; pseudomanifold-induction cases | **retained**, internal |
| `Kkills`, `KGen`, `Kmap`, `Kmap_eq_self`, `Kmap_eq_zero_of_closed`, `nrm_Kmap_add_killed_le`, `nrm_le_killed_add_killed`, `nrm_add_le_killed_add_killed`, `no_double_kill`, `hybrid_structure`, `no_extreme_hybrid`, `not_taut_complete_cone`, `bdry_lk_eq_zero`, `eq_zero_of_closed_supp_card_eq`, `eq_zero_of_supp_card_lt`, `exists_fill_eq_Zvol`, `kills_of_two_sdiff`, `kills_of_mem` | additivity/splitting proof internals (kill-map projection + the no-cone argument) | **retained**, internal |
| `aleph_base_*`, `aleph_disjoint_eligible_pair(_family)`, `capped_cut_splits_unit`, `taut_splits_for_capped_cut`, `degree3_cut_setup`, `degree3_cut_star_side_glue`, `cappedCutLeft`, `cappedCutRight`, `cutSet`, `cutChain` | machine-found (Aleph) degree-3-cut geometry | **retained**, internal |
| `degree3_hanchor`, `degree3_apex_notMem_*`, `degree3_star_start_cleanShellFrom`, `cleanGlueStep_firstStar`, `cleanGlueStep_star_of_remainder`, `cleanGlueStep_eligible`, `flipBoundary`, `FlipEdgePresent`, `flipEdgePresent_side_*`, `glueStep_bridge_left/right`, `glueStep_flipBoundary_of_eligible`, `isSphere2_flipBoundary_of_eligible`, `unitOn_flipBoundary_of_eligible`, `isTaut_removeTet`, `removeTet`, `sharedFaces`, `exposedFaces`, `EligibleTet`, `exists_eligibleTet`, `exists_clean_shelling_prime_case1/2`, `faceCount_removeTet_sharedFace_eq_zero` | degree-3 / prime reduction internals | **retained**, internal |
| `clean3Complex_insert`, `isPseudomanifold_insert`, `edgeLinkConnected_insert`, `vertexLinkConnected_insert`, `FreelyCleanShellable.insert_of_cleanGlueStep` | single-insertion preservation lemmas | **retained**, internal |
| `bd1`, `bd2`, `gammaChain`, `edgeDeg`, `linkGraph`, `skel`, `edgeLinkVerts`, `vertexLinkVerts`, `ConnOn` | homology / link implementation (the *fact* `H₁=0` is paper-worthy as `range_bd2_eq_ker_bd1`; these operator names are not) | **retained**, internal |

**Paper-facing names (these SHOULD anchor the writeup):** `Zvol`, `IsTaut`,
`Zvol_add_of_almost_disjoint_full`, `IsTaut.splits_full`, `range_bd2_eq_ker_bd1`, `exists_cut`,
`IsClean3Complex` (= `Pure3 ∧ TriangleBounded3 ∧ Normal3`), `Normal3`, `EdgeLinkConnected`,
`VertexLinkConnected`, `IsCleanBall`, `FreelyCleanShellable`, `IsStickerball`, `IsAnyrootedStickerball`,
`taut_filling_is_anyrootedStickerball` / `_stickerball` / `_clean3Complex` / `_shellable`;
hypotheses `IsSphere2`, `UnitOn`, `SimplicialChain`.

---

## 6. Final status

- **Branch:** `clean-anyrooted-stickerball`
- **Commit:** `b5a2428f89d9e5c249e0310b7e9f8e5692123695` (`b5a2428`, "comment audit (batch 2/2): ruthless prune of 13 files")
- **Build:** `cd lean && lake build` → **Build completed successfully (8273 jobs).**
- **`grep -rnE "\b(sorry|admit)\b" lean/Taut`** (excluding admit-words) → **ZERO**. (Also zero `axiom`/`native_decide`/`unsafe`.)
- **Final public theorem — "a taut filling of a simplicial 2-sphere is an anyrooted stickerball":**
  `Taut.taut_filling_is_anyrootedStickerball` (file `lean/Taut/Theorem3Clean.lean`); conclusion
  `IsAnyrootedStickerball M.support σ`; axioms `[propext, Classical.choice, Quot.sound]` (§3).

---

## 7. Addendum (2026-06-25): hS-free public endpoints

NOTE: the §1 signatures above are the `b5a2428` snapshot and show a `SimplicialChain M` hypothesis on
the stickerball endpoints. As of `a8f4566` that hypothesis is **derived, not assumed** — the bridge
`taut_filling_is_simplicialChain` (`Theorem3Clean.lean`) proves `SimplicialChain M` from tautness, and
`taut_filling_is_anyrootedStickerball` (+ `_stickerball`/`_clean3Complex`/`_shellable`) now derive it
internally and carry **no** `SimplicialChain` hypothesis.

**Theorem 4 (flag complex) public endpoint — now hS-free** (this commit). `taut_filling_is_flagComplex`
(`lean/Taut/Theorem4.lean`) was changed to derive simpliciality from the bridge, like the stickerball
endpoint; the internal hS-taking lemma `theorem4_flag` is unchanged. Exact `#check` (verbatim
`lake env lean`):

```
@taut_filling_is_flagComplex : ∀ {V : Type u_1} [inst : LinearOrder V] {σ : Finset (Finset V)} {X M : Chain V},
  IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → IsFlagComplex M.support
```

No `SimplicialChain M` in the signature. `#print axioms taut_filling_is_flagComplex` =
`[propext, Classical.choice, Quot.sound]`. Build green (8273 jobs); grep over `lean/Taut` for
`sorry`/`admit`/`axiom`/`native_decide` = ZERO. G1 consult:
`notes/codex-consults/2026-06-25-g1-th4-hs-mismatch-{spec,…}.txt` (Codex PASS, typechecked the wrapper).
