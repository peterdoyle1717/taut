# Architect request (codex): the per-target removal structure (avoids `hstart_t`); pin exact reassembly statements

Role: codex architect, continuing the FreelyShellable restructure. Banked since your
last pass (`019ecc3a`): **M-FS2** (`03488e6`, `GlueStep.sphere` dropped — glue step is
now purely combinatorial) and **M-FS2b** (`39d13bf`, the transport lemmas). Now pin
the remaining reassembly. A structural simplification needs your sign-off before I
hand targets to AlephProver.

## Banked tools (read to ground)
- `lean/Taut/Ball.lean`: `GlueStep` (now `card4 ∧ shared∈{1,2} ∧ newBdry`),
  `ShellFrom`, `IsShelling`, `IsBall`, `FreelyShellable τ B := ∀ t∈τ, ∃ l, head? = t ∧
  toFinset = τ ∧ Nodup ∧ IsShelling l B`; `ShellFrom_snoc`, `IsShelling_snoc`,
  `IsShelling_append`, and the NEW `GlueStep.union_disjoint`,
  `ShellFrom_union_disjoint` (transport across a disjoint ambient piece `K`);
  `freelyShellable_singleton`. Also the (now-`hstart_t`-laden) `FreelyShellable.
  insert_of_glueStep` in `Theorem3.lean` and `base_free`.
- `lean/Taut/Eligible.lean`: `EligibleTet`, `exists_eligibleTet_of_noDegree3`.
- `lean/Taut/Theorem2.lean` (M21 flip API): `removeTet`, `FlipEdgePresent`,
  `support_flipBoundary_of_eligible`, `unitOn_flipBoundary_of_eligible`,
  `nrm_removeTet_of_simplicial`.
- `lean/Taut/Theorem2Aleph.lean`: `aleph_disjoint_eligible_pair` (M25b: two eligible
  tets with disjoint sharedFaces), `aleph_deg3_split`, `degree3_cut_star_side_glue`,
  `ball_reassemble_of_filter_support_singleton`, and the deg3 cut data.
- `lean/Taut/Theorem23.lean`: `theorem3_core` (holes `deg3_step`, `prime_step`, both
  given the IH `∀ smaller filling, FreelyShellable`).

## The insight to validate
`FreelyShellable M.support σ` ≡ `∀ s ∈ M.support, ∃ shelling-from-s`. For each target
`s`, CHOOSE the removed eligible tet to be `≠ s`: `aleph_disjoint_eligible_pair` gives
two eligible tets with disjoint shared-face sets, hence two distinct tets, hence at
least one `≠ s`. Remove it; `s` lands in the smaller filling(s) as an OLD target
(handled by the IH's free shelling of the smaller filling), and the removed tet glues
LAST (`IsShelling_snoc`) or via the bridge (`ShellFrom_union_disjoint`). Therefore
the `hstart_t` case of L1 (a shelling that STARTS at the removed tet) is never needed
in `prime_step`.

## Questions
Q1. Confirm soundness: is it true that for ANY `s ∈ M.support`, the M25b disjoint
    eligible pair always supplies an eligible tet `e ≠ s`? (Two tets with disjoint
    shared-face sets are distinct; could one still equal `s`? then use the other.)
    Confirm this discharges every target without `hstart_t`.
Q2. The two sub-cases of removing eligible `e` (no-deg-3 σ): case 1 — `¬FlipEdgePresent`,
    the flip yields a single smaller taut filling `M_e` of `σ_e` with `GlueStep e σ_e
    σ` and `nrm M_e < nrm M` (→ `IsShelling_snoc`); case 2 — `FlipEdgePresent`, the
    removal splits into `M₁ ⊔ M₂` (→ bridge via transport). Map each to the EXISTING
    M21 flip lemmas (`support_flipBoundary_of_eligible`, `removeTet`,
    `nrm_removeTet_of_simplicial`) and the M23 edge-join split. Which lemma certifies
    "M_e is a taut filling of σ_e, nrm smaller" (case 1) and the split-as-two-fillings
    (case 2)? Is case 2 actually reachable for a *single* eligible tet, or does the
    split only arise via the edge-join (two eligible tets)?
Q3. Exact Lean statements (typecheckable against the banked API), for:
    (a) a snoc-old-target helper: from `FreelyShellable τ B`, `GlueStep e B σ`,
        `e ∉ τ`, `s ∈ τ` ⇒ `∃ l, l.head? = some s ∧ l.toFinset = insert e τ ∧
        l.Nodup ∧ IsShelling l σ` (this is L1's old-target half, no `hstart_t`);
    (b) L2 `FreelyShellable.bridge` built on `ShellFrom_union_disjoint`: state the
        almost-disjointness hypothesis (the second ball's tets' faces avoid the first
        ball's ambient boundary piece `K`) so BOTH pieces' targets are old; give the
        concatenation for target in `τ₁` and for target in `τ₂`;
    (c) `deg3_step`: does target-avoidance apply (the star tet is forced — for the
        target = star tet, do we instead use the capped remainder's FREENESS to start
        at its γ-adjacent tet, gluing the star first by the one link-triangle face γ,
        then transport)? Give the exact start-handling for target = star tet vs.
        target in the capped remainder.
    (d) the `prime_step` proof skeleton (intro s; get e≠s; case on FlipEdgePresent;
        snoc or bridge).
Q4. Best AlephProver target(s) and order; riskiest flagged. Keep verified Aleph
    proofs untouched; put new lemmas in `Theorem3.lean` / a small new file.

End with `APPROVED: <one-line>` or `BLOCKED: <one-line reason>`.
