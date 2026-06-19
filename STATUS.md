# STATUS — clean-shelling migration, hOppEmpty case-1

## Branch / commit
- Branch `claude/clean-shelling`, HEAD `0c79b53`.
- Working tree CLEAN; full `lake build` green (8272 jobs); grep `sorry/admit/axiom/native_decide` over `lean/Taut` → ZERO.

## Checked facts (all std-3 axioms: propext, Classical.choice, Quot.sound)
- Weak `theorem2`/`theorem3` LOCKED and intact (`4e52d07`), statements unchanged.
- `deg3_step_clean` CHECKED (`6f6931f`).
- `theorem3_core_clean` + `base_free_clean` CHECKED (`935b2ca`).
- `cleanGlueStep_eligible` CHECKED (`4f75b83`) — re-glues the eligible tet `e`, consuming `hOppEmpty : edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅`.
- `oppEdge_empty_of_flipEdgePresent` CHECKED (`9bbc633`) — the `FlipEdgePresent` half of `hOppEmpty` (combinatorial, side-separation).
- **`oppEdge_empty_of_full_edgeLinkConnected` CHECKED (`0c79b53`)** — the reduction lemma: GIVEN `hELM : EdgeLinkConnected M.support`, the flip-opposite edge lies in no remaining tet (proof: rogue-tet apex is unreachable from the Adj-closed flip-edge pair, contradicting `EdgeLinkConnected`). `#print axioms` = std-3.

## hOppEmpty case-1 now reduces to ONE input
`hOppEmpty` (case-1, `¬FlipEdgePresent`) is fully reduced to the single hypothesis
**`EdgeLinkConnected M.support`** via the CHECKED `oppEdge_empty_of_full_edgeLinkConnected`. That
input is exactly the new theorem
```lean
theorem taut_edgeLinkConnected {σ : Finset (Finset V)} {X M : Chain V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0)
    (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4) :
    EdgeLinkConnected M.support
```

## Authorization (2026-06-19): clean-route topology AUTHORIZED
User authorized proceeding through the remaining clean-route topology WITHOUT per-lemma approval.
Codex stays architect; Claude implements. **Authorized without further user approval:**
`taut_edgeLinkConnected` (or any narrower theorem supplying `hELM : EdgeLinkConnected M.support`)
and its supporting edge-link lemmas; the clean RelShelling bridge for `prime_step_clean` case-2;
completing `hOppEmpty`/`cleanGlueStep_eligible`/`prime_step_clean`/`theorem3_clean`/`theorem2_clean`;
AlephProver on named local lemmas; Codex consults for next-target selection; bounded subagents;
committing green checkpoints. **Do NOT stop merely because the next lemma is "new topology."**

**Still require user approval before:** changing core defs (`Clean3Complex`, `Normal3`,
`CleanGlueStep`, `IsCleanBall`, `FreelyCleanShellable`, `IsPseudomanifold`, `EdgeLinkConnected`);
weakening theorem statements; touching locked weak `theorem2`/`theorem3` (beyond harmless
imports/shared-helper movement); adding `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; leaving
the repo broken; abandoning the clean route.

`taut_edgeLinkConnected` is the analogue of `taut_isPseudomanifold` at the edge-link level
(`IsPseudomanifold` bounds triangle counts but does not give edge-link connectivity); Codex is
selecting the smallest sufficient statement + proof route.

## Refined plan for `taut_edgeLinkConnected` (Codex consult `prime-elc-architect`, 2026-06-19)
CHECKED so far: `oppEdge_empty_of_full_edgeLinkConnected` (`0c79b53`), `oppEdge_empty_of_disjoint_eligible_remainder` (`2b087ba`, the edge LEMMA C, modulo `hOu : ¬O⊆u` + `hELMu`).
Codex corrections: a GLOBAL `removeTet_edgeLinkConnected` is FALSE (flip-present remainder = two
fillings pinched on the flip edge, disconnected until `e` reinserted); the survivor `hOu` is supplied
NOT by strengthening pair-selection but by an ORIENTATION lemma; the 5-non-opposite-edge argument is
CONFIRMED sound.

Lemma stack (all in `Theorem3Clean.lean`; `PrimeStep` machinery imported). **CHECKED so far:**
1.✓ geometry helpers `eligible_oppEdge_geom`, `oppEdge_eq_flip` (`f82ce8c`).
2.✓ `eligible_pair_oriented_opp_avoidance` (`f82ce8c`) — survivor gap closed (`¬O_e⊆u ∨ ¬O_u⊆e`; both ⟹ e=u).
3.✓ `edgeLinkCompat_nonOpp_of_exposed_face` (`5b007e7`) — 5 non-opposite edges' RIGHT disjunct.
4.✓ `oppEdge_empty_of_disjoint_eligible_remainder` WEAKENED to single-edge `ConnOn` at `O_e` (this commit):
   hypothesis is now `ConnOn (edgeLinkGraph (removeTet M u) O_e) (edgeLinkVerts (removeTet M u) O_e)`
   (not full `EdgeLinkConnected (removeTet M u)`), so a flip-present `u` is fine (its pinch is only at
   `u`'s flip edge, and `O_e ≠` that since `¬O_e⊆u`).
**CASE-1 SOURCING — ALL CHECKED** (Codex `case1-elc-architect`):
5.✓ `removeTet_edgeLinkConnected_noFlip` (`41b5066`): IH → `EdgeLinkConnected (removeTet M e)` (¬Flip e).
6.✓ `flipPresent_removeTet_connOn_at_nonflip_edge` + helper `connOn_oppEdge_of_subset_local` (`80e6d95`):
   `ConnOn` at `O_e` in `removeTet M u` when `u` flip-present (side-local; `O_e` in one side).
7.✓ `removeTet_connOn_oppEdge_of_disjoint_eligible` (`bc7c554`): dispatcher, case on `FlipEdgePresent u`.
8.✓ `prime_edgeLinkConnected_case1` (`41b5066`): assembles `edgeLinkConnected_insert` over `removeTet M e`
   (hELMe from (5); opp edge via weakened (4) + dispatcher (7); 5 others via (3)). Takes hELMe + hConnOu.

**REMAINING for `taut_edgeLinkConnected` (Codex `finish-elc-architect`, PASS — full plan):**
Patch order: (B) `edgeLinkConnected_insert_flipBridge` + helpers → (case2) `prime_edgeLinkConnected_case2`
→ (A) `prime_edgeLinkConnected` → `deg3_edgeLinkConnected` → `base_edgeLinkConnected` → `taut_edgeLinkConnected`.
A. prime assembly: `aleph_disjoint_eligible_pair` → `(e₀,u₀)`; orientation lemma → ORIENT to `(r,w)` with
   `¬O_r⊆w` (swap if it returns the `u`-form); split on `FlipEdgePresent r₃ r₄`: ¬Flip = (5)+(7)+(8);
   Flip = case2.
B. **case2 bridge** `edgeLinkConnected_insert_flipBridge`: NOT `edgeLinkConnected_insert` (the pinched
   `removeTet M e` isn't edge-connected). Direct proof from side facts (`flipEdgePresent_side_sets/_algebra`):
   seam edge `cd=f₃∩f₄` — side-IH connects A-apexes to the `f₃\cd` apex, B-apexes to `f₄\cd`, inserted `e`
   joins those two; non-seam edges — link lives in one side (a link spans both sides only if edge ⊆ A∩B=cd).
   Helpers: `edgeLinkVerts_union_side_local_or_seam` (both-sides ⟹ edge=cd; the HARD-STOP dichotomy),
   `edgeLinkConnected_union_side_local`, `side_face_apex_mem_edgeLinkVerts` (seam apex from a side f₃/f₄ tet,
   rederive via `taut_isPseudomanifold`+`faceCount_eq_one_of_boundary` as in `flipEdgePresent_side_data`).
   NO new topological theorem needed.
C. `deg3_edgeLinkConnected`: mirror `deg3_isPM` — ONE star tet `starTet σ v`, non-star side IH, `M.support =
   insert (starTet σ v) R.support`, `edgeLinkConnected_insert` using star helc from `cleanGlueStep_star_of_remainder`.
   base = `edgeLinkConnected_singleton` (mirror `base_free_clean`: `M.support = {vertsOf σ}`).
D. `taut_edgeLinkConnected` = `Nat.strong_induction_on (nrm M)` clone of `taut_isPseudomanifold`.
NEXT BOUNDED TARGET: `edgeLinkConnected_insert_flipBridge` + helpers. Hard-stop if the side-local/seam
dichotomy (`edge with tets/apexes on both sides ⇒ edge = f₃∩f₄`) cannot be proved.
Then: `taut_edgeLinkConnected` ⟹ `hELM` ⟹ `hOppEmpty` case-1 ⟹ `cleanGlueStep_eligible` ⟹ `prime_step_clean`
case-1. Still open: `prime_step_clean` case-2 (clean RelShelling bridge, Ball.lean:281) — DEFERRED;
`theorem3_clean` = `theorem3_core_clean base_free_clean deg3_step_clean prime_step_clean`; `theorem2_clean`.

## AlephProver record
`oppEdge_empty_of_full_edgeLinkConnected`: FAILED-ALEPHPROVER on 2 attempts (IDs `3d0c22ca`,
`063af707`) — both server-side "Validation Error: couldn't build your Lean project" (40s/32s, cost
0.00), NOT counterexamples; local `lake build` green. Proof then completed manually. See
`notes/aleph-requests.md`.
