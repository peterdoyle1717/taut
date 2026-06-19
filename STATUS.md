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

Lemma stack (place in `Theorem3Clean.lean` — import-driven: it reuses `oppEdge_empty_of_disjoint_eligible_remainder` which already lives there; `PrimeStep` machinery is imported):
1. geometry: `eligible_sharedFaces_eq_complement_exposed_pair`, `eligible_oppEdge_eq_sharedFaces_inter`
   (`sharedFaces e` = the two faces `e.erase p` (`p ∈ f₃∩f₄`), each ⊇ `O_e = e\(f₃∩f₄)`; `O_e ∈ edgesOf σ`).
2. **`eligible_pair_oriented_opp_avoidance`** (CRUX, provable — proof verified by hand): for a disjoint
   eligible pair `e,u`, `¬ O_e ⊆ u ∨ ¬ O_u ⊆ e`. Proof: if both, then `O_e`'s only σ-faces are `e`'s
   shared faces (disjoint from `u`'s) ⟹ `u`'s faces on `O_e` are exposed ⟹ `O_e = g₃∩g₄`; symmetrically
   `O_u = f₃∩f₄`; so `e = O_e ⊔ (f₃∩f₄) = (g₃∩g₄) ⊔ O_u = u`, contra `e≠u`. Uses `exists_two_faces`.
3. `edgeLinkCompat_nonOpp_of_exposed_face`: the 5 non-opposite edges' hcompat (RIGHT disjunct) via the
   exposed face's surviving neighbor tet (`exposed_triangle_unique_remaining_tet`).
4. `removeTet_edgeLinkConnected_noFlip`: IH → `EdgeLinkConnected (removeTet M e)` in the ¬FlipEdgePresent case.
5. `prime_edgeLinkConnected_case1`: assemble via `edgeLinkConnected_insert` (opp edge = LEFT disjunct via
   `oppEdge_empty_of_disjoint_eligible_remainder` + orientation lemma; 5 others via (3)).
6. **HARD STOP** before full `taut_edgeLinkConnected`: the flip-present case needs a SEPARATE bridge
   `prime_edgeLinkConnected_case2` / `edgeLinkConnected_insert_flipBridge` (not yet routed).
Then: `taut_edgeLinkConnected` ⟹ `hELM` ⟹ `hOppEmpty` case-1 ⟹ `cleanGlueStep_eligible` ⟹ `prime_step_clean`
case-1. Still open: `prime_step_clean` case-2 (clean RelShelling bridge, Ball.lean:281) — DEFERRED;
`theorem3_clean` = `theorem3_core_clean base_free_clean deg3_step_clean prime_step_clean`; `theorem2_clean`.

## AlephProver record
`oppEdge_empty_of_full_edgeLinkConnected`: FAILED-ALEPHPROVER on 2 attempts (IDs `3d0c22ca`,
`063af707`) — both server-side "Validation Error: couldn't build your Lean project" (40s/32s, cost
0.00), NOT counterexamples; local `lake build` green. Proof then completed manually. See
`notes/aleph-requests.md`.
