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

## Authorization gate (DO NOT proceed without it)
- **`taut_edgeLinkConnected` is a NEW topology theorem** ("every taut filling of a 2-sphere is
  edge-link connected"). Codex (architect) HARD-STOPPED on it; `IsPseudomanifold` is insufficient
  (it bounds triangle counts but does not give edge-link connectivity). It is the analogue of
  `taut_isPseudomanifold` at the edge-link level and is expected to be a substantial induction.
- **It is NOT authorized yet.** Per protocol, launching it is a design decision (substantial new
  topology development) requiring **Codex architecture + user authorization**.
- **No further clean-migration work should proceed without Codex architecture and user
  authorization.** In particular: do not start `taut_edgeLinkConnected`, do not open
  `prime_step_clean` case-2 (the clean RelShelling bridge), and do not touch the locked weak
  `theorem2`/`theorem3`, without sign-off.

## Remaining chain to `theorem3_clean` / `theorem2_clean`
1. `taut_edgeLinkConnected` (NEW, unauthorized) ⟹ discharges `hELM` ⟹ `hOppEmpty` case-1 closes via `oppEdge_empty_of_full_edgeLinkConnected` + `cleanGlueStep_eligible`.
2. `prime_step_clean` case-2: clean RelShelling bridge (a `CleanShellFrom`-based analogue of `FreelyShellable.relShelling_over_insert_boundary_face`, Ball.lean:281) — DEFERRED.
3. `theorem3_clean` = `theorem3_core_clean base_free_clean deg3_step_clean prime_step_clean`; `theorem2_clean` downstream.

## AlephProver record
`oppEdge_empty_of_full_edgeLinkConnected`: FAILED-ALEPHPROVER on 2 attempts (IDs `3d0c22ca`,
`063af707`) — both server-side "Validation Error: couldn't build your Lean project" (40s/32s, cost
0.00), NOT counterexamples; local `lake build` green. Proof then completed manually. See
`notes/aleph-requests.md`.
