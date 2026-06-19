# STATUS — clean-shelling migration, hOppEmpty case-1

## Branch / commit
- Branch `claude/clean-shelling`, HEAD `9bbc633`.
- Working tree CLEAN (no uncommitted `.lean` changes). Full build green (8272 jobs). grep `sorry/admit/native_decide` over `lean/Taut` → ZERO.

## Checked facts (all std-3 axioms: propext, Classical.choice, Quot.sound)
- Weak `theorem2`/`theorem3` LOCKED and intact (`4e52d07`), statements unchanged.
- `deg3_step_clean` CHECKED (`6f6931f`).
- `cleanGlueStep_eligible` CHECKED (`4f75b83`) — proves all 6 `CleanGlueStep` fields for re-gluing the eligible tet `e`, **consuming** `hOppEmpty : edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅` as a hypothesis.
- `theorem3_core_clean` + `base_free_clean` CHECKED (`935b2ca`).
- `oppEdge_empty_of_flipEdgePresent` CHECKED (`9bbc633`) — the **`FlipEdgePresent` half** of `hOppEmpty`, via side-separation (`flipEdgePresent_side_sets`); purely combinatorial, no edge-link topology.
- `prime_step_clean` is the only blocker for `theorem3_clean`/`theorem2_clean`. Case-2 (clean RelShelling bridge) is DEFERRED, not under consideration here.

## Current target (proposed — for architect ruling)
`no_rogue_oppEdge_of_not_flipEdgePresent` / `hOppEmpty` case-1 (`¬ FlipEdgePresent`).
This is the half of `hOppEmpty` that `cleanGlueStep_eligible` actually needs in prime case-1 (the eligible tet is re-glued exactly when `¬ FlipEdgePresent`).

### Exact proposed lemma statement (TYPECHECKS — built with a transient `sorry`, since removed; tree clean)
```lean
private lemma no_rogue_oppEdge_of_not_flipEdgePresent {σ : Finset (Finset V)}
    {X M : Chain V} {e u f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (he : EligibleTet M e) (hu : EligibleTet M u)
    (hdisj : Disjoint (sharedFaces M e) (sharedFaces M u))
    (hPMu : IsPseudomanifold (removeTet M u).support)
    (hPMe : IsPseudomanifold (removeTet M e).support)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hNotFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅
```
Hypotheses are exactly `cleanGlueStep_eligible`'s, with `hOppEmpty` replaced by `hNotFlip`. Conclusion is character-identical to `hOppEmpty`. (Whether `hNotFlip`, or `u`/`hdisj`/`hPMu`, are actually needed is part of the architect's route ruling.)

### Exact Lean goal after the natural reduction
`edgeLinkVerts_eq_empty` (below) reduces the goal to:
```
⊢ ∀ t ∈ (removeTet M e).support, ¬ (e \ (f₃ ∩ f₄)) ⊆ t
```
i.e. after `intro t ht hsub` with `ht : t ∈ (removeTet M e).support`, `hsub : (e \ (f₃ ∩ f₄)) ⊆ t`, the goal is `False`.

## Facts found by targeted search (only the named edge-link items)
- `EdgeLinkConnected` EXISTS (def `Pseudomanifold.lean:105`): `∀ e, e.card = 2 → ConnOn (edgeLinkGraph τ e) (edgeLinkVerts τ e)` — i.e. the apex set is **connected**, nothing about degree/manifold.
- **No lemma found producing `EdgeLinkConnected` from taut / pseudomanifold / sphere data.** Only producers are: `EdgeLinkConnected` of a singleton (`:130`) and `insert`-preservation given a prior `EdgeLinkConnected` (`:196`). Neither yields it for a taut filling `M.support` or for `removeTet M e`.
- `not_edgeLinkConnected_of_subset` (`:280`) is a **refutation tool**, not an emptiness theorem: from two apexes `x,y ∈ edgeLinkVerts τ' e` that are NOT reachable in `edgeLinkGraph τ e`, it concludes `¬ EdgeLinkConnected τ'`. It consumes existing apexes; it cannot prove `edgeLinkVerts = ∅`.
- `edgeLinkVerts_eq_empty` (`:110`) is the emptiness closer: from `(∀ t ∈ τ, ¬ e ⊆ t)` it gives `edgeLinkVerts τ e = ∅`.
- No `degree`/`path`/`cycle`/"connected + degree≤2 ⟹ 1-manifold" helper exists in `Pseudomanifold.lean`.
- `taut_isPseudomanifold` (`PrimeStep.lean:1637`) DOES give `IsPseudomanifold M.support` from `IsSphere2`/taut/simplicial data (so triangle-count of the full `M` is derivable; `Pseudomanifold` ⟹ each triangle in ≤ 2 tets).

## Observed obstruction in the contradiction skeleton (for architect; not a ruling)
Assuming `t ∈ (removeTet M e).support`, `(e \ (f₃∩f₄)) ⊆ t`:
- The two boundary (shared) faces of `e` are the two triangles containing the opposite edge `e \ (f₃∩f₄)`; `faceCount_removeTet_sharedFace_eq_zero` (LEMMA C) rules out any rogue `t` that contains either of those two boundary faces (so the two flip-edge endpoints `c,d` are excluded from `t`).
- A "fresh" rogue `t = {opp-edge} ∪ {p,q}` with `p,q` outside the flip edge is NOT excluded by LEMMA C / `IsPseudomanifold`: triangle-count permits it. Excluding it appears to require connectivity (or 1-manifold structure) of the edge-link of the opposite edge — which is not among the available hypotheses (only `IsPseudomanifold`), and no library lemma produces it.

## Files edited / state
- `lean/Taut/Theorem3Clean.lean`: committed `9bbc633` (the `oppEdge_empty_of_flipEdgePresent` lemma + its 2 type-error fixes). A transient `no_rogue_...` stub was added to typecheck the statement and then removed — tree is clean.
- Build green (8272), grep ZERO, `oppEdge_empty_of_flipEdgePresent` axioms = std-3.

## AlephProver
Not yet attempted on `no_rogue_oppEdge_of_not_flipEdgePresent` (target not yet ruled by architect).
