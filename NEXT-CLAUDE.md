# NEXT-CLAUDE — continuation baton (weak→clean migration)

Repo: `/Users/doyle/Dropbox/taut`  ·  Lean: `/Users/doyle/Dropbox/taut/lean`  ·  build: `cd lean && lake build`
Branch: `claude/clean-shelling`. Audit at every checkpoint:
`grep -RInE "\bsorry\b|\badmit\b|^axiom |[^a-zA-Z]axiom |native_decide|unsafe" lean/Taut lean/Taut.lean`.

## Current CHECKED state
- Weak `theorem2`/`theorem3` are LOCKED and still intact (sorry-free, standard-3 axioms, statements unchanged). Do not touch.
- `deg3_step_clean` is CHECKED at commit `6f6931f`.
- `cleanGlueStep_eligible` is CHECKED at commit `4f75b83`.
- `theorem3_core_clean` + `base_free_clean` are CHECKED (`935b2ca`).
- `prime_step_clean` is the ONLY blocker for `theorem3_clean`/`theorem2_clean`.
- case-1 of `prime_step_clean` is reduced to ONE missing edge-link emptiness fact `hOppEmpty`.
- case-2 still needs the clean RelShelling bridge — DO NOT work on case-2 yet.
- All clean lemmas live in `lean/Taut/Theorem3Clean.lean`. Whole `lean/Taut` is sorry-free; build green (8272 jobs).

## Next exact target
Prove the edge-link rule-out lemma needed for `hOppEmpty`. Use the EXACT local statement
`cleanGlueStep_eligible` consumes (read it in `Theorem3Clean.lean`), not a vague reformulation:
```
hOppEmpty : edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅
```
(`e` eligible, `exposedFaces M e = {f₃, f₄}`; `e \ (f₃ ∩ f₄)` is the flip-OPPOSITE edge = the two apexes.)

## Goal
Create + prove a named lemma, preferably near `cleanGlueStep_eligible`, with hypotheses exactly
matching the eligible-prime (case-1, `¬FlipEdgePresent`) context and conclusion exactly `hOppEmpty`
(or the smallest generalization Lean naturally wants).

## Suggested proof route
- Mirror `faceCount_removeTet_sharedFace_eq_zero` (PrimeStep.lean:1499 = LEMMA C) at the EDGE-LINK level.
- Use the disjoint eligible pair `u` (`aleph_disjoint_eligible_pair`).
- Use `not_edgeLinkConnected_of_subset` (Pseudomanifold.lean:280).
- Use the 2-sphere edge-link-cycle topology / `EdgeLinkConnected` machinery.
- Point: rule out a rogue remaining tetrahedron containing the flip-opposite edge.
- Do NOT use `IsPseudomanifold` alone — triangle counts cannot see this.
- Do NOT touch `deg3_step_clean` or the locked weak `theorem2`/`theorem3`.

## Deliverable
CHECKED: named `hOppEmpty` lemma accepted by Lean; `cleanGlueStep_eligible` consumed without
assuming `hOppEmpty` if possible (else prime case-1 advanced to the next exact obstruction);
`lake build` green; grep audit clean; `#print axioms` for the new lemma.

FAILED: exact minimal unproved Lean lemma statement; exact failed field / missing topological fact;
exact existing theorem that almost applies but fails, with the mismatch.

## Detail / context
Full state + the two prime-step obstructions: `TEAMWORK.md` (entries dated 2026-06-19). The case-2
obstruction (clean RelShelling bridge, a `CleanShellFrom`-based analogue of
`FreelyShellable.relShelling_over_insert_boundary_face`, Ball.lean:281) is documented but DEFERRED.
