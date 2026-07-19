# Taut fillings — the two stalled frontier sessions, consolidated

Distilled 2026-07-19 from the two most recent taut-fillings working sessions. Both did their
work 2026-06-17/18, both stalled, and both transcript files were last touched 2026-07-18 by
brief revival attempts that produced no new work:

- **Session A** — `~/.claude/projects/-Users-doyle-Dropbox-taut/2f808446-fdb7-450a-81dc-51bb92c3969e.jsonl`,
  continuation of `bea0ff72-…` (its opening compact summary is the record of that predecessor's
  work). The pseudomanifold-carry frontier ("M-PM4"). Stalled 2026-06-18 on repeated
  "prompt too long" errors with its milestone commit staged but never run.
- **Session B** — `…-taut--claude-worktrees-musing-maxwell-2f386b/f8b422b9-0cec-4695-80b5-b881b0a5344b.jsonl`,
  in the `musing-maxwell-2f386b` worktree. The shellability-definition session. Stalled at a
  design fork awaiting Peter's call.

Terms used below: *PM* = `IsPseudomanifold` ("every triangle lies in ≤ 2 tets of the complex").
*Weak `GlueStep`* = the then-current shelling step: shared-boundary-face count ∈ {1,2} plus a
boundary symmetric-difference update, nothing else. *Case 2* = removing an eligible tet leaves a
filling of two spheres joined along an edge. *H1* = the `degree3_hanchor` sorry, *H2* = the
`flipEdgePresent_side_bridge` sorry — the two geometry holes of the weak-route Theorems 2/3.

## What Session A established

- The weak `GlueStep` has a faithfulness defect: it admits gluings that are not simplicial-ball
  steps (e.g. a triangle re-exposed into a third tet). The chosen repair was to carry PM through
  the whole induction alongside `FreelyShellable`.
- Its codex G1 consult concluded **both** holes need PM: H1 needs the unique anchor tet
  containing the cap (`faceCount = 1`, from PM + parity), and H2 needs bridge-tet uniqueness
  (`faceCount_eq_one_of_boundary` for `IsPseudomanifold M₂.support`). "PM is the master key."
- PM needs no `Good` single-or-split disjunction: PM is union-closed across the case-2 edge cut
  (no triangle crosses a 2-vertex cut), so the plain IH applies to each split piece and
  Lemma A glues them.
- It built the PM engine sorry-free, std-3 axioms: Lemma A `isPseudomanifold_union_of_sideSep`
  (StickerballRuleouts.lean), Lemma B `removeTet_isPseudomanifold`, Lemma C
  `faceCount_removeTet_sharedFace_eq_zero` (PrimeStep.lean).
- It found the default `lake build` had been building only through `Theorem3` — FlipGeom,
  PrimeStep, Pseudomanifold, Stickerball were orphaned. Wiring them into `Taut.lean` surfaced
  both sorries (8270 jobs, exactly 2).
- End state: 10 files / 18,513 insertions staged for the M-PM4 bank; the commit never ran. Its
  forward plan: thread `FreelyShellable ∧ IsPseudomanifold` through `theorem3_core`, then close
  H1 (PM anchor uniqueness) and H2 (a six-lemma ambient-transport recipe).

## What Session B established

Resuming in the worktree, it first discovered the real frontier was **uncommitted in the main
tree** (Session A's files), that there were two sorries rather than the remembered one, and that
the `Good` invariant had been deliberately abandoned in favor of PM + Lemma A.

Peter then asked the architecture question: should the induction carry *normality* (connected
links), as the old `taut1100.tex` proof did, in addition to PM? The answer developed in stages:

1. **Union-closure asymmetry.** Under the case-2 split: PM and vertex-link-connectedness are
   union-closed (vertex links wedge at a shared point), but edge-link-connectedness is *false*
   for the split object — the shared edge's link is two disjoint pieces. Carrying edge-link
   therefore forces the `Good` disjunction; carrying PM does not.
2. **The correction.** Peter pushed back twice ("we went far beyond this"; "look for a
   discussion of why we need to know that the link of an edge is connected"). The settled r2
   consult (`notes/codex-consults/2026-06-17-g1-pm-proof-r2-output.txt`, tracked) lists
   **three** obstructions to re-gluing the eligible tet: (A) doubled tet, (B) interior triangle,
   and (C) a rogue interior edge whose link disconnects when the tet returns — and (C) is
   invisible to PM and to the weak `GlueStep`. The session retracted its own earlier position
   that edge-link was "just output."
3. **Peter's principle, which closed the question.** Shellable must mean each prefix is a
   simplicial 3-ball; a 3-ball is clean; so a shelling definition that admits unclean complexes
   is wrong. The weak `FreelyShellable` (the M-FS2 "purely combinatorial certificate"
   simplification) was therefore not a definition of shellability at all — the definition
   itself was the bug.

Its codex consult on the fix recommended: keep the weak machinery as renamed bookkeeping
(`Boundary*`), make the public ball the conjunction
`IsStickerball = FreelyShellable ∧ IsPseudomanifold ∧ EdgeLinkConnected`, and carry that through
the induction; it argued against rewriting `GlueStep` first (both options bottom out in the same
PM + edge-link induction). It also confirmed the case-2 asymmetry is real — the split object
must *not* be required to be edge-link-connected (only the reglued single-sphere filling is) —
and that no separate vertex-link invariant is needed in the prime two-face re-glue (vertex
pathology lives only in the degree-3 branch). The session wrote `SHELLING-CONSULT.md` for an
outside opinion (now preserved untracked at `cruft-quarantine/20260628-181815/`), held all
refactoring, and stopped at the fork: (a) strengthen the glue step itself vs (b) keep the weak
step and carry the clean conjunction.

## Where they agree

- The weak-`GlueStep` certificate alone is not the faithful theorem; PM must be carried, and
  the engine for that (Lemmas A/B/C) is correct and reusable.
- `Good` is unnecessary for PM: union-closure across the case-2 cut does the work.
- The two geometry holes H1/H2 are the real remaining content of the weak-route shellability
  proof.

## Where they conflict

1. **Edge-link connectedness — the load-bearing conflict.** Session A's architecture (its
   StickerballRuleouts header, quoted in B) held edge-link "never needs to be a named
   invariant"; its target was weak-shellable + PM. Session B established the opposite: without
   ruling out obstruction (C), the certified object need not be a manifold, and the weak notion
   is the wrong definition. B supersedes A here.
2. **Whether H2 needs PM.** A recorded "both holes need PM" (bridge-tet uniqueness for M₂);
   B's reading was that H2 is independent of PM — it needs side-cleanliness / ambient transport
   from the card-2 cut, and its consult said PM "is not enough" for H2. Not formally
   contradictory (necessity vs sufficiency), but the two diagnoses of H2 point in different
   directions.
3. **Vertex-link.** Within B only: first floated as a cheap invariant to carry, then dropped on
   r2's grounds (no separate vertex obstruction in the prime re-glue). Resolved inside B.

## What was open then — and where it stands now (main `39a9849`, checked 2026-07-19)

- **The (a)/(b) fork → resolved by the clean-shelling migration**, in the direction of a genuine
  clean shelling notion: Phase 1 clean predicate hierarchy `IsClean3Complex / IsStickerball /
  IsAnyrootedStickerball` (`47cd9a3`), `CleanShelling.lean` (`CleanRelShellingFrom`,
  `cleanGlueStep_crossSeam_head`, …), and the carried `taut_edgeLinkConnected` stack. The weak
  machinery was ultimately **deleted**, not kept-renamed (`69705ab`…`1d08558`; `eeddc0a` keeps
  only a documented `GlueStep` remnant) — stronger than B's codex recommendation.
- **H1/H2 → moot in the clean route.** `theorem3_clean` is fully discharged
  (`base_free_clean` / `deg3_step_clean` / `prime_step_clean`, per STATUS.md), and
  `grep sorry|admit|native_decide|axiom` over `lean/Taut` returns zero today.
- **Beyond both sessions' horizon:** `SimplicialChain` was later removed as an *endpoint*
  hypothesis via the Route-Y hens-and-baskets bridge `taut_filling_is_simplicialChain`
  (M-SB1…M-SB8, `a8f4566`; public endpoints now in `Theorem3Clean.lean:3462/3636`). Both
  sessions treated simpliciality as a standing hypothesis; neither anticipated this. Internally
  `taut_isPseudomanifold` still takes `SimplicialChain M` (`PrimeStep.lean:1646`) — an
  induction invariant, no longer a public hypothesis.
- **Loose ends still open today:**
  - PR #1 (`clean-anyrooted-stickerball` → `claude/clean-shelling`) is OPEN on GitHub while
    `main` already contains the branch; merging or closing it is housekeeping.
  - The `musing-maxwell-2f386b` worktree still sits at `83fedb2` with 9 uncommitted files —
    Session B's stale copies of the June frontier, superseded by main. Candidate for removal.
  - `STATUS.md` is a `43faa7d`-era snapshot and stale on every open item it lists: the weak
    routes were since deleted; `Theorem4.lean` landed (`fc1b394`); Corollary 1 is COMPLETE
    (`bcb3401` M-COR1-7, `IsQTaut.splits_full` / `Qvol_add_of_almost_disjoint_full` in
    `Corollary1.lean`, zero sorries); and the |A∩B| ≤ 1 Theorem-1 cases are covered by the
    `_full` endpoints (`IsTaut.splits_full`, `Splitting.lean:510`;
    `Zvol_add_of_almost_disjoint_full`, `Theorem1.lean:430`). The baton commit `9f963f1`
    records "COROLLARY 1 COMPLETE; entire paper formalized."
  - The two b5a2428-era audit reports adjacent to these sessions
    (`notes/simpliciality-hypothesis-repair.md`, `notes/th1-CCXY-kmap-audit.md`, committed
    `39a9849`) stand: the CCXY audit found no gap (bad prose, not missing proof), and the
    simpliciality repair it scoped was subsequently carried out by the M-SB bridge.
