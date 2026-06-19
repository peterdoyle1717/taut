# THEOREM4-START — baton for the next session

> Written at the end of a saturated (99% context) session, immediately before Theorem 4.
> The next session should **audit Theorem 4 first** — do not assume any Theorem-4 status.

## Current checkpoint (pushed)
- **Branch:** `claude/clean-shelling`
- **Remote:** https://github.com/peterdoyle1717/taut (public; `origin`)
- **HEAD at handoff:** `ba73b41` (`Add MIT license`); the Lean milestones are at `202678b` / `43faa7d`.
- **Build / grep / axioms (as of the pushed checkpoint):** `cd lean && lake build` green (8272 jobs);
  grep `sorry/admit/axiom/native_decide/unsafe` over `lean/Taut` → ZERO; all endpoints below
  `#print axioms = [propext, Classical.choice, Quot.sound]`.

## Milestones CHECKED (verified this session; nothing below is a Theorem-4 claim)
- `Zvol_add_of_almost_disjoint_full` (`lean/Taut/Theorem1.lean`) — Theorem 1 part 1 at the paper
  hypothesis `(A∩B).card ≤ n+1`, no `p,q` (fresh-vertex WLOG, `[Infinite V]`).
- `IsTaut.splits_full` (`lean/Taut/Splitting.lean`) — Theorem 1 part 2 (n ≥ 2), no `p,q`.
- `theorem2_clean` (`IsCleanBall M.support σ`) and `theorem3_clean` (`FreelyCleanShellable M.support σ`)
  (`lean/Taut/Theorem3Clean.lean`) — the weak→clean migration, COMPLETE.
- Weak `theorem2`/`theorem3` (`PrimeStep.lean`) unchanged + intact.
- AlephProver is currently **unusable for this repo** (server-side mathlib-v4.29.1 build-validation
  failure; works for no-mathlib toys). See `notes/aleph-requests.md`. (Relevant to the audit's
  "is AlephProver relevant" question — expect NO until the server-side mathlib build is fixed.)

## Next target: Theorem 4 — STATUS UNKNOWN, AUDIT FIRST
Paper: Theorem 4 of "Taut fillings" is the `S³ ⊄ B³` result (`taut/taut.tex`, label `th4`/around the
Th2–Th4 block). **Do not assume it is started, stubbed, or absent — audit.**

### THEOREM 4 AUDIT TASK (next session — do NOT edit Lean files; audit only)
```
cd /Users/doyle/Dropbox/taut
git status --short
git pull --ff-only
git grep -n "Theorem 4\|theorem4\|theorem_4\|Corollary\|corollary\|Zvol\|IsTaut\|splits\|clean" lean TEAMWORK.md STATUS.md THEOREM4-START.md
```
Find: (1) the exact paper statement of Theorem 4 (read `taut/taut.tex` — search `th4` / `S^3` / `B^3`);
(2) closest existing Lean theorem(s); (3) whether any `theorem4` endpoint already exists; (4) its
dependencies on Theorem 1 / `theorem2_clean` / `theorem3_clean` / Corollary 1; (5) the exact missing
Lean statement, if any.
Report only:
```
THEOREM 4 AUDIT
- paper statement:
- current Lean endpoint candidates:
- checked dependencies:
- missing endpoint:
- likely proof route:
- first bounded implementation target:
- whether Codex architect consult is needed:
- whether AlephProver is relevant:
```

## Other open (per STATUS.md / TEAMWORK.md)
Corollary 1 (ℚ-fillings, via clearing denominators from Theorem 1). Theorem 4 (S³⊄B³).
(The combinatorial Theorems 1/2/3 are done; Theorem 1 in full, Theorems 2/3 in both weak and clean routes.)
