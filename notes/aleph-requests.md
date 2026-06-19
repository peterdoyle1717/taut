# AlephProver requests (taut fillings)

Poll a request:  `eval "$(grep -E '^export (ALEPH_API_KEY|PROVER_API_KEY|PROVER_API_URL|ALEPH_API_URL)=' ~/.zshrc)" && uvx alephprover status <REQUEST_ID>`
(or the View URL). On success it returns a `git apply` patch filling the target's `sorry`.
Targets live in `lean/Taut/FlipGeom.lean` (scratch, sorried, uncommitted).

## 2026-06-15 — case-1 flip geometry

- **isSphere2_flipBoundary_of_eligible** (the crux: bistellar 2-2 flip preserves the
  2-sphere; needs `¬FlipEdgePresent`).
  - Request ID: `742c6fcd-fe81-4d94-bfe2-1d5410d0ee8b`
  - URL: https://alephprover.logicalintelligence.com/requests/742c6fcd-fe81-4d94-bfe2-1d5410d0ee8b
  - Budget: time 900 min, cost 500.
  - Submitted 2026-06-15. Status: RUNNING (--no-poll).

Not yet submitted (more tractable; may prove by hand or submit later):
- `glueStep_flipBoundary_of_eligible` (pure set algebra: `e ∩ σe = exposedFaces`,
  `σ = σe △ tetFaces e`).
- `isTaut_removeTet_of_eligible` (removing an eligible tet preserves tautness).

## 2026-06-18 — PM-carry (taut_isPseudomanifold)

Added the standalone "every taut filling of a 2-sphere is a pseudomanifold"
strong induction to `lean/Taut/PrimeStep.lean` (decls: `base_isPM`, `prime_isPM`,
`deg3_clean_glue_of_remainder`, `deg3_isPM`, `taut_isPseudomanifold`).

No AlephProver requests were needed: every obligation closed directly by mirroring
the existing free-shelling induction (`base_free`/`deg3_step_free`/`prime_step_free`)
and reusing the banked supporting lemmas (`removeTet_isPseudomanifold`,
`faceCount_removeTet_sharedFace_eq_zero`, `isPseudomanifold_insert`,
`faceCount_eq_one_of_boundary`, `unitOn_flipBoundary_of_eligible`,
`aleph_disjoint_eligible_pair`, the `degree3_cut_setup`/`star_filter_support_singleton`
machinery). The clean-glue leaves (shared faces vanish on removal; exposed/link
faces are unit boundary faces in exactly one tet) were small Finset/cardinality
arguments. `#print axioms taut_isPseudomanifold` = `[propext, Classical.choice,
Quot.sound]` (no `sorryAx`). Full `lake build` green, 8271 jobs.

## 2026-06-18 — H1 (degree3_hanchor) — NO submissions (architectural blocker)

Target: close `degree3_hanchor` sorry in `lean/Taut/Theorem3.lean` using
`taut_isPseudomanifold` (PrimeStep.lean).

BLOCKER (demonstrated, not hypothesized): `taut_isPseudomanifold` lives in
`PrimeStep.lean`, which `import`s `Taut.Theorem3`. So `Theorem3.lean` cannot
import `PrimeStep`. Lean confirms:
    error: build cycle detected: Taut.PrimeStep <-> Taut.Theorem3
    error: Taut/Theorem3.lean: bad import 'Taut.PrimeStep'
The cycle is real: `taut_isPseudomanifold`'s induction (`deg3_isPM`) uses
`degree3_apex_notMem_{right,left}_verts_of_{left,right}_star`, both DEFINED in
Theorem3.lean. No PM-producing lemma exists in Theorem3's import closure
(Theorem2Aleph/Theorem23/Degree3/OrientedBridge/Eligible/Theorem2/...).

No AlephProver request was submitted: the 5 set-algebra leaves of the body
(hinter, hKt0, newBdry, v in K-face, reconstruction) are all sound and
AlephProver-friendly, but they are blocked behind the `IsPseudomanifold
MR.support` input, which cannot be produced inside Theorem3 without an
architecture change (relocating the PM induction, or threading the PM property
through theorem3_core/deg3_step_free — both explicitly out of scope).

Scaffold validated: with a temporary `import Taut.Stickerball` + a stub
`have hPMR : IsPseudomanifold MR.support := by sorry`, the rest of the body
compiles green, leaving exactly the 5 leaves above. Reverted; file is clean.

## 2026-06-19 — oppEdge_empty_of_full_edgeLinkConnected (hOppEmpty case-1 reduction)

Target: `oppEdge_empty_of_full_edgeLinkConnected` in `lean/Taut/Theorem3Clean.lean` — the
Codex-ruled reduction lemma (consumes `hELM : EdgeLinkConnected M.support`, concludes
`edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅`). Local goal exposed = the bare
conclusion (transient `sorry` as target).

Exact command (from `lean/`, keys eval'd from `~/.zshrc`):
`uvx alephprover prove Taut/Theorem3Clean.lean oppEdge_empty_of_full_edgeLinkConnected --no-poll --hints "<Codex route>"`

- **Attempt 1** — Request `3d0c22ca-471b-447d-8447-23dae77bedf3`:
  **FAILED-ALEPHPROVER** (NOT a counterexample). `Status: failed` — *"Validation Error | We
  couldn't build your Lean project. Make sure `lake build` succeeds and try again."* Failed at the
  `prove` stage in 40s, cost 0.00; clone/prep completed. This is a **server-side build-validation
  failure**, not a math result: locally `lake build` is GREEN (8272 jobs) with the target `sorry`
  present, and the archive ("27 files, 0.2 MB") ≈ all 24 project `.lean` + lakefile + manifest +
  toolchain (complete). artifact prover_result.zip id=77524fce-89bb-4a27-963b-e37e33fc5b6a.
- **Attempt 2** — Request `063af707-397a-4ca6-a428-f5b8ff91f406` (same command/archive):
  **FAILED-ALEPHPROVER**, identical *Validation Error* ("We couldn't build your Lean project"),
  failed at `prove`/build stage in 32s, cost 0.00. Two consistent failures ⟹ server-side
  build-validation issue for this project, NOT transient and NOT a counterexample.
  artifact prover_result.zip id=4f55038d-04b0-4920-ac53-a7dae3e6e8e0.

**Verdict: FAILED-ALEPHPROVER for this target** (AlephProver cannot build the project server-side;
local `lake build` is green). Per protocol, resuming the bounded manual/Codex route from the exposed
goal. (If the AlephProver build-validation is fixed later, the same target can be resubmitted.)

## 2026-06-19 — AlephProver SERVER-SIDE UNAVAILABLE (diagnosed; corrects the packagesDir guess)

Four submissions all FAILED identically — `Validation Error | We couldn't build your Lean project`,
failing at the `prove`/build stage in 32-40s, cost 0.00, BEFORE any proving:
- `3d0c22ca`, `063af707` (oppEdge_empty_of_full_edgeLinkConnected, real project).
- `cc4d6562` (portable smoke copy: absolute `packagesDir` removed → default `.lake/packages`).
- `96a16e7e` (MINIMAL 4-file project: just `require mathlib @ v4.29.1` + one `theorem … := by sorry`).

CONCLUSION (evidence-based): the failure is **AlephProver server-side**, building a `mathlib @ v4.29.1`
project — NOT our code (local `lake build` green, 8272 jobs), NOT login/key (all 4 keys SET, submissions
accepted with Request IDs), NOT the absolute `packagesDir` (portable copy failed identically — my earlier
high-confidence packagesDir claim was WRONG), NOT project size (a minimal 4-file mathlib project failed
the same). Toolchain + mathlib pin are IDENTICAL to `db3e30a` (2026-06-14) when AlephProver DID work and
banked aleph_base/aleph_deg3_split/M25b — so AlephProver's server environment for `mathlib v4.29.1`
changed in the intervening 5 days (most likely: the prebuilt mathlib cache for our pinned commit is no
longer fetchable on their end, so their `lake build` can't produce mathlib within the ~35s validation
window). The 1.4 KB result artifact for the minimal run confirms the server never built mathlib.

NOT fixable from this repo without changing the mathlib version (risky — would ripple through all proofs).
Per protocol: record FAILED-ALEPHPROVER and proceed manually until AlephProver's mathlib-v4.29.1 build
is restored on their side.
