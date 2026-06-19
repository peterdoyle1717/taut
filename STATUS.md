# STATUS — clean-shelling migration COMPLETE

## Branch / commit
- Branch `claude/clean-shelling`, HEAD `43faa7d`.
- Full `lake build` green (8272 jobs); grep `sorry/admit/axiom/native_decide/unsafe` over `lean/Taut` → ZERO.

## ✅ DONE: weak→clean migration is COMPLETE (all std-3 axioms: propext, Classical.choice, Quot.sound)
- **`theorem2_clean`** (`43faa7d`): taut filling of a 2-sphere ⟹ `IsCleanBall M.support σ`.
- **`theorem3_clean`** (`43faa7d`): taut filling ⟹ `FreelyCleanShellable M.support σ`.
  = `theorem3_core_clean base_free_clean deg3_step_clean prime_step_clean …` — all three clean steps discharged.
- Supporting (all CHECKED, std-3): `base_free_clean`, `deg3_step_clean`, `prime_step_clean` (`e27ba91`),
  the case-2 clean-shelling bridge (`CleanRelShellingFrom`, `cleanGlueStep_crossSeam_head`,
  `CleanShellFrom_prepend_crossSeam`, `freelyCleanShellable_cleanRelShelling_over_bridge`,
  `exists_clean_shelling_prime_case1/2`), and the whole `taut_edgeLinkConnected` stack (`ac1c0bb`).
- **Weak `theorem2`/`theorem3` (PrimeStep.lean) UNCHANGED and intact** (still sorry-free, std-3).
  Both routes now coexist; `theorem2_clean`/`theorem3_clean` are the faithful-stickerball upgrade.

## AlephProver (Track B) — diagnosis status
AlephProver/CLI/auth WORK: a no-mathlib toy (`ba066fc4`) PASSED validation and ran proof search
(cost 0.39). But EVERY mathlib submission failed at the server build-validation stage ("couldn't
build your Lean project", ~20–120s, cost 0.00): v4.29.1, v4.31.0 (despite a confirmed-live prebuilt
cache fetched locally), v4.32.0, a minimal 4-file mathlib project, and a require-but-don't-import
project. So it is NOT login/key, NOT our code (local build green), NOT `packagesDir` (portable copy
failed too), NOT project size, NOT a single bad version. It worked on 2026-06-14 (`db3e30a`) on the
identical pins. Classification: **AlephProver works but its mathlib build environment fails for our
submissions** — leaning SERVICE-BROKEN or PROJECT-PACKAGING-WRONG (a doc-confirmed known-good mathlib
submission form was not located). MOOT for now: the clean migration closed manually; AlephProver was a
try-first accelerator, not needed. Full record: `notes/aleph-requests.md`.

## Open (other theorems, not the clean migration)
- Corollary 1 (ℚ-fillings), |A∩B| ≤ 1 Theorem-1 cases, Theorem 4 (flag complex) — per TEAMWORK.md.

## OBJECTION → RESOLVED (2026-06-19): Theorem-4 sub-target 3 excluded the wrong edge
Codex's sub-target-3 PLAN (`notes/codex-consults/2026-06-19-1901-g1-theorem4-sub345-*`) gives
`edge_witness_ne_removed_of_not_flipEdge` + `hasEmptyK3/K4_removeTet_of_avoids_flipEdge` whose
exclusion / `havoid` is **`x ≠ f₃ ∩ f₄`** with `{f₃,f₄} = exposedFaces M e`. **Claim: this excludes
the wrong edge and the lemma is false as stated.** Evidence (all from code):
- `sharedFaces M e = tetFaces e ∩ (bdry M).support` (boundary faces); `exposedFaces M e = tetFaces e \
  sharedFaces` = INTERIOR faces ("become new boundary faces", `Theorem2.lean:87-91`).
- Boundary flip `σe = (σ \ sharedFaces M e) ∪ exposedFaces M e` (`FlipGeom.lean:9,28`): the boundary
  LOSES the sharedFaces (loses edge `sharedFaces`∩ = "ab") and GAINS the exposedFaces (gains
  `exposedFaces`∩ = `f₃∩f₄` = "cd").
- `cd = f₃∩f₄ ⊆` an exposed (interior) face `⊆` a neighbouring tet `≠ e` ⇒ **cd SURVIVES** `removeTet`.
- `ab = sharedFaces`∩ is private to `e` (its two faces are boundary ⇒ only on `e`; `EdgeLinkConnected`
  — which we have for taut `M` via `taut_edgeLinkConnected` — forces `e` to be the only tet at `ab`)
  ⇒ **ab DISAPPEARS**. Paper: "the only edge that disappears from τ is the edge that gets flipped" = ab.
- Internal inconsistency: Codex's OWN counting lemma `disjoint_eligible_family_hit_two_faces_card_le_two`
  keys on `sharedFaces`; sub-target 3 keys on `exposedFaces`. They must be the same structure.
- Counterexample to the lemma as stated: `x = ab` satisfies `x ≠ f₃∩f₄` (= cd) but has **no** witness
  tet `≠ e`, contradicting the conclusion `∃ t ∈ M.support, t ≠ e ∧ x ⊆ t`.
**Proposed correction:** exclude `(sharedFaces M e)`'s intersection ("ab"), not `exposedFaces`'s.
Restate via the shared-face pair `{g₃,g₄} = sharedFaces M e` and exclude `g₃ ∩ g₄`.
**RESOLVED:** the focused follow-up (`…-1910-g1-theorem4-sub3-objection-*`) — Codex verdict WARN,
"Claude is right." Corrected to `edge_witness_ne_removed_of_not_sharedEdge` + `hasEmptyK3/K4_removeTet_of_avoids_sharedEdge`
(exclude `g₃ ∩ g₄`, `{g₃,g₄} = sharedFaces M e`); downstream counting unaffected (already keys on
`sharedFaces`). Implementing the corrected sub-target 3.
