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
- Corollary 1 (ℚ-fillings), |A∩B| ≤ 1 Theorem-1 cases, Theorem 4 (S³ ⊄ B³) — per TEAMWORK.md.
