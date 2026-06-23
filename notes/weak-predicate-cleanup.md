# Weak shelling-predicate cleanup

Branch `clean-anyrooted-stickerball`, audited from HEAD `ba499eb`.

Goal: delete/internalize the weak boundary-trace shelling predicates so they cannot be
read as public mathematical conclusions, without changing theorem content. Public
endpoints already conclude only the clean predicates (`IsStickerball`,
`IsAnyrootedStickerball`, `IsClean3Complex`, `IsCleanBall`); **no public endpoint
concludes weak `IsBall`/`FreelyShellable`** (verified by `git grep`).

## 1. Usage table (audited at `ba499eb`)

| Predicate / name | def | live code consumers | classification | disposition |
|---|---|---|---|---|
| **GlueStep** | Ball.lean:63 (structure) | `CleanGlueStep.weak : BoundaryGlueStep` (CleanShelling:50); ~12 `hweak : GlueStep` witnesses fed into clean glue (Theorem3Clean); `glueStep_flipBoundary_of_eligible` (FlipGeom), flip-side glue lemmas (PrimeStep), `degree3_cut_*_glue` (Theorem2Aleph) | **essential boundary bookkeeping** (live, underpins the clean route) | **KEEP**, document as weak; `BoundaryGlueStep` alias is the preferred name |
| **ShellFrom** | Ball.lean:70 (def) | only `IsShelling` (dead) + reassembly lemmas (dead) + `BoundaryShellFrom`/`toBoundaryShellFrom` (dead projection) | **dead** | **DELETE** |
| **IsShelling** | Ball.lean:77 (def) | only `IsBall`/`FreelyShellable` defs (dead), `IsShelling_append`/`_snoc` (dead), singleton proofs (dead), `BoundaryIsShelling` (dead) | **dead** | **DELETE** |
| **IsBall** | Ball.lean:83 (def) | `theorem2_core` (Theorem23, dead); `theorem2_modulo_prime_step`/`aleph_base`/`aleph_deg3_split`/`degree3_reassemble_from_cut_split`/`ball_reassemble_of_filter_support_singleton` (Theorem2Aleph weak-Thm-2 route, all dead); `IsBall.insert_of_glueStep`/`isBall_singleton` (dead); `BoundaryIsBall`/`toBoundaryIsBall` (dead) | **dead** (entire weak Theorem-2 route) | **DELETE** |
| **FreelyShellable** | Ball.lean:89 (def) | `degree3_hanchor`'s `hfreeR` param — **unused in its proof** (Theorem3:169); fed only by `hfreeR_weak`/`hfreeL_weak` via `toBoundaryFreelyShellable` (Theorem3Clean:781/925); `FreelyShellable.insert_of_glueStep`/`exists_shelling_insert_of_glueStep_old`/`freelyShellable_singleton` (dead); `BoundaryFreelyShellable` (dead) | **dead after dropping the vestigial param** | drop vestigial `degree3_hanchor` param, then **DELETE** |
| Ball-named weak lemmas | — | `IsBall.insert_of_glueStep`, `isBall_singleton`, `ball_reassemble_of_filter_support_singleton`, all reassembly (`ShellFrom_append/snoc/union_disjoint/erase_union_disjoint`, `GlueStep.union_disjoint/erase_union_disjoint`, `IsShelling_append/snoc`) | all **dead** (comment-only refs) | **DELETE** |
| `BoundaryGlueStep` (alias) | Ball.lean:297 | `CleanGlueStep.weak` (CleanShelling:50, 121, 569) | **live** | **KEEP** (preferred weak name) |
| `Boundary{ShellFrom,IsShelling,IsBall,FreelyShellable}` (aliases) | Ball.lean:300–308 | only their dead `toBoundary*` mirror lemmas | **dead** | **DELETE** |
| `toBoundary{ShellFrom,IsShelling,IsBall,FreelyShellable}`, `CleanGlueStep.toBoundaryGlueStep` | CleanShelling:121–151 | `toBoundaryFreelyShellable` feeds the vestigial param only; rest no consumer | **dead** (after param drop) | **DELETE** |

### Dead weak-`IsBall` Theorem-2 route (Theorem2Aleph + Theorem23), all verified `git grep`-dead:
`theorem2_modulo_prime_step` (only ref: self) → `theorem2_core` (only consumer: the former) → `aleph_base`, `aleph_deg3_split` (only consumer: the former) → `degree3_reassemble_from_cut_split` (only consumer: `aleph_deg3_split`) → `ball_reassemble_of_filter_support_singleton` (only consumer: `degree3_reassemble_from_cut_split`) → `IsBall.insert_of_glueStep`, `isBall_singleton`. The *shared* geometric `aleph_*` helpers (e.g. `aleph_base_support_nonempty`, `aleph_base_taut_support_card4_subset_verts`, `degree3_cut_*`) are **live** (used by the PM route `base_isPM`/`deg3_isPM` and the clean route) and are **retained**.

## 2. Disposition policy applied
- A (unused) → delete: `ShellFrom`, `IsShelling`, `IsBall`, `FreelyShellable` (+ their dead support and the dead weak-Thm-2 route).
- B (used only inside clean predicates) → keep + document: `GlueStep` / `BoundaryGlueStep`.
- C (weak predicate in a public statement) → N/A (no public endpoint concludes a weak predicate).
- D (compatibility alias) → `BoundaryGlueStep` retained as the weak name; other `Boundary*` aliases deleted as dead.

## 3–7. Results
(Filled in per stage below.)

### Stage A — drop vestigial param + dead boundary-projection scaffolding: DONE
- Dropped the unused `hfreeR : FreelyShellable` parameter from `degree3_hanchor` (Theorem3.lean);
  updated its two clean-route call sites (Theorem3Clean) and deleted the two now-dead
  `hfreeR_weak`/`hfreeL_weak` witness `have`s.
- Deleted the dead `FreelyShellable.insert_of_glueStep` / `…exists_shelling_insert_of_glueStep_old`
  (Theorem3.lean).
- Deleted the entire dead boundary-projection block (CleanShelling.lean): `CleanGlueStep.toBoundary`,
  `CleanShellFrom.toBoundaryShellFrom`, `IsCleanShelling.toBoundaryIsShelling`,
  `IsCleanBall.toBoundaryIsBall`, `FreelyCleanShellable.toBoundaryFreelyShellable`.
- After this, `FreelyShellable` (def) is orphaned (only `freelyShellable_singleton` /
  `BoundaryFreelyShellable`, both dead, remain) — removed with the Ball.lean weak family in Stage C.
- Build green (8274); ZERO sorry/admit.

### Stage B — delete weak `IsBall` Theorem-2 route: DONE
- Verified (`git grep`) the IsBall assemblers form a closed dead chain with **no** orphan cascade into
  the shared geometric helpers (`capped_cut_splits_unit`, `taut_splits_for_capped_cut`,
  `degree3_cut_*`, `star_filter_support_singleton`, `support_eq_insert_of_filter_support_singleton`,
  `starTet_card_of_degree3`, `vertsOf_tetFaces_eq`, … — all heavily used by the live PM/clean route, kept).
- Deleted from `Theorem2Aleph.lean`: `aleph_base`, `ball_reassemble_of_filter_support_singleton`,
  `degree3_reassemble_from_cut_split`, `aleph_deg3_split`, `theorem2_modulo_prime_step` (≈233 lines).
- Deleted the now-empty module **`Theorem23.lean`** (its only decl, `theorem2_core`, was dead);
  removed `import Taut.Theorem23` from `Taut.lean` and from `Theorem2Aleph.lean` (replaced with the two
  imports `Theorem23` provided: `Taut.Eligible`, `Taut.Pseudomanifold`); rewrote the Theorem2Aleph
  module docstring to describe its actual (shared-helper) content.
- After this, `IsBall`'s only non-comment refs are inside `Ball.lean` (its def + dead helpers) — removed
  in Stage C. Build green (8273); ZERO sorry/admit; endpoints std-3.

### Stage C — delete the Ball.lean weak family (`FreelyShellable`/`IsBall`/`IsShelling`/`ShellFrom` + reassembly + dead aliases); document `GlueStep`: PENDING
