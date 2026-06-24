# Endpoint terminology alignment — report

Branch `clean-anyrooted-stickerball`. Build green (`lake build`, 8273 jobs) at the terminology patch
described below. This report covers the steering instruction's eight items. **Read item 2 first: the
`SimplicialChain` removal is blocked and was not performed.**

## Summary: what was done / what is blocked

| Steering item | Status |
|---|---|
| 1. `IsStickerball` = monotone clean shelling | confirmed already true; docstring sharpened |
| 2. `IsRootedStickerball τ B t` predicate | **added** (`CleanShelling.lean`) |
| 3. `IsAnyrootStickerball` public name + docstring | **added** as abbrev alias of `IsAnyrootedStickerball` |
| 4. final theorem **without** `SimplicialChain` | **BLOCKED** — bridge is circular from existing machinery; not done, not faked |
| 5. CCXY / K-map confirmation note | done (`notes/th1-CCXY-kmap-audit.md`) |
| 6. validation greps + this report | done |

The terminology (items 1–3, 5) is a safe additive patch and is in. Item 4 cannot be completed by
composing existing ingredients; the precise obstruction is in item 2 below. No `sorry`/`admit` was
introduced and the public endpoint's hypotheses were **not** changed.

---

## 1. Final theorem statement (exact)

`lean/Taut/Theorem3Clean.lean:3433`, verbatim:

```lean
theorem taut_filling_is_anyrootedStickerball {σ : Finset (Finset V)} {X M : Chain V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : IsAnyrootedStickerball M.support σ :=
  ⟨⟨theorem2_clean hσ hU hXc hMX hT hS, hσ.nonempty⟩, theorem3_clean hσ hU hXc hMX hT hS⟩
```

Conclusion `IsAnyrootedStickerball M.support σ` is **defeq** to the new public name
`IsAnyrootStickerball M.support σ` (item 3), so the statement is already expressible in the adopted
terminology; only the spurious hypothesis remains.

## 2. Is `SimplicialChain M` assumed? — YES, and it cannot currently be removed

The endpoint carries `(hS : SimplicialChain M)`. The steering instruction asked to remove it via a
bridge `taut_filling_is_simplicialChain` built "from existing multiplicity-one / eligible-tet /
minimality ingredients." **That bridge is not available from existing machinery.** Verified this turn
by `git grep` and confirming definitions:

- `tet_coeff_eq_pm_one_of_eligible` (`Theorem2.lean:250`) — the multiplicity-one step — has signature
  `(hS : SimplicialChain M) (h : EligibleTet M t) : M t = 1 ∨ M t = -1`; its proof is literally
  `rcases hS t`. It **is** simpliciality applied to one tet. Circular.
- `exists_eligibleTet` (`Eligible.lean:90`) requires `(hS : SimplicialChain M)` **and** `hShared2`
  (the triangle-bound, i.e. pseudomanifoldness). So even *finding* an eligible tet presupposes
  simpliciality.
- `taut_isPseudomanifold` (`PrimeStep.lean`) — the triangle-bound `faceCount ≤ 2` — also requires
  `(hS : SimplicialChain M)`. Without unit coefficients a triangle can lie in ≥3 tets with
  cancellation, so triangle-boundedness genuinely needs unit coefficients.
- A grep for *any* lemma concluding a coefficient bound (`(M t).natAbs ≤ 1`, `M t = ±1`, or
  `SimplicialChain M`) from `IsTaut`/minimality **without** a `SimplicialChain` hypothesis returns
  **nothing**.

So every entry point — multiplicity-one, eligible-tet existence, triangle-boundedness — assumes
`SimplicialChain`. The only routes to *global* unit coefficients (induction via eligible-tet removal;
or a direct `|M t| ≥ 2 ⇒ reduce ‖M‖` minimality argument) are respectively circular at the base case
or **unformalized** (no boundary-preserving norm-reduction primitive exists in the API).

**Concrete obstruction (the attempted model):** a bridge proof
```lean
theorem taut_filling_is_simplicialChain (hσ : IsSphere2 σ) (hU : UnitOn X σ)
    (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M) : SimplicialChain M
```
must, to use the multiplicity-one step, first exhibit an eligible tet — which calls
`exists_eligibleTet`, whose hypotheses include `SimplicialChain M`, the goal. There is no
`SimplicialChain`-free supply for that hypothesis, and `taut_isPseudomanifold` (needed for `hShared2`)
is in the same circle. This matches the prior investigation `notes/simpliciality-hypothesis-repair.md`
(written at `b5a2428`): the formalization appears to assume `SimplicialChain` precisely because the
clean route does not independently establish it; removing it is not a local bridge but a reproof of
the structure without simpliciality — a broad refactor, explicitly out of scope here.

**Decision:** per the evidence rule and "report before patching," I did **not** remove the hypothesis
and did **not** introduce a `sorry`-backed or otherwise unverified bridge. The other (independent)
hypotheses `UnitOn X σ`, `bdry X = 0`, `bdry M = X` are **not** spurious — together they are the paper
statement "`M` is a taut filling of the simplicial 2-sphere `σ`" (there is no canonical `X σ` function
in the API). Only `SimplicialChain M` is spurious, and it is the one we cannot yet discharge.

## 3. Bridge theorem — NOT used

`taut_filling_is_simplicialChain` was **not** created (see item 2). The endpoint composition *given*
such a bridge is a ~5-line, zero-risk change documented in `simpliciality-hypothesis-repair.md §6`;
the cost is entirely the bridge itself, which is missing and unsupported.

## 4. Exact stickerball / rooted / anyroot definitions (`lean/Taut/CleanShelling.lean`)

```lean
def IsStickerball (τ B : Finset (Finset V)) : Prop :=
  IsCleanBall τ B ∧ B.Nonempty

def IsAnyrootedStickerball (τ B : Finset (Finset V)) : Prop :=
  IsStickerball τ B ∧ FreelyCleanShellable τ B

-- added this turn:
def IsRootedStickerball (τ B : Finset (Finset V)) (t : Finset V) : Prop :=
  IsStickerball τ B ∧
    ∃ l : List (Finset V), l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B

abbrev IsAnyrootStickerball (τ B : Finset (Finset V)) : Prop := IsAnyrootedStickerball τ B
```

Supporting lemmas added: `IsRootedStickerball.toStickerball`, `IsAnyrootStickerball.rooted`
(anyroot ⇒ rooted at every `t ∈ τ`), `IsAnyrootStickerball.of_forall_rooted` (converse from a
stickerball). The existential in `IsRootedStickerball τ B t` is exactly the per-`t` body of
`FreelyCleanShellable τ B = ∀ t ∈ τ, ∃ l, l.head? = some t ∧ …`, so
`IsAnyrootStickerball ↔ IsStickerball ∧ ∀ t ∈ τ, (the rooted clause)` holds definitionally; the two
`.rooted` / `.of_forall_rooted` lemmas expose both directions. All five `#check` correctly.

Naming choice: `IsAnyrootStickerball` is an `abbrev` alias rather than a rename, to keep the patch
additive (no churn across the ~56 `Theorem3Clean` / 30 `PrimeStep` references to the old name) and
build-green. Migration of the public endpoint's *name* is deferred together with item 2, since the
user's target shape for that endpoint also drops `SimplicialChain`; producing an
`IsAnyrootStickerball`-named endpoint that still carried `SimplicialChain` would contradict the
target, so it was not added.

## 5. Monotone-shelling confirmation — CONFIRMED

The stickerball is a **monotone** clean shelling. Chain of definitions:

- `IsStickerball τ B := IsCleanBall τ B ∧ B.Nonempty`.
- `IsCleanBall τ B := ∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsCleanShelling l B`.
- `IsCleanShelling (t :: l) B := t.card = 4 ∧ CleanShellFrom {t} (tetFaces t) l B` — head tet, then
  glue the rest in order.
- each glue is a `CleanGlueStep`, whose `weak` field is a `GlueStep`; `GlueStep`'s `shared` field
  requires the new tet to meet the running boundary in **one or two triangles** (card 1 or 2), and
  `newBdry` updates the boundary by symmetric difference.

So each tetrahedron after the first is attached along one or two boundary triangles — the monotone
"sticking on" the prose calls a sticker move. The `IsStickerball` docstring was sharpened this turn to
state the 1-or-2-triangle attachment explicitly.

## 6. Ball-certificate confirmation — CONFIRMED

`IsStickerball`/`IsAnyrootStickerball` certify a **ball** `B³`, not a sphere shelling: the shelling
builds *up* with a **nonempty** boundary `B` (`B.Nonempty` in `IsStickerball`), and the self-
certification `IsStickerball.isClean3Complex` shows the result is a pure, triangle-bounded, edge- and
vertex-link-connected clean 3-complex. The docstrings of `IsStickerball` and `IsAnyrootStickerball`
state "ball certificate, not a sphere-shelling certificate" explicitly. (The external PL theorem
"shellable normal 3-pseudomanifold with nonempty boundary ⇒ PL ball" is named in the `IsStickerball`
docstring but, as noted there, is **not** formalized.)

## 7. CCXY / K-map confirmation

Full trace in `notes/th1-CCXY-kmap-audit.md`. Key points, confirmed against the Lean:

- `Kkills_or_Kkills` (`Theorem1.lean:263`) is an **inclusive**-or (each generator is killed by *at
  least* one of `K_{A,p}`, `K_{B,q}` ⇒ retained by *at most* one); it is the **norm-additivity**
  ingredient `‖M‖ ≥ ‖K_A M‖ + ‖K_B M‖` only, **not** a no-double-kill statement.
- The **splitting** (Theorem 2.4) uses the strictly stronger `no_double_kill` (`Splitting.lean:149`),
  valid for taut `M`. The CCXY term ({c₁,c₂} ∈ C, x ∈ A∖C, y ∈ B∖C) is eliminated in
  `hybrid_structure` (`Splitting.lean:237–246`): it picks the kill-pair `(p',q') = (c₁,c₂)` from
  `t ∩ (A∩B)` via `exists_pair_of_one_lt_card`, shows `t` is killed by **both** `K_{A,c₁}` and
  `K_{B,c₂}` (`kills_of_mem`), and applies `no_double_kill` to derive `False`. So CCXY is
  **eliminated in the splitting**, not merely bounded.
- `p ≠ q` is required (the `hpq` hypothesis throughout `Kkills_or_Kkills`, `no_double_kill`,
  `IsTaut.splits`). When `|A∩B| ≤ 1` there is no admissible distinct pair, and the proof instead uses
  the fresh-vertex expansion (`IsTaut.splits_full`, `Splitting.lean:523–558`).
- `no_extreme_hybrid` (`Splitting.lean:286`) closes the remaining hybrid via `bdry_lk_eq_zero` +
  `not_taut_complete_cone` at the coefficient level — **not** an F₂-cut; the splitting uses no cut.

No code change was needed for this item.

## 8. Build status + commit

- `lake build` → **8273 jobs, success** (terminology patch).
- `grep -RnE "\bsorry\b|\badmit\b" Taut` → **NONE**. `grep -RnE "^\s*axiom " Taut` → **NONE**.
- Files changed this turn: `lean/Taut/CleanShelling.lean` (docstring + 3 defs/abbrev + 3 lemmas),
  and this report. Public endpoint signatures **unchanged**.
- Commit hash: recorded in the commit's evidence stamp (`.session/claude-commit-evidence.md`) once the
  G2 gate approves; pre-commit HEAD was `b5a2428`.
