# Architect request (codex): M22 — ball reassembly (Ball.lean)

Role: codex is architect (Fable away). Design M22 in implementable Lean detail;
I implement exactly what you specify. M22 is milestone 3/7 of your Theorem 2+3
audit (019ec265). M20 (chain/facet bridge) and M21 (tet-removal/edge-flip API,
`removeTet`/`EligibleTet`/`support_flipBoundary_of_eligible`/
`unitOn_flipBoundary_of_eligible`) are DONE and committed.

## Existing Ball.lean API (READ IT before designing)
- `tetFaces t := t.powersetCard 3`.
- `structure GlueStep (t B B')`: `card4 : t.card=4`; `shared : (tetFaces t ∩ B).card = 1 ∨ = 2`;
  `newBdry : B' = (B \ tetFaces t) ∪ (tetFaces t \ B)`; `sphere : IsSphere2 B'`.
- `ShellFrom B₀ l B`: glue tets of `l` in order from boundary `B₀` to `B`
  (`[] ↦ B = B₀`; `t::l ↦ ∃ B₁, GlueStep t B₀ B₁ ∧ ShellFrom B₁ l B`).
- `IsShelling (t₀ :: l) B := t₀.card = 4 ∧ ShellFrom (tetFaces t₀) l B`.
- `IsBall τ B := ∃ l, l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B`.
- `FreelyShellable τ B := ∀ t ∈ τ, ∃ l, l.head? = some t ∧ l.toFinset = τ ∧ l.Nodup ∧ IsShelling l B`.
- `ShellFrom.isSphere2`, `IsShelling.isSphere2`, `IsBall.isSphere2`,
  `isBall_singleton`, `freelyShellable_singleton`, `isSphere2_powersetCard3`.

## What the induction (M26) needs from M22
Two reassembly moves (paper §Th2):
- **Case 1 (flip): append the removed tet back.** After flipping, `M − t` is a
  ball (induction) with boundary `σ_t`; adding `t` back glues it on as the LAST
  tet (type-1/2), giving a ball for `M` with boundary `σ`. Needs: from
  `IsBall τ B`, `GlueStep t B B'`, `t ∉ τ`, conclude `IsBall (insert t τ) B'`
  (append `t` to the shelling). The flip's new boundary is exactly a `GlueStep`
  `newBdry` shape? (`σ` vs `σ_t` via the two shared/exposed faces — relate to
  M21's `support_flipBoundary_of_eligible`.)
- **Case 2 (split): glue two balls through the bridging tet.** `M − t = M₁ + M₂`
  with `Mᵢ` filling `σᵢ` (two spheres joined along the flipped triangle), both
  balls by induction; `M` is the two balls glued with `t` between them. Needs a
  `IsBall τ₁ B₁ → IsBall τ₂ B₂ → (glue condition on t, B₁, B₂) → IsBall (τ₁ ∪ τ₂ ∪ {t}) B`
  lemma. THIS IS THE HARD ONE — concatenating two shellings through a bridge tet.

Also: **FreelyShellable preservation** for Theorem 3 (any tet can start) — how it
threads through both moves.

## Design questions
Q1. **Case-1 append.** State the exact lemma(s): `ShellFrom`/`IsShelling`
    closure under appending one `GlueStep` tet at the end
    (`ShellFrom_snoc`/`IsShelling_snoc`), then `IsBall (insert t τ) B'` from
    `IsBall τ B` + `GlueStep t B B'` + `t ∉ τ`. Watch the Nodup/toFinset
    bookkeeping for `l ++ [t]`. Give the proof skeleton.
Q2. **Case-2 concatenation — the precise gluing hypothesis.** What is the right
    Lean statement for "glue two balls across a bridging tet"? Concretely: which
    faces of `t` are shared with `B₁` vs `B₂`, what is the combined boundary `B`,
    and how do the two shellings `l₁`, `l₂` concatenate (does `l₁ ++ l₂ ++ [t]`
    work, or must `t` bridge differently)? Identify the minimal hypotheses M26
    can actually supply from the separation (`separates`/the flip), and whether
    this needs an extra invariant beyond the current `GlueStep`.
Q3. Is the current `GlueStep`/`ShellFrom` API sufficient for both moves, or does
    M22 need an auxiliary (e.g. a "glue a whole sub-shelling onto a boundary
    region" generalization of `ShellFrom`)? Recommend the minimal addition.
Q4. **FreelyShellable.** How does each move preserve it (the paper: shucking can
    remove any tet last)? Is `FreelyShellable` even needed for M26's induction,
    or only for the final Theorem-3 wrapper — can we carry plain `IsBall`
    through the induction and upgrade to `FreelyShellable` only at the end?
Q5. **Biggest risk / minimal viable M22.** If case-2 concatenation balloons,
    what is the smallest M22 that still unblocks M26 (e.g. land case-1 append
    now, and treat case-2 as its own sub-milestone)? Recommend the staging.
Q6. Decompose M22 into named lemmas in dependency order.

End with `APPROVED: <one-line>` or `BLOCKED: <one-line reason>`.
