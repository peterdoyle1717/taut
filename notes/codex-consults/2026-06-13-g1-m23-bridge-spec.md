# Architect request (codex): M23 — oriented separation bridge

Role: codex architect (Fable away). Design M23 in implementable Lean detail; I
implement exactly what you specify. M23 is milestone 4/7 of your Theorem 2+3
audit (019ec265), and you flagged it (with M25) as a piece to isolate before
the main induction. M20/M21/M22a are DONE & committed.

## Goal
Case-2 of the induction needs the INTEGRAL split `M − t = M₁ + M₂` with
`∂Mᵢ = Xᵢ`, `Xᵢ` supported on the two capped spheres. The 𝔽₂ `separates` only
gives the SET-level split (the two `cutSet` sides). M23 = the orientation-
packaging lemma `oriented_split_chains_of_separates` feeding `IsTaut.splits`.

## What we have
- `separates` (M19) and its internals (Separation.lean): `cutSet σ W`,
  `cutSet σ (W + 𝟙) = σ \ cutSet σ W` (`cutSet_add_one_eq_sdiff`), the two sides
  partition σ; `isSphere2_cut` gives `IsSphere2 (insert γ (cutSet σ W))`. These
  are 𝔽₂ (`C2 σ = σ → ZMod 2`).
- `IsTaut.splits` (Splitting.lean:435): given `2 ≤ n`, `p ≠ q ∈ A ∩ B`,
  `(A∩B).card ≤ n+1`, `X Y : Chain V` with `∀ s ∈ X.support, s ⊆ A ∧ s.card =
  n+1`, same for Y on B, `bdry X = 0`, `bdry Y = 0`, `IsTaut M`, `bdry M = X+Y`
  ⟹ M splits as `M.filter (·⊆A) + M.filter (·⊆A)ᶜ`, each taut, with the right
  boundaries. Here `Chain V = Finset V →₀ ℤ` (integral, signed).
- M20: `UnitOn X σ` (X.support = σ, all coeffs ±1), `SimplicialChain`.
- M21: `removeTet`, the flip; `unitOn_flipBoundary_of_eligible`.
- M10-M14 forward guidance: "the X=X₁+X₂ step needs an orientation-coherence
  lemma (∂ of X restricted to a side = ±the γ/cd-boundary, from bdry X=0 + ±1
  coeffs + edge_cut_parity)."

## The mismatch to resolve
`separates`/`cutSet` live over `C2 σ = ZMod 2` (faces of σ, a fixed sphere).
But case-2 starts from `M − t` (an integral `Chain V`) with boundary `∂(M−t) =
X'` a unit chain on `σ_t`, and `σ_t = σ₁ ∪_cd σ₂` (two spheres joined along the
flipped edge cd). The split is of the INTEGRAL boundary `X'`, by the SET
partition of `σ_t` into the two capped sides. So:
- A = insert (the cd-triangle?) σ₁'s faces, B = the other side — but wait, case-2
  joins along an EDGE cd, not a triangle. Re-examine: in case-2 the flip created
  an existing edge cd, splitting `σ_t` into σ₁, σ₂ sharing cd. The bridging tet t
  is added between. So A, B for `IsTaut.splits` are the two solid sides; A∩B
  shares cd (an edge, 2 vertices) — but `IsTaut.splits` needs `2 ≤ |A∩B|` with
  p≠q ∈ A∩B (n=2 ⟹ tets have 4 vertices, faces 3; the shared simplices...).
  CLARIFY the exact A, B, n for the case-2 application.

## Design questions
Q1. State `oriented_split_chains_of_separates` precisely: from a unit chain `X'`
    on `σ_t` (closed, `bdry X' = 0` — IS it closed? X' = ∂(M−t), so yes), plus
    the cut data, produce `X₁ X₂ : Chain V` and finite sets `A B` with
    `bdry X₁ = 0`, `bdry X₂ = 0`, `X' = X₁ + X₂`, supports in A/B, ready for
    `IsTaut.splits`. What are A, B, and n concretely for case-2 (edge-join)?
Q2. The orientation coherence: `X₁ := X'.filter (· ⊆ A)`? Does filtering an
    integral unit cycle by a side give a CLOSED chain (`bdry = 0`)? The M10-M14
    note says this needs `bdry X' = 0 + ±1 coeffs + edge_cut_parity`. Give the
    precise argument that `bdry (X'.filter P) = 0` for the side-predicate P.
Q3. Does `IsTaut.splits` apply directly to `X'` (the boundary), or to `M−t`
    (the filling)? `IsTaut.splits` consumes `bdry M = X+Y` and splits M. So we
    set `M := M−t`, `X := X₁`, `Y := X₂`, and need `M−t` taut (from M taut,
    `t` eligible — is `M−t` taut? minimality/Zvol argument). CLARIFY whether
    M23 should also establish `IsTaut (M−t)` or leave it to M26.
Q4. The n and A∩B: case-2 spheres join along edge cd (2 shared vertices). For
    `IsTaut.splits` with the 2-spheres' fillings (3-chains, tets card 4, n=2 so
    n+1=3 faces, n+2=4 tets), A∩B must contain p≠q with `|A∩B| ≤ 3`. Is A∩B =
    cd's 2 vertices enough (`2 ≤ |A∩B|=2 ≤ 3` ✓)? Confirm the numerology.
Q5. Biggest risk + minimal M23. If the full bridge balloons, what is the
    smallest piece that unblocks M26's case-2 (e.g. just the closed-filter
    lemma `bdry (X.filter P) = 0`)? Stage it.
Q6. Decompose M23 into named lemmas, dependency order. Flag any spot needing a
    new integral-orientation primitive vs. reusing Chains/Splitting.

End with `APPROVED: <one-line>` or `BLOCKED: <one-line reason>`.
