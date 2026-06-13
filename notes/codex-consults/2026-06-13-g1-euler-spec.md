# G1 design spec: `euler` for the cut pieces → `IsSphere2 (insert γ σᵢ)`

Target: prove the last `IsSphere2` field (`euler`, χ=2) for the capped sides of
the separation, then assemble `IsSphere2 (insert γ σᵢ)` for both sides. M17
landed `linkConn_cut`; the pieces now have pure + closed_cut + conn_cut +
linkConn_cut. Only `euler` remains.

## 0. Grounded dependency findings (this session)
Grep of `Taut/Homology2.lean`: `euler` is used in EXACTLY two places —
`IsSphere2.nonempty` (the empty complex fails V+F=E+2) and the watershed
`range_bd2_eq_ker_bd1` (uses χ=2 ⇒ H₁=0; genuinely circular for χ). The
b₂=1 / r₁=V−1 machinery uses euler ONLY transitively via `h.nonempty` /
`h.vertsOf_nonempty`. Direct field use:
- `dualGraph_preconnected`: `h.conn`, `h.pure` (b₂=1 source).
- `finrank_ker_bd2`: `h.nonempty`.
- `finrank_ker_aug`: `h.vertsOf_nonempty` (which uses nonempty + pure).
- `finrank_range_bd1`: no direct field (via helpers).
So: **the entire b₂/r₁ machinery needs only {pure, closed, conn, linkConn} +
nonemptiness; euler enters only as "σ ≠ ∅".** For the pieces nonemptiness is
trivial (γ ∈ insert γ σᵢ).

## 1. χ ≤ 2 from a closed surface (no euler) — the key new lemma
Chain complex `C2 →[bd2] C1 →[bd1] C0`, dims F=|σ|, E=|edgesOf σ|, V=|vertsOf σ|.
- b₂ := dim ker bd2 = 1  (generalized `finrank_ker_bd2`).
- r₁ := dim range bd1 = V−1  (generalized `finrank_range_bd1`).
- range bd2 ⊆ ker bd1 (∂∂=0, `bd1_comp_bd2`), so
  dim range bd2 ≤ dim ker bd1, i.e. (F − b₂) ≤ (E − r₁):
  (F − 1) ≤ (E − (V−1)) ⟹ V − E + F ≤ 2 ⟹ **χ ≤ 2**.
No euler used. (Full χ=2 = H₁=0 is the watershed, which DOES need euler; we do
NOT use it for the pieces.)

## 2. The refactor (the load-bearing design decision)
Generalize the hypothesis of the b₂/r₁ lemmas from `IsSphere2 σ` to a weaker
bundle, since their proofs never touch euler. **Recommended (Option C):**
introduce `structure IsClosedSurface (σ) : Prop` with the 4 geometric fields
(pure, closed, linkConn, conn), DO NOT redefine `IsSphere2` (avoids touching
every construction site), and provide a forgetful
`def IsSphere2.toClosedSurface (h : IsSphere2 σ) : IsClosedSurface σ :=
  ⟨h.pure, h.closed, h.linkConn, h.conn⟩`.
Then restate these lemmas to take `(h : IsClosedSurface σ) (hne : (vertsOf σ).Nonempty)`:
`dualGraph_preconnected`, `finrank_ker_bd2` (+ `ker_bd2_eq_span`),
`finrank_ker_aug`, `bd1_single_pair`, `accumulate`, `finrank_range_bd1`.
Internal callers (the watershed) pass `h.toClosedSurface` + `h.vertsOf_nonempty`.
Add `chi_le_two (h : IsClosedSurface σ) (hne) : (vertsOf σ).card + σ.card ≤ (edgesOf σ).card + 2`.

Alternatives considered: Option A (`IsSphere2 extends IsClosedSurface`) — clean
but redefines IsSphere2 ⇒ every construction site (`isSphere2_tetraBdry`,
Ball.lean glue) needs `⟨⟨…⟩, euler⟩`. Option B (thread 4 explicit hyps) — no
new structure but verbose 5-arg signatures.

## 3. χ-additivity (codex Q4 route): χτ₁ + χτ₂ = 4
With τ₁ = insert γ (cutSet σ W), τ₂ = insert γ (cutSet σ (W+𝟙)). State as
Finset identities, then count:
- `vertsOf τ₁ ∪ vertsOf τ₂ = vertsOf σ`,  `vertsOf τ₁ ∩ vertsOf τ₂ = γ`;
- `edgesOf τ₁ ∪ edgesOf τ₂ = edgesOf σ`,  `edgesOf τ₁ ∩ edgesOf τ₂ = γ.powersetCard 2`;
- `τ₁ ∩ τ₂ = {γ}`,  `τ₁ ∪ τ₂ = σ ∪ {γ}` (and `σ ∩ {γ} = ∅` since γ∉σ).
Inclusion–exclusion (`Finset.card_union_add_card_inter`) on each of V, E, F
then gives χτ₁ + χτ₂ = χσ + χ(shared). With χσ = 2 (IsSphere2.euler) and the
shared triangle γ (3 verts + 3 edges + 1 face, χ=1)… the bookkeeping must yield
**χτ₁ + χτ₂ = 4**. [Need the exact constant verified — see Q3.]

## 4. euler for the pieces, then assemble IsSphere2
- Each piece is `IsClosedSurface` (pure: faces are γ or cutSet⊆σ, all card 3;
  + closed_cut, linkConn_cut, conn_cut) and nonempty (γ ∈ it).
- chi_le_two ⇒ χτ₁ ≤ 2 and χτ₂ ≤ 2; additivity χτ₁+χτ₂=4 ⇒ both = 2 = euler.
- `IsSphere2 (insert γ σ₁) := ⟨pure, closed_cut, linkConn_cut, conn_cut, euler⟩`.
- σ₂ side: `bd2 (W+𝟙) = gammaChain σ γ` (since `bd2 𝟙 = 0` = `bd2_one`), so all
  the *_cut lemmas apply verbatim with `W+𝟙`.

## 5. Files / commands
`lean/Taut/Complex2.lean` (add IsClosedSurface + toClosedSurface),
`lean/Taut/Homology2.lean` (generalize the ~6 lemmas + add chi_le_two),
`lean/Taut/Separation.lean` (additivity set lemmas + euler + assemble). Build
`cd lean && lake build`; greps + `#print axioms`.

## Questions for the auditor
Q1. Confirm Option C (new `IsClosedSurface`, no IsSphere2 redefinition, forgetful
    map) over A/B as least-churn-and-clean. Any reason to prefer `extends`?
Q2. Is the χ≤2 derivation in §1 the cleanest, and is `dim range ≤ dim ker` from
    `range ≤ ker` (submodule) the right Mathlib lemma
    (`Submodule.finrank_mono` / `Submodule.finrank_le_finrank_of_le`)?
Q3. The additivity constant: is χτ₁+χτ₂ = 4 correct, and what is the cleanest
    inclusion–exclusion bookkeeping (do it on V, E, F separately, or on χ as a
    ℤ-combination)? Any orientation/double-count trap with `edgesOf τ₁ ∩ τ₂ =
    γ.powersetCard 2` (i.e. is every γ-edge actually in BOTH pieces)?
Q4. Generalizing `finrank_range_bd1` to IsClosedSurface: it needs r₁=V−1, i.e.
    the 1-skeleton is connected with one component — does that proof use only
    `conn` + nonempty, or does it smuggle euler somewhere I missed?
Q5. Anything in the σ₂ side (`W+𝟙`) that won't mirror σ₁?
