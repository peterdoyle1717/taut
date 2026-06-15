# Architect request (codex): drop `GlueStep.sphere`; make "sticker ball" the clean combinatorial object; finish the FreelyShellable reassembly

Role: codex architect (continuing 019ecbfa, the FreelyShellable restructure). A
direct design directive from Peter (the paper's author) resolves the remaining
"sphere-preservation under glue" difficulty by removing it from the critical path.
I implement what you vet. Be Lean-level and concrete.

## Peter's directive (the design authority)
Verbatim: "what this comes down to is that we haven't proven that the boundary of a
sticker ball is a sphere. that is actually very simple if you know the
classification of surfaces. gluing the edges of a collection of triangles in pairs
yields a 2-manifold. if it's connected and orientable, and has euler char 2, it's
the 2-sphere. those conditions are trivially preserved by this surgery. what's hard
is to prove that the whole thing is a ball. we're going to sidestep that by stating
the theorem that a taut filling is a sticker ball. that's actually much stronger,
but that implication sticker ball -> ball is not something we need to prove."

Consequences:
- The theorem is **"a taut filling of a 2-sphere σ is a (free) sticker ball with
  boundary σ"** — i.e. `FreelyShellable M.support σ`. The gluing sequence IS the
  certificate. We do NOT prove sticker-ball ⇒ 3-ball (deferred, not needed).
- The boundary of `M.support` is σ, GIVEN as a sphere (`IsSphere2 σ` is a
  hypothesis). So per-step sphere-hood of intermediate boundaries is NOT needed to
  finish the theorem.
- "Boundary of a sticker ball is a sphere" is a TRUE, easy, but SEPARATE statement
  (classification: closed+connected+orientable+χ=2). Deferred.

## The proposal to vet
`Ball.lean`'s `GlueStep t B B'` currently bakes in a field `sphere : IsSphere2 B'`
(the post-glue boundary is a 2-sphere). That field is what forces, at every stick,
the `linkConn` (manifold-at-vertices) preservation — the field the prior consult
(019ecc0d) flagged as "genuinely hard." Grep result: `GlueStep.sphere` is consumed
ONLY at `Ball.lean:102` (inside `ShellFrom.isSphere2` → `IsShelling.isSphere2` →
`IsBall.isSphere2`), a standalone "boundary of a ball is a sphere" validation lemma
that nothing in the induction (`theorem2_core`/`theorem3_core`/the reassembly/the
eligible-tet branches) consumes.

**Proposal: delete the `sphere` field from `GlueStep`.** Then
`GlueStep t B B' := card4 t ∧ (shared = 1 ∨ shared = 2) ∧ B' = (B \ tetFaces t) ∪
(tetFaces t \ B)` — the clean combinatorial stick.

## Questions
Q1. **Soundness + blast radius.** Confirm dropping the field is sound for the
    theorem (no induction step needs intermediate sphere-hood; σ is the only
    boundary and it is given). Enumerate every site that CONSTRUCTS a `GlueStep`
    (so loses an argument) or CONSUMES `.sphere` (so must be repaired/deleted):
    candidates are `Ball.lean` `IsBall.insert_of_glueStep`, `RelShelling`/
    `IsBall.bridge_of_relShelling`, `ShellFrom.isSphere2`/`IsShelling.isSphere2`/
    `IsBall.isSphere2`, and anything in `Theorem2Aleph.lean` (does
    `aleph_deg3_split`'s reassembly `IsBall M' → IsBall M` build GlueSteps?). Give
    the exact fix per site. Confirm `aleph_base`/`base_free` (single tet, empty glue
    list) and `freelyShellable_singleton` are unaffected.
Q2. **The deferred boundary-sphere lemma.** State the standalone target precisely
    against `Ball.lean`/`Complex2.lean`, e.g.
    `theorem ShellFrom.isSphere2_of_seed : ShellFrom B₀ l B → IsSphere2 B₀ →
    IsSphere2 B` (induction on `l`, each step a `glueStep_preserves_isSphere2`). Is
    the cleanest per-step route via the existing `IsSphere2` fields (pure/closed/
    linkConn/conn/euler — `linkConn` the only nontrivial one, a single-cycle
    subdivision for type-1 and contraction-at-2 + subdivision-at-2 for type-2), or
    via a `closed ∧ connected ∧ orientable ∧ χ=2 ⇒ IsSphere2` re-characterisation
    (does Mathlib/`Complex2.lean` give that, or would it need the surface
    classification, which is NOT available)? RECOMMEND which, but mark the whole
    lemma DEFERRED — do not put it on the critical path; do not axiomatise/sorry it.
Q3. **The now-unblocked reassembly (lean `GlueStep`).** With no per-step sphere
    obligation, design these so they are pure combinatorics:
    - L1's `hstart_t` (the `∃ l, ShellFrom (tetFaces t) l B'` re-shelling of τ from
      the new tet's footprint): how is it discharged from `FreelyShellable τ B` +
      the attachment geometry, now that no sphere proof rides along?
    - **L2** `FreelyShellable.bridge`: free ball₁ + bridge tet `t` + free ball₂,
      almost-disjoint (meeting only through `t`'s shared faces) ⇒ free combined
      ball, for ANY start target. State the almost-disjointness hypothesis cleanly
      on the facet/boundary sets; give the concatenation order; show each glue is
      type-1/2 by disjointness (the shared-count and sym-diff both commute with the
      disjoint ambient part).
    - `deg3_step` (FreelyShellable): star tet (single, free) + capped remainder M₂
      (free by IH) — is this an L1 single-face stick or an L2 bridge? Reuse
      `aleph_deg3_split`'s chain-split data where possible.
    - `prime_step` (FreelyShellable): case 1 (L1, stick the flipped eligible tet
      back; the post-flip boundary is σ, given) and case 2 (L2 bridge; consumes M25b
      `aleph_disjoint_eligible_pair` + the M23 edge-join split-as-fillings).
Q4. **Hand-off + milestones.** Which of {L1-discharge, L2, deg3_step, prime_step
    case1, prime_step case2} are pure-combinatorial and good AlephProver targets,
    and in what dependency order? Flag the riskiest. Minimise edits to the verified
    Aleph proofs.

End with `APPROVED: <one-line>` or `BLOCKED: <reason>`.
