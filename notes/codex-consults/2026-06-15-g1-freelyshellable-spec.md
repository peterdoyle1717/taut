# Architect request (codex): restructure to the FreelyShellable ("free sticker ball") invariant

Role: codex architect. Design the restructure that ties up Theorem 2 (+3). I
implement what you specify. **A correction from Peter (the paper's author) reframes
the whole remaining problem and dissolves the M22b "hidden topology" wall I/you
flagged.**

## The reframe (this is the key)
"Shellable ball" is a bad name; think **sticker ball**: a ball built by sticking
tets on one at a time (a GlueStep, type 1 or 2). We NEVER form a general
triangulation of a ball, so non-shellable-ball pathologies (Furch/Bing) are
irrelevant — there is no object to certify after the fact; the construction IS the
proof. The induction must carry **`FreelyShellable`** (free sticker ball = a sticker
ball that can be started at ANY tet), not plain `IsBall`. With the free invariant,
the case-2 reassembly is a STRAIGHTFORWARD concatenation, not a deep lemma:

> Build ball₁ (any order). Stick the bridge tet on along its one shared face. The
> tet of ball₂ that the bridge meets becomes ball₂'s FIRST sticker, stuck to the
> bridge along the shared face. Stick on the rest of ball₂ in its own order. Done.

The only fact used: ball₂ can be started at the bridge-adjacent tet — i.e. ball₂ is
a FREE sticker ball. That is exactly why the paper carries free shellability
(Theorem 3), and it is the input — not an extra theorem about the glued result.

This also explains why the `$500` Aleph run stalled on `prime_step`: `theorem2_core`
carried `IsBall`, so case-2 looked like it needed a relative-shelling lemma; with
`FreelyShellable` it's two type-1 sticks + concatenation.

## Existing Lean (committed, building)
- `Ball.lean`: `tetFaces`, `GlueStep` (shared = 1 or 2 faces, sym-diff boundary,
  IsSphere2 baked in), `ShellFrom B₀ l B` (accumulator), `IsShelling`, `IsBall τ B`
  (∃ shelling list), `FreelyShellable τ B` (∀ t∈τ, ∃ shelling with t first),
  `IsBall.insert_of_glueStep` (grow a ball by a GlueStep tet), `RelShelling τ B₀ B`,
  `IsBall.bridge_of_relShelling`, `isBall_singleton`, `freelyShellable_singleton`,
  `ShellFrom_append`/`_snoc`, `IsShelling_append`/`_snoc`.
- `Theorem23.lean`: `theorem2_core` — strong induction on `nrm M` proving `IsBall
  M.support σ` modulo 3 hypotheses (base, deg3_split, prime_step).
- `Theorem2Aleph.lean` (Aleph-proved, VERIFIED, committed): `aleph_base`,
  `aleph_deg3_split` (the IsBall versions of the base/deg3 holes),
  `aleph_disjoint_eligible_pair` (M25b: two eligible tets with disjoint sharedFaces),
  `theorem2_modulo_prime_step`. Plus the deg3 machinery defs Aleph produced
  (`cutChain`, `cappedCutLeft/Right`, `starTet`, `degree3_cut_setup`,
  `taut_splits_for_capped_cut`, `degree3_reassemble_from_cut_split`, …).
- `Eligible.lean`: `exists_eligibleTet_of_noDegree3`, `EligibleTet`, the flip API.
- `Theorem2.lean` (M21): `removeTet`, `support_flipBoundary_of_eligible`,
  `unitOn_flipBoundary_of_eligible`, `nrm_removeTet_of_simplicial`, `FlipEdgePresent`.
- Paper `taut/taut.tex`: Theorem 2 §834-883 (the flip, cases 1/2); Theorem 3
  §885-960 (free shellability via the "shucking" recursion — the FORWARD version of
  which is Peter's sticker recipe above).

## Design questions
Q1. **The strong-induction statement.** Free shellability = `∀ t₁ ∈ M.support,
    ∃ shelling starting at t₁`. The shucking picks the removed tet RELATIVE to t₁
    (remove an eligible/deg-3 tet not sharing a face with t₁, so t₁ survives as the
    seed). So is the right statement `∀ M (taut filling of sphere σ), ∀ t₁ ∈
    M.support, ∃ ShellFrom-from-t₁`, strong induction on `nrm M`, choosing the
    removed tet via M25b (the disjoint pair guarantees an eligible tet avoiding
    t₁)? Give the exact `theorem3_core` statement and how `IsBall`/Theorem 2 falls
    out as a corollary.
Q2. **The two sticker-ball list lemmas** (the heart). State precisely against
    `Ball.lean`:
    - (L1) free sticker ball `B` + a `GlueStep t B B'` tet → free sticker ball `B'`
      (with shellings-from-t₁ for t₁ old = old-shelling ++ [t], and from t = [t] ++
      old-from-adjacent).
    - (L2) free ball₁ + bridge tet `t` + free ball₂, meeting only through `t`
      (almost-disjoint along the flip edge), → free combined ball; for ANY target
      t₁ (in ball₁ or ball₂) give the concatenation order (per Peter's recipe).
    How to state "almost-disjoint, meeting only through the bridge" cleanly on the
    facet sets / boundaries? Do `RelShelling` + `bridge_of_relShelling` (M22a)
    already give (L2), or do they need the FREE strengthening?
Q3. **The branches**, each producing `FreelyShellable` from the IH (`FreelyShellable`
    on smaller fillings): base (`freelyShellable_singleton`); deg-3 (star side =
    single tet (free) + the capped remainder M₂ (free by IH), glued — is this an
    (L2) bridge or an (L1) single-face stick of the star tet onto M₂?); prime
    case-1 (L1, stick the eligible tet back); prime case-2 (L2). What does each
    consume from the existing `separates` / Aleph deg3 chain-split / the M21 flip /
    M25b? Reuse Aleph's `aleph_deg3_split` chain-split logic where possible.
Q4. **Reuse vs redo.** Keep `theorem2_core` (IsBall) and derive it from `theorem3_
    core` (FreelyShellable → IsBall)? Do the committed Aleph IsBall proofs of
    base/deg3 still serve (e.g. their chain-split data), or are they superseded by
    the FreelyShellable versions? Minimize wasted/duplicated work; say what to keep.
Q5. **Milestones + dependency order** to tie up Theorem 2 (+3) fully, with the
    riskiest piece flagged.

Be concrete and Lean-level. End with `APPROVED: <one-line>` or `BLOCKED: <reason>`.
