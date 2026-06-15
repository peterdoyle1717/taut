# Architect request (codex): the ambient-lift crux for the free-shelling reassembly

Follow-up to 019ecbfa (FreelyShellable restructure, APPROVED; M-FS1 landed:
theorem3_core, L1 `FreelyShellable.insert_of_glueStep`, base_free, isBall_of_mem —
all committed, building). Now design the ONE flagged-risk piece: the ambient lift
that discharges L1's `hstart_t` and L2's relative-shelling hypotheses.

## The crux as I now see it
`GlueStep t B B'` bakes in `sphere : IsSphere2 B'`. In the ambient lift, ball₂'s
free shelling steps must be re-run with ball₁+bridge already present: the
shared-face COUNT and the symmetric-difference newBdry COMMUTE with a disjoint
ambient offset C (easy: if `tetFaces tᵢ ∩ C = ∅` then `(tetFaces tᵢ ∩ (Bᵢ∪C)).card
= (tetFaces tᵢ ∩ Bᵢ).card` and `(Bᵢ∪C) ▵-glue = Bᵢ' ∪ C`). The ONLY non-trivial
obligation is the per-step `IsSphere2 (Bᵢ' ∪ C)` — sphere-hood of each ambient
intermediate boundary.

## Questions
Q1. **Is the right enabling lemma `glue_preserves_isSphere2`?** i.e.
    ```
    (hB : IsSphere2 B) (ht4 : t.card = 4)
    (hsh : (tetFaces t ∩ B).card = 1 ∨ (tetFaces t ∩ B).card = 2) :
      IsSphere2 ((B \ tetFaces t) ∪ (tetFaces t \ B))
    ```
    If this holds, then `GlueStep` minus its `sphere` field already implies the
    sphere field, so (a) building any `ShellFrom`/`GlueStep` no longer needs a
    separately-supplied sphere proof, and (b) every ambient intermediate is a
    sticker step onto a sphere, so the ambient-lift sphere obligations are free.
    Is this the cleanest route? Confirm or give a better one.
Q2. **Proof of `glue_preserves_isSphere2`.** Sketch the 5 IsSphere2 fields under a
    type-1 (1 shared face) and type-2 (2 shared faces, sharing an edge) glue:
    - euler: type 1 adds (V,E,F) += (1,3,2) → χ unchanged; type 2 += (0,1,2)?
      give the exact deltas and the omega.
    - pure: trivial (new faces are card 3).
    - closed: each edge still in exactly 2 faces — which edges change degree and why
      it stays 2.
    - linkConn / conn: the new/old vertices' links and the skeleton stay connected.
    Which are the hard sub-facts? Is type-2's edge-becomes-interior the crux? Is
    there existing machinery (edgeDeg, linkGraph, the Euler counting lemmas in
    Complex2) to lean on? Be honest if any field is genuinely hard.
Q3. **The ambient-commute lemma.** State precisely: from `ShellFrom B₀ l B`, a
    disjoint ambient `C` (∀ t ∈ l, `tetFaces t ∩ C = ∅`), and (if needed)
    sphere-hood supplied by Q1, conclude `ShellFrom (B₀ ∪ C) l (B ∪ C)`. How to
    phrase the disjointness so it's actually available from the almost-disjoint
    geometry of the two cut sides?
Q4. **Discharging hstart_t / the L2 rel hyps.** With Q1+Q3, give the concrete
    derivation of L1's `hstart_t` (start at the new tet) and L2's `rel₂_after₁`
    etc. from the pieces' free shellings + the glue. Where does the bridge-adjacent
    tet `u` and its single shared face come from (M21 flip data / separation)?
Q5. Milestone order for the remaining tie-up, riskiest piece flagged. Is
    `glue_preserves_isSphere2` tractable, or is one of its fields (closed / linkConn
    under type-2) a genuine multi-day lemma?

End with `APPROVED: <one-line>` or `BLOCKED: <one-line reason>`.
