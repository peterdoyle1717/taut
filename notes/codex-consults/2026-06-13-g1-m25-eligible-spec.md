# Architect request (codex): M25 — eligible-tet existence

Role: codex architect (Fable away). Design M25 in implementable Lean detail; I
implement what you specify. M25 is milestone 6/7 of your Theorem 2+3 audit
(019ec265), which YOU flagged as the biggest ballooning risk and recommended
isolating before the main induction (M26). M20–M23 + M22a are DONE & committed.

## The paper's argument (taut.tex 807-832)
For a minimal bad filling pair `(σ, M)`, `v > 4`, σ prime (no degree-3 vertex):
- `|M| = Zvol(σ) ≤ f − maxdeg(σ)` (Prop 2).
- Map each 2-simplex α of σ to some tet of M of which α is a properly oriented
  face. This map is at most 2-to-1 (no tet has >2 boundary faces, since σ has no
  degree-3 vertex). So ≥ maxdeg tets are hit twice ⟹ ≥ maxdeg *disjointly
  eligible* tets (eligible = shares 2 oriented faces with σ; disjoint = their
  boundary-face pairs are disjoint). "For the nonce we will only need two."

## Existing Lean
- `deg x M = nrm (nbhd x M)` (Chains.lean:486); `nbhd x M s = if x∈s then M s else 0`.
- Prop 2: `Zvol_add_deg_le (x) (hX : bdry X = 0) : Zvol X + deg x X ≤ nrm X`
  (Zvol.lean:118). `maxdeg(X)` = max over x of `deg x X` — NOT yet defined.
- `IsTaut M := nrm M = Zvol (bdry M)`; `nrm M`, `bdry`, `Chain V = Finset V →₀ ℤ`.
- M20: `UnitOn (bdry M) σ` (∂M is ±1 on σ), `SimplicialChain M`.
- M21: `EligibleTet M t := t.card=4 ∧ t∈M.support ∧ (sharedFaces M t).card=2 ∧
  ∀ s∈sharedFaces M t, (bdry M) s = tetContribution M t s`;
  `sharedFaces M t = tetFaces t ∩ (bdry M).support`; the flip API.
- `IsSphere2 σ` (closed pseudomanifold, χ=2); `edgeDeg`, `linkVerts`,
  `link_two_regular`, `three_le_card_linkVerts` (Complex2).

## Design questions
Q1. **The face→tet map + 2-to-1 count.** State the precise Lean lemma(s). Is the
    map "α ↦ the tet t∈M.support with α ∈ tetFaces t and ∂M α = ∂(t-contribution)
    α"? Each boundary face α (= a face of σ = (∂M).support) is in exactly one
    such tet? (Why — `∂M α = ±1`, and α appears in M's tets; the net is ±1, so an
    ODD number of tets have α as a face with the orientation... how do we pin "the"
    tet?) Give the cleanest formalization of "every σ-face is a face of an M-tet".
Q2. **"tet with 3 boundary faces ⟹ degree-3 vertex".** State and sketch this
    combinatorial lemma. A tet t={a,b,c,d}; if 3 of its 4 faces are in σ=∂M, the
    shared vertex of those 3 faces has link... Define what "degree-3 vertex of σ"
    means (`edgeDeg`/`linkVerts`/face-count) and prove the implication.
Q3. **maxdeg.** Do we need a `maxdeg σ := σ.sup (deg · X)` definition, or can we
    avoid it (the count only needs ≥ 1 or ≥ 2 eligible tets, not exactly maxdeg)?
    Recommend the minimal route.
Q4. **Minimal viable M25.** The induction's case-1 needs a SECOND disjoint
    eligible tet (for the multiplicity-2 argument); case-2 needs only ONE. What
    is the smallest M25 that unblocks M26 — just `∃ t, EligibleTet M t` (one), with
    the disjoint pair as M25b? Or can we structure M26 to assume eligible-tet
    existence as a hypothesis and prove it separately? Recommend.
Q5. **Biggest risk.** Which sub-fact (the face→tet map well-definedness; the
    2-to-1 bound; the disjoint extraction; the deg-3 lemma) is most likely to
    balloon, and how to contain it. Is `prime` (no deg-3 vertex) the right
    hypothesis to TAKE, deferring its establishment to M24?
Q6. Decompose M25 into named lemmas, dependency order. Flag any new primitive
    (maxdeg, an orientation-incidence lemma) vs. reuse.

End with `APPROVED: <one-line>` or `BLOCKED: <one-line reason>`.
