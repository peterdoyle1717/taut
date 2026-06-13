# G1 design spec: the Theorem 2 + 3 induction (taut filling ⟹ freely shellable B³)

Target: formalize Theorem 2 (any taut filling of a triangulated S² arises from a
simplicial triangulation of B³) merged with Theorem 3 (it is freely shellable).
This is the central remaining theorem and the largest packet. We have just
finished the SEPARATION theorem `separates` (M19) and all of Theorem 1.

## 0. The paper's proof (taut.tex §"Filling a triangulation of the 2-sphere")
Minimal-counterexample induction on `|M|` (= `nrm M`):
- A *filling pair* `(σ, M)`: σ a triangulated S², M a taut filling (`∂M = X(σ)`,
  `nrm M = Zvol(σ)`). *Good* if M arises from a triangulation of B³.
- Take a bad pair with `|M|` minimal. `v > 4`. Assume σ *prime* (no degree-3
  vertex) — justified because taut fillings split under connected sum (Th1).
- *Eligible* tet `t ∈ M`: shares 2 oriented faces with σ (≤2 since no deg-3
  vertex). By Prop 2 (`Zvol ≤ f − maxdeg`) + a 2-to-1 counting map, there are
  ≥ maxdeg *disjointly* eligible tets (pairwise-disjoint boundary-face pairs).
  We need only TWO.
- Eligible `t` with boundary faces `s₁=[a,b,c]`, `s₂=[b,a,d]`. Removing `t`:
  `M−t` fills `σ_t`, where `s₁,s₂` are replaced by `[c,d,b],[d,c,a]` — edge `ab`
  is *flipped* to `cd`. Two cases:
  (1) `cd ∉ edges σ`: `σ_t` is a triangulation of S². By minimality `(σ_t,M−t)`
      good ⟹ `M−t` arises from a B³-triangulation ⟹ `M=(M−t)+t` good UNLESS `t`
      has multiplicity 2 in M; rule that out using a *disjoint* eligible tet `u`
      (else `(σ_u, M−u)` would be a bad pair smaller, since `2t ⊆ M−u` is not
      simplicial — contradiction with minimality the other way).
  (2) `cd ∈ edges σ`: `σ_t` is the almost-disjoint union of two S²
      triangulations `σ₁,σ₂` joined along `cd`. `M−t` splits as `M₁+M₂` (Th1
      `IsTaut.splits`), both good by minimality ⟹ glue the two B³ balls + `t` ⟹
      B³ triangulation. Contradiction.

## 1. Existing Lean to build on
- Theorem 1: `IsTaut`, `Zvol`, `nrm`, `deg`/`maxdeg`(?), `Zvol_add_deg_le`
  (Prop 2: `Zvol X + deg x X ≤ nrm X`), `IsTaut.splits` (split a taut chain
  along A∩B with `2 ≤ n`, `p≠q ∈ A∩B`), `Zvol_add_of_almost_disjoint`.
  Chains: `Chain V := Finset V →₀ ℤ`, augmented, canonical orientation.
- `separates` (M19): for `IsSphere2 σ` and a non-face triangle γ,
  `∃ σ₁ σ₂, IsSphere2 (insert γ σ₁) ∧ IsSphere2 (insert γ σ₂)`. (𝔽₂-level, on σ.)
- Ball.lean: `IsShelling`/`IsBall`/`FreelyShellable` as List shelling
  certificates; `GlueStep` (type-1/2 glue, IsSphere2 baked in); `IsBall.isSphere2`;
  `isBall_singleton`, `freelyShellable_singleton`.
- `IsSphere2` and the whole Complex2/Homology2 layer.

## 2. The load-bearing design decisions (what to audit)
### (A) "M arises from a triangulation of B³" / "good"
Candidate: M is *simplicial* (all coeffs ±1, `nrm M = M.support.card`) and
`M.support` is `IsBall` (a shelling-certified ball) with the boundary chain
`∂M = X(σ)`. For the merged Th3, target `FreelyShellable M.support` directly.
Question: define `Good (σ) (M) : Prop := IsTautFilling σ M ∧ ∃ (shelling), …`?
Or carry the shelling as data? The induction reassembles shellings (case 1: append
`t`; case 2: concatenate two shellings through `t`), so a List-certificate
(Ball.lean style) seems right, but the chain↔facet-set bridge must be pinned.

### (B) The eligible-tet / flip mechanism (the integral-chain heart)
`t` shares 2 ORIENTED faces with `∂M`. The flip replaces `s₁,s₂` by the other
two faces of the tetrahedron `{a,b,c,d}`. This is oriented-chain bookkeeping on
`∂(M − t) = ∂M − ∂t`. Need: a clean primitive for "tet `t={a,b,c,d}`, its 4
oriented boundary faces, removing it flips edge ab↔cd". Is the current `bdry`/
`cone` API enough, or do we add a `tet`/flip primitive?

### (C) The induction
Strong induction (well-founded) on `nrm M : ℕ`. Minimal-counterexample =
`Nat.strong_induction` / `WellFoundedRecursion`. The "prime / no deg-3 vertex"
reduction: is it necessary, or can we restructure to avoid the connected-sum
preprocessing (which is itself a separate sub-induction via `separates`+Th1)?

### (D) The bridge separates ↔ case (2)
`separates` is 𝔽₂ and on σ; case (2) needs the INTEGRAL split `M−t = M₁+M₂`
with `∂Mᵢ = X(σᵢ)`. The M10-M14 G1 verdict flagged an "orientation coherence"
lemma (∂ of the split restricted to a side = ±the γ/cd-boundary). Does `separates`
need an integral/oriented strengthening, or does `IsTaut.splits` already deliver
the integral split given the 𝔽₂ separation as the support pattern?

### (E) Reassembly
Case 1: `IsBall (M−t).support` + adding back `t` (type-2 glue, two shared
faces) ⟹ `IsBall M.support` — Ball.lean `GlueStep`. Case 2: glue two balls
across the tet `t` ⟹ ball. Free shellability: any tet can start (Th3).

## 3. Validation invariants / smoke tests
- `∂Δ³` (tetrahedron boundary, `isSphere2_powersetCard3`) is the base case: its
  unique taut filling is the single tet (`isBall_singleton`).
- Euler/`maxdeg` counting cross-checks eligible-tet existence.

## 4. Files / commands
New `lean/Taut/Theorem2.lean` (+ maybe primitives into Chains/Ball). Build
`cd lean && lake build`; greps + `#print axioms`.

## Questions for the auditor
Q1. The right formalization of "good" / "arises from a B³ triangulation" — a
    `Prop` (∃ shelling) vs. carrying the List certificate as data — given the
    induction reassembles shellings in both cases. Recommend the cleanest.
Q2. The eligible-tet/flip: can the current Chains/`bdry` API express it cleanly,
    or is a `tet`+`flip` primitive (with a build-checked ∂-flip identity)
    warranted? Sketch the key lemma.
Q3. The minimal-counterexample induction in Lean: strong induction on `nrm M`.
    Is the "σ prime / no deg-3 vertex" preprocessing avoidable, or must it be a
    first-class sub-induction (connected-sum reduction via separates+Th1)?
Q4. The separates↔case-2 bridge: does `separates` (𝔽₂) need an integral/oriented
    strengthening to produce `M−t = M₁+M₂` with `∂Mᵢ = X(σᵢ)`, or does
    `IsTaut.splits` already give the integral split from the support pattern?
    Name the precise extra lemma if one is needed.
Q5. The single biggest risk: which sub-piece (eligible-tet existence via the
    2-to-1/maxdeg count; the flip's sphere-preservation; the multiplicity-2
    argument; the ball-gluing reassembly) is most likely to balloon, and is the
    whole thing tractable, or should it be staged into named sub-theorems each
    with its own milestone?
Q6. Recommend the milestone decomposition (ordered sub-theorems) for this packet.
