# G1 design spec: 𝔽₂ homology and the separation theorem

Target: the **separation theorem** for combinatorial 2-spheres — a non-face
triangle (3-cycle in the 1-skeleton that is not a face) partitions σ into two
sides, each capping to a sphere. This is the watershed of Theorem 2 (the flip
dichotomy's splitting case). The PI (Doyle) co-designed this route in session;
this spec audits only the **Lean encoding**, the math is settled.

## 0. The mathematical route (settled with the PI)

Earlier plan was tree–cotree for χ ≤ 2. That is now known to be **overkill**:
χ = 2 is already a hypothesis in `IsSphere2`. The Euler–Poincaré identity
χ = b₀ − b₁ + b₂ is pure linear algebra, so with b₀ = 1 (connected) and
b₂ = 1 (the fundamental class is unique up to scale — "a 2-cycle assigns
equal weight across every edge, hence is constant", PI's argument), the given
χ = 2 forces **b₁ = 0**, i.e. H₁ = 0, i.e. every 1-cycle bounds. The non-face
triangle's cycle then bounds a 2-chain = one side; the other side is the
complement. Over 𝔽₂ the "2-chain" IS a set of faces, giving the partition
directly; orientation is re-attached afterward via the existing integral
fundamental cycle X.

We do NOT build Betti numbers. We work with ranks directly:
- r₁ := finrank (range ∂₁),  r₂ := finrank (range ∂₂).
- b₂ = 1  ⟺  finrank (ker ∂₂) = 1  ⟺  r₂ = F − 1   (rank-nullity on ∂₂).
- b₀ = 1 (connected)  ⟺  r₁ = V − 1   (skeleton-connectivity).
- ∂₁ ∘ ∂₂ = 0  ⟹  range ∂₂ ⊆ ker ∂₁.
- rank-nullity on ∂₁: finrank (ker ∂₁) = E − r₁ = E − (V−1).
- given V − E + F = 2: E − (V−1) = F − 1 = finrank (range ∂₂).
- so range ∂₂ ⊆ ker ∂₁ with **equal finrank** ⟹ range ∂₂ = ker ∂₁ ⟹ H₁ = 0.

## 1. Proposed encoding (the audited artifact)

Field `K := ZMod 2` (`Fact (Nat.Prime 2)` gives the `Field` instance).

Chain groups as function spaces on Finset-coerced subtypes (Fintype, with
`Module.finrank_fintype_fun_eq_card` giving finrank = card):

    C0 σ := ↥(vertsOf σ) → K
    C1 σ := ↥(edgesOf σ) → K
    C2 σ := ↥σ          → K       -- ↥s = {x // x ∈ s}

Boundary maps as `K`-linear maps between these function spaces, each a sum of
"coordinate indicators" (no signs over 𝔽₂):

    (bd2 w) ⟨e,_⟩ := ∑ f ∈ σ.attach, if e ⊆ (f:Finset V) then w f else 0
    (bd1 u) ⟨x,_⟩ := ∑ e ∈ (edgesOf σ).attach, if x ∈ (e:Finset V) then u e else 0

built as `LinearMap`s (toFun + map_add' + map_smul', linearity = sum-linearity),
OR via an incidence `Matrix` and `Matrix.mulVecLin` / `Matrix.rank` — see Q1.

`bd1 ∘ bd2 = 0`: each face f and vertex x∈f, the edges e with x∈e⊆f number
exactly 2 (the two edges of f at x), so the coefficient is 2 = 0 in `ZMod 2`.

Connectivity inputs (the two real lemmas):
- **r₁ = V − 1**: `range bd1 = ker(augmentation ε : C0 → K, ε u = ∑ u)`, since
  σ connected (`IsSphere2.conn`). Proven by Walk induction on `skel σ`:
  x,y reachable ⟹ `e_x + e_y ∈ range bd1` (sum edge-indicators along a walk).
  Then finrank(range bd1) = finrank(ker ε) = V − 1 (ε surjective onto K).
- **r₂ = F − 1**: `ker bd2 = K · 𝟙` (all-faces vector), since the dual graph
  (faces, edge-adjacency) is connected. "w ∈ ker bd2 ⟹ w constant across each
  shared edge ⟹ (dual connected) w constant ⟹ w ∈ {0, 𝟙}". Then
  finrank(ker bd2)=1, so r₂ = F − 1 by rank-nullity. Dual connectivity itself:
  faces at a vertex are dual-connected via `linkConn`; `conn` chains vertices.

Separation deliverable (consumed by `IsTaut.splits`):

    theorem separates (h : IsSphere2 σ) (γ : Finset V) (hγ3 : γ.card = 3)
        (hedges : γ.powersetCard 2 ⊆ edgesOf σ) (hnonface : γ ∉ σ) :
      ∃ σ₁ σ₂ : Finset (Finset V), σ = σ₁ ∪ σ₂ ∧ σ₁ ∩ σ₂ = ∅ ∧
        IsSphere2 (insert γ σ₁) ∧ IsSphere2 (insert γ σ₂) ∧ …
    -- from H₁=0: the 1-cycle ∂₂⟨γ⟩ (the three edges of γ) lies in ker bd1 =
    -- range bd2, so = bd2 W for a face-set W =: σ₁; σ₂ := σ \ σ₁.

Integral re-orientation: with the existing fundamental 2-cycle X (∂X = 0,
support σ, ±1), set X₁ := X restricted to σ₁ capped by −⟨γ⟩, X₂ likewise; then
X = X₁ + X₂ with the two ⟨γ⟩ copies cancelling — the almost-disjoint-union
input of Theorem 1's `IsTaut.splits`.

## 2. Conventions

𝔽₂ for the homology/separation (set-level cut, no signs); orientation lives in
the integral chain layer (the existing `Chain V := Finset V →₀ ℤ`, `X`). No
topology, no geometric realization. Chain groups are subtype-function-spaces,
NOT the `Finset V →₀ ℤ` chains of the existing layer — the 𝔽₂ homology is a
self-contained side computation whose only output is the face partition.

## 3. Validation invariants (build-checked)

(a) `bd1 ∘ bd2 = 0`.
(b) On the tetrahedron boundary (`tetraBdry`, V=4,E=6,F=4): r₁ = 3, r₂ = 3,
    finrank ker bd1 = 3, finrank range bd2 = 3, ker bd1 = range bd2 (H₁=0).
(c) The separation theorem applied to a concrete non-face triangle if a cheap
    instance exists (e.g. in a bipyramid); otherwise (b) is the smoke test.

## 4. Failure modes caught

(a) catches a wrong bd (bd1∘bd2 ≠ 0); (b) catches a wrong finrank/rank wiring
(the equal-finrank step fails numerically on the tetra); the dual-connectivity
lemma cross-checks `closed` against `linkConn` exactly as the prior
links-are-cycles lemma did.

## 5. Files and commands

    lean/Taut/Homology2.lean — new: C0/C1/C2, bd1/bd2, bd1∘bd2=0, the two
                               connectivity-rank lemmas, H₁=0, `separates`.
    Reuses Complex2 (IsSphere2, edgesOf/vertsOf/skel/linkGraph/ConnOn) and,
    for the integral X=X₁+X₂ packaging, Chains/Zvol/Splitting.
    Build: cd lean && lake build. Greps + #print axioms per commit gate.

## Questions for the auditor

Q1. Chain groups as `↥Finset → ZMod 2` with `bd` as explicit `LinearMap`s and
    `Submodule.finrank` / `Submodule.eq_of_le_of_finrank_eq`, vs. an incidence
    `Matrix` + `Matrix.rank`. Which is less painful for (i) proving bd1∘bd2=0,
    (ii) the two connectivity-rank lemmas, (iii) extracting the face-set W from
    z ∈ range bd2? I lean LinearMap+Submodule for (iii). Endorse or redirect.

Q2. The "equal weight across every edge ⟹ constant" step (for ker bd2 = K·𝟙)
    and the symmetric "reachable ⟹ e_x+e_y ∈ range bd1" step are both Walk
    inductions on a connected graph. Is there a cleaner Mathlib idiom than
    hand-rolling `Walk.rec`? (Scout found no packaged "constant on reachable".)

Q3. Working over 𝔽₂ for the partition, then re-attaching orientation via the
    existing integral X for X = X₁ + X₂: sound? Any trap in proving the two
    capped pieces `insert γ σᵢ` satisfy `IsSphere2` (each of closed / linkConn /
    conn / euler must be re-derived for the pieces — is euler the only nontrivial
    one, via χ-additivity χ(σ₁)+χ(σ₂) = χ(σ)+χ(γ) and χ≤2-each = b₁≥0)?

Q4. Is the `separates` signature above the right consumable for the Theorem 2
    induction (does it hand `IsTaut.splits` what it needs), or should it instead
    directly produce the chain decomposition X = X₁ + X₂ and the two taut
    sub-fillings? I.e. should `separates` be stated complex-side, chain-side,
    or both?

Q5. Anything in the rank argument that secretly needs more than V−E+F = 2 +
    connectivity + dual-connectivity? In particular: does extracting an
    **integral** ±1 partition (not merely an 𝔽₂ one) need a torsion-freeness
    argument I'm not seeing, or does "W is a set of faces over 𝔽₂, oriented by
    the existing X" fully sidestep it?
