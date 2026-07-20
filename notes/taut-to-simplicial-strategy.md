# `taut → simplicial`: corrected strategy + Lean lemma statements

Branch `clean-anyrooted-stickerball`, HEAD `c521d27`, build green (8273 jobs). Read-only investigation;
no codebase change. Supersedes the strategy half of `notes/taut-to-simplicial-feasibility.md` (the
inventory there stands; its "keystone" framing is corrected below).

## 0. The one fact that reframes everything (build-verified)

**`EligibleTet M t` together with `UnitOn (bdry M) σ` forces `M t = 1 ∨ M t = -1`.** Verified by a
throwaway `example` that compiles against the current definitions (then deleted; not added to the
build). Derivation, all from inspected defs:

- `sharedFaces M t = tetFaces t ∩ (bdry M).support` (`Theorem2.lean:73`).
- `UnitOn (bdry M) σ = ((bdry M).support = σ ∧ ∀ s ∈ σ, (bdry M) s = ±1)` (`Theorem2.lean:21`).
- So any shared face `s` is in `σ`, hence `∂M s = ±1`.
- `EligibleTet`'s 4th conjunct: `∂M s = tetContribution M t s` (`Theorem2.lean:84-86`), and
  `tetContribution M t = bdry (single t (M t)) = (M t) • bdryGen t` (`Theorem2.lean:67`), so
  `∂M s = (M t) · bdryGen t s` with `bdryGen t s ∈ {−1,0,1}`.
- `(sharedFaces M t).card = 2 > 0`, so such an `s` exists; `±1 = (M t)·(±1)` ⇒ `M t = ±1`.

**Consequence.** The current Lean `EligibleTet` is *not* the paper's eligibility. The paper (`th2`,
line 833) defines eligible = "shares two faces with σ", a purely geometric condition with **no
coefficient constraint**. The Lean predicate is that **plus an orientation conjunct**, which under
`UnitOn` already pins the coefficient to `±1`. Your premise — "a tetrahedron can be eligible without
coefficient ±1" — is correct for the *paper's* eligibility but **false for the current Lean
`EligibleTet`**. They are different predicates. This mismatch is the first obstruction (§C7).

You are right that the missing lemma is **not** `eligible_coeff_eq_pm_one` and **is** a
counting/avoidance lemma. The correction this report adds: that counting must run over a **new
geometric-eligibility predicate** (the first three conjuncts), because the existing `EligibleTet`
silently excludes exactly the high-coefficient tets the argument is about.

## A. Where the paper handles the coefficient / chooses another tet

`th2` proof (`text/tautxy/tautxy_formalizable.tex`):

- **Counting** (836–840): `|M| = Zvol(σ) ≤ f − maxdeg(σ)` ⇒ "at least `maxdeg(σ)` **disjointly
  eligible** tets" (eligible = geometric).
- **Avoidance** (841–847): "we only need two… for any face `s` of `σ` there is an eligible tet without
  `s` as a face" (the two disjoint eligible tets cannot both touch `s`, else a degree-3 vertex).
- **Simpliciality** (868–874): "Suppose some tetrahedron `u` occurs with multiplicity `> 1`. Choose an
  eligible tetrahedron `t ≠ u`… Then `M − t` still contains `u` with multiplicity `> 1`, contradicting
  the simpliciality of `M − t`." Here `u` is the **retained** bad tet; `t` is the **removed** eligible
  tet; `t ≠ u` is supplied by "≥ 2 eligible."
- The paper does **not** spell out a separate "if `coeff(t) ≠ ±1` then …" step. Its clean-removal
  ("`M − t` is a taut filling of `σ_t`", 849–851) **implicitly requires the removed `t` to have
  coefficient `±1`**. That implicit requirement is exactly what the orientation conjunct encodes in
  Lean — so in Lean the removed `EligibleTet` is automatically clean, and the work shifts entirely to
  *existence* (does a non-simplicial `M` contain an oriented-eligible tet?). See §C7 for the fork this
  creates.

## B. Current Lean definitions (exact)

```
support               Finsupp.support  (Mathlib; M.support = {t | M t ≠ 0})
EligibleTet M t       (Theorem2.lean:84)  t.card = 4 ∧ t ∈ M.support ∧ (sharedFaces M t).card = 2 ∧
                                          ∀ s ∈ sharedFaces M t, (bdry M) s = tetContribution M t s
sharedFaces M t       (Theorem2.lean:73)  tetFaces t ∩ (bdry M).support
exposedFaces M t      (Theorem2.lean:76)  tetFaces t \ sharedFaces M t           -- the 2 interior faces
UnitOn X σ            (Theorem2.lean:21)  X.support = σ ∧ ∀ s ∈ σ, X s = 1 ∨ X s = -1
SimplicialChain M     (Theorem2.lean:27)  ∀ t, M t = -1 ∨ M t = 0 ∨ M t = 1
removeTet M t         (Theorem2.lean:70)  M - single t (M t)                      -- zeros out t
Case-1 new boundary   flipBoundary σ M e := (σ \ sharedFaces M e) ∪ exposedFaces M e   (FlipGeom)
Case-1 facts          IsSphere2 (flipBoundary σ M e), IsTaut (removeTet M e),
                      GlueStep e (flipBoundary σ M e) σ   -- FlipGeom, ALL carry (hS : SimplicialChain M)
Case-2 split          flipEdgePresent_removeTet_support_partition (PrimeStep.lean:203), carries hS:
                      ∃ A B, (∀ t ∈ (removeTet M e).support, t ⊆ A ∨ t ⊆ B) ∧ (exclusive)  -- two sides
endpoint              taut_filling_is_anyrootedStickerball (Theorem3Clean.lean:3433):
                      IsSphere2 σ → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M →
                        SimplicialChain M → IsAnyrootedStickerball M.support σ
```

## C. Corrected lemma statements needed

### C1. Finset of eligible supports

Existing pattern (already on supports, no multiplicity — good): the `disjoint_eligible_family_*`
lemmas (`Theorem4.lean:639,823`) use
```lean
E : Finset (Finset V)      (↑E).PairwiseDisjoint (fun e => sharedFaces M e)     ∀ e ∈ E, EligibleTet M e
```
**Correction needed:** `EligibleTet` here forces `±1` (§0), so such an `E` can never contain a
high-coefficient tet. To count as the strategy intends, introduce the **geometric** predicate (the
paper's "shares two faces"):
```lean
def GeomEligible (M : Chain V) (t : Finset V) : Prop :=
  t.card = 4 ∧ t ∈ M.support ∧ (sharedFaces M t).card = 2          -- EligibleTet minus the 4th conjunct
```
and count `E ⊆ M.support` with `∀ t ∈ E, GeomEligible M t`. (`EligibleTet M t → GeomEligible M t` is
immediate; the converse is the `±1`-vs-arbitrary gap.)

### C2. Counting lemma (MISSING)

```lean
-- there are k pairwise vertex-disjoint geometrically-eligible supports
theorem exists_disjoint_geomEligible_family
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hT : IsTaut M) (hprime : NoDegree3Vertex σ) :
    ∃ E : Finset (Finset V), E ⊆ M.support ∧ (↑E : Set _).PairwiseDisjoint id ∧
      (∀ t ∈ E, GeomEligible M t) ∧ maxDeg σ ≤ E.card
```
This is the paper's "`|M| ≤ f − maxdeg ⇒ ≥ maxdeg disjointly eligible." The bound ingredient
`Zvol_add_deg_le` (`Zvol.lean:113`, `Zvol X + deg x X ≤ nrm X`) exists and is `SimplicialChain`-free,
but **the existence statement itself is not in the codebase** (only the per-family *upper* bounds in
`disjoint_eligible_family_*`). Pairwise **vertex**-disjoint (`PairwiseDisjoint id`) is stronger than the
existing `PairwiseDisjoint sharedFaces`; vertex-disjoint supports are automatically distinct, removing
the repetition worry you flagged.

### C3. Avoidance lemma (route-neutral, trivial — clearly needed)

```lean
theorem exists_mem_not_mem_of_card_lt {α} [DecidableEq α] {E F : Finset α}
    (h : F.card < E.card) : ∃ u ∈ E, u ∉ F
```
Pure `Finset` (one line from `Finset.exists_mem_not_mem_of_card_lt_card` / pigeonhole). Used as: with
`F` = the bounded set of local supports touched by the move/cut, and `E` the eligible family of §C2,
`F.card < E.card` yields an available `u ∈ E \ F`. The *upper bounds on `F`* already exist as
`disjoint_eligible_family_hit_two_faces_card_le_two` (`≤ 2`) and `…_flipEdge_card_le_one` (`≤ 1`).

### C4. Case-1 minimality lemma (statement; depends on the route, §C7)

"Removing `u` gives a bad filling of `M − u`." In current terms the *clean* (route-X) version is:
```lean
-- if u is (oriented) eligible, M − u is a taut filling of the sphere flipBoundary σ M u
removeTet M u : Chain V,  IsTaut (removeTet M u),  IsSphere2 (flipBoundary σ M u),
  UnitOn (bdry (removeTet M u)) (flipBoundary σ M u),  nrm (removeTet M u) < nrm M
```
— all of which exist `hS`-free (`isTaut_removeTet`) or are FlipGeom outputs currently stated with `hS`.
The *bad-filling* (route-Y) version — "if `u` is only geometrically eligible with `M u ∉ {±1}` then
`∂(removeTet M u)` is **not** unit on `flipBoundary σ M u` (some exposed face carries `∓ M u`,
`|M u| ≥ 2`)" — **cannot be stated against a sphere**: `removeTet M u` no longer fills a 2-sphere, so
`IsSphere2`/minimality do not apply directly. Pinning down what "bad" contradicts (tautness of a
non-sphere boundary? a volume strict inequality?) is **not cleanly expressible with current
definitions** and is the substantive gap (§C7).

### C5. Case-2 side-local minimality lemma (statement)

The two sides are the supports `A`, `B` from `flipEdgePresent_removeTet_support_partition`
(`PrimeStep.lean:203`): `(removeTet M e).filter (· ⊆ A)` and `(· ⊆ B)`, each shown `IsTaut`
(`PrimeStep.lean:1204-1205`). The needed statement: the bad tet `u` lies in exactly one side
(`u ⊆ A` xor `u ⊆ B`, from the exclusive partition), and removing/examining `u` on that side gives the
contradiction on that side's filling. The Theorem-1 split (`IsTaut.splits`) provides the two taut
sub-fillings; what is missing is the same "bad filling" predicate as §C4, localized to a side.

### C6. Existing lemmas that already prove parts

- `removeTet`, `removeTet_apply_ne` (coeff of `u` survives removal of `t ≠ u`), `bdry_removeTet`,
  `support_removeTet_of_mem`, `isTaut_removeTet` — all `SimplicialChain`-free. (Paper steps "remove
  tet", "M − t still contains u".)
- `Zvol_add_deg_le` (Prop 2 volume bound) — `SimplicialChain`-free.
- `disjoint_eligible_family_hit_two_faces_card_le_two`, `…_flipEdge_card_le_one` — the **avoidance
  upper bounds** (`|F| ≤ 2`, `≤ 1`); take `EligibleTet` + `PairwiseDisjoint sharedFaces`.
- `flipBoundary`, the FlipGeom `IsSphere2 (flipBoundary σ M e)` + `GlueStep` facts (Case 1),
  `flipEdgePresent_removeTet_support_partition` + the A/B `IsTaut` lemmas (Case 2) — exist, but all
  **carry `hS`**.
- `exists_eligibleTet` — the only existence lemma; needs `hS` (via `exists_properBoundaryFaceTet`'s
  `{−1,0,1}`-sum argument, which fails non-simplicially).

### C7. First actual obstruction — and the fork it forces

The current definitions cannot even *state* "a geometrically-eligible tet with coefficient 2 is
eligible," because `EligibleTet` ⇒ `±1` (§0). Two routes follow, and they need different lemmas:

- **Route X — keep `EligibleTet` (oriented, ⇒ ±1).** Then the removed eligible tet is automatically
  clean, `u` (bad, `|M u| ≥ 2`) is automatically *not* eligible so `t ≠ u` is free, and §C4/§C5 are the
  existing FlipGeom/split outputs with `hS` stripped (mechanical given the eligible tet is passed in).
  The **entire** difficulty collapses to one statement: *existence of an oriented eligible tet in a
  non-simplicial taut filling, without `hS`* — i.e. re-prove `exists_eligibleTet` dropping
  `SimplicialChain`. **Risk:** this may be *false* as stated, or provable only by the counting argument
  itself; `exists_properBoundaryFaceTet`'s covering step genuinely uses `{−1,0,1}` and has no
  non-simplicial analogue.

- **Route Y — introduce `GeomEligible` (geometric, any coeff), per your strategy.** Counting/avoidance
  (§C2/§C3) run cleanly on `GeomEligible`. But §C4/§C5 ("removing a high-coefficient `u` gives a *bad*
  filling") are **not cleanly expressible**: `removeTet M u` with `|M u| ≥ 2` does not fill a 2-sphere
  (exposed faces carry `∓2`), so `IsSphere2`-minimality cannot be invoked, and the codebase has no
  predicate for "taut filling of a non-unit boundary that contradicts minimality." Formalizing that is
  new machinery.

**The obstruction is therefore not a missing one-liner but a modeling decision** the strategy has to
fix first: *what does "bad filling" mean in Lean when the removed tet has multiplicity > 1, and against
what is the contradiction taken?* Until that is answered, §C4/§C5 cannot be stated, and neither route
is unblocked. Everything upstream (counting, avoidance, removal, coeff-survival) is either present or
trivially addable; everything downstream of §C4 is blocked on this single definitional question.

## Recommended smallest next lemma (after your route decision)

Route-neutral and clearly needed regardless: **§C3 avoidance** (pure `Finset`, one line) plus the
**`GeomEligible` definition** (§C1). Neither commits the hard modeling choice. I did **not** code them
yet — the §C7 fork (X vs Y, and the "bad filling" model) is a strategy decision that should be made
before I add anything, per "correct the strategy before coding." Tell me the route (or that the
"bad-filling" contradiction should be modeled as a strict-volume inequality vs. a non-unit-boundary
tautness violation) and I will start with the smallest lemma on that path.
