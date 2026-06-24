# `taut_filling_is_simplicialChain` — Lean feasibility report

Branch `clean-anyrooted-stickerball`, HEAD `c521d27`. Build green (`lake build`, 8273 jobs). Read-only
investigation; **no bridge attempted, no code changed.** Guidance: the revised paper
`text/tautxy/tautxy_formalizable.tex`, Theorem 2 (`th2`, lines 807–874) — the minimal-counterexample /
eligible-tet argument. The oracle for feasibility is the Lean.

## 0. Verdict (read first)

The minimal-counterexample argument is **partly supported and partly missing**. The *downstream* half
(remove a tet, tautness/coefficients are preserved, induct on `nrm`, derive the multiplicity
contradiction) already exists `SimplicialChain`-free or is mechanically adaptable. The *upstream*
half — **existence of an (oriented) eligible tet in a non-simplicial filling** — is genuinely missing
and is the crux. Classification: **C (Medium)**, with the entire risk concentrated in that one piece;
it is *new upstream work*, not a teardown of the existing simplicial machinery.

A load-bearing fact I verified (math, from the definitions; not yet build-checked): **an eligible tet
has coefficient `±1` from `EligibleTet + UnitOn` alone, with no `SimplicialChain`** (§6, keystone).
That is what keeps this out of class D.

## 1. Target theorem statement

Desired (nearest type-correct form in the current API; there is no canonical `X σ` function, so the
unit cycle is pinned by `UnitOn`/`bdry X = 0`/`bdry M = X`, exactly as in the existing endpoints):

```lean
theorem taut_filling_is_simplicialChain
    {σ : Finset (Finset V)} {X M : Chain V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) : SimplicialChain M
```
`SimplicialChain M := ∀ t, M t = -1 ∨ M t = 0 ∨ M t = 1` (`Theorem2.lean:27`). Paper `th2` proves
*clean + simplicial*; the bridge needs only the **simplicial** half (the clean half is what the
existing stickerball machinery already supplies, *given* simpliciality).

## 2. Existing eligible-tet lemmas (area A)

```
exists_eligibleTet            (Eligible.lean:90)   needs hS  -- the only existence lemma
exists_eligibleTet_of_noDegree3 (Eligible.lean:286) needs hS  -- wrapper, delegates to the above
exists_properBoundaryFaceTet  (Eligible.lean:49)   needs hS  -- the covering step inside the above
EligibleTet (def)             (Theorem2.lean:84)            -- t.card=4 ∧ t∈supp ∧ #sharedFaces=2 ∧
                                                               ∀ s∈sharedFaces, ∂M s = tetContribution M t s
disjoint_eligible_family_*    (Theorem4.lean:639,823)        -- take `∀ e∈E, EligibleTet M e` as a
                                                               HYPOTHESIS; prove disjointness/cardinality,
                                                               NOT existence
```

- **There is exactly one eligible-existence theorem, and it assumes `SimplicialChain M`.** The "at
  least two / disjointly eligible / choose `t ≠ u`" content of the paper (lines 840–847) is **not**
  proved as an existence statement; `disjoint_eligible_family_*` only bound a *given* eligible family.
- The volume bound the paper uses (`|M| = Zvol(σ) ≤ f − maxdeg`) **is** present as
  `Zvol_add_deg_le` (`Zvol.lean:113`, Prop 2), `SimplicialChain`-free at the `Zvol` level. But its
  consumer that turns it into a face-count inequality (`support.card + deg ≤ σ.card`,
  `Theorem2Aleph.lean:1114`) currently routes through `nrm_eq_support_card_of_simplicial hS`.

## 3. Existing eligible-removal / tautness lemmas (area B)

```
removeTet (def)               (Theorem2.lean:70)   removeTet M t = M - single t (M t)   -- zeros out t
isTaut_removeTet              (FlipGeom.lean:56)   IsTaut M → IsTaut (removeTet M e)     -- NO hS (hT.subChain)
bdry_removeTet                (Theorem2.lean:120)  ∂(removeTet M t) = ∂M − tetContribution M t  -- NO hS
support_removeTet_of_mem      (Theorem2.lean:133)  support(removeTet M t) = support.erase t      -- NO hS
flipEdgePresent_removeTet_support_partition (PrimeStep.lean:203)  -- case-2 split; carries hS
FlipGeom flip family          (FlipGeom.lean:136…1548, ~12 lemmas)  -- σₜ a sphere / GlueStep; ALL carry hS
```

- **Removal preserves tautness with no simpliciality** (`isTaut_removeTet`). ✓ This is the paper's
  "`M − t` is a taut filling."
- The *geometric* content — "`σₜ` is again an `S²` (case 1), or `M − t` splits into two `S²` fillings
  (case 2, via Theorem 1)" — is the FlipGeom flip family + the support-partition lemma. **All of these
  uniformly carry `hS`.** Whether `hS` is essential there: see §4/§6 — it bottoms out in the
  eligible-coefficient fact, which is re-derivable without `hS`.

## 4. Where the current proof assumes `SimplicialChain` (area C)

Three sites, in increasing depth:

1. **`exists_properBoundaryFaceTet` (essential, Eligible.lean:53–76).** To cover a boundary face
   `α` (`∂M α = ±1`) by a tet, it argues: each `M t · bdryGen t α ∈ {−1,0,1}` (`rcases hS t`), and a
   `{−1,0,1}`-valued sum equal to `±1` must have a term equal to `±1`. **This fails for non-simplicial
   `M`** (`1 = 2 + (−1)`: no term equals `1`). This is the genuine circularity: finding the *oriented*
   eligible tet uses simpliciality.

2. **Pigeonhole bound (incidental, Eligible.lean:109+).** `support.card < σ.card` is obtained via
   `nrm_eq_support_card_of_simplicial hS`. **Removable:** `support.card ≤ nrm M` holds for any chain,
   and the paper's bound is `nrm M = Zvol ≤ f − maxdeg < f = σ.card`, so `support.card ≤ nrm M < σ.card`
   survives. Needs one trivial new lemma `support.card ≤ nrm M`.

3. **The induction itself (structural).** `theorem3_core_clean` (`Theorem3Clean.lean:8`) does
   `Nat.strong_induction_on (nrm M)`, but its IH **assumes** `SimplicialChain M'` for every smaller
   filling, and supplies it at recursion sites via `simplicialChain_removeTet hS` — simpliciality is
   carried as an *invariant*, never concluded. The bridge needs the **inverted** induction: a separate
   minimal-counterexample induction that *concludes* `SimplicialChain`. The skeleton is a reusable
   template; **this does not require editing `theorem3_core_clean`** (the bridge sits upstream of it).

So changing the existing induction is **not** the plan — adding a new upstream induction is. The
downstream lemmas (`simplicialChain_removeTet`, the clean/stickerball machinery) keep `hS` internally,
unchanged.

## 5. Existing coefficient / removal lemmas (area D)

```
removeTet_apply_self  (Theorem2.lean:126)  (removeTet M t) t = 0                     -- NO hS
removeTet_apply_ne    (Theorem2.lean:129)  s ≠ t → (removeTet M t) s = M s           -- NO hS  ← the key one
simplicialChain_removeTet (Theorem2.lean:141)  SimplicialChain M → SimplicialChain (removeTet M t)
nrm_removeTet_add_one_of_simplicial (Theorem2.lean:148)  needs hS
SimplicialChain (def) (Theorem2.lean:27)   ∀ t, M t ∈ {−1,0,1}
```

- **The final contradiction is immediate.** Paper step 6 ("`M − t` still contains `u` with
  multiplicity `> 1`") is exactly `removeTet_apply_ne (u ≠ t) : (removeTet M t) u = M u`, with no
  simpliciality. Given `M − t` simplicial (from the IH), `(M − t) u ∈ {−1,0,1}` contradicts
  `|M u| ≥ 2`. ✓
- Missing but trivial: a general `nrm (removeTet M t) = nrm M − (M t).natAbs` (or just
  `nrm (removeTet M t) < nrm M` when `t ∈ support`) to feed the induction — the existing one is
  `_of_simplicial`. `nrm` zeros one coordinate, so this is a few lines, `hS`-free.

## 6. Can the multiplicity-one proof be formalized directly?

**The downstream argument: yes, and most pieces already exist `hS`-free.** Paper steps 2 (`M − t`
taut), 6 (coefficient of `u` survives), 7 (contradiction) map to `isTaut_removeTet`,
`removeTet_apply_ne`, and `SimplicialChain` unfolding. The strong-induction-on-`nrm` template exists.

**Keystone (verified mathematically; not yet build-checked).** `tet_coeff_eq_pm_one_of_eligible`
currently reads `(hS) (h : EligibleTet M t) : M t = ±1` and is proved by `rcases hS t`. But it is
re-derivable **without `hS`**, from `EligibleTet + UnitOn`:
`sharedFaces M t = tetFaces t ∩ (bdry M).support` (`Theorem2.lean:73`); `UnitOn (bdry M) σ` gives
`(bdry M).support = σ` and `∂M s = ±1` for `s ∈ σ`; so every shared face `s` has `∂M s = ±1`. The
eligible 4th conjunct `∂M s = tetContribution M t s = M t · bdryGen t s` with `bdryGen t s = ±1` then
forces **`M t = ±1`**. This is the only place the geometric flip machinery (FlipGeom) essentially
needs simpliciality, so **§3's FlipGeom `hS` is mechanically strippable**: replace
`tet_coeff_eq_pm_one_of_eligible hS he` by the keystone (UnitOn — `hU` — is already in scope in every
FlipGeom lemma) and delete the `hS` arguments. (Per-lemma check still required that no FlipGeom proof
*also* calls `exists_properBoundaryFaceTet`; the eligible tet is passed in as `he`, so existence is not
re-invoked.)

**The one genuinely missing piece: oriented-eligible *existence* for non-simplicial `M`.** The paper
gets eligibility by counting (`|M| ≤ f − maxdeg ⇒ ≥ maxdeg disjointly *geometrically* eligible tets`,
"shares two faces with `σ`"). The Lean's `EligibleTet` is *stronger* — it bundles the orientation
condition (`∂M s = tetContribution M t s`). For non-simplicial `M`, a merely geometrically-eligible tet
(shares `s₁,s₂ ∈ σ`) need **not** satisfy that condition, because other tets can contribute to `s₁,s₂`.
The existing bridge from "shares two faces" to the oriented `EligibleTet` is precisely
`exists_properBoundaryFaceTet`, which needs simpliciality (§4.1). **No `hS`-free oriented-eligible
existence exists, and producing one is the crux.** Whether it is Medium or hard turns on whether the
volume-bound argument can deliver the orientation condition directly (the paper's clean-removal step
appears to assume an eligible tet has multiplicity `1`, which — pre-simpliciality — is itself the
keystone applied to an *oriented* eligible tet, i.e. circular unless existence is established
geometrically first). **This is the single question to probe before committing.**

## 7. Difficulty classification: **C (Medium)**

Not **A** (no such theorem exists). Not **B** (oriented-eligible existence without `hS` is genuinely
missing — not a compose of existing lemmas). Not **D**: the existing machinery is **reusable**, not in
need of teardown — removal/tautness/coefficient/induction are `hS`-free or trivially so, and the
eligible-coefficient fact (the only essential simpliciality use downstream) is re-derivable (§6
keystone). The bridge is **new upstream work that leaves `theorem3_core_clean` and the simplicial
machinery untouched**, which is the signature of C, not D.

The residual risk that would push to D is entirely in §6's last paragraph: if oriented-eligible
existence for non-simplicial fillings cannot be established without first knowing (partial)
simpliciality, the clean minimal-counterexample structure would need re-architecting. Conservatively:
**C, contingent on a positive result from the existence probe below.**

## 8. Recommended next patch (NOT the bridge; smallest-decisive-first)

1. **Keystone lemma (small, low-risk, verified math).** Add, `hS`-free:
   ```lean
   lemma eligible_coeff_eq_pm_one {σ} (hU : UnitOn (bdry M) σ) (h : EligibleTet M t) :
       M t = 1 ∨ M t = -1
   ```
   a strict weakening of `tet_coeff_eq_pm_one_of_eligible` (drop `hS`, add `hU`). Confirms the §6
   keystone in Lean and unblocks `hS`-stripping of FlipGeom. Plus the trivial `support.card ≤ nrm M`
   and `nrm (removeTet M t) < nrm M` (`t ∈ support`) lemmas.

2. **Existence probe (the make-or-break).** *Before* any bridge, attempt — as a scoped, reportable
   experiment — to prove oriented-eligible existence **without `hS`**:
   ```lean
   -- target of the probe (not the bridge):
   ∃ t, EligibleTet M t   -- from IsSphere2 σ, UnitOn (bdry M) σ, IsTaut M,
                          --      hPure, hShared2 — but NOT SimplicialChain
   ```
   i.e. re-derive `exists_eligibleTet` from the volume bound `Zvol_add_deg_le` + a covering argument
   that does not assume `{−1,0,1}` contributions. Outcome decides Medium-vs-large and whether the full
   bridge is worth starting.

**Do not** modify `theorem3_core_clean` or the simplicial-invariant lemmas; the bridge is a separate
upstream theorem. **Do not** start the minimal-counterexample induction until the existence probe
returns positive.

## 9. Exact `#check` output

```
exists_eligibleTet :
  IsSphere2 σ → UnitOn (bdry M) σ → SimplicialChain M → IsTaut M →
    (∀ t ∈ M.support, t.card = 4) → (∀ t ∈ M.support, (sharedFaces M t).card ≤ 2) →
    ∃ t, EligibleTet M t
exists_properBoundaryFaceTet :
  SimplicialChain M → (∀ t ∈ M.support, t.card = 4) →
    (bdry M) α = 1 ∨ (bdry M) α = -1 → ∃ t, ProperBoundaryFaceTet M α t
isTaut_removeTet :
  IsTaut M → IsTaut (removeTet M e)
removeTet_apply_ne :
  s ≠ t → (removeTet M t) s = M s
tet_coeff_eq_pm_one_of_eligible :
  SimplicialChain M → EligibleTet M t → M t = 1 ∨ M t = -1
simplicialChain_removeTet :
  SimplicialChain M → SimplicialChain (removeTet M t)
nrm_removeTet_add_one_of_simplicial :
  SimplicialChain M → t ∈ M.support → nrm (removeTet M t) + 1 = nrm M
bdry_removeTet :
  bdry (removeTet M t) = bdry M - tetContribution M t
Zvol_add_deg_le :
  bdry X = 0 → Zvol X + deg x X ≤ nrm X
EligibleTet M t  (def, Theorem2.lean:84) :
  t.card = 4 ∧ t ∈ M.support ∧ (sharedFaces M t).card = 2 ∧
    ∀ s ∈ sharedFaces M t, (bdry M) s = tetContribution M t s
```

## Validation (run this turn)

```
cd lean && lake build         → Build completed successfully (8273 jobs).
grep -r "SimplicialChain" Taut → 141 occurrences
grep -r "eligible" Taut        → 250 occurrences
grep -r "removeTet|erase|coeff" Taut → 1058 occurrences
```
