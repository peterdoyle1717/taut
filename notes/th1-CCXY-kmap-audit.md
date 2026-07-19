# Theorem 1 — CCXY / K-map killing audit

Branch `clean-anyrooted-stickerball`, commit `b5a2428`, build green. Proof-trace only; no edits.

## Verdict (read first)

**There is no gap. The Lean proof does prove the CCXY term "dies on both sides" — but that argument
lives in the *splitting* theorem, not the additivity inclusive-or.** Two distinct arguments exist:

- **Additivity** (`Zvol_add_of_almost_disjoint_full`) uses the inclusive "or": every type-(n+2)
  simplex is killed by **at least one** of `K_{A,p}`, `K_{B,q}` for a *fixed ambient* pair `p≠q ∈ C`
  (`Kkills_or_Kkills`). For a CCXY tet this is `p∈{c1,c2} ∨ q∈{c1,c2}` = `{p,q}∩{c1,c2}≠∅` — exactly
  the paper's `|C|=3` intersection fact (realized in Lean by cardinality, see Q4). Inclusive-or is all
  additivity needs.
- **Splitting** (`IsTaut.splits_full`) eliminates the CCXY tet by a **double kill**: it picks the kill
  pair `(p',q') = (c1,c2)` *from `t ∩ C`* and shows `t` is killed by **both** `K_{A,c1}` **and**
  `K_{B,c2}`, which `no_double_kill` proves impossible for a taut filling. So CCXY tets are **absent**
  from a taut `M`. This is the "dies on both sides" argument. It is `hybrid_structure` +
  `no_double_kill`, **not** `Kkills_or_Kkills`.

So the attempted prose ("…killed by at least one of `K_A,p`, `K_B,q`") describes the *additivity*
inclusive-or and indeed does **not** explain the splitting's CCXY elimination — the user's observation
is correct as a critique of the *prose*, but the Lean has the stronger argument. **Bad prose, not a
missing proof.**

---

## Current endpoints

```
IsTaut.splits_full  (Splitting.lean:510) :
  [Infinite V] → 2 ≤ n → (A ∩ B).card ≤ n + 1 →
  (∀ s ∈ X.support, s ⊆ A ∧ s.card = n+1) → (∀ s ∈ Y.support, s ⊆ B ∧ s.card = n+1) →
  bdry X = 0 → bdry Y = 0 → IsTaut M → bdry M = X + Y →
    bdry (M.filter (·⊆A)) = X ∧ bdry (M.filter (¬·⊆A)) = Y ∧
    IsTaut (M.filter (·⊆A)) ∧ IsTaut (M.filter (¬·⊆A)) ∧ M.filter(·⊆A) + M.filter(¬·⊆A) = M

Zvol_add_of_almost_disjoint_full  (Theorem1.lean:430) :
  [Infinite V] → 1 ≤ n → (A ∩ B).card ≤ n + 1 → (…X…) → (…Y…) → bdry X = 0 → bdry Y = 0 →
    Zvol (X + Y) = Zvol X + Zvol Y
```

---

## Q1. The K-maps (`Projection.lean`)

```
def Kkills (A : Finset V) (p : V) (s : Finset V) : Prop :=          -- Projection.lean:29
  ¬ s ⊆ A ∧ ¬ ((s \ A).card = 1 ∧ p ∉ s)

noncomputable def KGen (A : Finset V) (p : V) (s : Finset V) : Chain V :=   -- :35
  if s ⊆ A then Finsupp.single s 1
  else if (s \ A).card = 1 ∧ p ∉ s then ∑ z ∈ s \ A, sgn z s • coneGen p (s.erase z)
  else 0

noncomputable def Kmap (A : Finset V) (p : V) : Chain V →ₗ[ℤ] Chain V :=    -- :42
  Finsupp.lsum ℤ fun s => LinearMap.toSpanSingleton ℤ (Chain V) (KGen A p s)
  -- docstring: "the projection chain map induced by π(v) = if v ∈ A then v else p"
```

- **Domain / codomain:** `Kmap A p : Chain V →ₗ[ℤ] Chain V` (integer chains to integer chains; same for `B,q`).
- **Formula on a basis simplex `s`** (`KGen`): fix `s` if `s ⊆ A`; if exactly one vertex `z` lies outside
  `A` and `p ∉ s`, replace `z` by `p` (cone of `s.erase z` to `p`, signed); otherwise send `s` to `0`.
  (`π(v)=v` on `A`, `π(v)=p` off `A`.)
- **What makes `s` die** (`Kkills A p s`, i.e. `KGen A p s = 0`): `¬(s ⊆ A)` **and** `¬(|s\A|=1 ∧ p∉s)`
  — i.e. `s` has **≥ 2** vertices outside `A`, **or** exactly one outside vertex but `p ∈ s` (the
  projection folds that vertex onto an already-present `p`). Helper lemmas:
  `kills_of_two_sdiff (h : 2 ≤ (t\A).card) : Kkills A p t` (Splitting.lean:97);
  `kills_of_mem (h1 : (t\A).card = 1) (h2 : p ∈ t) : Kkills A p t` (Splitting.lean:106).
- **`p ∈ C`, `q ∈ C`, `p ≠ q`:** **not** part of the `Kmap`/`Kkills` *definitions* (`Kmap A p` is defined
  for any `p`). They are hypotheses of the *consuming theorems* (`Kkills_or_Kkills`, `no_double_kill`,
  `IsTaut.splits`): see Q2.

## Q2. Where `p` and `q` are chosen

- **`IsTaut.splits` (base, Splitting.lean:412):** `p,q` are **explicit hypotheses** —
  `(hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q)`. They are **arbitrary** distinct elements of
  `C = A ∩ B`. `p ≠ q` is **required**.
- **`IsTaut.splits_full` (Splitting.lean:510):** derives them.
  - If `2 ≤ |A∩B|`: `obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp h2` — straight from `C`
    (Splitting.lean:524).
  - If `|A∩B| ≤ 1`: **fresh-vertex / WLOG step** (Splitting.lean:526–558) using `[Infinite V]`
    (`Infinite.exists_superset_card_eq`): adjoin a fresh `F` disjoint from `A∪B`, set `A'=A∪F`,
    `B'=B∪F`, so `A'∩B' = (A∩B)∪F` with `(A'∩B').card = 2` (**not** `n+1` — just enough for a pair),
    take `p≠q ∈ A'∩B'`, apply `IsTaut.splits`, transport filters back via `t ⊆ A' ↔ t ⊆ A` on
    `M.support`. Identical pattern in `Zvol_add_of_almost_disjoint_full`.
  - So the expansion enlarges `C` to size **2** only in the degenerate `|A∩B| ≤ 1` case. The CCXY case
    (`|C| = 3 = n+1`, `n=2`) is in the `2 ≤ |A∩B|` branch — **no fresh vertices; `p,q ∈ C` directly.**
- **Per-tet pair inside `hybrid_structure`:** crucially, the kill pair used against a *specific* tet is
  **not** the ambient `p,q` — it is a pair `(p',q')` chosen **from `t ∩ (A ∩ B)`**
  (`exists_pair_of_one_lt_card`, Splitting.lean:92). For a CCXY tet `t = {c1,c2,x,y}`, `t∩C = {c1,c2}`,
  so `(p',q') = (c1,c2)`. The ambient `p,q` are passed along only to invoke additivity inside
  `no_double_kill`.

## Q3. How Lean proves the CCXY term dies (exact chain)

For `t = {c1,c2,x,y}` with `c1,c2 ∈ C`, `x ∈ A\C`, `y ∈ B\C` (so `t\A = {y}`, `t\B = {x}`,
`t∩C = {c1,c2}`):

`IsTaut.splits` → `hdich` (every tet `⊆A` or `⊆B`) → `hybrid_structure`
(Splitting.lean:204, conclusion is `t ⊆ A ∨ t ⊆ B ∨ (|t\A|=1 ∧ t∩C=∅) ∨ (|t\B|=1 ∧ t∩C=∅)`).
The CCXY tet falls into the **eliminated** branch `|t\A|=1 ∧ |t\B|=1 ∧ |t∩C| ≥ 2`
(Splitting.lean:237–246):

```lean
by_cases hxa1 : (t \ A).card = 1
· by_cases hxb1 : (t \ B).card = 1
  · have hc2 : 2 ≤ (t ∩ (A ∩ B)).card := by omega
    obtain ⟨p', hp', q', hq', hpq'⟩ := exists_pair_of_one_lt_card hc2     -- p',q' ∈ t∩C  (= c1,c2)
    exact (no_double_kill hn1 hp hq hpq hC hX hY hXc hYc hM1 hMt
      hp'AB hq'AB hpq' ht
      (kills_of_mem hxa1 (Finset.mem_inter.mp hp').1)     -- K_{A,c1} kills t   (|t\A|=1, c1 ∈ t)
      (kills_of_mem hxb1 (Finset.mem_inter.mp hq').1)).elim -- K_{B,c2} kills t   (|t\B|=1, c2 ∈ t)
```

So Lean exhibits **A** (`t` dies on the `A`-side, via `c1 ∈ t`) **and B** (`t` dies on the `B`-side, via
`c2 ∈ t`) — a **double kill** — and `no_double_kill` turns that into `False`. Hence a CCXY tet cannot
be in `M.support`; the surviving `hybrid_structure` output has `t∩C = ∅` (the extreme hybrids, later
killed by `no_extreme_hybrid`). **This is option A + B (dies on both sides), not C.**

(For additivity, by contrast, CCXY is only required to be killed by ≥ 1 — option C — and that is what
`Kkills_or_Kkills` delivers.)

`no_double_kill` (Splitting.lean:149) itself uses: `Kkills_or_Kkills hp' hq' hpq'` (every tet killed by
≥1, for the mass bound `nrm_add_le_killed_add_killed`), the double-kill hypotheses `hkA,hkB`, the
per-map bound `nrm_Kmap_add_killed_le`, and additivity `Zvol_add_of_almost_disjoint hp hq hpq` — giving
`nrm M + |M t₀| ≤ … ≤ nrm M`, so `|M t₀| ≤ 0`, contradiction.

## Q4. The combinatorial lemma `{c1,c2} ∩ {p,q} ≠ ∅`

- **No named lemma of that exact shape exists.**
- For **additivity**, the equivalent fact is realized **by cardinality** inside `Kkills_or_Kkills`
  (Theorem1.lean:304–321, the 4th case): assume neither side kills `t`, i.e. `|t\A|=1 ∧ p∉t` and
  `|t\B|=1 ∧ q∉t`; then `|t∩C| = n`, and `insert p (insert q (t∩C)) ⊆ C` with `p,q ∉ t∩C` and `p≠q`
  gives `C.card ≥ n+2`, contradicting `|C| ≤ n+1`. For `n=2`, `|C| ≤ 3`: this is precisely
  "`p,q,c1,c2` cannot be four distinct elements of a 3-set," i.e. `{p,q}∩{c1,c2}≠∅`. Same content,
  expressed as `card` arithmetic, not a set-intersection lemma.
- For **splitting CCXY**, the intersection argument is **bypassed**: Lean does not need `{c1,c2}` to meet
  the ambient `{p,q}`; it takes the kill pair *from* `t∩C` (`exists_pair_of_one_lt_card`, Splitting.lean:92).

## Q5. `Kkills_or_Kkills`

```
theorem Kkills_or_Kkills {A B : Finset V} {p q : V} {n : ℕ}                 -- Theorem1.lean:263
    (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q) (hC : (A ∩ B).card ≤ n + 1)
    {t : Finset V} (htAB : t ⊆ A ∪ B) (htcard : t.card = n + 2) :
    Kkills A p t ∨ Kkills B q t
```

- **Inclusive-or, yes** — its conclusion is a plain `∨` ("killed by at least one"), for a *fixed* `p,q`.
- **Used in:** the additivity proof `Zvol_add_of_almost_disjoint` (for the `nrm M ≥ Zvol X + Zvol Y`
  bound), and as a sub-step of `no_double_kill` (to feed `nrm_add_le_killed_add_killed`).
- **Used in the CCXY case?** Only indirectly, inside `no_double_kill`. The CCXY *elimination* is the
  **double kill**, not `Kkills_or_Kkills`. You do **not** get from inclusive-or to dies-on-both-sides;
  the stronger fact comes from *choosing the kill pair `(c1,c2)` from `t∩C`* and applying
  `no_double_kill` (which is available because `M` is taut: the additivity equality forbids any tet
  from being killed by both).
- **Stronger lemma that handles CCXY:** `no_double_kill` (Splitting.lean:149), invoked by
  `hybrid_structure` (Splitting.lean:243) with `(p',q') = (c1,c2) ∈ t∩C`.

---

## Summary answers to the audit questions

| question | answer |
|---|---|
| K-maps | `Kmap A p` / `Kmap B q` = projections collapsing off-`A` (off-`B`) vertices to `p` (`q`); `Kkills` = sent to 0 (≥2 outside, or 1 outside with base point ∈ `t`). `p∈C,q∈C,p≠q` are hypotheses of the consumers, not the def. |
| `p≠q` required? | **Yes** (`hpq`), in `IsTaut.splits`, `Kkills_or_Kkills`, `no_double_kill`. |
| `p,q ∈ C`? arbitrary? | Yes — arbitrary distinct elements of `C=A∩B` (base theorem). |
| fresh-vertex expansion? | Only in `_full` when `|A∩B| ≤ 1` (to size 2). **Not** for CCXY (`|C|=3`). |
| `|C|=3` intersection lemma named? | **No.** Equivalent realized by `card` arithmetic in `Kkills_or_Kkills` (additivity); bypassed (pair from `t∩C`) in splitting. |
| CCXY: A & B, or only C? | **A & B (dies on both sides)** in splitting, via double kill `(c1,c2)` + `no_double_kill`. (Only-C inclusive-or is the additivity ingredient.) |
| Gap? | **No gap.** The flagged prose described the additivity inclusive-or; the splitting's CCXY elimination is the stronger double-kill argument and is fully present. |
