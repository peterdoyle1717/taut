# G1 design spec: chain encoding for the taut-fillings formalization

Target: formalize Doyle–Ellison–Wang "Taut fillings" (taut/taut.tex) in Lean 4
(Mathlib v4.29.1). This spec fixes the foundational encoding and sign
conventions for simplicial chains on a full simplex. Everything downstream
(Props 1–4, Theorem 1 additivity+splitting, later the S²/B³ combinatorics)
builds on these.

## 1. Exact formulas

Vertex type `V` with `[LinearOrder V]`. **Chains are dimension-mixed**:

    Chain V := Finset V →₀ ℤ

A generator is an *unoriented* simplex `s : Finset V` (sorted by the order =
canonical orientation; `s.card = n+1` means dimension n; `∅` is the
(−1)-simplex, i.e. this is the AUGMENTED chain complex of the full simplex
on V). Dimension homogeneity, where needed, is a hypothesis
`∀ s ∈ M.support, s.card = k`, not part of the type.

Sign bookkeeping via "count below":

    cnt x s := (s.filter (· < x)).card
    sgn x s := (-1 : ℤ) ^ (cnt x s)

Operators (each ℤ-linear, defined on generators, extended by Finsupp.lsum):

  - boundary:  ∂s := ∑_{x ∈ s} sgn x s • [s.erase x]
  - cone:      cone x s := if x ∈ s then 0 else sgn x s • [insert x s]
  - link/strip: lk x M := ∑_{s ∈ supp M, x ∈ s} (sgn x s * M s) • [s.erase x]
  - neighborhood: nbhd x M := M.filter (x ∈ ·)   (restriction, not linear-extended)
  - projection (A : Finset V, p ∈ A), the chain map induced by
    π(v) = if v ∈ A then v else p:
      K_{A,p} s :=
        if s ⊆ A then [s]
        else if (s \ A).card = 1 ∧ p ∉ s then
          (let z := the element of s \ A;  (-1)^(cnt z s) • cone p (s.erase z))
        else 0
  - norm: nrm M := ∑_s |M s|  ∈ ℕ;  vert M := ⋃_{s ∈ supp M} s;
    deg x M := nrm (nbhd x M).
  - SubChain U M := ∀ s, (U s).natAbs + (M s − U s).natAbs = (M s).natAbs
    (the multiset-containment of the paper).
  - Zvol X := sInf { nrm M | ∂M = X };  Taut M := nrm M = Zvol (∂M).

## 2. Orientation conventions

Canonical orientation of a simplex = its vertices in increasing order. The
i-th vertex (0-indexed) of sorted s has exactly i smaller elements, so the
classical (−1)^i face sign is (−1)^(cnt x s). Coning prepends x then sorts:
moving x from front to its sorted position costs (cnt x s) transpositions,
giving the same sgn x s. The vertex-replacement sign in K (replace z ∉ A by
p) is (−1)^(cnt z s + cnt p (s.erase z)), realized as the stated composite
with cone, keeping one sign primitive.

Key parity identities driving all proofs (x ≠ z):
  cnt z (s.erase x) = cnt z s − [x < z],
  cnt z (insert x s) = cnt z s + [x < z]  (x ∉ s),
  [x < z] + [z < x] = 1.

## 3. Strongest validation invariants (build-checked theorems, not tests)

  (a) ∂ ∘ ∂ = 0 on all of Chain V.
  (b) Contracting homotopy, exact and global (the augmentation makes it
      correction-free): ∀ x M, ∂(cone x M) + cone x (∂M) = M.
  (c) cone x (lk x M) = nbhd x M.
  (d) Chain-map property: ∂ ∘ K_{A,p} = K_{A,p} ∘ ∂.
  (e) Norm accounting: nrm (cone x M) = nrm M − deg x M (no cancellation:
      t ↦ insert x t is injective on {t | x ∉ t});
      nrm (K_{A,p} M) ≤ nrm M − (mass of K-killed generators).

(b) on the augmented complex was hand-checked on generators including the
degenerate cases (x ∈ s; 0-simplices, where ∂{y} = [∅] is essential).
(a),(b),(d) jointly pin the sign convention up to a global unit.

## 4. Failure modes caught

Any sign error in ∂, cone, lk, or K breaks (a), (b), or (d) — these are
identities over ℤ, not parities, so they catch magnitude errors too (e.g.
double-counting in lsum extension). (c) catches mismatch between the
restriction and the cone/strip signs. (e) catches silent cancellation, which
would corrupt every Zvol argument (Props 2–4, Th1 norm bookkeeping).
Omitting the augmentation would silently break (b) for 0-chains and with it
filling-existence (∂(cone x X) = X for closed X), which Zvol's
well-definedness needs.

## 5. Files and commands

  lean/Taut/Chains.lean   — cnt/sgn lemmas, ∂, cone, lk, nbhd, vert, nrm,
                            invariants (a)–(c), (e)-cone
  lean/Taut/Zvol.lean     — SubChain, Zvol, Taut, Props 1–4 of the paper
  lean/Taut/Projection.lean — K_{A,p}, (d), (e)-K, kill lemmas,
                            small-support triviality (C_n(W)=0 for |W| ≤ n,
                            Z_n(W)=0 for |W| ≤ n+1)
  lean/Taut/Additivity.lean, lean/Taut/Splitting.lean — Theorem 1.

Build: `cd ~/Dropbox/taut/lean && lake build` after each lemma cluster.
Greps before each commit: `grep -rn "sorry\|admit\|axiom\|native_decide" lean/Taut/`.
`#print axioms` for the exported theorems at each milestone.

## Specific questions for the auditor

  Q1. Augmented complex (∅ as generator) vs truncated: any downstream trap?
      (Augmented chosen to make invariant (b) exact and global.)
  Q2. Dimension-mixed Finsupp with card-hypotheses vs dimension-indexed
      family of types: agree mixed is right for this paper's multiset-heavy
      arguments?
  Q3. The K_{A,p} three-case definition with the composite sign via cone:
      sound, or is there a cleaner equivalent that makes (d) easier?
  Q4. SubChain as the pointwise natAbs equation: right primitive?
