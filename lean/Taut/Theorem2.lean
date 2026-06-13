import Taut.Separation

/-!
# Theorem 2 + 3: a taut filling of a triangulated S² is a freely shellable B³

This file builds toward the central theorem (taut filling of `IsSphere2 σ`
arises from a freely shellable simplicial triangulation of B³) by the
minimal-counterexample induction of the paper (§"Filling a triangulation of the
2-sphere"). Per the G1 audit (codex 019ec265) the packet is staged:

* **M20 (here): the chain/facet bridge.** `UnitOn` (a `±1`-chain supported on
  σ), `SimplicialChain` (coefficients in `{-1,0,1}`), and the bridge
  `nrm_eq_support_card_of_simplicial` (`|M| = #support` when simplicial). These
  connect the integral chain `M` (a multiset of oriented tets) to the facet set
  `M.support` that the `IsBall`/`FreelyShellable` certificates live on.

Later milestones: the tet-removal/flip API (M21), ball reassembly (M22), the
oriented separation bridge to `IsTaut.splits` (M23), the connected-sum/degree-3
reduction (M24), eligible-tet existence (M25), and the main induction (M26).
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- A chain `X` is a *unit chain on `σ`* if it is supported exactly on `σ` with
every coefficient `±1`. The boundary `X(σ)` of a triangulated sphere is such a
chain (some choice of orientation); nothing downstream depends on the choice. -/
def UnitOn (X : Chain V) (σ : Finset (Finset V)) : Prop :=
  X.support = σ ∧ ∀ s ∈ σ, X s = 1 ∨ X s = -1

/-- A chain is *simplicial* if every coefficient is `-1`, `0`, or `1` — i.e. it
is a genuine multiset of oriented simplices with no repeats. A taut filling that
"arises from a triangulation" is such a chain on the tets of a ball. -/
def SimplicialChain (M : Chain V) : Prop :=
  ∀ t, M t = -1 ∨ M t = 0 ∨ M t = 1

lemma SimplicialChain.natAbs_eq_one {M : Chain V} (h : SimplicialChain M) {s : Finset V}
    (hs : s ∈ M.support) : (M s).natAbs = 1 := by
  have hne : M s ≠ 0 := Finsupp.mem_support_iff.mp hs
  rcases h s with h1 | h0 | h1
  · rw [h1]; decide
  · exact absurd h0 hne
  · rw [h1]; decide

/-- **The norm/support bridge.** For a simplicial chain the norm `|M|` counts
its support: `nrm M = #(M.support)`. This is what lets the induction on `|M|`
(`nrm`) talk to the ball's facet count (`M.support.card`). -/
lemma nrm_eq_support_card_of_simplicial {M : Chain V} (h : SimplicialChain M) :
    nrm M = M.support.card := by
  rw [nrm, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun s hs => h.natAbs_eq_one hs

/-- A unit chain on `σ` is simplicial. -/
lemma UnitOn.simplicialChain {X : Chain V} {σ : Finset (Finset V)} (h : UnitOn X σ) :
    SimplicialChain X := by
  intro t
  by_cases ht : t ∈ X.support
  · rcases h.2 t (h.1 ▸ ht) with h1 | h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inl h1
  · exact Or.inr (Or.inl (Finsupp.notMem_support_iff.mp ht))

/-- A unit chain on `σ` has `nrm = #σ` (each face carries weight one). -/
lemma UnitOn.nrm_eq {X : Chain V} {σ : Finset (Finset V)} (h : UnitOn X σ) :
    nrm X = σ.card := by
  rw [nrm_eq_support_card_of_simplicial h.simplicialChain, h.1]

end Taut
