import Taut.Separation
import Taut.Ball

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

/-! ## M21: tet removal and the edge flip (architect: codex 019ec271)

Removing an *eligible* tet `t` from a simplicial filling `M` flips two boundary
faces to the tet's other two — the paper's `ab → cd` edge flip. We work over ℤ
with the canonical-orientation signs of `Chains.lean`. -/

/-- The boundary contribution of the single tet `t` (with `M`'s coefficient). -/
noncomputable def tetContribution (M : Chain V) (t : Finset V) : Chain V :=
  bdry (Finsupp.single t (M t))

/-- Remove the tet `t` from the filling `M`. -/
noncomputable def removeTet (M : Chain V) (t : Finset V) : Chain V :=
  M - Finsupp.single t (M t)

/-- The tet faces currently on the boundary of `M`. -/
noncomputable def sharedFaces (M : Chain V) (t : Finset V) : Finset (Finset V) :=
  tetFaces t ∩ (bdry M).support

/-- The tet faces NOT on the boundary of `M` (they become new boundary faces). -/
noncomputable def exposedFaces (M : Chain V) (t : Finset V) : Finset (Finset V) :=
  tetFaces t \ sharedFaces M t

/-- A tet `t` is *eligible*: a genuine `4`-simplex of `M` with exactly two of its
faces on the boundary, those two carrying `t`'s own oriented coefficient. The
other two faces are then absent from the boundary (so removal cannot create a
`±2` coefficient — this is why eligibility is stronger than "two matching
faces"). -/
def EligibleTet (M : Chain V) (t : Finset V) : Prop :=
  t.card = 4 ∧ t ∈ M.support ∧ (sharedFaces M t).card = 2 ∧
    ∀ s ∈ sharedFaces M t, (bdry M) s = tetContribution M t s

/-- The flipped edge `cd` is already present in `σ` (the case-2 hook). -/
def FlipEdgePresent (σ : Finset (Finset V)) (f₃ f₄ : Finset V) : Prop :=
  f₃ ∩ f₄ ∈ edgesOf σ

/-! ### Tet-face combinatorics -/

lemma card_tetFaces {t : Finset V} (ht : t.card = 4) : (tetFaces t).card = 4 := by
  rw [tetFaces, Finset.card_powersetCard, ht]; decide

lemma erase_mem_tetFaces {t : Finset V} {x : V} (ht : t.card = 4) (hx : x ∈ t) :
    t.erase x ∈ tetFaces t := by
  refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
  · intro y hy; exact Finset.mem_of_mem_erase hy
  · rw [Finset.card_erase_of_mem hx, ht]

lemma sharedFaces_subset_tetFaces (M : Chain V) (t : Finset V) :
    sharedFaces M t ⊆ tetFaces t := fun _ hs => (Finset.mem_inter.mp hs).1

lemma exposedFaces_subset_tetFaces (M : Chain V) (t : Finset V) :
    exposedFaces M t ⊆ tetFaces t := fun _ hs => (Finset.mem_sdiff.mp hs).1

lemma exposedFaces_card_of_eligible {M : Chain V} {t : Finset V} (h : EligibleTet M t) :
    (exposedFaces M t).card = 2 := by
  rw [exposedFaces, Finset.card_sdiff_of_subset (sharedFaces_subset_tetFaces M t),
    card_tetFaces h.1, h.2.2.1]

/-! ### Boundary algebra of removal -/

lemma bdry_sub_single (M : Chain V) (t : Finset V) (c : ℤ) :
    bdry (M - Finsupp.single t c) = bdry M - c • bdryGen t := by
  rw [map_sub, bdry_single]

lemma bdry_removeTet (M : Chain V) (t : Finset V) :
    bdry (removeTet M t) = bdry M - tetContribution M t := by
  rw [removeTet, tetContribution, map_sub]

/-! ### `removeTet` as a chain -/

@[simp] lemma removeTet_apply_self (M : Chain V) (t : Finset V) : removeTet M t t = 0 := by
  simp [removeTet, Finsupp.single_eq_same]

lemma removeTet_apply_ne {M : Chain V} {t s : Finset V} (h : s ≠ t) :
    removeTet M t s = M s := by
  simp [removeTet, Finsupp.single_eq_of_ne h]

lemma support_removeTet_of_mem {M : Chain V} {t : Finset V} (ht : t ∈ M.support) :
    (removeTet M t).support = M.support.erase t := by
  ext s
  simp only [Finset.mem_erase, Finsupp.mem_support_iff]
  by_cases hst : s = t
  · subst hst; simp [removeTet_apply_self]
  · simp [removeTet_apply_ne hst, hst]

lemma simplicialChain_removeTet {M : Chain V} {t : Finset V} (hS : SimplicialChain M) :
    SimplicialChain (removeTet M t) := by
  intro s
  by_cases hst : s = t
  · subst hst; rw [removeTet_apply_self]; exact Or.inr (Or.inl rfl)
  · rw [removeTet_apply_ne hst]; exact hS s

lemma nrm_removeTet_add_one_of_simplicial {M : Chain V} {t : Finset V}
    (hS : SimplicialChain M) (ht : t ∈ M.support) :
    nrm (removeTet M t) + 1 = nrm M := by
  rw [nrm_eq_support_card_of_simplicial (simplicialChain_removeTet hS),
    nrm_eq_support_card_of_simplicial hS, support_removeTet_of_mem ht,
    Finset.card_erase_of_mem ht]
  have : 0 < M.support.card := Finset.card_pos.mpr ⟨t, ht⟩
  omega

lemma nrm_removeTet_of_simplicial {M : Chain V} {t : Finset V}
    (hS : SimplicialChain M) (ht : t ∈ M.support) :
    nrm (removeTet M t) = nrm M - 1 := by
  have := nrm_removeTet_add_one_of_simplicial hS ht; omega

end Taut
