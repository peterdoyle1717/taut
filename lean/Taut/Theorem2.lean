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

/-! ### M21b: the edge-flip sign bookkeeping (architect: codex 019ec271) -/

/-- `∂` of a tet's basis vector, read off at one of its own faces, is the sign. -/
lemma bdryGen_apply_erase_of_mem {t : Finset V} {x : V} (hx : x ∈ t) :
    bdryGen t (t.erase x) = sgn x t := by
  rw [bdryGen, Finset.sum_apply']
  have key : ∀ y ∈ t, y ≠ x →
      (sgn y t • Finsupp.single (t.erase y) (1 : ℤ)) (t.erase x) = 0 := by
    intro y hy hyx
    have hne : t.erase x ≠ t.erase y := by
      intro hc
      have hmem : y ∈ t.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
      rw [hc] at hmem
      exact Finset.notMem_erase y t hmem
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hne, smul_zero]
  rw [Finset.sum_eq_single_of_mem x hx key, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

/-- The tet's contribution at one of its faces is `M t · sgn`. -/
lemma tetContribution_apply_erase_of_mem {M : Chain V} {t : Finset V} {x : V} (hx : x ∈ t) :
    tetContribution M t (t.erase x) = M t * sgn x t := by
  rw [tetContribution, bdry_single, Finsupp.smul_apply, bdryGen_apply_erase_of_mem hx,
    smul_eq_mul]

/-- Off the tet's four faces, the tet contributes nothing. -/
lemma tetContribution_apply_of_not_mem_tetFaces {M : Chain V} {t s : Finset V}
    (ht : t.card = 4) (hs : s ∉ tetFaces t) : tetContribution M t s = 0 := by
  have hz : bdryGen t s = 0 := by
    rw [bdryGen, Finset.sum_apply']
    apply Finset.sum_eq_zero
    intro y hy
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne
      (fun hc => (hc ▸ hs) (erase_mem_tetFaces ht hy)), smul_zero]
  rw [tetContribution, bdry_single, Finsupp.smul_apply, hz, smul_zero]

/-- Every tet face is `t.erase y` for a (unique) vertex `y ∈ t`. -/
lemma exists_erase_eq_of_mem_tetFaces {t s : Finset V} (ht : t.card = 4)
    (hs : s ∈ tetFaces t) : ∃ y, y ∈ t ∧ s = t.erase y := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
  have hd : (t \ s).card = 1 := by rw [Finset.card_sdiff_of_subset hsub, ht, hcard]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hd
  obtain ⟨hyt, hys⟩ := Finset.mem_sdiff.mp (hy ▸ Finset.mem_singleton_self y)
  refine ⟨y, hyt, Finset.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)⟩
  · exact Finset.mem_erase.mpr ⟨fun hzy => hys (hzy ▸ hz), hsub hz⟩
  · rw [Finset.mem_erase] at hz
    by_contra hzs
    exact hz.1 (by have := hy ▸ Finset.mem_sdiff.mpr ⟨hz.2, hzs⟩; rwa [Finset.mem_singleton] at this)

/-- On a tet face the contribution is nonzero (the tet is genuinely present). -/
lemma tetContribution_ne_zero_of_mem_tetFaces {M : Chain V} {t s : Finset V}
    (ht : t.card = 4) (htM : M t ≠ 0) (hs : s ∈ tetFaces t) : tetContribution M t s ≠ 0 := by
  obtain ⟨y, hyt, rfl⟩ := exists_erase_eq_of_mem_tetFaces ht hs
  rw [tetContribution_apply_erase_of_mem hyt]
  exact mul_ne_zero htM (by rw [sgn]; exact pow_ne_zero _ (by norm_num))

/-- An exposed face is absent from the current boundary. -/
lemma bdry_apply_eq_zero_of_mem_exposedFaces {M : Chain V} {t s : Finset V}
    (hs : s ∈ exposedFaces M t) : (bdry M) s = 0 := by
  rw [exposedFaces, Finset.mem_sdiff, sharedFaces, Finset.mem_inter] at hs
  by_contra h0
  exact hs.2 ⟨hs.1, Finsupp.mem_support_iff.mpr h0⟩

/-- **The flip on supports.** Removing an eligible tet drops its two shared
boundary faces and adds its two exposed ones — the paper's `ab → cd` flip. -/
theorem support_flipBoundary_of_eligible {M : Chain V} {t : Finset V} (h : EligibleTet M t) :
    (bdry (removeTet M t)).support
      = ((bdry M).support \ sharedFaces M t) ∪ exposedFaces M t := by
  obtain ⟨ht4, htM, _, hshared⟩ := h
  have htM' : M t ≠ 0 := Finsupp.mem_support_iff.mp htM
  ext s
  simp only [Finsupp.mem_support_iff, bdry_removeTet, Finsupp.sub_apply, Finset.mem_union,
    Finset.mem_sdiff]
  by_cases hsf : s ∈ tetFaces t
  · by_cases hss : s ∈ sharedFaces M t
    · rw [hshared s hss, sub_self]
      constructor
      · intro h; exact absurd rfl h
      · rintro (⟨_, hns⟩ | hex)
        · exact absurd hss hns
        · exact absurd (Finset.mem_sdiff.mp hex).2 (not_not.mpr hss)
    · have hse : s ∈ exposedFaces M t := Finset.mem_sdiff.mpr ⟨hsf, hss⟩
      rw [bdry_apply_eq_zero_of_mem_exposedFaces hse, zero_sub, neg_ne_zero]
      constructor
      · intro _; exact Or.inr hse
      · intro _; exact tetContribution_ne_zero_of_mem_tetFaces ht4 htM' hsf
  · rw [tetContribution_apply_of_not_mem_tetFaces ht4 hsf, sub_zero]
    have hns : s ∉ sharedFaces M t := fun hc => hsf (sharedFaces_subset_tetFaces M t hc)
    have hne : s ∉ exposedFaces M t := fun hc => hsf (exposedFaces_subset_tetFaces M t hc)
    constructor
    · intro h; exact Or.inl ⟨h, hns⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact absurd h hne

/-- An eligible tet of a simplicial filling carries coefficient `±1`. -/
lemma tet_coeff_eq_pm_one_of_eligible {M : Chain V} {t : Finset V}
    (hS : SimplicialChain M) (h : EligibleTet M t) : M t = 1 ∨ M t = -1 := by
  have htM : M t ≠ 0 := Finsupp.mem_support_iff.mp h.2.1
  rcases hS t with h1 | h0 | h1
  · exact Or.inr h1
  · exact absurd h0 htM
  · exact Or.inl h1

/-- On a tet face, a `±1`-coefficient tet contributes `±1`. -/
lemma tetContribution_eq_pm_one_of_mem_tetFaces {M : Chain V} {t s : Finset V}
    (ht : t.card = 4) (hpm : M t = 1 ∨ M t = -1) (hs : s ∈ tetFaces t) :
    tetContribution M t s = 1 ∨ tetContribution M t s = -1 := by
  obtain ⟨y, hyt, rfl⟩ := exists_erase_eq_of_mem_tetFaces ht hs
  rw [tetContribution_apply_erase_of_mem hyt]
  have hsgn : sgn y t = 1 ∨ sgn y t = -1 := mul_self_eq_one_iff.mp (sgn_mul_self y t)
  rcases hpm with hm | hm <;> rcases hsgn with hs1 | hs1 <;> rw [hm, hs1] <;> decide

/-- **The flip on unit chains.** If `bdry M` is a unit chain on `σ`, then after
removing an eligible tet the new boundary is a unit chain on the flipped sphere
`(σ \ sharedFaces) ∪ exposedFaces`. -/
theorem unitOn_flipBoundary_of_eligible {M : Chain V} {σ : Finset (Finset V)} {t : Finset V}
    (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M) (h : EligibleTet M t) :
    UnitOn (bdry (removeTet M t)) ((σ \ sharedFaces M t) ∪ exposedFaces M t) := by
  have ht4 := h.1
  have hpm := tet_coeff_eq_pm_one_of_eligible hS h
  refine ⟨by rw [support_flipBoundary_of_eligible h, hU.1], ?_⟩
  intro s hs
  rw [Finset.mem_union] at hs
  rcases hs with hs | hs
  · rw [Finset.mem_sdiff] at hs
    have hssupp : s ∈ (bdry M).support := by rw [hU.1]; exact hs.1
    have hsf : s ∉ tetFaces t := fun hcon =>
      hs.2 (Finset.mem_inter.mpr ⟨hcon, hssupp⟩)
    rw [bdry_removeTet, Finsupp.sub_apply, tetContribution_apply_of_not_mem_tetFaces ht4 hsf,
      sub_zero]
    exact hU.2 s hs.1
  · rw [bdry_removeTet, Finsupp.sub_apply, bdry_apply_eq_zero_of_mem_exposedFaces hs, zero_sub]
    rcases tetContribution_eq_pm_one_of_mem_tetFaces ht4 hpm
      (exposedFaces_subset_tetFaces M t hs) with h1 | h1 <;> rw [h1] <;> decide

/-! ## M23: the oriented separation bridge (architect: codex 019ec2e0)

For the *edge-join* case-2 of the induction, the side-filter of a closed unit
cycle is again closed — because the two sides share a single edge, and a closed
chain supported on one edge must vanish. This is the orientation/coherence fact
the paper hides; it is what lets `IsTaut.splits` apply to the integral split. -/

/-- Filtering a chain by `P` does not change a boundary coefficient `u` for which
no `¬P` generator contributes. -/
lemma bdry_filter_apply_eq_bdry_of_no_cross {X : Chain V} {P : Finset V → Prop}
    [DecidablePred P] {u : Finset V}
    (hvanish : ∀ s ∈ X.support, ¬ P s → bdryGen s u = 0) :
    bdry (X.filter P) u = bdry X u := by
  have hz : bdry (X.filter (fun s => ¬ P s)) u = 0 := by
    rw [bdry_apply_eq_sum]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at ht
    rw [hvanish t ht.1 ht.2, mul_zero]
  have hsum : bdry (X.filter P) u + bdry (X.filter (fun s => ¬ P s)) u = bdry X u := by
    rw [← Finsupp.add_apply, ← map_add, Finsupp.filter_pos_add_filter_neg]
  rw [hz, add_zero] at hsum; exact hsum

/-- **The edge-join closed-filter lemma.** If `X` is a closed chain whose faces
are triangles each lying on the `A`-side or the `B`-side, and `A ∩ B` is a single
edge, then the `A`-side filter of `X` is again closed — its boundary is a closed
chain supported on the single shared edge `A ∩ B`, hence zero
(`eq_zero_of_closed_supp_card_eq`). A *triangle* cut would instead leave the
filter open; the edge-join is exactly what makes case 2 work. -/
lemma bdry_filter_subset_eq_zero_of_inter_card_two {X : Chain V} {A B : Finset V}
    (hXc : bdry X = 0) (hXsupp : ∀ s ∈ X.support, s.card = 3 ∧ (s ⊆ A ∨ s ⊆ B))
    (hAB2 : (A ∩ B).card = 2) :
    bdry (X.filter (fun s => s ⊆ A)) = 0 := by
  classical
  refine eq_zero_of_closed_supp_card_eq (W := A ∩ B) (k := 2) (by norm_num) ?_ hAB2
    (bdry_bdry _)
  intro u hu
  have hfaces : ∀ s ∈ (X.filter (fun s => s ⊆ A)).support, s ⊆ A ∧ s.card = 2 + 1 := by
    intro s hs
    rw [Finsupp.support_filter, Finset.mem_filter] at hs
    exact ⟨hs.2, by rw [(hXsupp s hs.1).1]⟩
  obtain ⟨huA, huc⟩ := bdry_supp_of_supp hfaces u hu
  have huB : u ⊆ B := by
    by_contra hcon
    have hcross : bdry (X.filter (fun s => s ⊆ A)) u = bdry X u := by
      refine bdry_filter_apply_eq_bdry_of_no_cross fun s hsX hsA => ?_
      by_contra hbg
      obtain ⟨w, _, hue⟩ := exists_facet_of_bdryGen_ne_zero hbg
      exact hcon (hue ▸ (Finset.erase_subset w s).trans (((hXsupp s hsX).2).resolve_left hsA))
    rw [hXc, Finsupp.coe_zero, Pi.zero_apply] at hcross
    exact Finsupp.mem_support_iff.mp hu hcross
  exact ⟨Finset.subset_inter huA huB, huc⟩

end Taut
