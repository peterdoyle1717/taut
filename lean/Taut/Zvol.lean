import Taut.Chains

/-!
# Zvol, tautness, and Propositions 1–4 of "Taut fillings"

* `SubChain U M` — the paper's sub-multiset relation `U ⊂ M`.
* `Zvol X` — minimum L¹ norm of a filling of `X`.
* `IsTaut M` — `M` is an optimal filling of its boundary.
* Proposition 1 (`IsTaut.subChain`): sub-chains of taut chains are taut.
* Proposition 2 (`Zvol_add_deg_le`): `Zvol X + deg x X ≤ nrm X` for closed
  `X` (the paper's `Zvol(X) ≤ |X| − maxdeg(X)`, per vertex).
* Proposition 3 (`not_taut_complete_cone`): a taut chain contains no
  nontrivial complete cone.
* Proposition 4 (`IsTaut.no_internal_vertex`): a taut chain (in dimensions
  ≥ 1) has no internal vertices.  The dimension guard is necessary: in the
  augmented complex `c • [{x}]` is taut and `x` is internal to it.
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

/-! ## Sub-chains -/

/-- `U` is a sub-multiset of `M`: at every simplex the coefficient of `U`
lies between `0` and that of `M`. -/
def SubChain (U M : Chain V) : Prop :=
  ∀ s, (U s).natAbs + (M s - U s).natAbs = (M s).natAbs

lemma SubChain.support_subset {U M : Chain V} (h : SubChain U M) :
    U.support ⊆ M.support := by
  intro s hs
  rw [Finsupp.mem_support_iff] at hs ⊢
  intro hM
  have hh := h s
  rw [hM] at hh
  simp only [Int.natAbs_zero, zero_sub, Int.natAbs_neg] at hh
  exact hs (Int.natAbs_eq_zero.mp (by omega))

lemma SubChain.sub_support_subset {U M : Chain V} (h : SubChain U M) :
    (M - U).support ⊆ M.support := by
  intro s hs
  rw [Finsupp.mem_support_iff] at hs ⊢
  intro hM
  have hh := h s
  rw [hM] at hh
  simp only [Int.natAbs_zero, zero_sub, Int.natAbs_neg] at hh
  have : U s = 0 := Int.natAbs_eq_zero.mp (by omega)
  rw [Finsupp.sub_apply, hM, this, sub_zero] at hs
  exact hs rfl

/-- The norm splits along a sub-chain: `|U| + |M − U| = |M|`. -/
lemma SubChain.nrm_add_nrm_sub {U M : Chain V} (h : SubChain U M) :
    nrm U + nrm (M - U) = nrm M := by
  rw [nrm_eq_sum_subset h.support_subset,
    nrm_eq_sum_subset h.sub_support_subset, ← Finset.sum_add_distrib, nrm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.sub_apply]
  exact h s

lemma subChain_filter (p : Finset V → Prop) [DecidablePred p] (M : Chain V) :
    SubChain (M.filter p) M := by
  intro s
  rw [Finsupp.filter_apply]
  by_cases hp : p s
  · rw [if_pos hp, sub_self, Int.natAbs_zero, add_zero]
  · rw [if_neg hp, Int.natAbs_zero, sub_zero, zero_add]

lemma subChain_nbhd (x : V) (M : Chain V) : SubChain (nbhd x M) M :=
  subChain_filter _ M

/-! ## Zvol and tautness -/

/-- The filling volume: the least L¹ norm of a chain with boundary `X`. -/
noncomputable def Zvol (X : Chain V) : ℕ :=
  sInf {n | ∃ M : Chain V, bdry M = X ∧ nrm M = n}

/-- `M` is an optimal filling of its own boundary. -/
def IsTaut (M : Chain V) : Prop := nrm M = Zvol (bdry M)

lemma Zvol_le {X M : Chain V} (h : bdry M = X) : Zvol X ≤ nrm M :=
  Nat.sInf_le ⟨M, h, rfl⟩

lemma bdry_cone_of_closed {x : V} {X : Chain V} (hX : bdry X = 0) :
    bdry (cone x X) = X := by
  have h := bdry_cone_add_cone_bdry x X
  rw [hX, map_zero, add_zero] at h
  exact h

lemma exists_optimal_fill (W : Chain V) :
    ∃ M : Chain V, bdry M = bdry W ∧ nrm M = Zvol (bdry W) := by
  have hne : {n | ∃ M : Chain V, bdry M = bdry W ∧ nrm M = n}.Nonempty :=
    ⟨nrm W, W, rfl, rfl⟩
  obtain ⟨M, hM, hn⟩ := Nat.sInf_mem hne
  exact ⟨M, hM, hn⟩

/-- Proposition 1 (subtaut): a sub-chain of a taut chain is taut. -/
theorem IsTaut.subChain {M U : Chain V} (hM : IsTaut M) (hU : SubChain U M) :
    IsTaut U := by
  obtain ⟨W, hW, hWn⟩ := exists_optimal_fill U
  have hbd : bdry (M - U + W) = bdry M := by
    rw [map_add, map_sub, hW]
    abel
  have hle : Zvol (bdry M) ≤ nrm (M - U) + nrm W :=
    le_trans (Zvol_le hbd) (nrm_add_le _ _)
  have hsplit := hU.nrm_add_nrm_sub
  have h1 : Zvol (bdry U) ≤ nrm U := Zvol_le rfl
  rw [IsTaut] at hM ⊢
  omega

/-- Proposition 2 (maxdeg bound, per vertex): for closed `X`,
`Zvol X + deg x X ≤ nrm X`. -/
theorem Zvol_add_deg_le (x : V) {X : Chain V} (hX : bdry X = 0) :
    Zvol X + deg x X ≤ nrm X := by
  have h1 : Zvol X ≤ nrm (cone x X) := Zvol_le (bdry_cone_of_closed hX)
  have h2 := nrm_cone_add_deg x X
  omega

/-- Proposition 3 (nocone): a taut chain contains no nontrivial complete
cone.  Here `cone x W ⊂ M` with `W` closed, `x ∉ vert W` (i.e.
`deg x W = 0`), and nontriviality is witnessed by a vertex `x'` of `W`. -/
theorem not_taut_complete_cone {x x' : V} {W M : Chain V}
    (hM : IsTaut M) (hU : SubChain (cone x W) M) (hW : bdry W = 0)
    (hx : deg x W = 0) (hx' : deg x' W ≠ 0) : False := by
  have hUt : IsTaut (cone x W) := hM.subChain hU
  have hbd : bdry (cone x W) = W := bdry_cone_of_closed hW
  have h1 := nrm_cone_add_deg x W
  have h2 := Zvol_add_deg_le x' hW
  rw [IsTaut, hbd] at hUt
  omega

/-- Proposition 4 (nointernal): a taut chain all of whose simplices have
at least two vertices has no internal vertices. -/
theorem IsTaut.no_internal_vertex {M : Chain V} (hM : IsTaut M) {x : V}
    (hdim : ∀ s ∈ M.support, 2 ≤ s.card)
    (hxM : x ∈ vert M) (hxB : x ∉ vert (bdry M)) : False := by
  set W := lk x M with hWdef
  have hUc : cone x W = nbhd x M := cone_lk x M
  have hx : deg x W = 0 := by rw [deg, hWdef, nbhd_lk, nrm_zero]
  have hWfree : nbhd x W = 0 := nbhd_lk x M
  have hWb : nbhd x (bdry W) = 0 := nbhd_bdry_eq_zero hWfree
  have hcb : cone x (bdry W) = 0 := by
    have hhom := bdry_cone_add_cone_bdry x W
    have h0 : nbhd x (bdry (cone x W)) = 0 := by
      rw [hUc, nbhd_bdry_nbhd, nbhd_eq_zero_iff.mpr hxB]
    have happ := congrArg (nbhd x) hhom
    rw [nbhd_add, h0, zero_add, nbhd_cone, hWfree] at happ
    exact happ
  have hWclosed : bdry W = 0 := by
    have h := eq_nbhd_of_cone_eq_zero hcb
    rw [hWb] at h
    exact h
  obtain ⟨s, hs, hxs⟩ := mem_vert.mp hxM
  have hcard := hdim s hs
  have hne : (s.erase x).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hxs]
    omega
  obtain ⟨y, hy⟩ := hne
  have hyW : y ∈ vert W := by
    have happ : cone x W s = M s := by rw [hUc, nbhd_apply, if_pos hxs]
    rw [cone_apply, if_pos hxs] at happ
    have hMs : M s ≠ 0 := Finsupp.mem_support_iff.mp hs
    have hWne : W (s.erase x) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at happ
      exact hMs happ.symm
    exact mem_vert.mpr ⟨s.erase x, Finsupp.mem_support_iff.mpr hWne, hy⟩
  have hy' : deg y W ≠ 0 := fun h => (deg_eq_zero_iff.mp h) hyW
  exact not_taut_complete_cone hM (hUc ▸ subChain_nbhd x M) hWclosed hx hy'

end Taut
