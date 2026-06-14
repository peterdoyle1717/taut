import Taut.Theorem2

/-!
# Eligible tets (M25, architect: codex 019ec428)

For the Theorem-2 induction we need, in a prime (no degree-3 vertex) taut
filling, an *eligible* tet — one sharing two oriented faces with the boundary.
The route (paper §"Filling a triangulation of the 2-sphere", the 2-to-1 count):

* every boundary face `α` (`∂M α = ±1`) is a *properly oriented* face of some tet
  of `M` — `∂M α` is a sum of `{-1,0,1}` tet contributions, so one of them equals
  `∂M α`. The tet is chosen, not unique;
* the choice map `σ → M.support` has fibers `⊆ sharedFaces`, hence (no deg-3)
  `≤ 2`; a *double* fiber is an eligible tet;
* a count + Prop 2 (`Zvol_add_deg_le`) forces a double fiber to exist.

M25a here: the face→tet layer and `exists_eligibleTet` modulo the
`sharedFaces ≤ 2` bound (the hard deg-3 lemma is M25a').
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- The tet's contribution at a face, unfolded: `M t · ∂(t)` at that face. -/
lemma tetContribution_apply (M : Chain V) (t α : Finset V) :
    tetContribution M t α = M t * bdryGen t α := by
  rw [tetContribution, bdry_single, Finsupp.smul_apply, smul_eq_mul]

/-- `∂(t)` evaluated at any face is `-1`, `0`, or `1` (a sign, or absent). -/
lemma bdryGen_apply_mem_pm (t α : Finset V) :
    bdryGen t α = -1 ∨ bdryGen t α = 0 ∨ bdryGen t α = 1 := by
  by_cases h : ∃ x ∈ t, α = t.erase x
  · obtain ⟨x, hx, rfl⟩ := h
    rw [bdryGen_apply_erase_of_mem hx]
    rcases mul_self_eq_one_iff.mp (sgn_mul_self x t) with h1 | h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inl h1
  · push_neg at h
    refine Or.inr (Or.inl ?_)
    rw [bdryGen, Finset.sum_apply']
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (h x hx), smul_zero]

/-- `α` is a *properly oriented boundary face* of the tet `t`: a genuine tet of
`M` whose contribution at `α` accounts for the whole boundary coefficient. -/
def ProperBoundaryFaceTet (M : Chain V) (α t : Finset V) : Prop :=
  t ∈ M.support ∧ α ∈ tetFaces t ∧ (bdry M) α = tetContribution M t α

/-- **Every boundary face is properly oriented by some tet.** `∂M α = ±1` is a
sum of `{-1,0,1}` tet contributions, so one of them equals `∂M α`. -/
lemma exists_properBoundaryFaceTet {M : Chain V} (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4) {α : Finset V}
    (hαpm : (bdry M) α = 1 ∨ (bdry M) α = -1) :
    ∃ t, ProperBoundaryFaceTet M α t := by
  have hbound : ∀ t ∈ M.support, M t * bdryGen t α = -1 ∨ M t * bdryGen t α = 0
      ∨ M t * bdryGen t α = 1 := by
    intro t _
    rcases hS t with hm | hm | hm <;> rcases bdryGen_apply_mem_pm t α with hg | hg | hg <;>
      rw [hm, hg] <;> decide
  have hsum : bdry M α = ∑ t ∈ M.support, M t * bdryGen t α := bdry_apply_eq_sum M α
  have hkey : ∃ t ∈ M.support, M t * bdryGen t α = bdry M α := by
    by_contra hcon
    push_neg at hcon
    rcases hαpm with hp | hp
    · have hle : (∑ t ∈ M.support, M t * bdryGen t α) ≤ 0 := by
        refine Finset.sum_nonpos fun t ht => ?_
        rcases hbound t ht with h | h | h
        · rw [h]; decide
        · rw [h]
        · exact absurd (h.trans hp.symm) (hcon t ht)
      rw [← hsum, hp] at hle; exact absurd hle (by decide)
    · have hge : (0 : ℤ) ≤ ∑ t ∈ M.support, M t * bdryGen t α := by
        refine Finset.sum_nonneg fun t ht => ?_
        rcases hbound t ht with h | h | h
        · exact absurd (h.trans hp.symm) (hcon t ht)
        · rw [h]
        · rw [h]; decide
      rw [← hsum, hp] at hge; exact absurd hge (by decide)
  obtain ⟨t, ht, hval⟩ := hkey
  refine ⟨t, ht, ?_, ?_⟩
  · -- α ∈ tetFaces t : bdryGen t α ≠ 0
    have hgne : bdryGen t α ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hval
      rcases hαpm with hp | hp <;> rw [hp] at hval <;> exact absurd hval.symm (by decide)
    obtain ⟨w, hw, hαe⟩ := exists_facet_of_bdryGen_ne_zero hgne
    exact hαe ▸ erase_mem_tetFaces (hPure t ht) hw
  · rw [tetContribution_apply, hval]

/-- **One eligible tet exists** (M25a), given the no-degree-3 face bound
`sharedFaces ≤ 2`. Two boundary faces collide under the face→tet choice map
(there are more faces than tets, by Prop 2), so their common tet has two shared,
coefficient-matched faces — an eligible tet. -/
theorem exists_eligibleTet {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M) (hT : IsTaut M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hShared2 : ∀ t ∈ M.support, (sharedFaces M t).card ≤ 2) :
    ∃ t, EligibleTet M t := by
  classical
  have hcov : ∀ α ∈ σ, ∃ t, ProperBoundaryFaceTet M α t := fun α hα =>
    exists_properBoundaryFaceTet hS hPure (hU.2 α hα)
  let f : {α // α ∈ σ} → {t // t ∈ M.support} := fun α =>
    ⟨Classical.choose (hcov α.1 α.2), (Classical.choose_spec (hcov α.1 α.2)).1⟩
  have hfspec : ∀ α : {α // α ∈ σ}, ProperBoundaryFaceTet M α.1 (f α).1 := fun α =>
    Classical.choose_spec (hcov α.1 α.2)
  -- Prop 2: more boundary faces than tets
  have hcard : M.support.card < σ.card := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ vert (bdry M) := by
      obtain ⟨s, hs⟩ := hσ.nonempty
      obtain ⟨y, hy⟩ : s.Nonempty := by rw [← Finset.card_pos, hσ.pure s hs]; omega
      exact ⟨y, mem_vert.mpr ⟨s, hU.1 ▸ hs, hy⟩⟩
    have hdeg : 1 ≤ deg x (bdry M) := Nat.pos_of_ne_zero fun h => (deg_eq_zero_iff.mp h) hx
    have h2 := Zvol_add_deg_le x (bdry_bdry M)
    rw [← hT, UnitOn.nrm_eq hU, nrm_eq_support_card_of_simplicial hS] at h2
    omega
  -- two faces collide
  obtain ⟨α₁, _, α₂, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset {α // α ∈ σ}))
      (t := (Finset.univ : Finset {t // t ∈ M.support})) (f := f)
      (by rw [Finset.card_univ, Finset.card_univ, Fintype.card_coe, Fintype.card_coe]; exact hcard)
      (fun a _ => Finset.mem_univ _)
  have ht : (f α₁).1 ∈ M.support := (f α₁).2
  have hαne : (α₁ : Finset V) ≠ (α₂ : Finset V) := fun h => hne (Subtype.ext h)
  have htt : (f α₁).1 = (f α₂).1 := congrArg Subtype.val heq
  have hα₁sh : (α₁ : Finset V) ∈ sharedFaces M (f α₁).1 :=
    Finset.mem_inter.mpr ⟨(hfspec α₁).2.1, hU.1 ▸ α₁.2⟩
  have hα₂sh : (α₂ : Finset V) ∈ sharedFaces M (f α₁).1 :=
    Finset.mem_inter.mpr ⟨htt ▸ (hfspec α₂).2.1, hU.1 ▸ α₂.2⟩
  have hsub : ({(α₁ : Finset V), (α₂ : Finset V)} : Finset (Finset V)) ⊆ sharedFaces M (f α₁).1 := by
    intro s hs; rw [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl; exacts [hα₁sh, hα₂sh]
  have hc2 : (sharedFaces M (f α₁).1).card = 2 := by
    have hge : 2 ≤ (sharedFaces M (f α₁).1).card :=
      (Finset.card_pair hαne).symm.le.trans (Finset.card_le_card hsub)
    have := hShared2 _ ht; omega
  refine ⟨(f α₁).1, hPure _ ht, ht, hc2, fun s hs => ?_⟩
  have hsharedEq : sharedFaces M (f α₁).1 = {(α₁ : Finset V), (α₂ : Finset V)} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hc2, Finset.card_pair hαne])).symm
  rw [hsharedEq, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact (hfspec α₁).2.2
  · rw [htt]; exact (hfspec α₂).2.2

end Taut
