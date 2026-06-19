import Taut.CleanShelling
import Taut.PrimeStep

namespace Taut

variable {V : Type*} [LinearOrder V]

/-- **Theorem 3 (core), clean-shelling route — SKELETON.** Mirror of `theorem3_core`,
carrying `FreelyCleanShellable M.support σ` instead of the boundary
`FreelyShellable M.support σ` (and without the pseudomanifold conjunct). The three
reduction steps are taken as explicit hypotheses: the base case is discharged
(`base_free_clean`), while the degree-3 and prime steps remain the named, unproven
obligations. The strong-induction plumbing is identical to `theorem3_core`; only the
conclusion type changed, which the proof body never mentions. -/
theorem theorem3_core_clean
    (base_clean : ∀ (σ : Finset (Finset V)) (X M : Chain V), IsSphere2 σ → UnitOn X σ →
      bdry M = X → IsTaut M → SimplicialChain M → (vertsOf σ).card ≤ 4 →
      FreelyCleanShellable M.support σ)
    (deg3_step_clean : ∀ (σ : Finset (Finset V)) (X M : Chain V), IsSphere2 σ →
      4 < (vertsOf σ).card → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M →
      SimplicialChain M → HasDegree3Vertex σ →
      (∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
        UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
        FreelyCleanShellable M'.support σ') →
      FreelyCleanShellable M.support σ)
    (prime_step_clean : ∀ (σ : Finset (Finset V)) (X M : Chain V), IsSphere2 σ →
      4 < (vertsOf σ).card → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M →
      SimplicialChain M → NoDegree3Vertex σ →
      (∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
        UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
        FreelyCleanShellable M'.support σ') →
      FreelyCleanShellable M.support σ)
    {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ) (hU : UnitOn X σ)
    (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M) :
    FreelyCleanShellable M.support σ := by
  suffices H : ∀ N, ∀ (σ : Finset (Finset V)) (X M : Chain V), nrm M = N → IsSphere2 σ →
      UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
      FreelyCleanShellable M.support σ by
    exact H (nrm M) σ X M rfl hσ hU hXc hMX hT hS
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro σ X M hN hσ hU hXc hMX hT hS
    by_cases hv : (vertsOf σ).card ≤ 4
    · exact base_clean σ X M hσ hU hMX hT hS hv
    · push_neg at hv
      by_cases hd3 : HasDegree3Vertex σ
      · refine deg3_step_clean σ X M hσ hv hU hXc hMX hT hS hd3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'
      · have hno3 : NoDegree3Vertex σ := fun v hvv hcard => hd3 ⟨v, hvv, hcard⟩
        refine prime_step_clean σ X M hσ hv hU hXc hMX hT hS hno3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'

/-- **base_free_clean** (the discharged base hole of `theorem3_core_clean`): a taut
filling of a 2-sphere on ≤ 4 vertices is a *free clean* sticker ball — it is a single
tetrahedron (`freelyCleanShellable_singleton`). Reuses the Aleph base lemmas verbatim;
only the final step changes from `freelyShellable_singleton` to
`freelyCleanShellable_singleton`. -/
theorem base_free_clean (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M)
    (hv : (vertsOf σ).card ≤ 4) : FreelyCleanShellable M.support σ := by
  have hcard : (vertsOf σ).card = 4 := aleph_base_verts_card_eq_four hσ hv
  have hσeq : σ = (vertsOf σ).powersetCard 3 := aleph_base_sphere_eq_powersetCard3 hσ hcard
  have hsuppInfo := aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
  have hne := aleph_base_support_nonempty hσ hU hMX
  have hsupp : M.support = {vertsOf σ} :=
    aleph_base_support_eq_singleton_of_four_vertices hcard hsuppInfo hne
  rw [hσeq, hsupp]   -- hσeq first: σ occurs only as the 2nd arg, so no over-rewrite of `vertsOf σ`
  exact freelyCleanShellable_singleton hcard

/-! ## Degree-3 star glue: one reusable `CleanGlueStep` constructor

For the degree-3 reduction the new tet is the star `starTet σ v = insert v γ`
(with `γ = linkVerts σ v`, `|γ| = 3`) glued onto the remainder tet-set `τ`, where
`v` is absent from every remainder tet and `γ` sits inside a (unique) remainder
tet `t₀`.  Under those geometric facts every `CleanGlueStep` field is discharged
mechanically: the only quantitative input is `faceCount τ γ ≤ 1` (carried from the
PM bound at the call site); the link/clean fields all come from the apex `t₀`. -/

/-- Apex membership for the edge-link: `w` is an apex of `e` in `τ` iff some tet of
`τ` contains both `e` and `w`, with `w ∉ e`. -/
private lemma mem_edgeLinkVerts_iff {τ : Finset (Finset V)} {e : Finset V} {w : V} :
    w ∈ edgeLinkVerts τ e ↔ (∃ t ∈ τ, e ⊆ t ∧ w ∈ t) ∧ w ∉ e := by
  simp only [edgeLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter]
  constructor
  · rintro ⟨⟨t, ⟨ht, hsub⟩, hwt⟩, hwe⟩; exact ⟨⟨t, ht, hsub, hwt⟩, hwe⟩
  · rintro ⟨⟨t, ht, hsub, hwt⟩, hwe⟩; exact ⟨⟨t, ⟨ht, hsub⟩, hwt⟩, hwe⟩

/-- Apex membership for the vertex-link: `w` is an apex of `x` in `τ` iff some tet of
`τ` contains both `x` and `w`, with `w ≠ x`. -/
private lemma mem_vertexLinkVerts_iff {τ : Finset (Finset V)} {x w : V} :
    w ∈ vertexLinkVerts τ x ↔ (∃ t ∈ τ, x ∈ t ∧ w ∈ t) ∧ w ≠ x := by
  simp only [vertexLinkVerts, Finset.mem_sdiff, mem_vertsOf, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨t, ⟨ht, hxt⟩, hwt⟩, hwx⟩; exact ⟨⟨t, ht, hxt, hwt⟩, hwx⟩
  · rintro ⟨⟨t, ht, hxt, hwt⟩, hwx⟩; exact ⟨⟨t, ⟨ht, hxt⟩, hwt⟩, hwx⟩

/-- **One clean glue step for the degree-3 star tet onto a fixed remainder.**
The new tet `starTet σ v = insert v γ` (`γ = linkVerts σ v`, three apexes) glues
onto the remainder tet-set `τ`, in which `v` is absent (`hvτ`) and `γ` lies in some
tet `t₀` (`ht₀`).  Given the boundary glue (`hweak`), freshness (`hTnot`), the
shared boundary face `γ` (`hγB`), and the single quantitative carry
`faceCount τ γ ≤ 1` (`hγcount`), all six `CleanGlueStep` fields are discharged: the
triangle/clean/link fields reduce to "`v ∉` any remainder tet" and "the third
γ-vertex is a common apex". -/
lemma cleanGlueStep_star_of_remainder {σ : Finset (Finset V)} {v : V} {γ : Finset V}
    {τ B B' : Finset (Finset V)}
    (hγ : γ = linkVerts σ v) (hγ3 : (linkVerts σ v).card = 3)
    (hstar4 : (starTet σ v).card = 4)
    (hweak : GlueStep (starTet σ v) B B')
    (hTnot : starTet σ v ∉ τ)
    (hvτ : ∀ t ∈ τ, v ∉ t)
    (ht₀ : ∃ t₀ ∈ τ, γ ⊆ t₀)
    (hγcount : faceCount τ γ ≤ 1)
    (hγB : γ ∈ tetFaces (starTet σ v) ∩ B) :
    CleanGlueStep (starTet σ v) τ B B' := by
  -- `starTet σ v = insert v γ`, with `v ∉ γ` and `|γ| = 3`.
  have hstar : starTet σ v = insert v γ := by rw [starTet, hγ]
  have hγcard : γ.card = 3 := hγ ▸ hγ3
  have hvγ : v ∉ γ := by
    intro hv
    rw [hstar, Finset.insert_eq_self.mpr hv] at hstar4
    omega
  -- A card-3 subset `f ⊆ insert v γ` with `v ∉ f` is exactly `γ`.
  have face_eq_γ : ∀ {f : Finset V}, f ⊆ starTet σ v → f.card = 3 → v ∉ f → f = γ := by
    intro f hf hf3 hvf
    have hfγ : f ⊆ γ := by
      intro x hxf
      have : x ∈ insert v γ := hstar ▸ hf hxf
      rcases Finset.mem_insert.mp this with rfl | hxγ
      · exact absurd hxf hvf
      · exact hxγ
    exact Finset.eq_of_subset_of_card_le hfγ (by rw [hγcard, hf3])
  obtain ⟨t₀, ht₀τ, hγt₀⟩ := ht₀
  refine
    { weak := hweak
      newTet := hTnot
      clean := ?_
      hpmc := ?_
      helc := ?_
      hvlc := ?_ }
  · -- clean: a face of `t` already in some τ-tet has `v ∉ f`, so `f ⊆ γ`; use `γ`.
    intro f hf ⟨s, hsτ, hfs⟩
    have hvf : v ∉ f := fun hvf => hvτ s hsτ (hfs hvf)
    have hfγ : f ⊆ γ := by
      intro x hxf
      have : x ∈ insert v γ := hstar ▸ hf hxf
      rcases Finset.mem_insert.mp this with rfl | hxγ
      · exact absurd hxf hvf
      · exact hxγ
    exact ⟨γ, hγB, hfγ⟩
  · -- hpmc: a card-3 face is either `γ` (count ≤ 1 by hγcount) or contains `v` (count 0).
    intro f hf3 hf
    by_cases hvf : v ∈ f
    · -- no τ-tet contains `f` (else it contains `v`), so the count is 0.
      have : faceCount τ f = 0 := faceCount_eq_zero (fun s hsτ hfs => hvτ s hsτ (hfs hvf))
      omega
    · rw [face_eq_γ hf hf3 hvf]; exact hγcount
  · -- helc: edge `e ⊆ t`. If `v ∈ e`, the link is empty; else the third γ-vertex is an apex.
    intro e he he2
    by_cases hve : v ∈ e
    · -- any apex would give a τ-tet containing `e ∋ v`, contra `hvτ`.
      left
      apply edgeLinkVerts_eq_empty
      intro s hsτ hes
      exact hvτ s hsτ (hes hve)
    · right
      -- `e ⊆ γ` (its two vertices avoid `v`), so `γ = e ∪ {w}` for the third vertex `w`.
      have heγ : e ⊆ γ := by
        intro x hxe
        have : x ∈ insert v γ := hstar ▸ he hxe
        rcases Finset.mem_insert.mp this with rfl | hxγ
        · exact absurd hxe hve
        · exact hxγ
      -- `γ \ e` is a single vertex `w`, lying in `t₀` together with `e`.
      have hcard : (γ \ e).card = 1 := by
        rw [Finset.card_sdiff_of_subset heγ, hγcard, he2]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
      have hwγe : w ∈ γ \ e := hw ▸ Finset.mem_singleton_self w
      rw [Finset.mem_sdiff] at hwγe
      obtain ⟨hwγ, hwe⟩ := hwγe
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · -- `w ∈ starTet σ v \ e`.
        rw [Finset.mem_sdiff, hstar]
        exact ⟨Finset.mem_insert_of_mem hwγ, hwe⟩
      · -- `w` is an apex of `e` in `τ`: `e ⊆ t₀` and `w ∈ t₀`.
        rw [mem_edgeLinkVerts_iff]
        exact ⟨⟨t₀, ht₀τ, heγ.trans hγt₀, hγt₀ hwγ⟩, hwe⟩
  · -- hvlc: vertex `x ∈ t`. If `x = v`, the link is empty; else another γ-vertex is an apex.
    intro x hx
    rw [hstar, Finset.mem_insert] at hx
    rcases hx with rfl | hxγ
    · -- `x = v`: no τ-tet contains `v`.
      left
      exact vertexLinkVerts_eq_empty hvτ
    · right
      -- `x ∈ γ`; pick another γ-vertex `w ≠ x` (|γ| = 3 ≥ 2), both in `t₀`.
      have hxv : x ≠ v := fun h => hvγ (h ▸ hxγ)
      have hcard : (γ \ {x}).card = 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hxγ), hγcard,
          Finset.card_singleton]
      have hne : (γ \ {x}).Nonempty := by rw [← Finset.card_pos, hcard]; omega
      obtain ⟨w, hw⟩ := hne
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
      obtain ⟨hwγ, hwx⟩ := hw
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · -- `w ∈ starTet σ v \ {x}`.
        rw [Finset.mem_sdiff, Finset.mem_singleton, hstar]
        exact ⟨Finset.mem_insert_of_mem hwγ, hwx⟩
      · -- `w` is a vertex-apex of `x` in `τ`: both `x, w ∈ t₀`.
        rw [mem_vertexLinkVerts_iff]
        exact ⟨⟨t₀, ht₀τ, hγt₀ hxγ, hγt₀ hwγ⟩, hwx⟩

/-! ## τ-extension of the link-compat fields (degree-3 star-start glue)

The clean STAR-START reduction (gluing the link tets onto `insert (starTet σ v) τ`
in turn) needs the `helc`/`hvlc` link-compat fields preserved as `starTet σ v` is
adjoined to the accumulated set.  Both follow from two structural facts about the
apex sets: they are monotone in `τ`, and the extra tet `starTet σ v` supplies an
apex for `e` only when `e ⊆ γ` (resp. for `x` only when `x ∈ γ`). -/

/-- The edge-link apex set is monotone in the tet-set: more tets give more apexes. -/
private lemma edgeLinkVerts_mono {τ τ' : Finset (Finset V)} (h : τ ⊆ τ') (e : Finset V) :
    edgeLinkVerts τ e ⊆ edgeLinkVerts τ' e := by
  intro w hw
  rw [mem_edgeLinkVerts_iff] at hw ⊢
  obtain ⟨⟨t, ht, het, hwt⟩, hwe⟩ := hw
  exact ⟨⟨t, h ht, het, hwt⟩, hwe⟩

/-- The vertex-link apex set is monotone in the tet-set. -/
private lemma vertexLinkVerts_mono {τ τ' : Finset (Finset V)} (h : τ ⊆ τ') (x : V) :
    vertexLinkVerts τ x ⊆ vertexLinkVerts τ' x := by
  intro w hw
  rw [mem_vertexLinkVerts_iff] at hw ⊢
  obtain ⟨⟨t, ht, hxt, hwt⟩, hwx⟩ := hw
  exact ⟨⟨t, h ht, hxt, hwt⟩, hwx⟩

/-- **Edge-link compat survives adjoining the star tet.**  The link tets of the
degree-3 reduction glue onto `insert (starTet σ v) τ`; this transports the
`helc` field for a tet `t` with `v ∉ t` from `τ` to `insert (starTet σ v) τ`.
For a γ-edge the third γ-vertex sits in the apex tet `t₀ ∈ τ`, so the apex set is
already nonempty and the given hypothesis's nonempty branch is forced and survives
by monotonicity; for a non-γ-edge the star tet contributes no apex, so the apex
set is unchanged and the hypothesis is used verbatim. -/
lemma helc_insert_star {σ : Finset (Finset V)} {v : V} {γ : Finset V} {t₀ t : Finset V}
    {τ : Finset (Finset V)}
    (hγ : γ = linkVerts σ v) (hγ3 : γ.card = 3)
    (hvt : v ∉ t)
    (ht₀τ : t₀ ∈ τ) (hγt₀ : γ ⊆ t₀) :
    (∀ e, e ⊆ t → e.card = 2 →
        edgeLinkVerts τ e = ∅ ∨ ((t \ e) ∩ edgeLinkVerts τ e).Nonempty) →
    (∀ e, e ⊆ t → e.card = 2 →
        edgeLinkVerts (insert (starTet σ v) τ) e = ∅ ∨
        ((t \ e) ∩ edgeLinkVerts (insert (starTet σ v) τ) e).Nonempty) := by
  intro H e he he2
  have hstar : starTet σ v = insert v γ := by rw [starTet, hγ]
  have hmono : edgeLinkVerts τ e ⊆ edgeLinkVerts (insert (starTet σ v) τ) e :=
    edgeLinkVerts_mono (Finset.subset_insert _ _) e
  have hve : v ∉ e := fun hv => hvt (he hv)
  by_cases heγ : e ⊆ γ
  · -- γ-edge: the third γ-vertex `w` is an apex of `e` via `t₀`, so `edgeLinkVerts τ e ≠ ∅`,
    -- forcing the nonempty branch of `H`, which survives by monotonicity.
    right
    have hcard : (γ \ e).card = 1 := by
      rw [Finset.card_sdiff_of_subset heγ, hγ3, he2]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
    have hwγe : w ∈ γ \ e := hw ▸ Finset.mem_singleton_self w
    rw [Finset.mem_sdiff] at hwγe
    obtain ⟨hwγ, hwe⟩ := hwγe
    have hwapex : w ∈ edgeLinkVerts τ e := by
      rw [mem_edgeLinkVerts_iff]
      exact ⟨⟨t₀, ht₀τ, heγ.trans hγt₀, hγt₀ hwγ⟩, hwe⟩
    have hne : edgeLinkVerts τ e ≠ ∅ := Finset.ne_empty_of_mem hwapex
    rcases H e he he2 with hH | hH
    · exact absurd hH hne
    · obtain ⟨z, hz⟩ := hH
      rw [Finset.mem_inter] at hz
      exact ⟨z, Finset.mem_inter.mpr ⟨hz.1, hmono hz.2⟩⟩
  · -- non-γ-edge: `e ⊄ starTet σ v` (else `v ∉ e` forces `e ⊆ γ`), so the star tet
    -- supplies no apex and the apex set is unchanged; reuse `H` verbatim.
    have hnotstar : ¬ e ⊆ starTet σ v := by
      intro hsub
      apply heγ
      intro x hxe
      have : x ∈ insert v γ := hstar ▸ hsub hxe
      rcases Finset.mem_insert.mp this with rfl | hxγ
      · exact absurd hxe hve
      · exact hxγ
    rw [edgeLinkVerts_insert_of_not_subset hnotstar]
    exact H e he he2

/-- **Vertex-link compat survives adjoining the star tet.**  Vertex analogue of
`helc_insert_star`: for a vertex `x ∈ t` (so `x ≠ v` by `hvt`), if `x ∈ γ` another
γ-vertex is an apex via `t₀` (nonempty branch forced, survives by monotonicity);
if `x ∉ γ` then `x ∉ starTet σ v`, the star tet contributes no apex, and the apex
set is unchanged. -/
lemma hvlc_insert_star {σ : Finset (Finset V)} {v : V} {γ : Finset V} {t₀ t : Finset V}
    {τ : Finset (Finset V)}
    (hγ : γ = linkVerts σ v) (hγ3 : γ.card = 3) (hvt : v ∉ t)
    (ht₀τ : t₀ ∈ τ) (hγt₀ : γ ⊆ t₀) :
    (∀ x ∈ t, vertexLinkVerts τ x = ∅ ∨ ((t \ {x}) ∩ vertexLinkVerts τ x).Nonempty) →
    (∀ x ∈ t, vertexLinkVerts (insert (starTet σ v) τ) x = ∅ ∨
      ((t \ {x}) ∩ vertexLinkVerts (insert (starTet σ v) τ) x).Nonempty) := by
  intro H x hx
  have hstar : starTet σ v = insert v γ := by rw [starTet, hγ]
  have hmono : vertexLinkVerts τ x ⊆ vertexLinkVerts (insert (starTet σ v) τ) x :=
    vertexLinkVerts_mono (Finset.subset_insert _ _) x
  have hxv : x ≠ v := fun h => hvt (h ▸ hx)
  by_cases hxγ : x ∈ γ
  · -- `x ∈ γ`: another γ-vertex `w ≠ x` is an apex of `x` via `t₀`, forcing nonempty.
    right
    have hcard : (γ \ {x}).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hxγ), hγ3,
        Finset.card_singleton]
    have hnonempty : (γ \ {x}).Nonempty := by rw [← Finset.card_pos, hcard]; omega
    obtain ⟨w, hw⟩ := hnonempty
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
    obtain ⟨hwγ, hwx⟩ := hw
    have hwapex : w ∈ vertexLinkVerts τ x := by
      rw [mem_vertexLinkVerts_iff]
      exact ⟨⟨t₀, ht₀τ, hγt₀ hxγ, hγt₀ hwγ⟩, hwx⟩
    have hne : vertexLinkVerts τ x ≠ ∅ := Finset.ne_empty_of_mem hwapex
    rcases H x hx with hH | hH
    · exact absurd hH hne
    · obtain ⟨z, hz⟩ := hH
      rw [Finset.mem_inter] at hz
      exact ⟨z, Finset.mem_inter.mpr ⟨hz.1, hmono hz.2⟩⟩
  · -- `x ∉ γ`: with `x ≠ v`, `x ∉ starTet σ v`, so the star tet supplies no apex.
    have hnotstar : x ∉ starTet σ v := by
      rw [hstar, Finset.mem_insert]
      rintro (rfl | hxγ')
      · exact hxv rfl
      · exact hxγ hxγ'
    rw [vertexLinkVerts_insert_of_not_mem hnotstar]
    exact H x hx

/-! ## Degree-3 old-target half: the old-target clean shelling composes -/

/-- **Degree-3 old-target clean shelling.**  Given the clean IH result for the
remainder (`hfreeMR : FreelyCleanShellable MRsupp σR`) and the star `CleanGlueStep`
gluing `starTet σ v` onto that remainder up to the final boundary `σtarget`, an old
target `s ∈ MRsupp` yields a clean shelling of `insert (starTet σ v) MRsupp`
starting at `s`.  This is the old-target half of the degree-3 reduction; it composes
directly from the banked old-target clean snoc lemma (the freshness input is the
glue's own `newTet` field). -/
lemma deg3_clean_old_target {σ : Finset (Finset V)} {v : V}
    {MRsupp σR σtarget : Finset (Finset V)} {s : Finset V}
    (hfreeMR : FreelyCleanShellable MRsupp σR)
    (hglue : CleanGlueStep (starTet σ v) MRsupp σR σtarget)
    (hsMR : s ∈ MRsupp) :
    ∃ l, l.head? = some s ∧ l.toFinset = insert (starTet σ v) MRsupp ∧ l.Nodup ∧
      IsCleanShelling l σtarget :=
  FreelyCleanShellable.exists_shelling_insert_of_cleanGlueStep_old hfreeMR hglue
    hglue.newTet hsMR

/-! ## Degree-3 STAR-START half: the star tet glues first, then the remainder shells

The star-start (new-target) half of the degree-3 reduction.  Here the *star* tet
`starTet σ v` is the head of the shelling and the remainder `τ` is shelled onto it.
The data is the clean analogue of the weak `degree3_star_start_shellFrom`
(`Theorem3.lean`): a clean free shelling of the remainder rooted at a first tet
`t₀` whose interface face is `γ = linkVerts σ v`, plus the clean inputs (v absent,
γ unique to `t₀`, the disjoint exposed-star piece `K`).  The transport adjoins
`starTet σ v` to the τ-base of the remainder shelling and swaps the interface face
`γ` for the exposed star boundary `K`. -/

/-- **τ-extension of one clean glue step by the star tet.**  Inserting the star tet
`starTet σ v` into the accumulated tet-set `τ` of a clean glue step `t` is again a
clean glue step, provided `v ∉ t`, `γ = linkVerts σ v` (card 3) sits in a tet
`t₀ ∈ τ`, and `γ ⊄ t` (so `t` is not the interface tet).  Every field is preserved:
`weak` is unchanged (boundary untouched); `newTet` adds `t ≠ starTet σ v`; `clean`
gains no case (a face `f ⊆ t` newly covered by `starTet σ v` has `v ∉ f`, hence
`f ⊆ γ ⊆ t₀ ∈ τ`, so it was already covered by the old `clean`); `hpmc` is
unchanged (a card-3 `f ⊆ t` with `f ⊆ starTet σ v` would force `f = γ ⊆ t`, against
`γ ⊄ t`, so the star contributes no count); `helc`/`hvlc` use the banked
`helc_insert_star`/`hvlc_insert_star`. -/
lemma cleanGlueStep_insert_star {σ : Finset (Finset V)} {v : V} {γ t₀ t : Finset V}
    {τ B B' : Finset (Finset V)}
    (hg : CleanGlueStep t τ B B')
    (hγ : γ = linkVerts σ v) (hγ3 : γ.card = 3)
    (ht₀τ : t₀ ∈ τ) (hγt₀ : γ ⊆ t₀)
    (hvt : v ∉ t) (hγnt : ¬ γ ⊆ t)
    (hstarNotτ : starTet σ v ∉ τ) (htstar : t ≠ starTet σ v) :
    CleanGlueStep t (insert (starTet σ v) τ) B B' := by
  have hstar : starTet σ v = insert v γ := by rw [starTet, hγ]
  refine
    { weak := hg.weak
      newTet := ?_
      clean := ?_
      hpmc := ?_
      helc := helc_insert_star hγ hγ3 hvt ht₀τ hγt₀ hg.helc
      hvlc := hvlc_insert_star hγ hγ3 hvt ht₀τ hγt₀ hg.hvlc }
  · -- clean: a face covered via the star tet is already covered via `t₀ ∈ τ`.
    intro f hf ⟨s, hsτ, hfs⟩
    apply hg.clean f hf
    rcases Finset.mem_insert.mp hsτ with rfl | hsτ'
    · -- `s = starTet σ v`: `v ∉ f` ⟹ `f ⊆ γ ⊆ t₀`.
      refine ⟨t₀, ht₀τ, ?_⟩
      have hvf : v ∉ f := fun hvf => hvt (hf hvf)
      have hfγ : f ⊆ γ := by
        intro x hxf
        have : x ∈ insert v γ := hstar ▸ hfs hxf
        rcases Finset.mem_insert.mp this with rfl | hxγ
        · exact absurd hxf hvf
        · exact hxγ
      exact hfγ.trans hγt₀
    · exact ⟨s, hsτ', hfs⟩
  · -- freshness: `t ∉ insert (starTet σ v) τ`.
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact htstar h
    · exact hg.newTet h
  · -- hpmc: the star tet contributes no count to a card-3 face of `t` (else `γ ⊆ t`).
    intro f hf3 hf
    rw [faceCount_insert_of_not_mem hstarNotτ]
    have hnotstar : ¬ f ⊆ starTet σ v := by
      intro hsub
      apply hγnt
      have hvf : v ∉ f := fun hvf => hvt (hf hvf)
      have hfγ : f ⊆ γ := by
        intro x hxf
        have : x ∈ insert v γ := hstar ▸ hsub hxf
        rcases Finset.mem_insert.mp this with rfl | hxγ
        · exact absurd hxf hvf
        · exact hxγ
      -- card-3 `f ⊆ γ` (card 3) is `γ`, so `γ = f ⊆ t`.
      have : f = γ := Finset.eq_of_subset_of_card_le hfγ (by rw [hγ3, hf3])
      exact this ▸ hf
    rw [if_neg hnotstar, Nat.add_zero]
    exact hg.hpmc f hf3 hf

/-- **Combined per-step upgrade for the degree-3 star-start shelling.**  Compose the
τ-extension by `starTet σ v` (`cleanGlueStep_insert_star`) with the boundary
erase-γ-add-K transport (`CleanGlueStep.erase_union_disjoint`).  The boundary
`clean`/`weak` survive the swap because the tet `t` avoids both `γ` and `K`
(`hdisj`); the τ-fields survive the extension because `γ ⊄ t`. -/
lemma cleanGlueStep_insert_star_erase {σ : Finset (Finset V)} {v : V} {γ t₀ t : Finset V}
    {τ B B' K : Finset (Finset V)}
    (hg : CleanGlueStep t τ B B')
    (hγ : γ = linkVerts σ v) (hγ3 : γ.card = 3)
    (ht₀τ : t₀ ∈ τ) (hγt₀ : γ ⊆ t₀)
    (hvt : v ∉ t) (hγnt : ¬ γ ⊆ t)
    (hstarNotτ : starTet σ v ∉ τ) (htstar : t ≠ starTet σ v)
    (hdisj : Disjoint (tetFaces t) (insert γ K)) :
    CleanGlueStep t (insert (starTet σ v) τ) (B.erase γ ∪ K) (B'.erase γ ∪ K) :=
  (cleanGlueStep_insert_star hg hγ hγ3 ht₀τ hγt₀ hvt hγnt hstarNotτ htstar).erase_union_disjoint
    hdisj

/-- **The degree-3 star-start transport (the heart).**  Clean analogue of
`ShellFrom_erase_union_disjoint`, additionally adjoining the star tet `starTet σ v`
to the accumulated τ-base at every step.  Given a clean relative shelling of `l`
from `τ₀` with interface tet `t₀ ∈ τ₀` (carrying `γ = linkVerts σ v ⊆ t₀`), in which
the apex `v` is absent everywhere, no rest tet contains `γ`, the star is fresh and
distinct from every rest tet, and every rest tet avoids `γ` and the exposed-star
piece `K`, the same list `l` is a clean relative shelling from `insert (starTet σ v) τ₀`
with the interface face `γ` swapped for `K`.

The invariant threaded through the induction is `t₀ ∈` the accumulated τ-base (it
starts in `τ₀` and only grows under `insert`), so the link-compat hypotheses of
`helc_insert_star`/`hvlc_insert_star` always hold. -/
lemma CleanShellFrom_starStart_transport {σ : Finset (Finset V)} {v : V} {γ t₀ : Finset V}
    {K : Finset (Finset V)} {l : List (Finset V)} :
    ∀ {τ₀ B₀ B : Finset (Finset V)}, CleanShellFrom τ₀ B₀ l B →
      t₀ ∈ τ₀ → γ ⊆ t₀ → γ = linkVerts σ v → γ.card = 3 →
      (∀ t ∈ l, v ∉ t) → (∀ t ∈ l, ¬ γ ⊆ t) →
      starTet σ v ∉ τ₀ → (∀ t ∈ l, t ≠ starTet σ v) →
      (∀ t ∈ l, Disjoint (tetFaces t) (insert γ K)) →
      CleanShellFrom (insert (starTet σ v) τ₀) (B₀.erase γ ∪ K) l (B.erase γ ∪ K) := by
  induction l with
  | nil =>
      intro τ₀ B₀ B h _ _ _ _ _ _ _ _ _
      simp only [CleanShellFrom] at h ⊢
      rw [h]
  | cons t l ih =>
      intro τ₀ B₀ B h ht₀τ hγt₀ hγ hγ3 hv hγn hstarNot htstar hdisj
      simp only [CleanShellFrom] at h ⊢
      obtain ⟨B₁, hstep, hrest⟩ := h
      -- per-step upgrade for the head tet `t`
      have hstep' : CleanGlueStep t (insert (starTet σ v) τ₀) (B₀.erase γ ∪ K) (B₁.erase γ ∪ K) :=
        cleanGlueStep_insert_star_erase hstep hγ hγ3 ht₀τ hγt₀
          (hv t (List.mem_cons.mpr (Or.inl rfl))) (hγn t (List.mem_cons.mpr (Or.inl rfl)))
          hstarNot (htstar t (List.mem_cons.mpr (Or.inl rfl)))
          (hdisj t (List.mem_cons.mpr (Or.inl rfl)))
      refine ⟨B₁.erase γ ∪ K, hstep', ?_⟩
      -- recurse on `insert t τ₀`; the invariant `t₀ ∈ insert t τ₀` is kept.
      have htail : ∀ {P : Finset V → Prop}, (∀ u ∈ t :: l, P u) → ∀ u ∈ l, P u :=
        fun H u hu => H u (List.mem_cons_of_mem t hu)
      have hrec := ih hrest (Finset.mem_insert_of_mem ht₀τ) hγt₀ hγ hγ3
        (htail hv) (htail hγn)
        (fun hc => hstarNot ((Finset.mem_insert.mp hc).resolve_left
          (fun h => htstar t (List.mem_cons.mpr (Or.inl rfl)) h.symm)))
        (htail htstar) (htail hdisj)
      -- align: `insert starTet (insert t τ₀) = insert t (insert starTet τ₀)`.
      rwa [Finset.insert_comm] at hrec

/-- **Degree-3 star-start clean shelling.**  Clean analogue of the weak
`degree3_star_start_shellFrom`.  From a clean free shelling of the remainder `τ`
rooted at the interface tet `t₀` (carrying the interface face `γ = linkVerts σ v`),
together with the clean inputs (apex `v` absent from every remainder tet, `γ` unique
to `t₀`, the first star glue across `γ`, and the rest tets disjoint from the
exposed-star piece `K`), the star tet `starTet σ v` heads a clean shelling of the
remainder onto it, ending at the target boundary `σ = B.erase γ ∪ K`.

The construction: `hfree t₀` gives a clean free shelling `t₀ :: rest` of `τ`; glue
the star tet first (the first `CleanGlueStep` `hglue₀` of `t₀` onto the single tet
`{starTet σ v}`), then transport the relative shelling of `rest` by adjoining
`starTet σ v` to the τ-base and swapping `γ` for `K`
(`CleanShellFrom_starStart_transport`). -/
lemma degree3_star_start_cleanShellFrom (σ B τ : Finset (Finset V)) {v : V}
    {γ t₀ : Finset V} {K : Finset (Finset V)}
    (hfree : FreelyCleanShellable τ B) (ht₀ : t₀ ∈ τ)
    (hγ : γ = linkVerts σ v) (hγ3 : γ.card = 3) (hγt₀ : γ ⊆ t₀)
    (hvτ : ∀ t ∈ τ, v ∉ t)
    (huniqγ : ∀ t ∈ τ, γ ⊆ t → t = t₀)
    (hstarNotτ : starTet σ v ∉ τ)
    (hglue₀ : CleanGlueStep t₀ {starTet σ v} (tetFaces (starTet σ v))
      ((tetFaces t₀).erase γ ∪ K))
    (hrest_disj : ∀ t ∈ τ, t ≠ t₀ → Disjoint (tetFaces t) (insert γ K))
    (hfinal : σ = B.erase γ ∪ K) :
    ∃ l : List (Finset V), l.head? = some t₀ ∧ l.toFinset = τ ∧ l.Nodup ∧
      CleanShellFrom {starTet σ v} (tetFaces (starTet σ v)) l σ := by
  obtain ⟨l, hhead, hlτ, hnodup, hsh⟩ := hfree t₀ ht₀
  cases l with
  | nil => simp at hhead
  | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst a
      simp only [IsCleanShelling] at hsh
      -- the remainder relative shelling, rooted at `t₀` with τ-base `{t₀}`.
      obtain ⟨ht₀card, hrest_sh⟩ := hsh
      -- membership of a `rest`-tet in `τ`, and that it is not `t₀`.
      have hmemτ : ∀ t ∈ rest, t ∈ τ := by
        intro t ht
        exact hlτ ▸ List.mem_toFinset.mpr (List.mem_cons_of_mem t₀ ht)
      have hne_t₀ : ∀ t ∈ rest, t ≠ t₀ := by
        intro t ht hc
        subst t
        exact (List.nodup_cons.mp hnodup).1 ht
      -- the per-rest-tet hypotheses for the transport.
      have hv_rest : ∀ t ∈ rest, v ∉ t := fun t ht => hvτ t (hmemτ t ht)
      have hγn_rest : ∀ t ∈ rest, ¬ γ ⊆ t := by
        intro t ht hc
        exact hne_t₀ t ht (huniqγ t (hmemτ t ht) hc)
      have hstarne_rest : ∀ t ∈ rest, t ≠ starTet σ v := by
        intro t ht hc
        exact hstarNotτ (hc ▸ hmemτ t ht)
      have hdisj_rest : ∀ t ∈ rest, Disjoint (tetFaces t) (insert γ K) :=
        fun t ht => hrest_disj t (hmemτ t ht) (hne_t₀ t ht)
      -- transport the remainder shelling onto `insert (starTet σ v) {t₀}`,
      -- swapping `γ` for `K`.
      have htransport :
          CleanShellFrom (insert (starTet σ v) {t₀}) ((tetFaces t₀).erase γ ∪ K) rest
            (B.erase γ ∪ K) :=
        CleanShellFrom_starStart_transport hrest_sh (Finset.mem_singleton_self t₀) hγt₀ hγ
          hγ3 hv_rest hγn_rest
          (fun hc => hstarNotτ (by
            rw [Finset.mem_singleton] at hc; rw [hc]; exact ht₀))
          hstarne_rest hdisj_rest
      refine ⟨t₀ :: rest, rfl, hlτ, hnodup, ?_⟩
      -- assemble: first the star glue, then the transported remainder.
      simp only [CleanShellFrom]
      refine ⟨(tetFaces t₀).erase γ ∪ K, hglue₀, ?_⟩
      -- `insert t₀ {starTet σ v} = insert (starTet σ v) {t₀}` (`Finset.pair_comm`).
      rw [show insert t₀ ({starTet σ v} : Finset (Finset V)) = insert (starTet σ v) {t₀} from
        Finset.pair_comm t₀ (starTet σ v)]
      exact hfinal ▸ htransport

/-! ## The first star glue: `t₀` onto the single star tet

The clean star-start shelling glues `starTet σ v` first onto a single-tet base
`{starTet σ v}`, then the interface tet `t₀` is the *next* tet glued on.  That
first non-head glue is `CleanGlueStep t₀ {starTet σ v} …` — the analogue of
`cleanGlueStep_star_of_remainder` but with the *remainder* collapsed to the single
star tet and the *new* tet being `t₀`.  All six fields discharge from the same
geometric facts (γ is the shared face, `v ∉ t₀`, and the third γ-vertex is a common
apex *via the star tet itself*). -/

/-- **One clean glue step for the interface tet `t₀` onto the single star tet.**
With the new tet `t₀` (`card 4`, `v ∉ t₀`, `γ = linkVerts σ v ⊆ t₀`) glued onto the
single-tet base `{starTet σ v}` across the shared face `γ` (the boundary glue
`hweak`), every `CleanGlueStep` field discharges: `clean`/`hpmc` use that a
`v`-free face of `t₀` lies in `γ ⊆ starTet σ v` (and a singleton's `faceCount ≤ 1`),
and `helc`/`hvlc` use that for a γ-edge/γ-vertex the apex sits in the star tet
itself, while a non-γ edge/vertex gives an empty star-link. -/
lemma cleanGlueStep_firstStar {σ : Finset (Finset V)} {v : V} {γ t₀ : Finset V}
    {K : Finset (Finset V)}
    (hγ : γ = linkVerts σ v) (hγ3 : (linkVerts σ v).card = 3)
    (hstar4 : (starTet σ v).card = 4)
    (hvt₀ : v ∉ t₀) (hγt₀ : γ ⊆ t₀) (ht₀4 : t₀.card = 4)
    (hweak : GlueStep t₀ (tetFaces (starTet σ v)) ((tetFaces t₀).erase γ ∪ K)) :
    CleanGlueStep t₀ ({starTet σ v} : Finset (Finset V)) (tetFaces (starTet σ v))
      ((tetFaces t₀).erase γ ∪ K) := by
  classical
  have hstar : starTet σ v = insert v γ := by rw [starTet, hγ]
  have hγcard : γ.card = 3 := hγ ▸ hγ3
  have hvγ : v ∉ γ := by
    intro hv
    rw [hstar, Finset.insert_eq_self.mpr hv] at hstar4
    omega
  -- the shared face `γ` is in `tetFaces t₀ ∩ tetFaces (starTet σ v)`.
  have hγstar : γ ∈ tetFaces (starTet σ v) :=
    Finset.mem_powersetCard.mpr ⟨by rw [hstar]; exact Finset.subset_insert _ _, hγcard⟩
  have hγt₀face : γ ∈ tetFaces t₀ := Finset.mem_powersetCard.mpr ⟨hγt₀, hγcard⟩
  -- the star tet is the unique τ-tet, and `v ∈ starTet`.
  have hvstar : v ∈ starTet σ v := by rw [hstar]; exact Finset.mem_insert_self _ _
  have ht₀ne : t₀ ≠ starTet σ v := fun h => hvt₀ (h ▸ hvstar)
  -- a `v`-free subset of `starTet σ v` lies in `γ`.
  have sub_γ : ∀ {f : Finset V}, f ⊆ starTet σ v → v ∉ f → f ⊆ γ := by
    intro f hf hvf x hxf
    have : x ∈ insert v γ := hstar ▸ hf hxf
    rcases Finset.mem_insert.mp this with rfl | hxγ
    · exact absurd hxf hvf
    · exact hxγ
  refine
    { weak := hweak
      newTet := by rw [Finset.mem_singleton]; exact ht₀ne
      clean := ?_
      hpmc := ?_
      helc := ?_
      hvlc := ?_ }
  · -- clean: a face of `t₀` covered by the (single) star tet is `v`-free, so `f ⊆ γ`; use `γ`.
    intro f hf ⟨s, hsτ, hfs⟩
    rw [Finset.mem_singleton] at hsτ
    subst hsτ
    have hvf : v ∉ f := fun hvf => hvt₀ (hf hvf)
    exact ⟨γ, Finset.mem_inter.mpr ⟨hγt₀face, hγstar⟩, sub_γ hfs hvf⟩
  · -- hpmc: a singleton's `faceCount` is ≤ 1 (`card_filter_le`).
    intro f _ _
    unfold faceCount
    simpa using Finset.card_filter_le ({starTet σ v} : Finset (Finset V)) (fun s => f ⊆ s)
  · -- helc: γ-edge has the third γ-vertex as an apex via the star tet; non-γ edge has empty link.
    intro e he he2
    by_cases heγ : e ⊆ γ
    · right
      have hcard : (γ \ e).card = 1 := by
        rw [Finset.card_sdiff_of_subset heγ, hγcard, he2]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
      have hwγe : w ∈ γ \ e := hw ▸ Finset.mem_singleton_self w
      rw [Finset.mem_sdiff] at hwγe
      obtain ⟨hwγ, hwe⟩ := hwγe
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [Finset.mem_sdiff]; exact ⟨hγt₀ hwγ, hwe⟩
      · rw [mem_edgeLinkVerts_iff]
        refine ⟨⟨starTet σ v, Finset.mem_singleton_self _, ?_, ?_⟩, hwe⟩
        · exact (heγ.trans (by rw [hstar]; exact Finset.subset_insert _ _))
        · rw [hstar]; exact Finset.mem_insert_of_mem hwγ
    · -- `e ⊄ starTet σ v` (a `v`-free `e ⊆ starTet` would lie in `γ`), so the link is empty.
      left
      apply edgeLinkVerts_eq_empty
      intro s hsτ hes
      rw [Finset.mem_singleton] at hsτ
      subst hsτ
      have hve : v ∉ e := fun hv => hvt₀ (he hv)
      exact heγ (sub_γ hes hve)
  · -- hvlc: a γ-vertex has another γ-vertex as apex via the star tet; non-γ vertex has empty link.
    intro x hx
    by_cases hxγ : x ∈ γ
    · right
      have hcard : (γ \ {x}).card = 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hxγ), hγcard,
          Finset.card_singleton]
      have hne : (γ \ {x}).Nonempty := by rw [← Finset.card_pos, hcard]; omega
      obtain ⟨w, hw⟩ := hne
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
      obtain ⟨hwγ, hwx⟩ := hw
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hγt₀ hwγ, hwx⟩
      · rw [mem_vertexLinkVerts_iff]
        refine ⟨⟨starTet σ v, Finset.mem_singleton_self _, ?_, ?_⟩, hwx⟩
        · rw [hstar]; exact Finset.mem_insert_of_mem hxγ
        · rw [hstar]; exact Finset.mem_insert_of_mem hwγ
    · -- `x ∉ starTet σ v` (else `x = v` or `x ∈ γ`, both excluded), so the link is empty.
      left
      apply vertexLinkVerts_eq_empty
      intro s hsτ hxs
      rw [Finset.mem_singleton] at hsτ
      subst hsτ
      have hxv : x ≠ v := fun h => hvt₀ (h ▸ hx)
      rw [hstar, Finset.mem_insert] at hxs
      rcases hxs with rfl | hxγ'
      · exact hxv rfl
      · exact hxγ hxγ'

/-! ## The clean degree-3 step: assemble the two halves

`deg3_step_clean` mirrors `deg3_step_free` (the cut, the ML/MR split, the star-side
dichotomy, `degree3_hanchor`), but where the weak step applies its IH to get
`FreelyShellable ∧ IsPseudomanifold`, here the IH delivers
`FreelyCleanShellable MR.support σR` directly; the weak `FreelyShellable` and
`IsPseudomanifold` facts the preamble + `degree3_hanchor` still need are *derived*
from it (`toBoundaryFreelyShellable`, `clean3Complex`).  The reassembly collapses to
one `FreelyCleanShellable.insert_of_cleanGlueStep` per branch, discharging the star
glue via `cleanGlueStep_star_of_remainder` and the bridge-start clean shelling via
`degree3_star_start_cleanShellFrom` (whose first non-head glue is the new
`cleanGlueStep_firstStar`). -/

/-- **deg3_step_clean** (the discharged degree-3 hole of `theorem3_core_clean`).
Mirror of `deg3_step_free`, concluding `FreelyCleanShellable M.support σ`. -/
theorem deg3_step_clean (sigma : Finset (Finset V)) (X M : Chain V)
    (hsigma : IsSphere2 sigma) (hbig : 4 < (vertsOf sigma).card)
    (hU : UnitOn X sigma) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hd3 : HasDegree3Vertex sigma)
    (IH : ∀ (sigma' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M →
      IsSphere2 sigma' → UnitOn X' sigma' → bdry X' = 0 → bdry M' = X' →
      IsTaut M' → SimplicialChain M' →
      FreelyCleanShellable M'.support sigma') :
    FreelyCleanShellable M.support sigma := by
  classical
  obtain ⟨v, W, hv, hγ3, hγe, hγσ, hW, hσL, hσR⟩ :=
    degree3_cut_setup sigma hsigma hbig hd3
  let γ : Finset V := linkVerts sigma v
  have hγ : γ = linkVerts sigma v := rfl
  let A : Finset V := vertsOf (insert γ (cutSet sigma W))
  let ML : Chain V := M.filter (fun t => t ⊆ A)
  let MR : Chain V := M.filter (fun t => ¬ t ⊆ A)
  obtain ⟨c, hUL, hXLc, hUR, hXRc, hXsum⟩ :=
    capped_cut_splits_unit sigma X hsigma hγ3 hγe hγσ hW hU hXc
  obtain ⟨hML, hMR, hTL, hTR, hSuppL, hSuppR, hMsum⟩ :=
    taut_splits_for_capped_cut sigma X M hsigma hσL hσR hγ3 hγe hW
      hUL hXLc hUR hXRc hXsum hMX hT
  have hsplit := degree3_cut_star_side_glue sigma hsigma hbig hv hγ3 hW
  rcases hsplit with hcase | hcase
  · rcases hcase with ⟨hstar, hglue⟩
    have hT4 : (starTet sigma v).card = 4 := starTet_card_of_degree3 sigma hγ3
    have hULtet : UnitOn (cappedCutLeft sigma W X γ c) (tetFaces (starTet sigma v)) := by
      dsimp [γ]
      rw [← hstar]
      exact hUL
    have hSuppLT : ∀ t ∈ ML.support, t ⊆ starTet sigma v := by
      intro t ht
      have htA : t ⊆ vertsOf (insert γ (cutSet sigma W)) :=
        hSuppL t (by simpa only [ML, A] using ht)
      dsimp [γ] at htA
      rw [hstar, vertsOf_tetFaces_eq (starTet sigma v) hT4] at htA
      exact htA
    have hMLsupp : ML.support = {starTet sigma v} := by
      exact star_filter_support_singleton ML (cappedCutLeft sigma W X γ c)
        (starTet sigma v) hT4 hULtet (by simpa only [ML, A, γ] using hML)
        (by simpa only [ML, A, γ] using hTL) hSuppLT
    have hlt : nrm MR < nrm M := by
      have hlt' : nrm (M.filter (fun t => ¬ t ⊆ A)) < nrm M :=
        norm_lt_filter_neg_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
      simpa only [MR] using hlt'
    have hSimpR : SimplicialChain MR := by
      intro t
      dsimp [MR, A, γ]
      rw [Finsupp.filter_apply]
      by_cases ht : ¬ t ⊆ vertsOf (insert (linkVerts sigma v) (cutSet sigma W))
      · rw [if_pos ht]
        exact hS t
      · rw [if_neg ht]
        exact Or.inr (Or.inl rfl)
    have hfreeMR : FreelyCleanShellable MR.support
        (insert γ (cutSet sigma (W + fun _ => 1))) :=
      IH (insert γ (cutSet sigma (W + fun _ => 1)))
        (cappedCutRight sigma W X γ c) MR hlt
        (by dsimp [γ]; exact hσR) (by dsimp [γ]; exact hUR)
        (by dsimp [γ]; exact hXRc) (by dsimp [MR, A, γ]; exact hMR)
        (by dsimp [MR, A, γ]; exact hTR) hSimpR
    -- weak facts derived from the clean IH result.
    have hsupport : M.support = insert (starTet sigma v) MR.support := by
      simpa only [MR] using
        support_eq_insert_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
    have hPT : (starTet sigma v) ⊆ A := by
      have hTin : starTet sigma v ∈ ML.support := by rw [hMLsupp]; simp
      have hTin' : ¬ M (starTet sigma v) = 0 ∧ (starTet sigma v) ⊆ A := by
        simpa [ML] using hTin
      exact hTin'.2
    have hTnot : starTet sigma v ∉ MR.support := by
      intro hmem
      have hne : MR (starTet sigma v) ≠ 0 := Finsupp.mem_support_iff.mp hmem
      have hzero : MR (starTet sigma v) = 0 := by simp [MR, hPT]
      exact hne hzero
    have hbdMR : bdry MR = cappedCutRight sigma W X γ c := by dsimp [MR, A, γ]; exact hMR
    have hMRne : MR.support.Nonempty := aleph_base_support_nonempty hσR hUR hbdMR
    have hPMR : IsPseudomanifold MR.support :=
      (hfreeMR.clean3Complex hMRne).2.1
    have hfreeR_weak : FreelyShellable MR.support
        (insert γ (cutSet sigma (W + fun _ => 1))) :=
      hfreeMR.toBoundaryFreelyShellable
    have hTRMR : IsTaut MR := by dsimp [MR, A, γ]; exact hTR
    have hsuppInfo :
        ∀ t ∈ MR.support,
          t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet sigma (W + fun _ => 1))) :=
      aleph_base_taut_support_card4_subset_verts hσR hUR hbdMR hTRMR
    have hvNotMR : ∀ t ∈ MR.support, v ∉ t := by
      have hvNotSigmaR : v ∉ vertsOf (insert γ (cutSet sigma (W + fun _ => 1))) :=
        degree3_apex_notMem_right_verts_of_left_star (σ := sigma) (v := v) (W := W)
          (γ := γ) hsigma hγ3 rfl (by simpa [γ] using hW) hstar
      intro t ht hvt
      exact hvNotSigmaR ((hsuppInfo t ht).2 hvt)
    have hanchor :
        ∃ t₀ K,
          t₀ ∈ MR.support ∧
          GlueStep t₀ (tetFaces (starTet sigma v)) ((tetFaces t₀).erase γ ∪ K) ∧
          (∀ t ∈ MR.support, t ≠ t₀ → Disjoint (tetFaces t) (insert γ K)) ∧
          sigma = (insert γ (cutSet sigma (W + fun _ => 1))).erase γ ∪ K := by
      exact degree3_hanchor sigma (insert γ (cutSet sigma (W + fun _ => 1))) MR
        M A false v W γ hsigma hbig hv rfl hγ3 hW hσR
        (by
          dsimp [MR, A, γ]
          rw [hMR]
          exact hUR)
        hfreeR_weak hSimpR (by dsimp only [MR, A, γ]; exact hTR) hPMR hTnot hvNotMR rfl
        (by simp [MR])
        (Or.inr rfl)
    obtain ⟨t₀, K, ht₀, hglue₀_weak, hrest_disj, hfinal⟩ := hanchor
    -- quantitative carries for the glue/start lemmas.
    have hPureR : ∀ t ∈ MR.support, t.card = 4 := fun t ht => (hsuppInfo t ht).1
    have hγ3' : γ.card = 3 := hγ ▸ hγ3
    -- `γ` lies in a unique remainder tet; the anchor's `hrest_disj` pins it to `t₀`.
    have huniqγ : ∀ t ∈ MR.support, γ ⊆ t → t = t₀ := by
      intro t htmem hγt
      by_contra hne
      have hdisj := hrest_disj t htmem hne
      have hγinT : γ ∈ tetFaces t := Finset.mem_powersetCard.mpr ⟨hγt, hγ3'⟩
      exact (Finset.disjoint_left.mp hdisj) hγinT (Finset.mem_insert_self _ _)
    have hbdγ : bdry MR γ = 1 ∨ bdry MR γ = -1 := by
      rw [hbdMR]; exact hUR.2 γ (Finset.mem_insert_self _ _)
    have hγcount : faceCount MR.support γ = 1 :=
      faceCount_eq_one_of_boundary hSimpR hPureR hPMR hγ3' hbdγ
    -- recover `γ ⊆ t₀`: the unique γ-containing tet (faceCount = 1) is `t₀` by `huniqγ`.
    have hγt₀ : γ ⊆ t₀ := by
      have hfilt : (MR.support.filter (fun t => γ ⊆ t)).card = 1 := hγcount
      obtain ⟨t₀', ht₀'set⟩ := Finset.card_eq_one.mp hfilt
      have hmem' : t₀' ∈ MR.support.filter (fun t => γ ⊆ t) := by
        rw [ht₀'set]; exact Finset.mem_singleton_self _
      obtain ⟨ht₀'mem, hγt₀'⟩ := Finset.mem_filter.mp hmem'
      rw [← huniqγ t₀' ht₀'mem hγt₀']; exact hγt₀'
    have hγB : γ ∈ tetFaces (starTet sigma v) ∩
        (insert γ (cutSet sigma (W + fun _ => 1))) := by
      refine Finset.mem_inter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
      have hstarEq : starTet sigma v = insert v γ := by rw [starTet, hγ]
      exact Finset.mem_powersetCard.mpr ⟨by rw [hstarEq]; exact Finset.subset_insert _ _, hγ3'⟩
    have hglueStar : CleanGlueStep (starTet sigma v) MR.support
        (insert γ (cutSet sigma (W + fun _ => 1))) sigma := by
      have hgw : GlueStep (starTet sigma v) (insert γ (cutSet sigma (W + fun _ => 1))) sigma :=
        hglue
      exact cleanGlueStep_star_of_remainder hγ hγ3 hT4 hgw hTnot hvNotMR
        ⟨t₀, ht₀, hγt₀⟩ (by omega) hγB
    have hvt₀ : v ∉ t₀ := hvNotMR t₀ ht₀
    have ht₀4 : t₀.card = 4 := hPureR t₀ ht₀
    have hglue₀ : CleanGlueStep t₀ ({starTet sigma v} : Finset (Finset V))
        (tetFaces (starTet sigma v)) ((tetFaces t₀).erase γ ∪ K) :=
      cleanGlueStep_firstStar hγ hγ3 hT4 hvt₀ hγt₀ ht₀4 hglue₀_weak
    have hstart : ∃ l : List (Finset V), l.head? = some t₀ ∧ l.toFinset = MR.support ∧
        l.Nodup ∧ CleanShellFrom {starTet sigma v} (tetFaces (starTet sigma v)) l sigma :=
      degree3_star_start_cleanShellFrom sigma
        (insert γ (cutSet sigma (W + fun _ => 1))) MR.support hfreeMR ht₀ hγ hγ3' hγt₀
        hvNotMR huniqγ hTnot hglue₀ hrest_disj hfinal
    rw [hsupport]
    obtain ⟨l, _, hlτ, hnodup, hcsf⟩ := hstart
    exact FreelyCleanShellable.insert_of_cleanGlueStep hfreeMR hglueStar
      ⟨l, hlτ, hnodup, hcsf⟩
  · rcases hcase with ⟨hstar, hglue⟩
    have hT4 : (starTet sigma v).card = 4 := starTet_card_of_degree3 sigma hγ3
    have hURtet : UnitOn (cappedCutRight sigma W X γ c) (tetFaces (starTet sigma v)) := by
      dsimp [γ]
      rw [← hstar]
      exact hUR
    have hSuppRT : ∀ t ∈ MR.support, t ⊆ starTet sigma v := by
      intro t ht
      have htA : t ⊆ vertsOf (insert γ (cutSet sigma (W + fun _ => 1))) :=
        hSuppR t (by simpa only [MR, A] using ht)
      dsimp [γ] at htA
      rw [hstar, vertsOf_tetFaces_eq (starTet sigma v) hT4] at htA
      exact htA
    have hMRsupp : MR.support = {starTet sigma v} := by
      exact star_filter_support_singleton MR (cappedCutRight sigma W X γ c)
        (starTet sigma v) hT4 hURtet (by simpa only [MR, A, γ] using hMR)
        (by simpa only [MR, A, γ] using hTR) hSuppRT
    have hML_eq : ML = M.filter (fun t => ¬ (¬ t ⊆ A)) := by
      dsimp [ML]
      ext t
      rw [Finsupp.filter_apply, Finsupp.filter_apply]
      by_cases ht : t ⊆ A
      · rw [if_pos ht, if_pos]
        intro hneg
        exact hneg ht
      · rw [if_neg ht, if_neg]
        intro hnn
        exact hnn ht
    have hlt : nrm ML < nrm M := by
      have hlt' : nrm (M.filter (fun t => ¬ (¬ t ⊆ A))) < nrm M :=
        norm_lt_filter_neg_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
      rwa [← hML_eq] at hlt'
    have hSimpL : SimplicialChain ML := by
      intro t
      dsimp [ML, A, γ]
      rw [Finsupp.filter_apply]
      by_cases ht : t ⊆ vertsOf (insert (linkVerts sigma v) (cutSet sigma W))
      · rw [if_pos ht]
        exact hS t
      · rw [if_neg ht]
        exact Or.inr (Or.inl rfl)
    have hfreeML : FreelyCleanShellable ML.support (insert γ (cutSet sigma W)) :=
      IH (insert γ (cutSet sigma W)) (cappedCutLeft sigma W X γ c) ML hlt
        (by dsimp [γ]; exact hσL) (by dsimp [γ]; exact hUL)
        (by dsimp [γ]; exact hXLc) (by dsimp [ML, A, γ]; exact hML)
        (by dsimp [ML, A, γ]; exact hTL) hSimpL
    -- weak facts derived from the clean IH result.
    have hsupport : M.support = insert (starTet sigma v) ML.support := by
      have hsupport' :
          M.support = insert (starTet sigma v)
            (M.filter (fun t => ¬ (¬ t ⊆ A))).support := by
        exact support_eq_insert_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
      rwa [← hML_eq] at hsupport'
    have hPstar : ¬ (starTet sigma v) ⊆ A := by
      have hTin : starTet sigma v ∈ MR.support := by rw [hMRsupp]; simp
      have hTin' : ¬ M (starTet sigma v) = 0 ∧ ¬ (starTet sigma v) ⊆ A := by
        simpa [MR] using hTin
      exact hTin'.2
    have hTnot : starTet sigma v ∉ ML.support := by
      intro hmem
      have hne : ML (starTet sigma v) ≠ 0 := Finsupp.mem_support_iff.mp hmem
      have hzero : ML (starTet sigma v) = 0 := by simp [ML, hPstar]
      exact hne hzero
    have hbdML : bdry ML = cappedCutLeft sigma W X γ c := by dsimp [ML, A, γ]; exact hML
    have hMLne : ML.support.Nonempty := aleph_base_support_nonempty hσL hUL hbdML
    have hPML : IsPseudomanifold ML.support :=
      (hfreeML.clean3Complex hMLne).2.1
    have hfreeL_weak : FreelyShellable ML.support (insert γ (cutSet sigma W)) :=
      hfreeML.toBoundaryFreelyShellable
    have hTLML : IsTaut ML := by dsimp [ML, A, γ]; exact hTL
    have hsuppInfo :
        ∀ t ∈ ML.support, t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet sigma W)) :=
      aleph_base_taut_support_card4_subset_verts hσL hUL hbdML hTLML
    have hvNotML : ∀ t ∈ ML.support, v ∉ t := by
      have hvNotSigmaL : v ∉ vertsOf (insert γ (cutSet sigma W)) :=
        degree3_apex_notMem_left_verts_of_right_star (σ := sigma) (v := v) (W := W)
          (γ := γ) hsigma hγ3 rfl (by simpa [γ] using hW) hstar
      intro t ht hvt
      exact hvNotSigmaL ((hsuppInfo t ht).2 hvt)
    have hanchor :
        ∃ t₀ K,
          t₀ ∈ ML.support ∧
          GlueStep t₀ (tetFaces (starTet sigma v)) ((tetFaces t₀).erase γ ∪ K) ∧
          (∀ t ∈ ML.support, t ≠ t₀ → Disjoint (tetFaces t) (insert γ K)) ∧
          sigma = (insert γ (cutSet sigma W)).erase γ ∪ K := by
      exact degree3_hanchor sigma (insert γ (cutSet sigma W)) ML
        M A true v W γ hsigma hbig hv rfl hγ3 hW hσL
        (by
          dsimp [ML, A, γ]
          rw [hML]
          exact hUL)
        hfreeL_weak hSimpL (by dsimp only [ML, A, γ]; exact hTL) hPML hTnot hvNotML rfl
        (by simp [ML])
        (Or.inl rfl)
    obtain ⟨t₀, K, ht₀, hglue₀_weak, hrest_disj, hfinal⟩ := hanchor
    -- quantitative carries for the glue/start lemmas.
    have hPureL : ∀ t ∈ ML.support, t.card = 4 := fun t ht => (hsuppInfo t ht).1
    have hγ3' : γ.card = 3 := hγ ▸ hγ3
    have huniqγ : ∀ t ∈ ML.support, γ ⊆ t → t = t₀ := by
      intro t htmem hγt
      by_contra hne
      have hdisj := hrest_disj t htmem hne
      have hγinT : γ ∈ tetFaces t := Finset.mem_powersetCard.mpr ⟨hγt, hγ3'⟩
      exact (Finset.disjoint_left.mp hdisj) hγinT (Finset.mem_insert_self _ _)
    have hbdγ : bdry ML γ = 1 ∨ bdry ML γ = -1 := by
      rw [hbdML]; exact hUL.2 γ (Finset.mem_insert_self _ _)
    have hγcount : faceCount ML.support γ = 1 :=
      faceCount_eq_one_of_boundary hSimpL hPureL hPML hγ3' hbdγ
    have hγt₀ : γ ⊆ t₀ := by
      have hfilt : (ML.support.filter (fun t => γ ⊆ t)).card = 1 := hγcount
      obtain ⟨t₀', ht₀'set⟩ := Finset.card_eq_one.mp hfilt
      have hmem' : t₀' ∈ ML.support.filter (fun t => γ ⊆ t) := by
        rw [ht₀'set]; exact Finset.mem_singleton_self _
      obtain ⟨ht₀'mem, hγt₀'⟩ := Finset.mem_filter.mp hmem'
      rw [← huniqγ t₀' ht₀'mem hγt₀']; exact hγt₀'
    have hγB : γ ∈ tetFaces (starTet sigma v) ∩ (insert γ (cutSet sigma W)) := by
      refine Finset.mem_inter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
      have hstarEq : starTet sigma v = insert v γ := by rw [starTet, hγ]
      exact Finset.mem_powersetCard.mpr ⟨by rw [hstarEq]; exact Finset.subset_insert _ _, hγ3'⟩
    have hglueStar : CleanGlueStep (starTet sigma v) ML.support
        (insert γ (cutSet sigma W)) sigma := by
      have hgw : GlueStep (starTet sigma v) (insert γ (cutSet sigma W)) sigma := hglue
      exact cleanGlueStep_star_of_remainder hγ hγ3 hT4 hgw hTnot hvNotML
        ⟨t₀, ht₀, hγt₀⟩ (by omega) hγB
    have hvt₀ : v ∉ t₀ := hvNotML t₀ ht₀
    have ht₀4 : t₀.card = 4 := hPureL t₀ ht₀
    have hglue₀ : CleanGlueStep t₀ ({starTet sigma v} : Finset (Finset V))
        (tetFaces (starTet sigma v)) ((tetFaces t₀).erase γ ∪ K) :=
      cleanGlueStep_firstStar hγ hγ3 hT4 hvt₀ hγt₀ ht₀4 hglue₀_weak
    have hstart : ∃ l : List (Finset V), l.head? = some t₀ ∧ l.toFinset = ML.support ∧
        l.Nodup ∧ CleanShellFrom {starTet sigma v} (tetFaces (starTet sigma v)) l sigma :=
      degree3_star_start_cleanShellFrom sigma
        (insert γ (cutSet sigma W)) ML.support hfreeML ht₀ hγ hγ3' hγt₀
        hvNotML huniqγ hTnot hglue₀ hrest_disj hfinal
    rw [hsupport]
    obtain ⟨l, _, hlτ, hnodup, hcsf⟩ := hstart
    exact FreelyCleanShellable.insert_of_cleanGlueStep hfreeML hglueStar
      ⟨l, hlτ, hnodup, hcsf⟩

/-! ## Prime step, case 1: one reusable `CleanGlueStep` for re-gluing the eligible tet

The prime-step case-1 reassembly glues the eligible tet `e` back onto its
remainder `removeTet M e` (boundary the `flipBoundary`, ending at `σ`).  The four
boundary-only `CleanGlueStep` fields (`weak`/`newTet`) and the triangle count
(`hpmc`) transport from the existing `prime_isPM` block verbatim.  The two link
fields and the `clean` no-rogue-face field are the genuinely new content, all
governed by the **exposed-triangle apex** mechanism: an exposed triangle `f` of
`e` is a unit boundary face of `removeTet M e`, so it sits in exactly one remaining
tet (`faceCount = 1`), which then supplies an apex vertex of `e \ e'`.

A vertex of `e` always has an exposed triangle through it (pigeonhole: only one of
`e`'s four triangles misses a given vertex, but two are exposed), so `hvlc` closes
unconditionally.  For an edge `e'` of `e` the pigeonhole fails on exactly **one**
edge — the common edge of the two *shared* faces, `e \ (f₃ ∩ f₄)` — through which
both triangles are shared (hence vanish on removal).  On that single edge the
nonempty branch is unavailable and the empty-link branch is required; that link
emptiness is **edge-manifold content not carried by `IsPseudomanifold`**, so it is
taken here as the single hypothesis `hOppEmpty`.  The same one edge governs the
`clean` field (an interface edge in a remaining tet must lie in an exposed
triangle, which again fails only on `e \ (f₃ ∩ f₄)`). -/

/-- **`hOppEmpty`, case-2 half (flip edge present).** When the flip edge
`f₃ ∩ f₄` is already in `σ`, removing the eligible `e` splits the remainder into
two vertex-sides `A, B` meeting only in that edge (`flipEdgePresent_side_sets`),
and **every** remaining tet is wholly in one side.  The flip-opposite edge
`e \ (f₃ ∩ f₄) = {z₃, z₄}` straddles the split (`z₃ ∈ f₄ ⊆ B` but `z₃ ∉ A`;
`z₄ ∈ f₃ ⊆ A` but `z₄ ∉ B`), so no single side — hence no remaining tet — contains
it.  This is the *combinatorial* half: it needs no edge-link topology, only the
side separation.  (The case-1 half — `¬ FlipEdgePresent`, where the remainder is a
single sphere — is the genuine edge-manifold content and is not closed here.) -/
private lemma oppEdge_empty_of_flipEdgePresent {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅ := by
  classical
  obtain ⟨A, B, hAB, hcd2, _, _, hcover, hsep, hf₃A, hf₃notB, hf₄B, hf₄notA, _⟩ :=
    flipEdgePresent_side_sets hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
  -- `f₃, f₄` are triangles of `e`; set `z₃ := e \ f₃`, `z₄ := e \ f₄`.
  have hf₃exp : f₃ ∈ exposedFaces M e := by rw [hexp]; exact Finset.mem_insert_self f₃ _
  have hf₄exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
  have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
  have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
  have hf₃e : f₃ ⊆ e := (Finset.mem_powersetCard.mp hf₃tet).1
  have hf₄e : f₄ ⊆ e := (Finset.mem_powersetCard.mp hf₄tet).1
  have hf₃3 : f₃.card = 3 := (Finset.mem_powersetCard.mp hf₃tet).2
  have hf₄3 : f₄.card = 3 := (Finset.mem_powersetCard.mp hf₄tet).2
  have he4 : e.card = 4 := he.1
  have hcard3 : (e \ f₃).card = 1 := by rw [Finset.card_sdiff_of_subset hf₃e, he4, hf₃3]
  have hcard4 : (e \ f₄).card = 1 := by rw [Finset.card_sdiff_of_subset hf₄e, he4, hf₄3]
  obtain ⟨z₃, hz₃⟩ := Finset.card_eq_one.mp hcard3
  obtain ⟨z₄, hz₄⟩ := Finset.card_eq_one.mp hcard4
  have hz₃mem : z₃ ∈ e \ f₃ := hz₃ ▸ Finset.mem_singleton_self z₃
  have hz₄mem : z₄ ∈ e \ f₄ := hz₄ ▸ Finset.mem_singleton_self z₄
  rw [Finset.mem_sdiff] at hz₃mem hz₄mem
  -- `f₃ = e.erase z₃`, `f₄ = e.erase z₄`.
  have heq3 : f₃ = e.erase z₃ := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₃mem.2 (h ▸ ha), hf₃e ha⟩
    · rw [Finset.card_erase_of_mem hz₃mem.1, he4, hf₃3]
  have heq4 : f₄ = e.erase z₄ := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₄mem.2 (h ▸ ha), hf₄e ha⟩
    · rw [Finset.card_erase_of_mem hz₄mem.1, he4, hf₄3]
  have hz₃₄ : z₃ ≠ z₄ := by
    rintro rfl; exact hf₃₄ (heq3.trans heq4.symm)
  -- `f₃ ∩ f₄ = e \ {z₃, z₄}`, so the flip-opposite edge is `{z₃, z₄}`.
  have hinter_eq : f₃ ∩ f₄ = e \ ({z₃, z₄} : Finset V) := by
    ext a
    simp only [Finset.mem_inter, heq3, heq4, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hopp_eq : e \ (f₃ ∩ f₄) = ({z₃, z₄} : Finset V) := by
    rw [hinter_eq]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hae, hac⟩; by_contra hane; exact hac ⟨hae, hane⟩
    · rintro (rfl | rfl)
      · exact ⟨hz₃mem.1, fun h => h.2 (Or.inl rfl)⟩
      · exact ⟨hz₄mem.1, fun h => h.2 (Or.inr rfl)⟩
  -- `f₃ ∩ f₄ ⊆ A` (since `f₃ ⊆ A`).
  have hcd_subA : f₃ ∩ f₄ ⊆ A := (Finset.inter_subset_left).trans hf₃A
  -- `z₃ ∉ A`: else `f₄ = insert z₃ (f₃ ∩ f₄) ⊆ A`, contradicting `¬ f₄ ⊆ A`.
  have hz₃notA : z₃ ∉ A := by
    intro hz₃A
    apply hf₄notA
    intro a ha
    -- `f₄ = e.erase z₄`; its elements are `z₃` or in `f₃ ∩ f₄`.
    have hae : a ∈ e := hf₄e ha
    by_cases haz₃ : a = z₃
    · exact haz₃ ▸ hz₃A
    · exact hcd_subA (Finset.mem_inter.mpr ⟨by
        rw [heq3, Finset.mem_erase]; exact ⟨haz₃, hae⟩, ha⟩)
  -- `z₄ ∉ B`: symmetric.
  have hcd_subB : f₃ ∩ f₄ ⊆ B := (Finset.inter_subset_right).trans hf₄B
  have hz₄notB : z₄ ∉ B := by
    intro hz₄B
    apply hf₃notB
    intro a ha
    have hae : a ∈ e := hf₃e ha
    by_cases haz₄ : a = z₄
    · exact haz₄ ▸ hz₄B
    · exact hcd_subB (Finset.mem_inter.mpr ⟨ha, by
        rw [heq4, Finset.mem_erase]; exact ⟨haz₄, hae⟩⟩)
  -- now no remaining tet contains `{z₃, z₄}`.
  rw [hopp_eq]
  apply edgeLinkVerts_eq_empty
  intro t ht hsub
  have hz₃t : z₃ ∈ t := hsub (by simp)
  have hz₄t : z₄ ∈ t := hsub (by simp)
  rcases hcover t ht with htA | htB
  · exact hz₃notA (htA hz₃t)
  · exact hz₄notB (htB hz₄t)

/-- A triangle of `e` that is **exposed** (`f ∈ exposedFaces M e`) is a unit
boundary face of `removeTet M e`, hence lies in exactly one remaining tet.  This
packages the `faceCount_eq_one_of_boundary` extraction used to read off an apex. -/
private lemma exposed_triangle_unique_remaining_tet {σ : Finset (Finset V)}
    {X M : Chain V} {e f : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hPMe : IsPseudomanifold (removeTet M e).support)
    (he : EligibleTet M e) (hf : f ∈ exposedFaces M e) :
    ∃ t ∈ (removeTet M e).support, f ⊆ t := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hftet : f ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf
  have hf3 : f.card = 3 := (Finset.mem_powersetCard.mp hftet).2
  have hUe : UnitOn (bdry (removeTet M e)) ((σ \ sharedFaces M e) ∪ exposedFaces M e) :=
    unitOn_flipBoundary_of_eligible hUb hS he
  have hfflip : f ∈ (σ \ sharedFaces M e) ∪ exposedFaces M e := Finset.mem_union_right _ hf
  have hbd : bdry (removeTet M e) f = 1 ∨ bdry (removeTet M e) f = -1 := hUe.2 f hfflip
  have hSe : SimplicialChain (removeTet M e) := simplicialChain_removeTet hS
  have hPureE : ∀ t ∈ (removeTet M e).support, t.card = 4 := by
    intro t ht
    rw [support_removeTet_of_mem he.2.1] at ht
    exact hPure t (Finset.mem_of_mem_erase ht)
  have h1 : faceCount (removeTet M e).support f = 1 :=
    faceCount_eq_one_of_boundary hSe hPureE hPMe hf3 hbd
  unfold faceCount at h1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h1
  have htmem : t ∈ (removeTet M e).support.filter (fun s => f ⊆ s) :=
    ht ▸ Finset.mem_singleton_self t
  rw [Finset.mem_filter] at htmem
  exact ⟨t, htmem.1, htmem.2⟩

/-- **`hOppEmpty`, reduction to full edge-link connectedness.** Given
`EdgeLinkConnected M.support`, the flip-opposite edge `e \ (f₃ ∩ f₄)` lies in no
remaining tet.  The `EdgeLinkConnected M.support` hypothesis is itself the new
theorem `taut_edgeLinkConnected`, not yet available. -/
private lemma oppEdge_empty_of_full_edgeLinkConnected {σ : Finset (Finset V)}
    {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hELM : EdgeLinkConnected M.support) :
    edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅ := by
  classical
  -- exposed-pair geometry: `f₃ = e.erase z₃`, `f₄ = e.erase z₄`, `e \ (f₃ ∩ f₄) = {z₃, z₄}`.
  have hf₃exp : f₃ ∈ exposedFaces M e := by rw [hexp]; exact Finset.mem_insert_self f₃ _
  have hf₄exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
  have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
  have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
  have hf₃e : f₃ ⊆ e := (Finset.mem_powersetCard.mp hf₃tet).1
  have hf₄e : f₄ ⊆ e := (Finset.mem_powersetCard.mp hf₄tet).1
  have hf₃3 : f₃.card = 3 := (Finset.mem_powersetCard.mp hf₃tet).2
  have hf₄3 : f₄.card = 3 := (Finset.mem_powersetCard.mp hf₄tet).2
  have he4 : e.card = 4 := he.1
  have hcard3 : (e \ f₃).card = 1 := by rw [Finset.card_sdiff_of_subset hf₃e, he4, hf₃3]
  have hcard4 : (e \ f₄).card = 1 := by rw [Finset.card_sdiff_of_subset hf₄e, he4, hf₄3]
  obtain ⟨z₃, hz₃⟩ := Finset.card_eq_one.mp hcard3
  obtain ⟨z₄, hz₄⟩ := Finset.card_eq_one.mp hcard4
  have hz₃mem : z₃ ∈ e \ f₃ := hz₃ ▸ Finset.mem_singleton_self z₃
  have hz₄mem : z₄ ∈ e \ f₄ := hz₄ ▸ Finset.mem_singleton_self z₄
  rw [Finset.mem_sdiff] at hz₃mem hz₄mem
  have heq3 : f₃ = e.erase z₃ := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₃mem.2 (h ▸ ha), hf₃e ha⟩
    · rw [Finset.card_erase_of_mem hz₃mem.1, he4, hf₃3]
  have heq4 : f₄ = e.erase z₄ := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₄mem.2 (h ▸ ha), hf₄e ha⟩
    · rw [Finset.card_erase_of_mem hz₄mem.1, he4, hf₄3]
  have hz₃₄ : z₃ ≠ z₄ := by
    rintro rfl; exact hf₃₄ (heq3.trans heq4.symm)
  have hinter_eq : f₃ ∩ f₄ = e \ ({z₃, z₄} : Finset V) := by
    ext a
    simp only [Finset.mem_inter, heq3, heq4, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hopp_eq : e \ (f₃ ∩ f₄) = ({z₃, z₄} : Finset V) := by
    rw [hinter_eq]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hae, hac⟩; by_contra hane; exact hac ⟨hae, hane⟩
    · rintro (rfl | rfl)
      · exact ⟨hz₃mem.1, fun h => h.2 (Or.inl rfl)⟩
      · exact ⟨hz₄mem.1, fun h => h.2 (Or.inr rfl)⟩
  rw [hopp_eq]
  -- `O = {z₃, z₄}` (card 2, ⊆ e); `{z₃,z₄}` ⊄ f₃ and ⊄ f₄.
  have hz₃e : z₃ ∈ e := hz₃mem.1
  have hz₄e : z₄ ∈ e := hz₄mem.1
  have hOcard : ({z₃, z₄} : Finset V).card = 2 := Finset.card_pair hz₃₄
  have hOsub : ({z₃, z₄} : Finset V) ⊆ e := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hz₃e
    · rw [Finset.mem_singleton] at ha; exact ha ▸ hz₄e
  have hz₃notf₃ : z₃ ∉ f₃ := by rw [heq3]; exact Finset.notMem_erase z₃ e
  have hz₄notf₄ : z₄ ∉ f₄ := by rw [heq4]; exact Finset.notMem_erase z₄ e
  -- `P = e \ {z₃, z₄} = {p₁, p₂}` (the two flip-edge vertices), `e = {z₃,z₄} ∪ {p₁,p₂}`.
  have hPcard : (e \ ({z₃, z₄} : Finset V)).card = 2 := by
    rw [Finset.card_sdiff_of_subset hOsub, he4, hOcard]
  obtain ⟨p₁, p₂, hp₁₂, hPeq⟩ := Finset.card_eq_two.mp hPcard
  have he_eq : e = ({z₃, z₄} : Finset V) ∪ {p₁, p₂} := by
    rw [← hPeq, Finset.union_sdiff_of_subset hOsub]
  -- `sharedFaces = tetFaces \ exposedFaces`.
  have hsh_eq2 : tetFaces e \ exposedFaces M e = sharedFaces M e := by
    rw [exposedFaces, Finset.sdiff_sdiff_self_left,
      Finset.inter_eq_right.mpr (sharedFaces_subset_tetFaces M e)]
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hPM : IsPseudomanifold M.support := taut_isPseudomanifold hσ hU hXc hMX hT hS
  -- KEY: any tet of `M` containing `insert p {z₃,z₄}` (p a flip-edge vertex) equals `e`.
  have huniq : ∀ p ∈ ({p₁, p₂} : Finset V), ∀ s ∈ M.support,
      insert p ({z₃, z₄} : Finset V) ⊆ s → s = e := by
    intro p hp s hs hsub
    have hp_e : p ∈ e := by rw [he_eq]; exact Finset.mem_union_right _ hp
    have hp_notO : p ∉ ({z₃, z₄} : Finset V) := by
      have hpP : p ∈ e \ ({z₃, z₄} : Finset V) := hPeq ▸ hp
      exact (Finset.mem_sdiff.mp hpP).2
    have hg_card : (insert p ({z₃, z₄} : Finset V)).card = 3 := by
      rw [Finset.card_insert_of_notMem hp_notO, hOcard]
    have hg_sub_e : insert p ({z₃, z₄} : Finset V) ⊆ e := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hp_e
      · exact hOsub ha
    have hg_tet : insert p ({z₃, z₄} : Finset V) ∈ tetFaces e :=
      Finset.mem_powersetCard.mpr ⟨hg_sub_e, hg_card⟩
    have hOsub_g : ({z₃, z₄} : Finset V) ⊆ insert p {z₃, z₄} := Finset.subset_insert _ _
    have hg_ne_f₃ : insert p ({z₃, z₄} : Finset V) ≠ f₃ := by
      intro h; exact hz₃notf₃ (h ▸ hOsub_g (Finset.mem_insert_self z₃ _))
    have hg_ne_f₄ : insert p ({z₃, z₄} : Finset V) ≠ f₄ := by
      intro h
      exact hz₄notf₄ (h ▸ hOsub_g (Finset.mem_insert_of_mem (Finset.mem_singleton_self z₄)))
    have hg_shared : insert p ({z₃, z₄} : Finset V) ∈ sharedFaces M e := by
      rw [← hsh_eq2, hexp]
      refine Finset.mem_sdiff.mpr ⟨hg_tet, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hg_ne_f₃, hg_ne_f₄⟩
    have hg_inBdry : insert p ({z₃, z₄} : Finset V) ∈ (bdry M).support := by
      have := hg_shared; rw [sharedFaces] at this; exact (Finset.mem_inter.mp this).2
    have hg_inσ : insert p ({z₃, z₄} : Finset V) ∈ σ := by rw [← hUb.1]; exact hg_inBdry
    have hbd : bdry M (insert p {z₃, z₄}) = 1 ∨ bdry M (insert p {z₃, z₄}) = -1 :=
      hUb.2 _ hg_inσ
    have hfc1 : faceCount M.support (insert p {z₃, z₄}) = 1 :=
      faceCount_eq_one_of_boundary hS hPure hPM hg_card hbd
    unfold faceCount at hfc1
    obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hfc1
    have he_in : e ∈ M.support.filter (fun x => insert p ({z₃, z₄} : Finset V) ⊆ x) :=
      Finset.mem_filter.mpr ⟨he.2.1, hg_sub_e⟩
    have hs_in : s ∈ M.support.filter (fun x => insert p ({z₃, z₄} : Finset V) ⊆ x) :=
      Finset.mem_filter.mpr ⟨hs, hsub⟩
    rw [hw0, Finset.mem_singleton] at he_in hs_in
    exact hs_in.trans he_in.symm
  -- no remaining tet contains the opposite edge `{z₃, z₄}`.
  apply edgeLinkVerts_eq_empty
  intro t ht hsub
  rw [support_removeTet_of_mem he.2.1, Finset.mem_erase] at ht
  obtain ⟨htne, htM⟩ := ht
  have ht4 : t.card = 4 := hPure t htM
  by_cases hcase : (t \ ({z₃, z₄} : Finset V)) ⊆ {p₁, p₂}
  · -- then `t \ {z₃,z₄} = {p₁,p₂}` and `t = e`, contradicting `t ≠ e`.
    have htdiff : (t \ ({z₃, z₄} : Finset V)).card = 2 := by
      rw [Finset.card_sdiff_of_subset hsub, ht4, hOcard]
    have heqd : t \ ({z₃, z₄} : Finset V) = {p₁, p₂} :=
      Finset.eq_of_subset_of_card_le hcase (by rw [htdiff, Finset.card_pair hp₁₂])
    have hte : t = e := by
      rw [he_eq, ← heqd, Finset.union_sdiff_of_subset hsub]
    exact htne hte
  · -- otherwise some apex `w ∈ t` avoids both `{z₃,z₄}` and `{p₁,p₂}`.
    rw [Finset.not_subset] at hcase
    obtain ⟨w, hwt, hwp⟩ := hcase
    rw [Finset.mem_sdiff] at hwt
    obtain ⟨hwt, hwO⟩ := hwt
    have hw_link : w ∈ edgeLinkVerts M.support ({z₃, z₄} : Finset V) := by
      rw [mem_edgeLinkVerts_iff]; exact ⟨⟨t, htM, hsub, hwt⟩, hwO⟩
    have hp₁_e : p₁ ∈ e := by
      rw [he_eq]; exact Finset.mem_union_right _ (Finset.mem_insert_self p₁ _)
    have hp₁_notO : p₁ ∉ ({z₃, z₄} : Finset V) := by
      have hpP : p₁ ∈ e \ ({z₃, z₄} : Finset V) := hPeq ▸ Finset.mem_insert_self p₁ _
      exact (Finset.mem_sdiff.mp hpP).2
    have hp₁_link : p₁ ∈ edgeLinkVerts M.support ({z₃, z₄} : Finset V) := by
      rw [mem_edgeLinkVerts_iff]; exact ⟨⟨e, he.2.1, hOsub, hp₁_e⟩, hp₁_notO⟩
    -- the flip-edge pair `{p₁,p₂}` is closed under edge-link adjacency.
    have hclosed : ∀ u ∈ ({p₁, p₂} : Finset V), ∀ v,
        (edgeLinkGraph M.support ({z₃, z₄} : Finset V)).Adj u v → v ∈ ({p₁, p₂} : Finset V) := by
      intro u hu v hadj
      obtain ⟨huv, hins⟩ := hadj
      have hsub2 : insert u ({z₃, z₄} : Finset V) ⊆ insert u (insert v {z₃, z₄}) := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)
      have heq_tet : insert u (insert v ({z₃, z₄} : Finset V)) = e := huniq u hu _ hins hsub2
      have hv_e : v ∈ e := by
        rw [← heq_tet]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hv_notO : v ∉ ({z₃, z₄} : Finset V) := by
        intro hvO
        have hue : insert u ({z₃, z₄} : Finset V) = e := by
          rw [← heq_tet, Finset.insert_eq_self.mpr hvO]
        have hlecard : (insert u ({z₃, z₄} : Finset V)).card ≤ 3 := by
          calc (insert u ({z₃, z₄} : Finset V)).card
              ≤ ({z₃, z₄} : Finset V).card + 1 := Finset.card_insert_le _ _
            _ = 3 := by rw [hOcard]
        rw [hue, he4] at hlecard
        omega
      rw [← hPeq]; exact Finset.mem_sdiff.mpr ⟨hv_e, hv_notO⟩
    have hnr : ¬ (edgeLinkGraph M.support ({z₃, z₄} : Finset V)).Reachable p₁ w := by
      rintro ⟨walk⟩
      exact hwp (walk_mem_of_adj_closed hclosed walk (Finset.mem_insert_self p₁ _))
    exact (not_edgeLinkConnected_of_subset (subset_refl M.support) hOcard hp₁_link hw_link hnr) hELM

/-- **One clean glue step for re-gluing the eligible tet `e`** onto its remainder
`removeTet M e` (boundary the flip-boundary, ending at `σ`).  All fields are
discharged from the eligible geometry except the edge-link emptiness on the single
flip-opposite edge `e \ (f₃ ∩ f₄)`, supplied as `hOppEmpty`.  `clean`, `helc`, and
`hvlc` are driven by the exposed-triangle apex mechanism. -/
lemma cleanGlueStep_eligible {σ : Finset (Finset V)} {X M : Chain V}
    {e u f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (he : EligibleTet M e) (hu : EligibleTet M u)
    (hdisj : Disjoint (sharedFaces M e) (sharedFaces M u))
    (hPMu : IsPseudomanifold (removeTet M u).support)
    (hPMe : IsPseudomanifold (removeTet M e).support)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hOppEmpty : edgeLinkVerts (removeTet M e).support (e \ (f₃ ∩ f₄)) = ∅) :
    CleanGlueStep e (removeTet M e).support
      ((σ \ sharedFaces M e) ∪ exposedFaces M e) σ := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hweak : GlueStep e ((σ \ sharedFaces M e) ∪ exposedFaces M e) σ :=
    glueStep_flipBoundary_of_eligible hUb he
  have he_not_old : e ∉ (removeTet M e).support := by
    rw [support_removeTet_of_mem he.2.1]; exact Finset.notMem_erase e M.support
  -- `tetFaces e ∩ flipBoundary = exposedFaces M e` (shared faces are erased from `σ`).
  have hsh_eq : sharedFaces M e = tetFaces e ∩ σ := by
    simp only [sharedFaces, hUb.1]
  have hexp_mem : ∀ x, x ∈ exposedFaces M e ↔ (x ∈ tetFaces e ∧ x ∉ σ) := by
    intro x
    simp only [exposedFaces, hsh_eq, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hinterB : tetFaces e ∩ ((σ \ sharedFaces M e) ∪ exposedFaces M e) = exposedFaces M e := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    rw [hexp_mem x, hsh_eq]
    simp only [Finset.mem_inter]
    tauto
  -- shared triangles vanish on removal.
  have hshared0 : ∀ r ∈ sharedFaces M e, faceCount (removeTet M e).support r = 0 :=
    fun r hr =>
      faceCount_removeTet_sharedFace_eq_zero hσ hU hXc hMX hT hS hPure he hu hdisj hPMu hr
  -- the exposed faces are exactly `f₃, f₄`.
  have hf₃exp : f₃ ∈ exposedFaces M e := by rw [hexp]; exact Finset.mem_insert_self f₃ _
  have hf₄exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
  -- a face `g ⊆ e` lying in a remaining tet has its containing triangles available.
  refine
    { weak := hweak
      newTet := he_not_old
      clean := ?_
      hpmc := ?_
      helc := ?_
      hvlc := ?_ }
  · -- clean: a face `f ⊆ e` in a remaining tet `s` lies in an exposed triangle.
    -- Triangles: shared ⟹ in no remaining tet (contra), exposed ⟹ itself; `f = e` ⟹
    -- `s = e` (contra freshness); vertices/edges sit in `f₃` or `f₄` unless `f ⊇` the
    -- flip-opposite edge, which would make its edge-link nonempty (contra `hOppEmpty`).
    rw [hinterB]
    rintro f hfe ⟨s, hsmem, hfs⟩
    have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
    have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
    have hf₃e : f₃ ⊆ e := (Finset.mem_powersetCard.mp hf₃tet).1
    have hf₄e : f₄ ⊆ e := (Finset.mem_powersetCard.mp hf₄tet).1
    have hf₃3 : f₃.card = 3 := (Finset.mem_powersetCard.mp hf₃tet).2
    have hf₄3 : f₄.card = 3 := (Finset.mem_powersetCard.mp hf₄tet).2
    have he4 : e.card = 4 := he.1
    have hPureE : ∀ t ∈ (removeTet M e).support, t.card = 4 := by
      intro t ht
      rw [support_removeTet_of_mem he.2.1] at ht
      exact hPure t (Finset.mem_of_mem_erase ht)
    have hs4 : s.card = 4 := hPureE s hsmem
    -- `z₃ := e \ f₃`, `z₄ := e \ f₄` (single vertices); `z₃ ≠ z₄`.
    have hcard3 : (e \ f₃).card = 1 := by rw [Finset.card_sdiff_of_subset hf₃e, he4, hf₃3]
    have hcard4 : (e \ f₄).card = 1 := by rw [Finset.card_sdiff_of_subset hf₄e, he4, hf₄3]
    obtain ⟨z₃, hz₃⟩ := Finset.card_eq_one.mp hcard3
    obtain ⟨z₄, hz₄⟩ := Finset.card_eq_one.mp hcard4
    have hz₃mem : z₃ ∈ e \ f₃ := hz₃ ▸ Finset.mem_singleton_self z₃
    have hz₄mem : z₄ ∈ e \ f₄ := hz₄ ▸ Finset.mem_singleton_self z₄
    rw [Finset.mem_sdiff] at hz₃mem hz₄mem
    -- a card-3 subset of `e` missing `z₃` is `f₃` (and the analogue for `z₄`/`f₄`).
    have heq3 : f₃ = e.erase z₃ := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₃mem.2 (h ▸ ha), hf₃e ha⟩
      · rw [Finset.card_erase_of_mem hz₃mem.1, he4, hf₃3]
    have heq4 : f₄ = e.erase z₄ := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₄mem.2 (h ▸ ha), hf₄e ha⟩
      · rw [Finset.card_erase_of_mem hz₄mem.1, he4, hf₄3]
    have hz₃₄ : z₃ ≠ z₄ := by
      rintro rfl; exact hf₃₄ (heq3.trans heq4.symm)
    -- membership in `f₃` / `f₄` reduces to avoiding `z₃` / `z₄`.
    have hmem3 : ∀ {a}, a ∈ e → (a ∈ f₃ ↔ a ≠ z₃) := by
      intro a hae; rw [heq3, Finset.mem_erase]; exact ⟨fun h => h.1, fun h => ⟨h, hae⟩⟩
    have hmem4 : ∀ {a}, a ∈ e → (a ∈ f₄ ↔ a ≠ z₄) := by
      intro a hae; rw [heq4, Finset.mem_erase]; exact ⟨fun h => h.1, fun h => ⟨h, hae⟩⟩
    -- the flip-opposite edge.
    have hopp_eq : e \ (f₃ ∩ f₄) = ({z₃, z₄} : Finset V) := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_inter, heq3, heq4, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hae, hni⟩; by_contra hc; push_neg at hc; exact hni ⟨⟨hc.1, hae⟩, ⟨hc.2, hae⟩⟩
      · rintro (rfl | rfl)
        · exact ⟨hz₃mem.1, fun h => h.1.1 rfl⟩
        · exact ⟨hz₄mem.1, fun h => h.2.1 rfl⟩
    by_cases hopp : ({z₃, z₄} : Finset V) ⊆ f
    · -- `f` contains the flip-opposite edge, which sits in remaining tet `s`: empty-link
      -- contradiction.  Pick an apex `w ∈ s \ {z₃, z₄}` (s has 4 vertices).
      exfalso
      have hsub : ({z₃, z₄} : Finset V) ⊆ s := hopp.trans hfs
      have hpc : ({z₃, z₄} : Finset V).card = 2 := Finset.card_pair hz₃₄
      have hsdiff : (s \ ({z₃, z₄} : Finset V)).card = 2 := by
        rw [Finset.card_sdiff_of_subset hsub, hs4, hpc]
      have hne : (s \ ({z₃, z₄} : Finset V)).Nonempty := by rw [← Finset.card_pos, hsdiff]; omega
      obtain ⟨w, hw⟩ := hne
      rw [Finset.mem_sdiff] at hw
      have hwapex : w ∈ edgeLinkVerts (removeTet M e).support ({z₃, z₄} : Finset V) := by
        rw [mem_edgeLinkVerts_iff]; exact ⟨⟨s, hsmem, hsub, hw.1⟩, hw.2⟩
      rw [hopp_eq] at hOppEmpty
      rw [hOppEmpty] at hwapex
      exact absurd hwapex (Finset.notMem_empty w)
    · -- `f` does not contain the opposite edge, so `z₃ ∉ f` or `z₄ ∉ f`; the matching
      -- exposed face then contains `f`.
      have hor : z₃ ∉ f ∨ z₄ ∉ f := by
        by_contra hc; push_neg at hc
        exact hopp (by
          intro a ha; rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hc.1
          · rw [Finset.mem_singleton] at ha; subst ha; exact hc.2)
      rcases hor with hz₃f | hz₄f
      · exact ⟨f₃, hf₃exp, fun a ha => (hmem3 (hfe ha)).mpr (fun h => hz₃f (h ▸ ha))⟩
      · exact ⟨f₄, hf₄exp, fun a ha => (hmem4 (hfe ha)).mpr (fun h => hz₄f (h ▸ ha))⟩
  · -- hpmc: identical to the `prime_isPM` clean-glue block.
    intro f hf3 hfe
    have hftet : f ∈ tetFaces e := Finset.mem_powersetCard.mpr ⟨hfe, hf3⟩
    by_cases hsh : f ∈ sharedFaces M e
    · have h0 : faceCount (removeTet M e).support f = 0 := hshared0 f hsh
      omega
    · have hexpf : f ∈ exposedFaces M e := Finset.mem_sdiff.mpr ⟨hftet, hsh⟩
      have hUe : UnitOn (bdry (removeTet M e)) ((σ \ sharedFaces M e) ∪ exposedFaces M e) :=
        unitOn_flipBoundary_of_eligible hUb hS he
      have hfflip : f ∈ (σ \ sharedFaces M e) ∪ exposedFaces M e :=
        Finset.mem_union_right _ hexpf
      have hbd : bdry (removeTet M e) f = 1 ∨ bdry (removeTet M e) f = -1 := hUe.2 f hfflip
      have hSe : SimplicialChain (removeTet M e) := simplicialChain_removeTet hS
      have hPureE : ∀ t ∈ (removeTet M e).support, t.card = 4 := by
        intro t ht
        rw [support_removeTet_of_mem he.2.1] at ht
        exact hPure t (Finset.mem_of_mem_erase ht)
      have h1 : faceCount (removeTet M e).support f = 1 :=
        faceCount_eq_one_of_boundary hSe hPureE hPMe hf3 hbd
      omega
  · -- helc: an edge `e' ⊆ e` either has an exposed triangle through it (apex via its
    -- unique remaining tet) or is the flip-opposite edge `e \ (f₃ ∩ f₄)` (empty link).
    intro e' he' he'2
    have he4 : e.card = 4 := he.1
    have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
    have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
    have hf₃e : f₃ ⊆ e := (Finset.mem_powersetCard.mp hf₃tet).1
    have hf₄e : f₄ ⊆ e := (Finset.mem_powersetCard.mp hf₄tet).1
    have hf₃3 : f₃.card = 3 := (Finset.mem_powersetCard.mp hf₃tet).2
    have hf₄3 : f₄.card = 3 := (Finset.mem_powersetCard.mp hf₄tet).2
    by_cases hsub : e' ⊆ f₃ ∨ e' ⊆ f₄
    · -- ≥ 1 exposed triangle through `e'`: apex from its unique remaining tet.
      right
      obtain ⟨f, hfexp, he'f, hfe, hf3⟩ :
          ∃ f, f ∈ exposedFaces M e ∧ e' ⊆ f ∧ f ⊆ e ∧ f.card = 3 := by
        rcases hsub with h | h
        · exact ⟨f₃, hf₃exp, h, hf₃e, hf₃3⟩
        · exact ⟨f₄, hf₄exp, h, hf₄e, hf₄3⟩
      obtain ⟨t, htmem, hft⟩ :=
        exposed_triangle_unique_remaining_tet hσ hU hMX hT hS hPure hPMe he hfexp
      -- `f \ e'` has card 1: the apex `w ∈ e \ e'`, with `e' ⊆ t` and `w ∈ t`.
      have hcard : (f \ e').card = 1 := by
        rw [Finset.card_sdiff_of_subset he'f, hf3, he'2]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
      have hwfe : w ∈ f \ e' := hw ▸ Finset.mem_singleton_self w
      rw [Finset.mem_sdiff] at hwfe
      obtain ⟨hwf, hwe'⟩ := hwfe
      refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [Finset.mem_sdiff]; exact ⟨hfe hwf, hwe'⟩
      · rw [mem_edgeLinkVerts_iff]
        exact ⟨⟨t, htmem, he'f.trans hft, hft hwf⟩, hwe'⟩
    · -- no exposed triangle through `e'`: then `e' = e \ (f₃ ∩ f₄)`, link empty.
      left
      push_neg at hsub
      obtain ⟨hn3, hn4⟩ := hsub
      -- `z₃ := e \ f₃` is a single vertex of `e' ` (`e' ⊄ f₃`); likewise `z₄`.
      have hcard3 : (e \ f₃).card = 1 := by rw [Finset.card_sdiff_of_subset hf₃e, he4, hf₃3]
      have hcard4 : (e \ f₄).card = 1 := by rw [Finset.card_sdiff_of_subset hf₄e, he4, hf₄3]
      obtain ⟨z₃, hz₃⟩ := Finset.card_eq_one.mp hcard3
      obtain ⟨z₄, hz₄⟩ := Finset.card_eq_one.mp hcard4
      have hz₃mem : z₃ ∈ e \ f₃ := hz₃ ▸ Finset.mem_singleton_self z₃
      have hz₄mem : z₄ ∈ e \ f₄ := hz₄ ▸ Finset.mem_singleton_self z₄
      rw [Finset.mem_sdiff] at hz₃mem hz₄mem
      -- `e' ⊄ f₃` forces `z₃ ∈ e'` (the only `e`-vertex outside `f₃`).
      have hz₃e' : z₃ ∈ e' := by
        by_contra hzn
        apply hn3
        intro a ha
        have hae : a ∈ e := he' ha
        by_contra haf
        have : a ∈ e \ f₃ := Finset.mem_sdiff.mpr ⟨hae, haf⟩
        rw [hz₃, Finset.mem_singleton] at this; subst this; exact hzn ha
      have hz₄e' : z₄ ∈ e' := by
        by_contra hzn
        apply hn4
        intro a ha
        have hae : a ∈ e := he' ha
        by_contra haf
        have : a ∈ e \ f₄ := Finset.mem_sdiff.mpr ⟨hae, haf⟩
        rw [hz₄, Finset.mem_singleton] at this; subst this; exact hzn ha
      have hz₃₄ : z₃ ≠ z₄ := by
        rintro rfl
        -- `z₃ = z₄` ⟹ `f₃ = e.erase z₃ = f₄`.
        have hfe3 : f₃ = e.erase z₃ := by
          apply Finset.eq_of_subset_of_card_le
          · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₃mem.2 (h ▸ ha), hf₃e ha⟩
          · rw [Finset.card_erase_of_mem hz₃mem.1, he4, hf₃3]
        have hfe4 : f₄ = e.erase z₃ := by
          apply Finset.eq_of_subset_of_card_le
          · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₄mem.2 (h ▸ ha), hf₄e ha⟩
          · rw [Finset.card_erase_of_mem hz₄mem.1, he4, hf₄3]
        exact hf₃₄ (hfe3.trans hfe4.symm)
      -- `{z₃, z₄} ⊆ e'`, both card 2, so `e' = {z₃, z₄} = e \ (f₃ ∩ f₄)`.
      have hpair_sub : ({z₃, z₄} : Finset V) ⊆ e' := by
        intro a ha; rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hz₃e'
        · rw [Finset.mem_singleton] at ha; subst ha; exact hz₄e'
      have hpair_eq : e' = {z₃, z₄} := by
        refine (Finset.eq_of_subset_of_card_le hpair_sub ?_).symm
        rw [he'2, Finset.card_pair hz₃₄]
      -- `f₃ ∩ f₄ = e \ {z₃, z₄}`, hence `e \ (f₃ ∩ f₄) = {z₃, z₄} = e'`.
      have hinter_eq : f₃ ∩ f₄ = e \ {z₃, z₄} := by
        have hfe3 : f₃ = e.erase z₃ := by
          apply Finset.eq_of_subset_of_card_le
          · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₃mem.2 (h ▸ ha), hf₃e ha⟩
          · rw [Finset.card_erase_of_mem hz₃mem.1, he4, hf₃3]
        have hfe4 : f₄ = e.erase z₄ := by
          apply Finset.eq_of_subset_of_card_le
          · intro a ha; exact Finset.mem_erase.mpr ⟨fun h => hz₄mem.2 (h ▸ ha), hf₄e ha⟩
          · rw [Finset.card_erase_of_mem hz₄mem.1, he4, hf₄3]
        ext a
        simp only [Finset.mem_inter, hfe3, hfe4, Finset.mem_erase, Finset.mem_sdiff,
          Finset.mem_insert, Finset.mem_singleton]
        tauto
      -- `e \ (f₃ ∩ f₄) = e \ (e \ {z₃,z₄}) = {z₃,z₄} = e'`.
      have hopp : e \ (f₃ ∩ f₄) = e' := by
        rw [hinter_eq, hpair_eq]
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hae, hac⟩
          by_contra hane
          exact hac ⟨hae, hane⟩
        · rintro (rfl | rfl)
          · exact ⟨hz₃mem.1, fun h => h.2 (Or.inl rfl)⟩
          · exact ⟨hz₄mem.1, fun h => h.2 (Or.inr rfl)⟩
      rw [← hopp]; exact hOppEmpty
  · -- hvlc: a vertex `x ∈ e` lies on ≥ 1 exposed triangle (only `e.erase x` misses it,
    -- but two faces are exposed), whose unique remaining tet supplies an apex in `e \ {x}`.
    intro x hx
    right
    -- `x` lies in `f₃` or `f₄` (else both equal `e.erase x`, contra `f₃ ≠ f₄`).
    have he4 : e.card = 4 := he.1
    have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
    have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
    have hf₃e : f₃ ⊆ e := (Finset.mem_powersetCard.mp hf₃tet).1
    have hf₄e : f₄ ⊆ e := (Finset.mem_powersetCard.mp hf₄tet).1
    have hf₃3 : f₃.card = 3 := (Finset.mem_powersetCard.mp hf₃tet).2
    have hf₄3 : f₄.card = 3 := (Finset.mem_powersetCard.mp hf₄tet).2
    have hxor : x ∈ f₃ ∨ x ∈ f₄ := by
      by_contra hc
      push_neg at hc
      obtain ⟨hx3, hx4⟩ := hc
      -- a card-3 subset of `e` not containing `x` equals `e.erase x`.
      have key : ∀ {g : Finset V}, g ⊆ e → g.card = 3 → x ∉ g → g = e.erase x := by
        intro g hge hg3 hxg
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          exact Finset.mem_erase.mpr ⟨fun h => hxg (h ▸ hy), hge hy⟩
        · rw [Finset.card_erase_of_mem hx, he4, hg3]
      exact hf₃₄ ((key hf₃e hf₃3 hx3).trans (key hf₄e hf₄3 hx4).symm)
    -- pick the exposed face through `x`.
    obtain ⟨f, hfexp, hxf, hfe, hf3⟩ :
        ∃ f, f ∈ exposedFaces M e ∧ x ∈ f ∧ f ⊆ e ∧ f.card = 3 := by
      rcases hxor with h | h
      · exact ⟨f₃, hf₃exp, h, hf₃e, hf₃3⟩
      · exact ⟨f₄, hf₄exp, h, hf₄e, hf₄3⟩
    obtain ⟨t, htmem, hft⟩ :=
      exposed_triangle_unique_remaining_tet hσ hU hMX hT hS hPure hPMe he hfexp
    -- `f \ {x}` has card 2; pick `w` there: `w ∈ e`, `w ≠ x`, `w ∈ t`.
    have hcard : (f \ {x}).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hxf), hf3,
        Finset.card_singleton]
    have hne : (f \ {x}).Nonempty := by rw [← Finset.card_pos, hcard]; omega
    obtain ⟨w, hw⟩ := hne
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
    obtain ⟨hwf, hwx⟩ := hw
    refine ⟨w, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hfe hwf, hwx⟩
    · rw [mem_vertexLinkVerts_iff]
      exact ⟨⟨t, htmem, hft hxf, hft hwf⟩, hwx⟩

end Taut
