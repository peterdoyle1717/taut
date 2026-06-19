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

end Taut
