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

/-- **Edge-link analogue of LEMMA C** (`faceCount_removeTet_sharedFace_eq_zero`):
rules out the flip-opposite edge `e \ (f₃ ∩ f₄)` from `removeTet M e` using the
IH-level `EdgeLinkConnected (removeTet M u).support` for a SECOND eligible tet `u`
whose removal still drops the opposite edge (`hOu : ¬ (e \ (f₃ ∩ f₄)) ⊆ u`).
Identical exposed-pair geometry and `huniq` (M-level) as
`oppEdge_empty_of_full_edgeLinkConnected`; the contradiction is run inside the
second remainder `(removeTet M u).support` instead of `M.support`. -/
private lemma oppEdge_empty_of_disjoint_eligible_remainder {σ : Finset (Finset V)}
    {X M : Chain V} {e u f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (he : EligibleTet M e) (hu : EligibleTet M u)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hOu : ¬ (e \ (f₃ ∩ f₄)) ⊆ u)
    (hConnOu : ConnOn (edgeLinkGraph (removeTet M u).support (e \ (f₃ ∩ f₄)))
      (edgeLinkVerts (removeTet M u).support (e \ (f₃ ∩ f₄)))) :
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
  -- (M-level, reused because the closure tets live in `removeTet M u ⊆ M.support`.)
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
  -- survivor facts: the opposite edge `{z₃,z₄}` is not ⊆ u, so `e` and any remaining `t`
  -- containing it survive the SECOND removal `removeTet M u`.
  rw [hopp_eq] at hOu
  have hsuppU : (removeTet M u).support = M.support.erase u := support_removeTet_of_mem hu.2.1
  have heu : e ≠ u := fun h => hOu (h ▸ hOsub)
  have heU : e ∈ (removeTet M u).support := by
    rw [hsuppU]; exact Finset.mem_erase.mpr ⟨heu, he.2.1⟩
  -- no remaining tet contains the opposite edge `{z₃, z₄}`.
  apply edgeLinkVerts_eq_empty
  intro t ht hsub
  rw [support_removeTet_of_mem he.2.1, Finset.mem_erase] at ht
  obtain ⟨htne, htM⟩ := ht
  have htu : t ≠ u := fun h => hOu (h ▸ hsub)
  have htU : t ∈ (removeTet M u).support := by
    rw [hsuppU]; exact Finset.mem_erase.mpr ⟨htu, htM⟩
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
  · -- otherwise some apex `w ∈ t` avoids both `{z₃,z₄}` and `{p₁,p₂}`; run the
    -- edge-link contradiction inside `(removeTet M u).support`.
    rw [Finset.not_subset] at hcase
    obtain ⟨w, hwt, hwp⟩ := hcase
    rw [Finset.mem_sdiff] at hwt
    obtain ⟨hwt, hwO⟩ := hwt
    have hw_link : w ∈ edgeLinkVerts (removeTet M u).support ({z₃, z₄} : Finset V) := by
      rw [mem_edgeLinkVerts_iff]; exact ⟨⟨t, htU, hsub, hwt⟩, hwO⟩
    have hp₁_e : p₁ ∈ e := by
      rw [he_eq]; exact Finset.mem_union_right _ (Finset.mem_insert_self p₁ _)
    have hp₁_notO : p₁ ∉ ({z₃, z₄} : Finset V) := by
      have hpP : p₁ ∈ e \ ({z₃, z₄} : Finset V) := hPeq ▸ Finset.mem_insert_self p₁ _
      exact (Finset.mem_sdiff.mp hpP).2
    have hp₁_link : p₁ ∈ edgeLinkVerts (removeTet M u).support ({z₃, z₄} : Finset V) := by
      rw [mem_edgeLinkVerts_iff]; exact ⟨⟨e, heU, hOsub, hp₁_e⟩, hp₁_notO⟩
    -- the flip-edge pair `{p₁,p₂}` is closed under edge-link adjacency.  An adjacency
    -- in `removeTet M u` gives a tet in `M.support` (erase ⊆), so M-level `huniq` applies.
    have hclosed : ∀ u' ∈ ({p₁, p₂} : Finset V), ∀ v,
        (edgeLinkGraph (removeTet M u).support ({z₃, z₄} : Finset V)).Adj u' v →
          v ∈ ({p₁, p₂} : Finset V) := by
      intro u' hu' v hadj
      obtain ⟨huv, hins⟩ := hadj
      have hinsM : insert u' (insert v ({z₃, z₄} : Finset V)) ∈ M.support := by
        rw [hsuppU] at hins; exact Finset.mem_of_mem_erase hins
      have hsub2 : insert u' ({z₃, z₄} : Finset V) ⊆ insert u' (insert v {z₃, z₄}) := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)
      have heq_tet : insert u' (insert v ({z₃, z₄} : Finset V)) = e := huniq u' hu' _ hinsM hsub2
      have hv_e : v ∈ e := by
        rw [← heq_tet]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hv_notO : v ∉ ({z₃, z₄} : Finset V) := by
        intro hvO
        have hue : insert u' ({z₃, z₄} : Finset V) = e := by
          rw [← heq_tet, Finset.insert_eq_self.mpr hvO]
        have hlecard : (insert u' ({z₃, z₄} : Finset V)).card ≤ 3 := by
          calc (insert u' ({z₃, z₄} : Finset V)).card
              ≤ ({z₃, z₄} : Finset V).card + 1 := Finset.card_insert_le _ _
            _ = 3 := by rw [hOcard]
        rw [hue, he4] at hlecard
        omega
      rw [← hPeq]; exact Finset.mem_sdiff.mpr ⟨hv_e, hv_notO⟩
    have hnr : ¬ (edgeLinkGraph (removeTet M u).support ({z₃, z₄} : Finset V)).Reachable p₁ w := by
      rintro ⟨walk⟩
      exact hwp (walk_mem_of_adj_closed hclosed walk (Finset.mem_insert_self p₁ _))
    rw [hopp_eq] at hConnOu
    exact hnr (hConnOu p₁ hp₁_link w hw_link)

/-- **Opposite-edge geometry of an eligible tet.** For an eligible tet `t` of `M`
with `exposedFaces M t = {a, b}` (`a ≠ b`), the flip-opposite edge `t \ (a ∩ b)`
is a genuine edge (card 2), `a ∩ b` is the flip edge (card 2), and they partition
`t`.  Moreover the opposite edge is an edge of `σ`, and — crucially — the *only*
`σ`-triangles containing it are the two shared faces of `t`.  The two shared faces
are the two `t.erase pᵢ` for `{p₁,p₂} = a ∩ b`, each containing `t \ (a ∩ b)`;
they are the two `σ`-faces over that edge by `exists_two_faces`. -/
private lemma eligible_oppEdge_geom {σ : Finset (Finset V)} {M : Chain V}
    {t a b : Finset V}
    (hσ : IsSphere2 σ) (hUb : UnitOn (bdry M) σ)
    (ht : EligibleTet M t) (hexp : exposedFaces M t = {a, b}) (hab : a ≠ b) :
    (t \ (a ∩ b)).card = 2 ∧ (a ∩ b).card = 2 ∧ (a ∩ b) ⊆ t ∧
      (t \ (a ∩ b)) ⊆ t ∧ (a ∩ b) ∪ (t \ (a ∩ b)) = t ∧
      (t \ (a ∩ b)) ∈ edgesOf σ ∧
      (∀ T ∈ σ, (t \ (a ∩ b)) ⊆ T → T ∈ sharedFaces M t) := by
  classical
  -- exposed-pair geometry: `a = t.erase z₃`, `b = t.erase z₄`, `t \ (a ∩ b) = {z₃, z₄}`.
  have haexp : a ∈ exposedFaces M t := by rw [hexp]; exact Finset.mem_insert_self a _
  have hbexp : b ∈ exposedFaces M t := by
    rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hatet : a ∈ tetFaces t := exposedFaces_subset_tetFaces M t haexp
  have hbtet : b ∈ tetFaces t := exposedFaces_subset_tetFaces M t hbexp
  have hae : a ⊆ t := (Finset.mem_powersetCard.mp hatet).1
  have hbe : b ⊆ t := (Finset.mem_powersetCard.mp hbtet).1
  have ha3 : a.card = 3 := (Finset.mem_powersetCard.mp hatet).2
  have hb3 : b.card = 3 := (Finset.mem_powersetCard.mp hbtet).2
  have ht4 : t.card = 4 := ht.1
  have hcarda : (t \ a).card = 1 := by rw [Finset.card_sdiff_of_subset hae, ht4, ha3]
  have hcardb : (t \ b).card = 1 := by rw [Finset.card_sdiff_of_subset hbe, ht4, hb3]
  obtain ⟨z₃, hz₃⟩ := Finset.card_eq_one.mp hcarda
  obtain ⟨z₄, hz₄⟩ := Finset.card_eq_one.mp hcardb
  have hz₃mem : z₃ ∈ t \ a := hz₃ ▸ Finset.mem_singleton_self z₃
  have hz₄mem : z₄ ∈ t \ b := hz₄ ▸ Finset.mem_singleton_self z₄
  rw [Finset.mem_sdiff] at hz₃mem hz₄mem
  have heq3 : a = t.erase z₃ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; exact Finset.mem_erase.mpr ⟨fun h => hz₃mem.2 (h ▸ hx), hae hx⟩
    · rw [Finset.card_erase_of_mem hz₃mem.1, ht4, ha3]
  have heq4 : b = t.erase z₄ := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; exact Finset.mem_erase.mpr ⟨fun h => hz₄mem.2 (h ▸ hx), hbe hx⟩
    · rw [Finset.card_erase_of_mem hz₄mem.1, ht4, hb3]
  have hz₃₄ : z₃ ≠ z₄ := by
    rintro rfl; exact hab (heq3.trans heq4.symm)
  have hinter_eq : a ∩ b = t \ ({z₃, z₄} : Finset V) := by
    ext x
    simp only [Finset.mem_inter, heq3, heq4, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hopp_eq : t \ (a ∩ b) = ({z₃, z₄} : Finset V) := by
    rw [hinter_eq]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxe, hxc⟩; by_contra hxne; exact hxc ⟨hxe, hxne⟩
    · rintro (rfl | rfl)
      · exact ⟨hz₃mem.1, fun h => h.2 (Or.inl rfl)⟩
      · exact ⟨hz₄mem.1, fun h => h.2 (Or.inr rfl)⟩
  have hz₃e : z₃ ∈ t := hz₃mem.1
  have hz₄e : z₄ ∈ t := hz₄mem.1
  have hOcard : (t \ (a ∩ b)).card = 2 := by rw [hopp_eq]; exact Finset.card_pair hz₃₄
  have hOsub : ({z₃, z₄} : Finset V) ⊆ t := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hz₃e
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hz₄e
  have hOsubt : (t \ (a ∩ b)) ⊆ t := Finset.sdiff_subset
  -- the flip edge `a ∩ b = {p₁,p₂}` and `t = (a ∩ b) ∪ (t \ (a ∩ b))`.
  have hICsubt : (a ∩ b) ⊆ t := hinter_eq ▸ Finset.sdiff_subset
  have hICcard : (a ∩ b).card = 2 := by
    rw [hinter_eq, Finset.card_sdiff_of_subset hOsub, ht4, Finset.card_pair hz₃₄]
  obtain ⟨p₁, p₂, hp₁₂, hPeq⟩ := Finset.card_eq_two.mp hICcard
  have htunion : (a ∩ b) ∪ (t \ (a ∩ b)) = t := Finset.union_sdiff_of_subset hICsubt
  -- the two shared faces are `t.erase p₁`, `t.erase p₂`, each ⊇ {z₃,z₄}.
  have hp₁mem : p₁ ∈ a ∩ b := hPeq ▸ Finset.mem_insert_self p₁ _
  have hp₂mem : p₂ ∈ a ∩ b := hPeq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self p₂)
  have hp₁t : p₁ ∈ t := hICsubt hp₁mem
  have hp₂t : p₂ ∈ t := hICsubt hp₂mem
  have hp₁notO : p₁ ∉ ({z₃, z₄} : Finset V) := by
    intro hpO
    exact (Finset.mem_sdiff.mp (hinter_eq ▸ hp₁mem)).2 hpO
  have hp₂notO : p₂ ∉ ({z₃, z₄} : Finset V) := by
    intro hpO
    exact (Finset.mem_sdiff.mp (hinter_eq ▸ hp₂mem)).2 hpO
  -- `sharedFaces = tetFaces \ exposedFaces`.
  have hsh_eq2 : tetFaces t \ exposedFaces M t = sharedFaces M t := by
    rw [exposedFaces, Finset.sdiff_sdiff_self_left,
      Finset.inter_eq_right.mpr (sharedFaces_subset_tetFaces M t)]
  -- `t.erase p` is a shared face whenever `p ∈ {p₁,p₂}` (it is ≠ a, b since p ∉ O).
  have herase_shared : ∀ p ∈ ({p₁, p₂} : Finset V), t.erase p ∈ sharedFaces M t ∧
      ({z₃, z₄} : Finset V) ⊆ t.erase p := by
    intro p hp
    have hpO : p ∉ ({z₃, z₄} : Finset V) := by
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hp₁notO
      · rw [Finset.mem_singleton] at hp; exact hp ▸ hp₂notO
    have hpt : p ∈ t := by
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hp₁t
      · rw [Finset.mem_singleton] at hp; exact hp ▸ hp₂t
    have hOsub_erase : ({z₃, z₄} : Finset V) ⊆ t.erase p := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, hOsub hx⟩
      rintro rfl; exact hpO hx
    have herasetet : t.erase p ∈ tetFaces t := erase_mem_tetFaces ht4 hpt
    have hz₃erase : z₃ ∈ t.erase p := hOsub_erase (Finset.mem_insert_self z₃ _)
    have hz₄erase : z₄ ∈ t.erase p :=
      hOsub_erase (Finset.mem_insert_of_mem (Finset.mem_singleton_self z₄))
    have hne_a : t.erase p ≠ a := fun h => hz₃mem.2 (h ▸ hz₃erase)
    have hne_b : t.erase p ≠ b := fun h => hz₄mem.2 (h ▸ hz₄erase)
    refine ⟨?_, hOsub_erase⟩
    rw [← hsh_eq2, hexp]
    refine Finset.mem_sdiff.mpr ⟨herasetet, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg; exact ⟨hne_a, hne_b⟩
  obtain ⟨hS₁sh, hS₁O⟩ := herase_shared p₁ (Finset.mem_insert_self p₁ _)
  obtain ⟨hS₂sh, hS₂O⟩ := herase_shared p₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self p₂))
  -- both shared faces sit in `σ` (they are boundary triangles).
  have hsh_subσ : ∀ s ∈ sharedFaces M t, s ∈ σ := by
    intro s hs
    rw [← hUb.1, sharedFaces] at *
    exact (Finset.mem_inter.mp hs).2
  have hS₁σ : t.erase p₁ ∈ σ := hsh_subσ _ hS₁sh
  have hS₂σ : t.erase p₂ ∈ σ := hsh_subσ _ hS₂sh
  have hS₁ne₂ : t.erase p₁ ≠ t.erase p₂ := by
    intro h
    have hp₂in : p₂ ∈ t.erase p₁ := Finset.mem_erase.mpr ⟨fun hc => hp₁₂ hc.symm, hp₂t⟩
    exact (Finset.notMem_erase p₂ t) (h ▸ hp₂in)
  -- the opposite edge is a σ-edge (it lies in the card-3 boundary triangle `t.erase p₁`).
  have hS₁card : (t.erase p₁).card = 3 := by rw [Finset.card_erase_of_mem hp₁t, ht4]
  have hOedge : (t \ (a ∩ b)) ∈ edgesOf σ := by
    rw [hopp_eq]
    exact mem_edgesOf.mpr ⟨t.erase p₁, hS₁σ, hS₁O, Finset.card_pair hz₃₄⟩
  -- by `exists_two_faces`, the two σ-faces over the opposite edge are exactly the
  -- two shared faces; any σ-face over it is one of them, hence shared.
  obtain ⟨g₁, hg₁σ, g₂, hg₂σ, hg₁₂, _, _, huniq⟩ :=
    exists_two_faces hσ.toClosedSurface hOedge
  rw [hopp_eq] at huniq
  have hany : ∀ T ∈ σ, (t \ (a ∩ b)) ⊆ T → T ∈ sharedFaces M t := by
    intro T hTσ hTsub
    rw [hopp_eq] at hTsub
    -- `t.erase p₁`, `t.erase p₂`, and `T` are σ-faces ⊇ O, so each is `g₁` or `g₂`.
    have hd₁ := huniq _ hS₁σ hS₁O
    have hd₂ := huniq _ hS₂σ hS₂O
    have hdT := huniq _ hTσ hTsub
    -- `{g₁,g₂} = {erase p₁, erase p₂}`, so `T ∈ {erase p₁, erase p₂} ⊆ sharedFaces`.
    have hTcase : T = t.erase p₁ ∨ T = t.erase p₂ := by
      rcases hdT with hT1 | hT2
      · -- `T = g₁`; whichever of `erase p₁`, `erase p₂` equals `g₁` gives the answer.
        rcases hd₁ with h11 | h12
        · exact Or.inl (hT1.trans h11.symm)
        · rcases hd₂ with h21 | h22
          · exact Or.inr (hT1.trans h21.symm)
          · exact absurd (h12.trans h22.symm) hS₁ne₂
      · -- `T = g₂`.
        rcases hd₁ with h11 | h12
        · rcases hd₂ with h21 | h22
          · exact absurd (h11.trans h21.symm) hS₁ne₂
          · exact Or.inr (hT2.trans h22.symm)
        · exact Or.inl (hT2.trans h12.symm)
    rcases hTcase with rfl | rfl
    · exact hS₁sh
    · exact hS₂sh
  exact ⟨hOcard, hICcard, hICsubt, hOsubt, htunion, hOedge, hany⟩

/-- **An edge inside a tet whose two faces over it are both exposed is the flip
edge.** If `t` is eligible with `exposedFaces M t = {a, b}` (`a ≠ b`, with
`(a ∩ b).card = 2`), `O ⊆ t` is an edge (card 2), and *every* triangular face of
`t` containing `O` is exposed (not shared), then `O = a ∩ b`.  Proof: the two
faces `t.erase q` (`q ∈ t \ O`) over `O` are then both exposed, hence `{a, b}`;
each contains `O`, so `O ⊆ a ∩ b`, and the cards (both 2) force equality. -/
private lemma oppEdge_eq_flip {M : Chain V} {t a b O : Finset V}
    (ht : EligibleTet M t) (hexp : exposedFaces M t = {a, b}) (hab : a ≠ b)
    (hICcard : (a ∩ b).card = 2) (hOt : O ⊆ t) (hOcard : O.card = 2)
    (hnsh : ∀ s ∈ tetFaces t, O ⊆ s → s ∉ sharedFaces M t) :
    O = a ∩ b := by
  classical
  have ht4 : t.card = 4 := ht.1
  -- `t \ O = {q₁,q₂}` (card 2); each `t.erase qᵢ` is a face of `t` over `O`.
  have hQcard : (t \ O).card = 2 := by rw [Finset.card_sdiff_of_subset hOt, ht4, hOcard]
  obtain ⟨q₁, q₂, hq₁₂, hQeq⟩ := Finset.card_eq_two.mp hQcard
  have hq₁mem : q₁ ∈ t \ O := hQeq ▸ Finset.mem_insert_self q₁ _
  have hq₂mem : q₂ ∈ t \ O := hQeq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q₂)
  -- `t.erase q ∈ exposedFaces M t` and `O ⊆ t.erase q` for `q ∈ {q₁,q₂}`.
  have herase_exp : ∀ q ∈ ({q₁, q₂} : Finset V), t.erase q ∈ exposedFaces M t ∧
      O ⊆ t.erase q := by
    intro q hq
    have hqQ : q ∈ t \ O := by
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hq₁mem
      · rw [Finset.mem_singleton] at hq; exact hq ▸ hq₂mem
    obtain ⟨hqt, hqO⟩ := Finset.mem_sdiff.mp hqQ
    have hOsub_erase : O ⊆ t.erase q := by
      intro x hx; exact Finset.mem_erase.mpr ⟨fun h => hqO (h ▸ hx), hOt hx⟩
    have herasetet : t.erase q ∈ tetFaces t := erase_mem_tetFaces ht4 hqt
    have hnotsh : t.erase q ∉ sharedFaces M t := hnsh _ herasetet hOsub_erase
    exact ⟨by rw [exposedFaces]; exact Finset.mem_sdiff.mpr ⟨herasetet, hnotsh⟩, hOsub_erase⟩
  obtain ⟨he₁exp, he₁O⟩ := herase_exp q₁ (Finset.mem_insert_self q₁ _)
  obtain ⟨he₂exp, he₂O⟩ := herase_exp q₂ (Finset.mem_insert_of_mem (Finset.mem_singleton_self q₂))
  rw [hexp, Finset.mem_insert, Finset.mem_singleton] at he₁exp he₂exp
  -- both `t.erase qᵢ ∈ {a,b}`; they are distinct, so `{a,b} = {erase q₁, erase q₂}`.
  have hq₂t : q₂ ∈ t := (Finset.mem_sdiff.mp hq₂mem).1
  have hS₁ne₂ : t.erase q₁ ≠ t.erase q₂ := by
    intro h
    have hq₂in : q₂ ∈ t.erase q₁ := Finset.mem_erase.mpr ⟨fun hc => hq₁₂ hc.symm, hq₂t⟩
    exact (Finset.notMem_erase q₂ t) (h ▸ hq₂in)
  -- `a` (and `b`) is one of `t.erase q₁`, `t.erase q₂`, both ⊇ `O`.
  have hAcase : a = t.erase q₁ ∨ a = t.erase q₂ := by
    rcases he₁exp with h1a | h1b
    · exact Or.inl h1a.symm
    · rcases he₂exp with h2a | h2b
      · exact Or.inr h2a.symm
      · exact absurd (h1b.trans h2b.symm) hS₁ne₂
  have hBcase : b = t.erase q₁ ∨ b = t.erase q₂ := by
    rcases he₁exp with h1a | h1b
    · rcases he₂exp with h2a | h2b
      · exact absurd (h1a.trans h2a.symm) hS₁ne₂
      · exact Or.inr h2b.symm
    · exact Or.inl h1b.symm
  have hOa : O ⊆ a := by rcases hAcase with rfl | rfl; exacts [he₁O, he₂O]
  have hOb : O ⊆ b := by rcases hBcase with rfl | rfl; exacts [he₁O, he₂O]
  have hOIC : O ⊆ a ∩ b := Finset.subset_inter hOa hOb
  exact Finset.eq_of_subset_of_card_le hOIC (by rw [hICcard, hOcard])

/-- **CRUX orientation lemma.** Two distinct eligible tets `e`, `u` with disjoint
shared faces cannot each have its flip-opposite edge contained in the other.
If both `e \ (f₃ ∩ f₄) ⊆ u` and `u \ (g₃ ∩ g₄) ⊆ e` held, then (by
`eligible_oppEdge_geom` + `oppEdge_eq_flip`, using disjointness so that no face of
`u` over `e`'s opposite edge can be shared) the opposite edge of `e` would equal
`u`'s flip edge `g₃ ∩ g₄` and vice versa, whence `e = (f₃∩f₄) ∪ (g₃∩g₄) = u`,
contradicting `e ≠ u`. -/
private lemma eligible_pair_oriented_opp_avoidance {σ : Finset (Finset V)} {X M : Chain V}
    {e u f₃ f₄ g₃ g₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hMX : bdry M = X)
    (he : EligibleTet M e) (hu : EligibleTet M u) (hne : e ≠ u)
    (hdisj : Disjoint (sharedFaces M e) (sharedFaces M u))
    (hexpe : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hexpu : exposedFaces M u = {g₃, g₄}) (hg₃₄ : g₃ ≠ g₄) :
    ¬ (e \ (f₃ ∩ f₄)) ⊆ u ∨ ¬ (u \ (g₃ ∩ g₄)) ⊆ e := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  by_contra hcon
  push_neg at hcon
  obtain ⟨hOe_u, hOu_e⟩ := hcon
  -- opposite-edge geometry for both tets.
  obtain ⟨hOe_card, hICe_card, hICe_sub, _, htune, _, hany_e⟩ :=
    eligible_oppEdge_geom hσ hUb he hexpe hf₃₄
  obtain ⟨hOu_card, hICu_card, hICu_sub, _, htunu, _, hany_u⟩ :=
    eligible_oppEdge_geom hσ hUb hu hexpu hg₃₄
  -- no face of `u` over `e`'s opposite edge is shared (else it is shared by both,
  -- via `hany_e`, contradicting `hdisj`); symmetrically for `e` over `u`'s edge.
  have hnsh_u : ∀ s ∈ tetFaces u, (e \ (f₃ ∩ f₄)) ⊆ s → s ∉ sharedFaces M u := by
    intro s _ hsub hsu
    have hsσ : s ∈ σ := by
      have := (Finset.mem_inter.mp (by rw [sharedFaces] at hsu; exact hsu)).2
      rw [← hUb.1]; exact this
    exact Finset.disjoint_left.mp hdisj (hany_e s hsσ hsub) hsu
  have hnsh_e : ∀ s ∈ tetFaces e, (u \ (g₃ ∩ g₄)) ⊆ s → s ∉ sharedFaces M e := by
    intro s _ hsub hse
    have hsσ : s ∈ σ := by
      have := (Finset.mem_inter.mp (by rw [sharedFaces] at hse; exact hse)).2
      rw [← hUb.1]; exact this
    exact Finset.disjoint_right.mp hdisj (hany_u s hsσ hsub) hse
  -- `e`'s opposite edge is `u`'s flip edge, and vice versa.
  have hOe_eq : (e \ (f₃ ∩ f₄)) = g₃ ∩ g₄ :=
    oppEdge_eq_flip hu hexpu hg₃₄ hICu_card hOe_u hOe_card hnsh_u
  have hOu_eq : (u \ (g₃ ∩ g₄)) = f₃ ∩ f₄ :=
    oppEdge_eq_flip he hexpe hf₃₄ hICe_card hOu_e hOu_card hnsh_e
  -- assemble `e = (f₃∩f₄) ∪ (g₃∩g₄) = u`.
  have he_eq : e = (f₃ ∩ f₄) ∪ (g₃ ∩ g₄) := by rw [← hOe_eq, htune]
  have hu_eq : u = (g₃ ∩ g₄) ∪ (f₃ ∩ f₄) := by rw [← hOu_eq, htunu]
  exact hne (by rw [he_eq, hu_eq, Finset.union_comm])

/-- **The non-opposite edges of an eligible tet have nonempty shared link.** Any
edge `e'` of `e` that lies in an exposed face `f` keeps a common apex on removal:
`f` survives in a unique neighbour tet of `removeTet M e`, whose third vertex
`f \ e'` is in `e \ e'` and is an apex of `e'`.  This discharges the RIGHT disjunct
of `edgeLinkConnected_insert`'s `hcompat` for every edge of `e` except the
flip-opposite edge `e \ (f₃ ∩ f₄)` (the only edge in no exposed face). -/
private lemma edgeLinkCompat_nonOpp_of_exposed_face {σ : Finset (Finset V)}
    {X M : Chain V} {e f e' : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hPMe : IsPseudomanifold (removeTet M e).support)
    (he : EligibleTet M e) (hf : f ∈ exposedFaces M e)
    (he'f : e' ⊆ f) (he'2 : e'.card = 2) :
    ((e \ e') ∩ edgeLinkVerts (removeTet M e).support e').Nonempty := by
  classical
  obtain ⟨N, hNmem, hfN⟩ :=
    exposed_triangle_unique_remaining_tet hσ hU hMX hT hS hPure hPMe he hf
  have hftet : f ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf
  have hfe : f ⊆ e := (Finset.mem_powersetCard.mp hftet).1
  have hf3 : f.card = 3 := (Finset.mem_powersetCard.mp hftet).2
  have hdiff : (f \ e').card = 1 := by rw [Finset.card_sdiff_of_subset he'f, hf3, he'2]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
  have hwmem : w ∈ f \ e' := hw ▸ Finset.mem_singleton_self w
  rw [Finset.mem_sdiff] at hwmem
  obtain ⟨hwf, hwe'⟩ := hwmem
  refine ⟨w, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hfe hwf, hwe'⟩, ?_⟩⟩
  rw [mem_edgeLinkVerts_iff]
  exact ⟨⟨N, hNmem, he'f.trans hfN, hfN hwf⟩, hwe'⟩

/-- **Edge-link connectedness of the remainder, no-flip case.** When the flip edge
`f₃ ∩ f₄` is absent from `σ`, `removeTet M e` is itself a strictly smaller single-sphere
taut filling, so the strong IH gives `EdgeLinkConnected (removeTet M e).support` directly.
(Mirror of `removeTet_isPseudomanifold` case 1.) -/
private lemma removeTet_edgeLinkConnected_noFlip {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hNoFlip : ¬ FlipEdgePresent σ f₃ f₄)
    (IHelc : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      EdgeLinkConnected M'.support) :
    EdgeLinkConnected (removeTet M e).support := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hσe := isSphere2_flipBoundary_of_eligible hσ hUb hS he hexp hf₃₄ hNoFlip
  have hUe := unitOn_flipBoundary_of_eligible hUb hS he
  have hTe : IsTaut (removeTet M e) := isTaut_removeTet hT
  have hSe : SimplicialChain (removeTet M e) := simplicialChain_removeTet hS
  have hlt : nrm (removeTet M e) < nrm M := by
    have h := nrm_removeTet_add_one_of_simplicial hS he.2.1; omega
  exact IHelc _ (bdry (removeTet M e)) (removeTet M e) hlt hσe hUe (bdry_bdry _) rfl hTe hSe

/-- **Edge-link connectedness of `M` from the disjoint-eligible remainder (prime case 1).**
Re-glues the eligible tet `e` onto its edge-link-connected remainder `removeTet M e`.
The only edge of `e` whose link could fail to extend is the flip-opposite edge
`e \ (f₃ ∩ f₄)`, ruled empty by `oppEdge_empty_of_disjoint_eligible_remainder` (the
second eligible tet `u` carries the IH-level connectivity); every other card-2 face of
`e` lies in an exposed triangle, whose unique remaining tet supplies the apex via
`edgeLinkCompat_nonOpp_of_exposed_face`. -/
private lemma prime_edgeLinkConnected_case1 {σ : Finset (Finset V)} {X M : Chain V}
    {e u f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (he : EligibleTet M e) (hu : EligibleTet M u)
    (hPMe : IsPseudomanifold (removeTet M e).support)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hOu : ¬ (e \ (f₃ ∩ f₄)) ⊆ u)
    (hELMe : EdgeLinkConnected (removeTet M e).support)
    (hConnOu : ConnOn (edgeLinkGraph (removeTet M u).support (e \ (f₃ ∩ f₄)))
      (edgeLinkVerts (removeTet M u).support (e \ (f₃ ∩ f₄)))) :
    EdgeLinkConnected M.support := by
  classical
  -- `M = insert e (removeTet M e)`, then glue the new tet onto the connected remainder.
  rw [← support_insert_removeTet_of_mem he.2.1]
  apply edgeLinkConnected_insert he.1 hELMe
  intro e' he'e he'2
  by_cases he'O : e' = e \ (f₃ ∩ f₄)
  · -- the flip-opposite edge: its link in the remainder is empty (LEFT disjunct).
    rw [he'O]
    exact Or.inl (oppEdge_empty_of_disjoint_eligible_remainder hσ hU hXc hMX hT hS hPure
      he hu hexp hf₃₄ hOu hConnOu)
  · -- any other card-2 face of `e` lies in `f₃` or `f₄`; use the exposed-triangle apex.
    refine Or.inr ?_
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
    have hz₃notf₃ : z₃ ∉ f₃ := by rw [heq3]; exact Finset.notMem_erase z₃ e
    have hz₄notf₄ : z₄ ∉ f₄ := by rw [heq4]; exact Finset.notMem_erase z₄ e
    -- `e' ≠ {z₃,z₄}` forces `e' ⊆ f₃` or `e' ⊆ f₄`.
    have he'sub : e' ⊆ f₃ ∨ e' ⊆ f₄ := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hnf₃, hnf₄⟩ := hcon
      rw [Finset.not_subset] at hnf₃ hnf₄
      obtain ⟨x, hxe', hxf₃⟩ := hnf₃
      obtain ⟨y, hye', hyf₄⟩ := hnf₄
      have hxe : x ∈ e := he'e hxe'
      have hye : y ∈ e := he'e hye'
      have hxz₃ : x = z₃ := by
        rw [heq3] at hxf₃
        by_contra hne
        exact hxf₃ (Finset.mem_erase.mpr ⟨hne, hxe⟩)
      have hyz₄ : y = z₄ := by
        rw [heq4] at hyf₄
        by_contra hne
        exact hyf₄ (Finset.mem_erase.mpr ⟨hne, hye⟩)
      have hz₃e' : z₃ ∈ e' := hxz₃ ▸ hxe'
      have hz₄e' : z₄ ∈ e' := hyz₄ ▸ hye'
      have hsub : ({z₃, z₄} : Finset V) ⊆ e' := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hz₃e'
        · rw [Finset.mem_singleton] at ha; exact ha ▸ hz₄e'
      have heqe' : e' = ({z₃, z₄} : Finset V) :=
        (Finset.eq_of_subset_of_card_le hsub (by rw [he'2, Finset.card_pair hz₃₄])).symm
      exact he'O (heqe'.trans hopp_eq.symm)
    -- in either case the exposed-triangle apex lives in the remainder link.
    rcases he'sub with hi | hi
    · exact edgeLinkCompat_nonOpp_of_exposed_face hσ hU hMX hT hS hPure hPMe he hf₃exp hi he'2
    · exact edgeLinkCompat_nonOpp_of_exposed_face hσ hU hMX hT hS hPure hPMe he hf₄exp hi he'2

/-- **Edge-link connectivity transfers from a closed-up subset.**  If `τ' ⊆ τ`
and every tet of `τ` containing `O` already lies in `τ'` (`hloc`), then the edge
`O` sees the *same* link in `τ` as in `τ'`; hence connectivity on `O`'s apexes in
`τ'` upgrades to `τ`.  Used to push the side-filling's edge-link connectivity (on
an edge that lives entirely on one side) up to `removeTet M u`. -/
private lemma connOn_oppEdge_of_subset_local {τ τ' : Finset (Finset V)} {O : Finset V}
    (hsub : τ' ⊆ τ) (hloc : ∀ t ∈ τ, O ⊆ t → t ∈ τ')
    (h : ConnOn (edgeLinkGraph τ' O) (edgeLinkVerts τ' O)) :
    ConnOn (edgeLinkGraph τ O) (edgeLinkVerts τ O) := by
  classical
  -- The two filters by `O ⊆ ·` agree, so both the apex set and the link graph do.
  have hfilter : τ.filter (fun t => O ⊆ t) = τ'.filter (fun t => O ⊆ t) := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hOt⟩; exact ⟨hloc t ht hOt, hOt⟩
    · rintro ⟨ht, hOt⟩; exact ⟨hsub ht, hOt⟩
  have hverts : edgeLinkVerts τ O = edgeLinkVerts τ' O := by
    unfold edgeLinkVerts; rw [hfilter]
  have hgraph : edgeLinkGraph τ O = edgeLinkGraph τ' O := by
    apply SimpleGraph.ext
    funext x y
    simp only [edgeLinkGraph]
    apply propext
    refine and_congr_right (fun _ => ?_)
    have hOin : O ⊆ insert x (insert y O) :=
      (Finset.subset_insert y O).trans (Finset.subset_insert x _)
    constructor
    · intro hmem; exact hloc _ hmem hOin
    · intro hmem; exact hsub hmem
  rw [hgraph, hverts]; exact h

/-- **Side-local edge-link connectivity at a non-flip edge (flip present).**  When
the flip edge of the eligible `u` is already in `σ`, `removeTet M u` splits into two
smaller single-sphere taut fillings `sideA`, `sideB` along `g₃ ∩ g₄` (the side
package + side algebra).  An edge `O ⊆ e` with `O ⊄ u` cannot straddle the seam, so
it lies on one side; the IH gives that side's edge-link connectivity at `O`, and
`connOn_oppEdge_of_subset_local` pushes it back up to `removeTet M u`. -/
private lemma flipPresent_removeTet_connOn_at_nonflip_edge {σ : Finset (Finset V)}
    {X M : Chain V} {e u g₃ g₄ O : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hu : EligibleTet M u) (heU : e ∈ (removeTet M u).support)
    (hOe : O ⊆ e) (hOu : ¬ O ⊆ u) (hO2 : O.card = 2)
    (hexpu : exposedFaces M u = {g₃, g₄}) (hg₃₄ : g₃ ≠ g₄)
    (hFlipu : FlipEdgePresent σ g₃ g₄)
    (IHelc : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      EdgeLinkConnected M'.support) :
    ConnOn (edgeLinkGraph (removeTet M u).support O) (edgeLinkVerts (removeTet M u).support O) := by
  classical
  -- The flip-present side package: two sides `A, B`, covering and exact-separating.
  obtain ⟨A, B, hAB, hcd, hsphA, hsphB, hcover, hsep, hg₃A, hg₃notB, hg₄B, hg₄notA, _⟩ :=
    flipEdgePresent_side_sets hσ hU hXc hMX hT hS hu hexpu hg₃₄ hFlipu
  -- Side-filling algebra: each side is a smaller single-sphere taut filling.
  obtain ⟨hUA, hUB, hbA, hbB, hTA, hTB, hSA, hSB, hnrmA, hnrmB, _, _, _, _⟩ :=
    flipEdgePresent_side_algebra hσ hU hXc hMX hT hS hu hexpu hg₃₄ hFlipu hAB hcd hcover hsep
  -- `g₃ ⊆ u` (it is a face of the tet `u`), so `A ∩ B = g₃ ∩ g₄ ⊆ g₃ ⊆ u`.
  have hg₃exp : g₃ ∈ exposedFaces M u := by rw [hexpu]; exact Finset.mem_insert_self g₃ _
  have hg₃tet : g₃ ∈ tetFaces u := exposedFaces_subset_tetFaces M u hg₃exp
  have hg₃u : g₃ ⊆ u := (Finset.mem_powersetCard.mp hg₃tet).1
  have hABu : A ∩ B ⊆ u := by
    rw [hAB]; exact (Finset.inter_subset_left).trans hg₃u
  -- A subset `O ⊆ e`, `O ⊄ u`, cannot lie in `A ∩ B`.
  have hOnotAB : ¬ O ⊆ A ∩ B := fun h => hOu (h.trans hABu)
  -- `e` lies on one side.
  rcases hcover e heU with heA | heB
  · -- `e ⊆ A`: use side A.
    have hloc : ∀ t ∈ (removeTet M u).support, O ⊆ t → t ∈
        ((removeTet M u).filter (fun t => t ⊆ A)).support := by
      intro t ht hOt
      rw [Finsupp.support_filter, Finset.mem_filter]
      refine ⟨ht, ?_⟩
      rcases hcover t ht with htA | htB
      · exact htA
      · exact absurd (Finset.subset_inter (hOe.trans heA) (hOt.trans htB)) hOnotAB
    have helcA : EdgeLinkConnected ((removeTet M u).filter (fun t => t ⊆ A)).support :=
      IHelc ((flipBoundary σ M u).filter (fun f => f ⊆ A))
        (bdry ((removeTet M u).filter (fun t => t ⊆ A)))
        ((removeTet M u).filter (fun t => t ⊆ A)) hnrmA hsphA hUA hbA rfl hTA hSA
    refine connOn_oppEdge_of_subset_local ?_ hloc (helcA O hO2)
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
  · -- `e ⊆ B`: use side B.
    have hloc : ∀ t ∈ (removeTet M u).support, O ⊆ t → t ∈
        ((removeTet M u).filter (fun t => t ⊆ B)).support := by
      intro t ht hOt
      rw [Finsupp.support_filter, Finset.mem_filter]
      refine ⟨ht, ?_⟩
      rcases hcover t ht with htA | htB
      · exact absurd (Finset.subset_inter (hOt.trans htA) (hOe.trans heB)) hOnotAB
      · exact htB
    have helcB : EdgeLinkConnected ((removeTet M u).filter (fun t => t ⊆ B)).support :=
      IHelc ((flipBoundary σ M u).filter (fun f => f ⊆ B))
        (bdry ((removeTet M u).filter (fun t => t ⊆ B)))
        ((removeTet M u).filter (fun t => t ⊆ B)) hnrmB hsphB hUB hbB rfl hTB hSB
    refine connOn_oppEdge_of_subset_local ?_ hloc (helcB O hO2)
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _

/-- **Dispatcher: `ConnOn` at `e`'s opposite edge inside `removeTet M u`.** Cases on
whether `u`'s flip edge is present: no-flip ⟹ full `EdgeLinkConnected (removeTet M u)` from
the IH (`removeTet_edgeLinkConnected_noFlip`), specialized at the edge; flip-present ⟹ the
side-local `flipPresent_removeTet_connOn_at_nonflip_edge`.  This supplies the `hConnOu`
input to `oppEdge_empty_of_disjoint_eligible_remainder` / `prime_edgeLinkConnected_case1`. -/
private lemma removeTet_connOn_oppEdge_of_disjoint_eligible {σ : Finset (Finset V)}
    {X M : Chain V} {e u f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (he : EligibleTet M e) (hu : EligibleTet M u)
    (hexpe : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hOu : ¬ (e \ (f₃ ∩ f₄)) ⊆ u)
    (IHelc : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      EdgeLinkConnected M'.support) :
    ConnOn (edgeLinkGraph (removeTet M u).support (e \ (f₃ ∩ f₄)))
      (edgeLinkVerts (removeTet M u).support (e \ (f₃ ∩ f₄))) := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  obtain ⟨hO2, _, _, hOe, _, _, _⟩ := eligible_oppEdge_geom hσ hUb he hexpe hf₃₄
  have heu : e ≠ u := fun h => hOu (h ▸ hOe)
  have heU : e ∈ (removeTet M u).support := by
    rw [support_removeTet_of_mem hu.2.1]; exact Finset.mem_erase.mpr ⟨heu, he.2.1⟩
  obtain ⟨g₃, g₄, hg₃₄, hexpu⟩ := exposedFaces_eq_pair_of_eligible hu
  by_cases hFlipu : FlipEdgePresent σ g₃ g₄
  · exact flipPresent_removeTet_connOn_at_nonflip_edge hσ hU hXc hMX hT hS hu heU hOe hOu hO2
      hexpu hg₃₄ hFlipu IHelc
  · exact (removeTet_edgeLinkConnected_noFlip hσ hU hXc hMX hT hS hu hexpu hg₃₄ hFlipu IHelc) _ hO2

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

/-! ## Case-2 flip-edge bridge: reconnecting two side-fillings across a seam edge

When the flip edge `cd = f₃ ∩ f₄` of the eligible tet is on the boundary,
`removeTet M e` splits into two sphere-fillings `s₁, s₂` pinched along `cd`.  The
union `s₁ ∪ s₂` is *not* edge-link connected (its `cd`-link has two components, one
per side), but re-inserting the eligible tet `e` bridges them: `e` carries an edge
`a₃ ~ a₄` joining a side-1 apex to a side-2 apex.  The lemmas below are stated
purely combinatorially over two tet-sets `s₁ s₂`, an inserted tet `e`, and the
seam edge `cd`, so that the prime-step call site supplies the geometry. -/

/-- **Seam dichotomy.**  With `A ∩ B = cd` (`cd.card = 2`), an edge `ε` (`ε.card = 2`)
that lies in a side-`A` tet `t₁` *and* a side-`B` tet `t₂` must be the seam `cd`
itself: `ε ⊆ A` and `ε ⊆ B` force `ε ⊆ A ∩ B = cd`, and equal cardinalities close
the gap.  This is the hard-stop that confines a non-seam edge to a single side. -/
private lemma flipBridge_edge_eq_seam {A B cd ε t₁ t₂ : Finset V}
    (hAB : A ∩ B = cd) (hcd2 : cd.card = 2) (hε2 : ε.card = 2)
    (ht₁A : t₁ ⊆ A) (ht₂B : t₂ ⊆ B) (hεt₁ : ε ⊆ t₁) (hεt₂ : ε ⊆ t₂) :
    ε = cd := by
  have hεcd : ε ⊆ cd := by
    rw [← hAB]
    exact Finset.subset_inter (hεt₁.trans ht₁A) (hεt₂.trans ht₂B)
  exact Finset.eq_of_subset_of_card_le hεcd (by rw [hcd2, hε2])

/-- **Side face apex is a seam apex.**  A tet `t` of the union containing a seam-face
`f` (with `cd ⊆ f`, `f.card = 3`, `cd.card = 2`) contributes the apex `a := f \ cd`
to the seam edge `cd` of the union: `cd ⊆ t`, `a ∈ t`, `a ∉ cd`.  This is how the
side-witness tets `t₃ ∈ s₁` (for `f₃`) and `t₄ ∈ s₂` (for `f₄`) make the bridge
apexes `a₃, a₄` real `cd`-apexes of `s₁ ∪ s₂`. -/
private lemma flipBridge_apex_mem_edgeLinkVerts {s₁ s₂ : Finset (Finset V)}
    {cd f t : Finset V} {a : V}
    (htmem : t ∈ s₁) (hft : f ⊆ t) (hcdf : cd ⊆ f) (hamem : a ∈ f) (hanotcd : a ∉ cd) :
    a ∈ edgeLinkVerts (s₁ ∪ s₂) cd := by
  rw [mem_edgeLinkVerts_iff]
  exact ⟨⟨t, Finset.mem_union_left _ htmem, hcdf.trans hft, hft hamem⟩, hanotcd⟩

/-- **Clean-glue compatibility of the eligible tet against one side.**  For the
side `s₁` (with witness tet `t₃ ∈ s₁` carrying the seam-face `f₃`), every edge `ε`
of `e` is either new to `s₁` (left disjunct) or already shares an apex with `s₁`'s
link there (right disjunct).  The three cases of the proof:
* `ε ⊆ f₃` — the third vertex of `f₃` is a common apex (it sits in `t₃ ⊇ f₃`);
* `ε ⊆ f₄` (but `ε ⊄ f₃`) — an `s₁`-witness would, with the `s₂`-witness `t₄ ⊇ f₄`,
  straddle the seam, forcing `ε = cd ⊆ f₃` (contra) by `flipBridge_edge_eq_seam`;
  so `ε` is new to `s₁`;
* otherwise `ε = e \ cd` is the flip-opposite edge, empty in the union (`hOppEmpty`),
  hence empty in `s₁` by monotonicity. -/
private lemma flipBridge_compat_side {s₁ s₂ : Finset (Finset V)}
    {A B cd e f₃ f₄ t₃ t₄ : Finset V}
    (hAB : A ∩ B = cd) (hcd2 : cd.card = 2) (he4 : e.card = 4)
    (hs₁A : ∀ t ∈ s₁, t ⊆ A) (hs₂B : ∀ t ∈ s₂, t ⊆ B)
    (hcdf₃ : cd ⊆ f₃) (hcdf₄ : cd ⊆ f₄) (hf₃e : f₃ ⊆ e) (hf₃3 : f₃.card = 3) (hf₄e : f₄ ⊆ e)
    (he : e = f₃ ∪ f₄)
    (ht₃ : t₃ ∈ s₁) (hf₃t₃ : f₃ ⊆ t₃) (ht₄ : t₄ ∈ s₂) (hf₄t₄ : f₄ ⊆ t₄)
    (hOppEmpty : edgeLinkVerts (s₁ ∪ s₂) (e \ cd) = ∅)
    {ε : Finset V} (hεe : ε ⊆ e) (hε2 : ε.card = 2) :
    edgeLinkVerts s₁ ε = ∅ ∨ ((e \ ε) ∩ edgeLinkVerts s₁ ε).Nonempty := by
  by_cases hεf₃ : ε ⊆ f₃
  · -- `ε ⊆ f₃`: the third vertex `w := f₃ \ ε` is a common apex via `t₃`.
    right
    have hdiff : (f₃ \ ε).card = 1 := by rw [Finset.card_sdiff_of_subset hεf₃, hf₃3, hε2]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
    have hwmem : w ∈ f₃ \ ε := hw ▸ Finset.mem_singleton_self w
    rw [Finset.mem_sdiff] at hwmem
    obtain ⟨hwf₃, hwε⟩ := hwmem
    refine ⟨w, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hf₃e hwf₃, hwε⟩, ?_⟩⟩
    rw [mem_edgeLinkVerts_iff]
    exact ⟨⟨t₃, ht₃, hεf₃.trans hf₃t₃, hf₃t₃ hwf₃⟩, hwε⟩
  · -- `ε ⊄ f₃`: show the apex set is empty.
    left
    by_cases hεf₄ : ε ⊆ f₄
    · -- `ε ⊆ f₄`: an `s₁`-witness would straddle the seam, forcing `ε = cd ⊆ f₃`.
      apply edgeLinkVerts_eq_empty
      intro t ht hεt
      have hcontra : ε = cd :=
        flipBridge_edge_eq_seam hAB hcd2 hε2 (hs₁A t ht) (hs₂B t₄ ht₄) hεt (hεf₄.trans hf₄t₄)
      exact hεf₃ (hcontra ▸ hcdf₃)
    · -- otherwise `ε = e \ cd`: empty in the union, hence empty in `s₁`.
      have hεopp : ε = e \ cd := by
        apply Finset.eq_of_subset_of_card_le
        · -- `ε ⊆ e \ cd`: no endpoint of `ε` is in `cd`.
          intro x hxε
          rw [Finset.mem_sdiff]
          refine ⟨hεe hxε, fun hxcd => ?_⟩
          -- the other endpoint `y` of `ε` lies in neither `f₃` (`ε ⊄ f₃`, `x ∈ f₃`) nor `f₄`,
          -- yet `y ∈ e = f₃ ∪ f₄` — contradiction.
          have hxf₃ : x ∈ f₃ := hcdf₃ hxcd
          have hxf₄ : x ∈ f₄ := hcdf₄ hxcd
          obtain ⟨y, hyε, hyx⟩ : ∃ y ∈ ε, y ≠ x := by
            have h2 : 1 < ε.card := by rw [hε2]; norm_num
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
            rcases eq_or_ne a x with rfl | h
            · exact ⟨b, hb, fun h => hab h.symm⟩
            · exact ⟨a, ha, h⟩
          have hεsub : ε ⊆ insert x {y} := by
            intro z hz
            rcases eq_or_ne z x with rfl | hzx
            · exact Finset.mem_insert_self _ _
            · have hzcard : (ε.erase x).card = 1 := by
                rw [Finset.card_erase_of_mem hxε, hε2]
              obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hzcard
              have h1 : z ∈ ({u} : Finset V) := hu ▸ Finset.mem_erase.mpr ⟨hzx, hz⟩
              have h2 : y ∈ ({u} : Finset V) := hu ▸ Finset.mem_erase.mpr ⟨hyx, hyε⟩
              rw [Finset.mem_singleton] at h1 h2
              rw [h1, ← h2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have hyf₃ : y ∉ f₃ := fun hy => hεf₃ (hεsub.trans (by
            intro z hz; rcases Finset.mem_insert.mp hz with rfl | hz
            · exact hxf₃
            · rw [Finset.mem_singleton] at hz; exact hz ▸ hy))
          have hyf₄ : y ∉ f₄ := fun hy => hεf₄ (hεsub.trans (by
            intro z hz; rcases Finset.mem_insert.mp hz with rfl | hz
            · exact hxf₄
            · rw [Finset.mem_singleton] at hz; exact hz ▸ hy))
          have hye : y ∈ e := hεe hyε
          rw [he, Finset.mem_union] at hye
          exact hye.elim hyf₃ hyf₄
        · -- cardinalities: `(e \ cd).card = 2 = ε.card`.
          rw [hε2, Finset.card_sdiff_of_subset (hcdf₃.trans hf₃e), he4, hcd2]
      rw [hεopp]
      exact Finset.subset_empty.mp (hOppEmpty ▸ edgeLinkVerts_mono Finset.subset_union_left _)

/-- **Case-2 flip-edge bridge.**  Re-inserting the eligible tet `e` onto the union of
two side-fillings `s₁, s₂` pinched along the seam edge `cd` restores edge-link
connectedness, *even though the union `s₁ ∪ s₂` alone is not edge-link connected*
(its `cd`-link splits into one component per side).  The reconnection is the single
edge `a₃ ~ a₄` of `e` joining a side-1 apex `a₃ := f₃ \ cd` to a side-2 apex
`a₄ := f₄ \ cd`.

Each side, augmented by `e`, *is* edge-link connected (`edgeLinkConnected_insert`
via `flipBridge_compat_side`): `flipBridge_compat_side` discharges the clean-glue
compatibility against each side.  At a non-seam edge `ε` the seam dichotomy
(`flipBridge_edge_eq_seam`) confines `ε`'s tets to a single side, so connectivity
transfers up by `connOn_oppEdge_of_subset_local`; at the seam `cd` itself every apex
reaches `a₃` (side-1 apexes directly, side-2 apexes via `a₄` and the bridge edge).

This avoids `edgeLinkConnected_insert` *on the union* (whose `EdgeLinkConnected
(s₁ ∪ s₂)` hypothesis is false at the seam), using it only on each side separately. -/
private lemma edgeLinkConnected_insert_flipBridge {s₁ s₂ : Finset (Finset V)}
    {A B cd e f₃ f₄ t₃ t₄ : Finset V}
    (hAB : A ∩ B = cd) (hcd2 : cd.card = 2) (he4 : e.card = 4)
    (hs₁A : ∀ t ∈ s₁, t ⊆ A) (hs₂B : ∀ t ∈ s₂, t ⊆ B)
    (hcdf₃ : cd ⊆ f₃) (hcdf₄ : cd ⊆ f₄)
    (hf₃e : f₃ ⊆ e) (hf₄e : f₄ ⊆ e) (hf₃3 : f₃.card = 3) (hf₄3 : f₄.card = 3)
    (hf₃₄ : f₃ ≠ f₄) (he : e = f₃ ∪ f₄)
    (hELC₁ : EdgeLinkConnected s₁) (hELC₂ : EdgeLinkConnected s₂)
    (ht₃ : t₃ ∈ s₁) (hf₃t₃ : f₃ ⊆ t₃) (ht₄ : t₄ ∈ s₂) (hf₄t₄ : f₄ ⊆ t₄)
    (hOppEmpty : edgeLinkVerts (s₁ ∪ s₂) (e \ cd) = ∅) :
    EdgeLinkConnected (insert e (s₁ ∪ s₂)) := by
  classical
  -- ### Geometry of the seam: `a₃ := f₃ \ cd`, `a₄ := f₄ \ cd`, `e \ cd = {a₃, a₄}`.
  have hcde : cd ⊆ e := hcdf₃.trans hf₃e
  have hcard3 : (f₃ \ cd).card = 1 := by rw [Finset.card_sdiff_of_subset hcdf₃, hf₃3, hcd2]
  have hcard4 : (f₄ \ cd).card = 1 := by rw [Finset.card_sdiff_of_subset hcdf₄, hf₄3, hcd2]
  obtain ⟨a₃, ha₃⟩ := Finset.card_eq_one.mp hcard3
  obtain ⟨a₄, ha₄⟩ := Finset.card_eq_one.mp hcard4
  have ha₃mem : a₃ ∈ f₃ \ cd := ha₃ ▸ Finset.mem_singleton_self a₃
  have ha₄mem : a₄ ∈ f₄ \ cd := ha₄ ▸ Finset.mem_singleton_self a₄
  rw [Finset.mem_sdiff] at ha₃mem ha₄mem
  obtain ⟨ha₃f₃, ha₃cd⟩ := ha₃mem
  obtain ⟨ha₄f₄, ha₄cd⟩ := ha₄mem
  -- `e \ cd = {a₃, a₄}`.
  have hopp_eq : e \ cd = ({a₃, a₄} : Finset V) := by
    have hdistrib : e \ cd = (f₃ \ cd) ∪ (f₄ \ cd) := by rw [he, Finset.union_sdiff_distrib]
    rw [hdistrib, ha₃, ha₄]; rfl
  -- `a₃ ≠ a₄` (else `e \ cd` is a singleton, but it has card `4 - 2 = 2`).
  have hopp_card : (e \ cd).card = 2 := by rw [Finset.card_sdiff_of_subset hcde, he4, hcd2]
  have ha₃₄ : a₃ ≠ a₄ := by
    intro h
    rw [hopp_eq, h] at hopp_card
    simp at hopp_card
  -- `insert a₃ (insert a₄ cd) = e`: it is `{a₃, a₄} ∪ cd = (e \ cd) ∪ cd = e`.
  have hbridge_tet : insert a₃ (insert a₄ cd) = e := by
    have h1 : insert a₃ (insert a₄ cd) = ({a₃, a₄} : Finset V) ∪ cd := by
      simp only [Finset.insert_union, Finset.singleton_union]
    rw [h1, ← hopp_eq, Finset.sdiff_union_of_subset hcde]
  -- ### Each side, augmented by `e`, is edge-link connected.
  have hsub₁ : s₁ ⊆ insert e (s₁ ∪ s₂) :=
    Finset.subset_union_left.trans (Finset.subset_insert e _)
  have hsub₂ : s₂ ⊆ insert e (s₁ ∪ s₂) :=
    Finset.subset_union_right.trans (Finset.subset_insert e _)
  have hEL₁ : EdgeLinkConnected (insert e s₁) :=
    edgeLinkConnected_insert he4 hELC₁ (fun ε hεe hε2 =>
      flipBridge_compat_side hAB hcd2 he4 hs₁A hs₂B hcdf₃ hcdf₄ hf₃e hf₃3 hf₄e he
        ht₃ hf₃t₃ ht₄ hf₄t₄ hOppEmpty hεe hε2)
  have hEL₂ : EdgeLinkConnected (insert e s₂) :=
    edgeLinkConnected_insert he4 hELC₂ (fun ε hεe hε2 =>
      flipBridge_compat_side (A := B) (B := A) (s₁ := s₂) (s₂ := s₁)
        (cd := cd) (f₃ := f₄) (f₄ := f₃) (t₃ := t₄) (t₄ := t₃)
        (by rw [Finset.inter_comm]; exact hAB) hcd2 he4 hs₂B hs₁A hcdf₄ hcdf₃ hf₄e hf₄3 hf₃e
        (he.trans (Finset.union_comm f₃ f₄)) ht₄ hf₄t₄ ht₃ hf₃t₃
        (by rw [Finset.union_comm s₂ s₁]; exact hOppEmpty) hεe hε2)
  -- ### Connectivity at every edge of the union.
  intro ε hε2 x hx y hy
  by_cases hεcd : ε = cd
  · -- **Seam regime `ε = cd`:** everything reaches the fixed apex `a₃`.
    rw [hεcd] at hx hy ⊢
    -- `a₃` is a `cd`-apex (via `t₃`); `a₄` is too (via `t₄`); both lie in `insert e (s₁∪s₂)`.
    have ha₃link : a₃ ∈ edgeLinkVerts (insert e (s₁ ∪ s₂)) cd :=
      edgeLinkVerts_mono (Finset.subset_insert e _) cd
        (flipBridge_apex_mem_edgeLinkVerts ht₃ hf₃t₃ hcdf₃ ha₃f₃ ha₃cd)
    -- the bridge adjacency `a₃ ~ a₄` via `e`.
    have hadj : (edgeLinkGraph (insert e (s₁ ∪ s₂)) cd).Adj a₃ a₄ :=
      ⟨ha₃₄, by rw [hbridge_tet]; exact Finset.mem_insert_self e _⟩
    -- every `cd`-apex `z` reaches `a₃`.
    have key : ∀ z ∈ edgeLinkVerts (insert e (s₁ ∪ s₂)) cd,
        (edgeLinkGraph (insert e (s₁ ∪ s₂)) cd).Reachable z a₃ := by
      intro z hz
      rw [mem_edgeLinkVerts_iff] at hz
      obtain ⟨⟨t, htmem, hcdt, hzt⟩, hzcd⟩ := hz
      rcases Finset.mem_insert.mp htmem with rfl | htU
      · -- `t = e`: `z ∈ e \ cd = {a₃, a₄}`.
        have hzopp : z ∈ ({a₃, a₄} : Finset V) := by
          rw [← hopp_eq, Finset.mem_sdiff]; exact ⟨hzt, hzcd⟩
        rcases Finset.mem_insert.mp hzopp with rfl | hz4
        · exact SimpleGraph.Reachable.refl _
        · rw [Finset.mem_singleton] at hz4; subst hz4; exact hadj.symm.reachable
      · rcases Finset.mem_union.mp htU with hts₁ | hts₂
        · -- `z` is a side-1 `cd`-apex: reaches `a₃` inside `s₁`'s link, lifted.
          have hzs₁ : z ∈ edgeLinkVerts s₁ cd := by
            rw [mem_edgeLinkVerts_iff]; exact ⟨⟨t, hts₁, hcdt, hzt⟩, hzcd⟩
          have ha₃s₁ : a₃ ∈ edgeLinkVerts s₁ cd := by
            rw [mem_edgeLinkVerts_iff]; exact ⟨⟨t₃, ht₃, hcdf₃.trans hf₃t₃, hf₃t₃ ha₃f₃⟩, ha₃cd⟩
          exact (hELC₁ cd hcd2 z hzs₁ a₃ ha₃s₁).mono (edgeLinkGraph_mono hsub₁ cd)
        · -- `z` is a side-2 `cd`-apex: reaches `a₄` inside `s₂`'s link, then `a₄ ~ a₃`.
          have hzs₂ : z ∈ edgeLinkVerts s₂ cd := by
            rw [mem_edgeLinkVerts_iff]; exact ⟨⟨t, hts₂, hcdt, hzt⟩, hzcd⟩
          have ha₄s₂ : a₄ ∈ edgeLinkVerts s₂ cd := by
            rw [mem_edgeLinkVerts_iff]; exact ⟨⟨t₄, ht₄, hcdf₄.trans hf₄t₄, hf₄t₄ ha₄f₄⟩, ha₄cd⟩
          have hza₄ : (edgeLinkGraph (insert e (s₁ ∪ s₂)) cd).Reachable z a₄ :=
            (hELC₂ cd hcd2 z hzs₂ a₄ ha₄s₂).mono (edgeLinkGraph_mono hsub₂ cd)
          exact hza₄.trans hadj.symm.reachable
    exact (key x hx).trans (key y hy).symm
  · -- **Non-seam regime `ε ≠ cd`:** `ε`'s tets sit on one side; transfer up.
    have hεcd' : ¬ ε ⊆ cd := by
      intro h
      exact hεcd (Finset.eq_of_subset_of_card_le h (by rw [hcd2, hε2]))
    by_cases hQ : ∃ t ∈ s₂, ε ⊆ t
    · -- a side-2 witness ⟹ no side-1 witness ⟹ all `ε`-tets in `insert e s₂`.
      obtain ⟨w₂, hw₂, hεw₂⟩ := hQ
      have hloc : ∀ t ∈ insert e (s₁ ∪ s₂), ε ⊆ t → t ∈ insert e s₂ := by
        intro t htmem hεt
        rcases Finset.mem_insert.mp htmem with rfl | htU
        · exact Finset.mem_insert_self _ s₂
        · rcases Finset.mem_union.mp htU with hts₁ | hts₂
          · exact absurd (flipBridge_edge_eq_seam hAB hcd2 hε2 (hs₁A t hts₁) (hs₂B w₂ hw₂)
              hεt hεw₂) (fun h => hεcd' (h ▸ Finset.Subset.refl cd))
          · exact Finset.mem_insert_of_mem hts₂
      refine connOn_oppEdge_of_subset_local
        (Finset.insert_subset_insert e Finset.subset_union_right) hloc ?_ x hx y hy
      exact hEL₂ ε hε2
    · -- no side-2 witness ⟹ all `ε`-tets in `insert e s₁`.
      have hloc : ∀ t ∈ insert e (s₁ ∪ s₂), ε ⊆ t → t ∈ insert e s₁ := by
        intro t htmem hεt
        rcases Finset.mem_insert.mp htmem with rfl | htU
        · exact Finset.mem_insert_self _ s₁
        · rcases Finset.mem_union.mp htU with hts₁ | hts₂
          · exact Finset.mem_insert_of_mem hts₁
          · exact absurd ⟨t, hts₂, hεt⟩ hQ
      refine connOn_oppEdge_of_subset_local
        (Finset.insert_subset_insert e Finset.subset_union_left) hloc ?_ x hx y hy
      exact hEL₁ ε hε2

/-- **Edge-link connectedness of `M` from the side-split remainder (prime case 2).**
The flip-present companion of `prime_edgeLinkConnected_case1`.  When `e`'s exposed
pair `f₃, f₄` already spans a flip edge of `σ`, `removeTet M e` splits along the seam
`f₃ ∩ f₄` into two smaller single-sphere taut fillings `M₁, M₂` (`flipEdgePresent_side_sets`
+ `flipEdgePresent_side_algebra`); the IH gives each side's edge-link connectedness.
Re-gluing `e` reconnects the two sides along the bridge edge `e \ (f₃ ∩ f₄)` whose link
in the union is empty (`oppEdge_empty_of_flipEdgePresent`); the seam apexes on each side
are the exposed-triangle apexes (`exposed_triangle_unique_remaining_tet`), and
`edgeLinkConnected_insert_flipBridge` assembles the result. -/
private lemma prime_edgeLinkConnected_case2 {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hPMe : IsPseudomanifold (removeTet M e).support)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    (IHelc : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      EdgeLinkConnected M'.support) :
    EdgeLinkConnected M.support := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  -- ### Side split: two smaller single-sphere taut fillings `M₁, M₂` along the seam.
  obtain ⟨A, B, hAB, hcd2, hsphA, hsphB, hcover, hsep, hf₃A, hf₃notB, hf₄B, hf₄notA, _⟩ :=
    flipEdgePresent_side_sets hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
  obtain ⟨hUA, hUB, hbA, hbB, hTA, hTB, hSA, hSB, hnA, hnB, heA, heB, _, hsupp⟩ :=
    flipEdgePresent_side_algebra hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip hAB hcd2 hcover hsep
  set M₁ := (removeTet M e).filter (fun t => t ⊆ A) with hM₁
  set M₂ := (removeTet M e).filter (fun t => t ⊆ B) with hM₂
  -- ### Each side, by the IH, is edge-link connected.
  have hELC₁ : EdgeLinkConnected M₁.support :=
    IHelc ((flipBoundary σ M e).filter (fun f => f ⊆ A)) (bdry M₁) M₁ hnA hsphA hUA hbA rfl hTA hSA
  have hELC₂ : EdgeLinkConnected M₂.support :=
    IHelc ((flipBoundary σ M e).filter (fun f => f ⊆ B)) (bdry M₂) M₂ hnB hsphB hUB hbB rfl hTB hSB
  -- ### Seam geometry from the eligible exposed pair.
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
  -- `cd ⊆ f₃`, `cd ⊆ f₄`, `cd.card = 2` (`cd := f₃ ∩ f₄`).
  have hcdf₃ : f₃ ∩ f₄ ⊆ f₃ := Finset.inter_subset_left
  have hcdf₄ : f₃ ∩ f₄ ⊆ f₄ := Finset.inter_subset_right
  -- `e = f₃ ∪ f₄`: `f₃ ∪ f₄ ⊆ e` with `|f₃ ∪ f₄| = 3 + 3 - 2 = 4 = |e|`.
  have hunioncard : (f₃ ∪ f₄).card + (f₃ ∩ f₄).card = f₃.card + f₄.card :=
    Finset.card_union_add_card_inter f₃ f₄
  have he_eq : e = f₃ ∪ f₄ := by
    refine (Finset.eq_of_subset_of_card_le (Finset.union_subset hf₃e hf₄e) ?_).symm
    rw [he4]; rw [hf₃3, hf₄3, hcd2] at hunioncard; omega
  -- ### Side-locality of `M₁, M₂` (filters by `⊆ A` / `⊆ B`).
  have hs₁A : ∀ t ∈ M₁.support, t ⊆ A := by
    intro t ht; rw [hM₁, Finsupp.support_filter, Finset.mem_filter] at ht; exact ht.2
  have hs₂B : ∀ t ∈ M₂.support, t ⊆ B := by
    intro t ht; rw [hM₂, Finsupp.support_filter, Finset.mem_filter] at ht; exact ht.2
  -- ### `(removeTet M e).support = M₁.support ∪ M₂.support` (from `hsupp`, `e ∉` each).
  have hsuppU : (removeTet M e).support = M₁.support ∪ M₂.support := by
    rw [support_removeTet_of_mem he.2.1, hsupp, Finset.erase_insert]
    rw [Finset.mem_union]; rintro (h | h)
    · exact heA h
    · exact heB h
  -- ### Seam-face witnesses: `f₃` lies in some `M₁`-tet, `f₄` in some `M₂`-tet.
  obtain ⟨t₃, ht₃R, hf₃t₃⟩ :=
    exposed_triangle_unique_remaining_tet hσ hU hMX hT hS hPure hPMe he hf₃exp
  obtain ⟨t₄, ht₄R, hf₄t₄⟩ :=
    exposed_triangle_unique_remaining_tet hσ hU hMX hT hS hPure hPMe he hf₄exp
  -- `t₃ ⊆ A` (else `t₃ ⊆ B` ⟹ `f₃ ⊆ B`, contradiction).
  have ht₃ : t₃ ∈ M₁.support := by
    rw [hM₁, Finsupp.support_filter, Finset.mem_filter]
    refine ⟨ht₃R, ?_⟩
    rcases hcover t₃ ht₃R with htA | htB
    · exact htA
    · exact absurd (hf₃t₃.trans htB) hf₃notB
  have ht₄ : t₄ ∈ M₂.support := by
    rw [hM₂, Finsupp.support_filter, Finset.mem_filter]
    refine ⟨ht₄R, ?_⟩
    rcases hcover t₄ ht₄R with htA | htB
    · exact absurd (hf₄t₄.trans htA) hf₄notA
    · exact htB
  -- ### Empty link of the bridge edge in the union.
  have hOppEmpty : edgeLinkVerts (M₁.support ∪ M₂.support) (e \ (f₃ ∩ f₄)) = ∅ := by
    rw [← hsuppU]
    exact oppEdge_empty_of_flipEdgePresent hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
  -- ### Assemble: `M.support = insert e (M₁.support ∪ M₂.support)`, then the bridge.
  rw [hsupp]
  exact edgeLinkConnected_insert_flipBridge hAB hcd2 he4 hs₁A hs₂B hcdf₃ hcdf₄ hf₃e hf₄e
    hf₃3 hf₄3 hf₃₄ he_eq hELC₁ hELC₂ ht₃ hf₃t₃ ht₄ hf₄t₄ hOppEmpty

/-- **Prime (no-degree-3) step of the edge-link-connectedness induction.**
Mirror of `prime_isPM`: when `σ` has no degree-3 vertex, pick a face-disjoint
eligible pair (`aleph_disjoint_eligible_pair`).  Orientation
(`eligible_pair_oriented_opp_avoidance`) names a favored tet `r` whose
flip-opposite edge `r \ (r₃ ∩ r₄)` avoids the other tet `w`.  If `r`'s exposed
pair spans a flip edge of `σ`, the side-split assembly
(`prime_edgeLinkConnected_case2`) applies; otherwise the remainder is itself a
smaller taut filling (edge-link connected by IH via
`removeTet_edgeLinkConnected_noFlip`) and the avoided edge's link in
`removeTet M w` is connected (`removeTet_connOn_oppEdge_of_disjoint_eligible`),
so the clean re-glue `prime_edgeLinkConnected_case1` finishes. -/
private lemma prime_edgeLinkConnected {σ : Finset (Finset V)} {X M : Chain V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hNo3 : NoDegree3Vertex σ)
    (IHelc : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      EdgeLinkConnected M'.support) :
    EdgeLinkConnected M.support := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hPure : ∀ t ∈ M.support, t.card = 4 :=
    fun t ht => (aleph_base_taut_support_card4_subset_verts hσ hU hMX hT t ht).1
  -- Reusable PM supplier for the smaller fillings (`taut_isPseudomanifold` is standalone).
  have IHpm : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      IsPseudomanifold M'.support :=
    fun σ' X' M' _ hσ' hU' hXc' hMX' hT' hS' => taut_isPseudomanifold hσ' hU' hXc' hMX' hT' hS'
  -- A single oriented step, applied to both disjunct orientations.
  have key : ∀ (r w r₃ r₄ : Finset V), EligibleTet M r → EligibleTet M w → r ≠ w →
      Disjoint (sharedFaces M r) (sharedFaces M w) → exposedFaces M r = {r₃, r₄} → r₃ ≠ r₄ →
      ¬ (r \ (r₃ ∩ r₄)) ⊆ w → EdgeLinkConnected M.support := by
    intro r w r₃ r₄ hr hw rne rdisj hrexp hr₃₄ hOu
    have hPMr : IsPseudomanifold (removeTet M r).support :=
      removeTet_isPseudomanifold hσ hU hXc hMX hT hS hr IHpm
    by_cases hFlip : FlipEdgePresent σ r₃ r₄
    · exact prime_edgeLinkConnected_case2 hσ hU hXc hMX hT hS hPure hPMr hr hrexp hr₃₄ hFlip IHelc
    · have hELMr : EdgeLinkConnected (removeTet M r).support :=
        removeTet_edgeLinkConnected_noFlip hσ hU hXc hMX hT hS hr hrexp hr₃₄ hFlip IHelc
      have hConnOw : ConnOn (edgeLinkGraph (removeTet M w).support (r \ (r₃ ∩ r₄)))
          (edgeLinkVerts (removeTet M w).support (r \ (r₃ ∩ r₄))) :=
        removeTet_connOn_oppEdge_of_disjoint_eligible hσ hU hXc hMX hT hS hr hw hrexp hr₃₄ hOu IHelc
      exact prime_edgeLinkConnected_case1 hσ hU hXc hMX hT hS hPure hr hw hPMr hrexp hr₃₄ hOu
        hELMr hConnOw
  obtain ⟨e₀, u₀, hne, he₀, hu₀, hdisj⟩ := aleph_disjoint_eligible_pair hσ hUb hS hT hPure hNo3
  obtain ⟨f₃, f₄, hf₃₄, hexpe⟩ := exposedFaces_eq_pair_of_eligible he₀
  obtain ⟨g₃, g₄, hg₃₄, hexpu⟩ := exposedFaces_eq_pair_of_eligible hu₀
  rcases eligible_pair_oriented_opp_avoidance hσ hU hMX he₀ hu₀ hne hdisj hexpe hf₃₄ hexpu hg₃₄
    with hOu | hOu
  · exact key e₀ u₀ f₃ f₄ he₀ hu₀ hne hdisj hexpe hf₃₄ hOu
  · exact key u₀ e₀ g₃ g₄ hu₀ he₀ hne.symm hdisj.symm hexpu hg₃₄ hOu

/-- **base_edgeLinkConnected** (edge-link base case, ≤ 4 vertices): a taut filling
of a 2-sphere on ≤ 4 vertices is a single tetrahedron, hence edge-link connected.
Mirrors `base_isPM` verbatim; only the final step changes from
`isPseudomanifold_singleton` to `edgeLinkConnected_singleton`. -/
private lemma base_edgeLinkConnected (σ : Finset (Finset V)) (X M : Chain V)
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) (hv : (vertsOf σ).card ≤ 4) :
    EdgeLinkConnected M.support := by
  have hcard : (vertsOf σ).card = 4 := aleph_base_verts_card_eq_four hσ hv
  have hsuppInfo := aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
  have hne := aleph_base_support_nonempty hσ hU hMX
  have hsupp : M.support = {vertsOf σ} :=
    aleph_base_support_eq_singleton_of_four_vertices hcard hsuppInfo hne
  rw [hsupp]
  exact edgeLinkConnected_singleton hcard

/-- **deg3_edgeLinkConnected** (edge-link degree-3 step): a taut filling of a
2-sphere with a degree-3 vertex is edge-link connected, given that every strictly
smaller single-sphere taut filling is.  Mirrors `deg3_isPM`'s setup (the cut, the
ML/MR filters, the star-side dichotomy, `hsupport`/`hTnot`/`hvNotR`); instead of
re-inserting the star tet with `isPseudomanifold_insert`, it applies the IH to the
remainder to get `EdgeLinkConnected R.support`, then re-inserts the star tet with
`edgeLinkConnected_insert`, discharging the edge-link clean-glue obligation by the
`helc` field of `cleanGlueStep_star_of_remainder` (the star glue retained from
`degree3_cut_star_side_glue`).  The remainder PM (needed to pin `γ` into a unique
tet via `faceCount_eq_one_of_boundary`) is supplied by the standalone
`taut_isPseudomanifold`. -/
private lemma deg3_edgeLinkConnected (σ : Finset (Finset V)) (X M : Chain V)
    (hσ : IsSphere2 σ) (hbig : 4 < (vertsOf σ).card) (hU : UnitOn X σ) (hXc : bdry X = 0)
    (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M) (hd3 : HasDegree3Vertex σ)
    (IHelc : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      EdgeLinkConnected M'.support) :
    EdgeLinkConnected M.support := by
  classical
  obtain ⟨v, W, hv, hγ3, hγe, hγσ, hW, hσL, hσR⟩ :=
    degree3_cut_setup σ hσ hbig hd3
  let γ : Finset V := linkVerts σ v
  have hγ : γ = linkVerts σ v := rfl
  let A : Finset V := vertsOf (insert γ (cutSet σ W))
  let ML : Chain V := M.filter (fun t => t ⊆ A)
  let MR : Chain V := M.filter (fun t => ¬ t ⊆ A)
  obtain ⟨c, hUL, hXLc, hUR, hXRc, hXsum⟩ :=
    capped_cut_splits_unit σ X hσ hγ3 hγe hγσ hW hU hXc
  obtain ⟨hML, hMR, hTL, hTR, hSuppL, hSuppR, hMsum⟩ :=
    taut_splits_for_capped_cut σ X M hσ hσL hσR hγ3 hγe hW
      hUL hXLc hUR hXRc hXsum hMX hT
  have hsplit := degree3_cut_star_side_glue σ hσ hbig hv hγ3 hW
  have hT4 : (starTet σ v).card = 4 := starTet_card_of_degree3 σ hγ3
  have hγ3' : γ.card = 3 := hγ ▸ hγ3
  -- γ lies in both candidate remainder spheres
  have hγL : γ ∈ insert γ (cutSet σ W) := Finset.mem_insert_self _ _
  have hγR : γ ∈ insert γ (cutSet σ (W + fun _ => 1)) := Finset.mem_insert_self _ _
  rcases hsplit with hcase | hcase
  · -- left side is the star; remainder is MR (the ¬⊆A side, sphere σR)
    rcases hcase with ⟨hstar, hglue⟩
    have hULtet : UnitOn (cappedCutLeft σ W X γ c) (tetFaces (starTet σ v)) := by
      dsimp [γ]; rw [← hstar]; exact hUL
    have hSuppLT : ∀ t ∈ ML.support, t ⊆ starTet σ v := by
      intro t ht
      have htA : t ⊆ vertsOf (insert γ (cutSet σ W)) :=
        hSuppL t (by simpa only [ML, A] using ht)
      dsimp [γ] at htA
      rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4] at htA
      exact htA
    have hMLsupp : ML.support = {starTet σ v} :=
      star_filter_support_singleton ML (cappedCutLeft σ W X γ c)
        (starTet σ v) hT4 hULtet (by simpa only [ML, A, γ] using hML)
        (by simpa only [ML, A, γ] using hTL) hSuppLT
    have hlt : nrm MR < nrm M := by
      have hlt' : nrm (M.filter (fun t => ¬ t ⊆ A)) < nrm M :=
        norm_lt_filter_neg_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
      simpa only [MR] using hlt'
    have hSimpR : SimplicialChain MR := by
      intro t
      dsimp [MR, A, γ]
      rw [Finsupp.filter_apply]
      by_cases ht : ¬ t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W))
      · rw [if_pos ht]; exact hS t
      · rw [if_neg ht]; exact Or.inr (Or.inl rfl)
    have hbdMR : bdry MR = cappedCutRight σ W X γ c := by dsimp [MR, A, γ]; exact hMR
    have hURMR : UnitOn (bdry MR) (insert γ (cutSet σ (W + fun _ => 1))) := by
      rw [hbdMR]; dsimp [γ]; exact hUR
    have hTRMR : IsTaut MR := by dsimp [MR, A, γ]; exact hTR
    have hσRdef : IsSphere2 (insert γ (cutSet σ (W + fun _ => 1))) := by dsimp [γ]; exact hσR
    have hPMR : IsPseudomanifold MR.support :=
      taut_isPseudomanifold hσRdef hURMR (bdry_bdry _) rfl hTRMR hSimpR
    have hELMR : EdgeLinkConnected MR.support :=
      IHelc (insert γ (cutSet σ (W + fun _ => 1))) (bdry MR) MR hlt hσRdef hURMR
        (bdry_bdry _) rfl hTRMR hSimpR
    have hPT : (starTet σ v) ⊆ A := by
      have hTin : starTet σ v ∈ ML.support := by rw [hMLsupp]; simp
      have hTin' : ¬ M (starTet σ v) = 0 ∧ (starTet σ v) ⊆ A := by simpa [ML] using hTin
      exact hTin'.2
    have hTnot : starTet σ v ∉ MR.support := by
      intro hmem
      have hne : MR (starTet σ v) ≠ 0 := Finsupp.mem_support_iff.mp hmem
      have hzero : MR (starTet σ v) = 0 := by simp [MR, hPT]
      exact hne hzero
    have hvNotMR : ∀ t ∈ MR.support, v ∉ t := by
      have hvNotSigmaR : v ∉ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) :=
        degree3_apex_notMem_right_verts_of_left_star (σ := σ) (v := v) (W := W)
          (γ := γ) hσ hγ3 rfl (by simpa [γ] using hW) hstar
      have hsuppInfo :
          ∀ t ∈ MR.support,
            t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) :=
        aleph_base_taut_support_card4_subset_verts hσRdef
          (by dsimp [γ]; exact hUR) hbdMR hTRMR
      intro t ht hvt
      exact hvNotSigmaR ((hsuppInfo t ht).2 hvt)
    have hPureMR : ∀ t ∈ MR.support, t.card = 4 := by
      have hsuppInfo :
          ∀ t ∈ MR.support,
            t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) :=
        aleph_base_taut_support_card4_subset_verts hσRdef
          (by dsimp [γ]; exact hUR) hbdMR hTRMR
      intro t ht; exact (hsuppInfo t ht).1
    have hURγ : bdry MR γ = 1 ∨ bdry MR γ = -1 := hURMR.2 γ hγR
    -- γ sits in a unique remainder tet (faceCount = 1), giving the apex `t₀`.
    have hγcount1 : faceCount MR.support γ = 1 :=
      faceCount_eq_one_of_boundary hSimpR hPureMR hPMR hγ3' hURγ
    have ht₀ : ∃ t₀ ∈ MR.support, γ ⊆ t₀ := by
      have hfilt : (MR.support.filter (fun t => γ ⊆ t)).card = 1 := hγcount1
      obtain ⟨t₀', ht₀'set⟩ := Finset.card_eq_one.mp hfilt
      have hmem' : t₀' ∈ MR.support.filter (fun t => γ ⊆ t) := by
        rw [ht₀'set]; exact Finset.mem_singleton_self _
      obtain ⟨ht₀'mem, hγt₀'⟩ := Finset.mem_filter.mp hmem'
      exact ⟨t₀', ht₀'mem, hγt₀'⟩
    have hγB : γ ∈ tetFaces (starTet σ v) ∩ (insert γ (cutSet σ (W + fun _ => 1))) := by
      refine Finset.mem_inter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
      have hstarEq : starTet σ v = insert v γ := by rw [starTet, hγ]
      exact Finset.mem_powersetCard.mpr ⟨by rw [hstarEq]; exact Finset.subset_insert _ _, hγ3'⟩
    have hsupport : M.support = insert (starTet σ v) MR.support := by
      simpa only [MR] using
        support_eq_insert_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
    rw [hsupport]
    refine edgeLinkConnected_insert hT4 hELMR ?_
    exact (cleanGlueStep_star_of_remainder hγ hγ3 hT4 hglue hTnot hvNotMR ht₀
      (by omega) hγB).helc
  · -- right side is the star; remainder is ML (the ⊆A side, sphere σL)
    rcases hcase with ⟨hstar, hglue⟩
    have hURtet : UnitOn (cappedCutRight σ W X γ c) (tetFaces (starTet σ v)) := by
      dsimp [γ]; rw [← hstar]; exact hUR
    have hSuppRT : ∀ t ∈ MR.support, t ⊆ starTet σ v := by
      intro t ht
      have htA : t ⊆ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) :=
        hSuppR t (by simpa only [MR, A] using ht)
      dsimp [γ] at htA
      rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4] at htA
      exact htA
    have hMRsupp : MR.support = {starTet σ v} :=
      star_filter_support_singleton MR (cappedCutRight σ W X γ c)
        (starTet σ v) hT4 hURtet (by simpa only [MR, A, γ] using hMR)
        (by simpa only [MR, A, γ] using hTR) hSuppRT
    have hML_eq : ML = M.filter (fun t => ¬ (¬ t ⊆ A)) := by
      dsimp [ML]
      ext t
      rw [Finsupp.filter_apply, Finsupp.filter_apply]
      by_cases ht : t ⊆ A
      · rw [if_pos ht, if_pos]; intro hneg; exact hneg ht
      · rw [if_neg ht, if_neg]; intro hnn; exact hnn ht
    have hlt : nrm ML < nrm M := by
      have hlt' : nrm (M.filter (fun t => ¬ (¬ t ⊆ A))) < nrm M :=
        norm_lt_filter_neg_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
      rwa [← hML_eq] at hlt'
    have hSimpL : SimplicialChain ML := by
      intro t
      dsimp [ML, A, γ]
      rw [Finsupp.filter_apply]
      by_cases ht : t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W))
      · rw [if_pos ht]; exact hS t
      · rw [if_neg ht]; exact Or.inr (Or.inl rfl)
    have hbdML : bdry ML = cappedCutLeft σ W X γ c := by dsimp [ML, A, γ]; exact hML
    have hULML : UnitOn (bdry ML) (insert γ (cutSet σ W)) := by
      rw [hbdML]; dsimp [γ]; exact hUL
    have hTLML : IsTaut ML := by dsimp [ML, A, γ]; exact hTL
    have hσLdef : IsSphere2 (insert γ (cutSet σ W)) := by dsimp [γ]; exact hσL
    have hPML : IsPseudomanifold ML.support :=
      taut_isPseudomanifold hσLdef hULML (bdry_bdry _) rfl hTLML hSimpL
    have hELML : EdgeLinkConnected ML.support :=
      IHelc (insert γ (cutSet σ W)) (bdry ML) ML hlt hσLdef hULML
        (bdry_bdry _) rfl hTLML hSimpL
    have hPstar : ¬ (starTet σ v) ⊆ A := by
      have hTin : starTet σ v ∈ MR.support := by rw [hMRsupp]; simp
      have hTin' : ¬ M (starTet σ v) = 0 ∧ ¬ (starTet σ v) ⊆ A := by simpa [MR] using hTin
      exact hTin'.2
    have hTnot : starTet σ v ∉ ML.support := by
      intro hmem
      have hne : ML (starTet σ v) ≠ 0 := Finsupp.mem_support_iff.mp hmem
      have hzero : ML (starTet σ v) = 0 := by simp [ML, hPstar]
      exact hne hzero
    have hvNotML : ∀ t ∈ ML.support, v ∉ t := by
      have hvNotSigmaL : v ∉ vertsOf (insert γ (cutSet σ W)) :=
        degree3_apex_notMem_left_verts_of_right_star (σ := σ) (v := v) (W := W)
          (γ := γ) hσ hγ3 rfl (by simpa [γ] using hW) hstar
      have hsuppInfo :
          ∀ t ∈ ML.support, t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet σ W)) :=
        aleph_base_taut_support_card4_subset_verts hσLdef
          (by dsimp [γ]; exact hUL) hbdML hTLML
      intro t ht hvt
      exact hvNotSigmaL ((hsuppInfo t ht).2 hvt)
    have hPureML : ∀ t ∈ ML.support, t.card = 4 := by
      have hsuppInfo :
          ∀ t ∈ ML.support, t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet σ W)) :=
        aleph_base_taut_support_card4_subset_verts hσLdef
          (by dsimp [γ]; exact hUL) hbdML hTLML
      intro t ht; exact (hsuppInfo t ht).1
    have hURγ : bdry ML γ = 1 ∨ bdry ML γ = -1 := hULML.2 γ hγL
    have hγcount1 : faceCount ML.support γ = 1 :=
      faceCount_eq_one_of_boundary hSimpL hPureML hPML hγ3' hURγ
    have ht₀ : ∃ t₀ ∈ ML.support, γ ⊆ t₀ := by
      have hfilt : (ML.support.filter (fun t => γ ⊆ t)).card = 1 := hγcount1
      obtain ⟨t₀', ht₀'set⟩ := Finset.card_eq_one.mp hfilt
      have hmem' : t₀' ∈ ML.support.filter (fun t => γ ⊆ t) := by
        rw [ht₀'set]; exact Finset.mem_singleton_self _
      obtain ⟨ht₀'mem, hγt₀'⟩ := Finset.mem_filter.mp hmem'
      exact ⟨t₀', ht₀'mem, hγt₀'⟩
    have hγB : γ ∈ tetFaces (starTet σ v) ∩ (insert γ (cutSet σ W)) := by
      refine Finset.mem_inter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
      have hstarEq : starTet σ v = insert v γ := by rw [starTet, hγ]
      exact Finset.mem_powersetCard.mpr ⟨by rw [hstarEq]; exact Finset.subset_insert _ _, hγ3'⟩
    have hsupport : M.support = insert (starTet σ v) ML.support := by
      have hsupport' :
          M.support = insert (starTet σ v)
            (M.filter (fun t => ¬ (¬ t ⊆ A))).support :=
        support_eq_insert_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
      rwa [← hML_eq] at hsupport'
    rw [hsupport]
    refine edgeLinkConnected_insert hT4 hELML ?_
    exact (cleanGlueStep_star_of_remainder hγ hγ3 hT4 hglue hTnot hvNotML ht₀
      (by omega) hγB).helc

/-- **Edge-link connectedness of every taut filling of a combinatorial 2-sphere.**
The manifold-along-edges half of a faithful stickerball, by a standalone strong
induction parallel to `taut_isPseudomanifold`: base case (≤ 4 vertices) by
`base_edgeLinkConnected`; degree-3 vertex by `deg3_edgeLinkConnected`; otherwise by
`prime_edgeLinkConnected`; the strong induction hypothesis is threaded to both
non-base steps as `IHelc`. -/
theorem taut_edgeLinkConnected {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : EdgeLinkConnected M.support := by
  suffices H : ∀ N, ∀ (σ : Finset (Finset V)) (X M : Chain V), nrm M = N → IsSphere2 σ →
      UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
      EdgeLinkConnected M.support by
    exact H (nrm M) σ X M rfl hσ hU hXc hMX hT hS
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro σ X M hN hσ hU hXc hMX hT hS
    by_cases hv : (vertsOf σ).card ≤ 4
    · exact base_edgeLinkConnected σ X M hσ hU hMX hT hS hv
    · push_neg at hv
      by_cases hd3 : HasDegree3Vertex σ
      · refine deg3_edgeLinkConnected σ X M hσ hv hU hXc hMX hT hS hd3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'
      · have hno3 : NoDegree3Vertex σ := fun v hvv hcard => hd3 ⟨v, hvv, hcard⟩
        refine prime_edgeLinkConnected hσ hU hXc hMX hT hS hno3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'

end Taut
