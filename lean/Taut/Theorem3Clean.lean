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

end Taut
