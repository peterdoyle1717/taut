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

end Taut
