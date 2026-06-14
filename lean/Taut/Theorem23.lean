import Taut.Eligible

/-!
# Theorem 2 (core): a taut filling of a 2-sphere is a ball — the induction skeleton

The central theorem of "Taut fillings": a taut integral filling `M` of a
combinatorial 2-sphere `σ` arises from a simplicial triangulation of `B³` — here,
`M.support` is a (shelling-certified) ball with boundary `σ` (`IsBall M.support
σ`). The paper's proof is a strong induction on `|M| = nrm M`.

This file is the **induction skeleton** (architect: codex 019ec44f, Q5): the
strong-induction plumbing, with the three reduction steps as explicit hypotheses
— the named holes the remaining milestones fill:

* `base` — the minimal sphere `(vertsOf σ).card ≤ 4` (a tetrahedron boundary): its
  taut filling is a single tet, a ball (M24 base / `isBall_singleton`);
* `deg3_split` — a sphere with a degree-3 vertex splits (connected sum along the
  link triangle) into a strictly smaller taut filling whose ball reassembles to
  the original (M24c `deg3_split`, interface per the codex 019ec44f Q4 design);
* `prime_step` — a no-degree-3 ("prime") sphere: remove an eligible tet
  (`exists_eligibleTet_of_noDegree3`, M25 ✓) and reassemble, consuming the
  induction hypothesis on strictly smaller fillings (the eligible-tet branch =
  M25b disjoint pair + M22b relative shelling + the M23 edge-join bridge).

`theorem2_core` discharges Theorem 2 modulo these three. Free shellability
(Theorem 3) is a strengthening of the invariant, deferred.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- **Theorem 2 (core), the strong induction.** Given the base case and the two
reduction steps, every taut filling of a 2-sphere is a ball. The proof is pure
strong-induction plumbing on `nrm M`; all geometric content lives in the three
hypotheses (the named holes M24/M25b/M22b fill). -/
theorem theorem2_core
    (base : ∀ (σ : Finset (Finset V)) (X M : Chain V), IsSphere2 σ → UnitOn X σ →
      bdry M = X → IsTaut M → SimplicialChain M → (vertsOf σ).card ≤ 4 →
      IsBall M.support σ)
    (deg3_split : ∀ (σ : Finset (Finset V)) (X M : Chain V), IsSphere2 σ →
      4 < (vertsOf σ).card → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M →
      SimplicialChain M → HasDegree3Vertex σ →
      ∃ (σ' : Finset (Finset V)) (X' M' : Chain V),
        IsSphere2 σ' ∧ UnitOn X' σ' ∧ bdry X' = 0 ∧ bdry M' = X' ∧ IsTaut M' ∧
        SimplicialChain M' ∧ nrm M' < nrm M ∧
        (IsBall M'.support σ' → IsBall M.support σ))
    (prime_step : ∀ (σ : Finset (Finset V)) (X M : Chain V), IsSphere2 σ →
      4 < (vertsOf σ).card → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M →
      SimplicialChain M → NoDegree3Vertex σ →
      (∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
        UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
        IsBall M'.support σ') →
      IsBall M.support σ)
    {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ) (hU : UnitOn X σ)
    (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M) :
    IsBall M.support σ := by
  -- strong induction on `nrm M`
  suffices H : ∀ N, ∀ (σ : Finset (Finset V)) (X M : Chain V), nrm M = N → IsSphere2 σ →
      UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
      IsBall M.support σ by
    exact H (nrm M) σ X M rfl hσ hU hXc hMX hT hS
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro σ X M hN hσ hU hXc hMX hT hS
    by_cases hv : (vertsOf σ).card ≤ 4
    · exact base σ X M hσ hU hMX hT hS hv
    · push_neg at hv
      by_cases hd3 : HasDegree3Vertex σ
      · obtain ⟨σ', X', M', hσ', hU', hX'c, hM'X', hT', hS', hlt, hreass⟩ :=
          deg3_split σ X M hσ hv hU hXc hMX hT hS hd3
        exact hreass (IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS')
      · have hno3 : NoDegree3Vertex σ := fun v hvv hcard => hd3 ⟨v, hvv, hcard⟩
        refine prime_step σ X M hσ hv hU hXc hMX hT hS hno3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'

end Taut
