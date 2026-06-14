import Taut.Theorem2

/-!
# The triangle-cut oriented bridge (M24b, architect: codex 019ec44f, Q2)

For the connected-sum (degree-3) reduction, a non-face triangle `γ` cuts the unit
boundary cycle `X = ∂M` of a 2-sphere into two oriented sides. Unlike the
edge-join (M23), the side-filter `X.filter (· ∈ σ₁)` is NOT closed — its boundary
is `c • ∂γ` for some `c` — so each side must be *capped* with `γ`:

    X₁ = X.filter (· ∈ σ₁) − c • [γ],   X₂ = X.filter (· ∈ σ₂) + c • [γ]

making both closed, with `X₁ + X₂ = X`. This feeds `IsTaut.splits` (`n = 2`,
`A ∩ B = γ`, `|γ| = 3 ≤ n+1`).

This file's foundation: a closed 1-chain supported on the three edges of a triangle
`γ` is a multiple of `∂γ` — proved via the contracting homotopy
`bdry_cone_add_cone_bdry`: coning the (closed) chain from a vertex `a ∈ γ` kills the
two edges through `a` and sends the opposite edge `γ \ {a}` to `±γ`, so the cone is
`c • [γ]` and the chain is its boundary `c • ∂γ`.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- **A closed 1-chain on a triangle's edges is a multiple of its boundary.** If
`bdry C = 0` and every face in `C.support` is a 2-edge of the triangle `γ` (card
3), then `C = c • bdryGen γ` for some integer `c`. -/
lemma closed_one_chain_supported_on_triangle {γ : Finset V} (hγ3 : γ.card = 3)
    {C : Chain V} (hCc : bdry C = 0)
    (hCsupp : ∀ e ∈ C.support, e ∈ γ.powersetCard 2) :
    ∃ c : ℤ, C = c • bdryGen γ := by
  classical
  obtain ⟨a, ha⟩ : γ.Nonempty := Finset.card_pos.mp (by rw [hγ3]; omega)
  -- `C` is the boundary of its cone from `a` (since `C` is closed)
  have hC : C = bdry (cone a C) := by
    have h := bdry_cone_add_cone_bdry a C
    rw [hCc, map_zero, add_zero] at h; exact h.symm
  -- the cone collapses to a multiple of `[γ]`
  set c : ℤ := C (γ.erase a) * sgn a (γ.erase a) with hcdef
  have hcone : cone a C = c • Finsupp.single γ 1 := by
    ext s
    rw [cone_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, hcdef]
    by_cases hsγ : s = γ
    · subst hsγ
      rw [if_pos ha, if_pos rfl, mul_one]; ring
    · rw [if_neg (Ne.symm hsγ), mul_zero]
      by_cases has : a ∈ s
      · rw [if_pos has]
        have hCz : C (s.erase a) = 0 := by
          by_contra hCne
          have hmem := Finset.mem_powersetCard.mp (hCsupp _ (Finsupp.mem_support_iff.mpr hCne))
          have hsea : s.erase a = γ.erase a := by
            refine Finset.eq_of_subset_of_card_le (fun u hu => ?_)
              (by rw [Finset.card_erase_of_mem ha, hγ3, hmem.2])
            exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hu, hmem.1 hu⟩
          exact hsγ (by rw [← Finset.insert_erase has, hsea, Finset.insert_erase ha])
        rw [hCz, mul_zero]
      · rw [if_neg has]
  refine ⟨c, ?_⟩
  rw [hC, hcone, map_smul, bdry_single, one_smul]

/-- **The capping algebra of the triangle cut.** Once the side-filter boundary is
identified as `bdry X₁ = c • bdryGen γ` (via `closed_one_chain_supported_on_triangle`
applied to the cut), capping the two sides with `± c • [γ]` makes both closed while
preserving their sum: `(X₁ − c•[γ]) + (X₂ + c•[γ]) = X`. The cut-machinery half
(showing `bdry X₁` lands on γ's edges) is the remaining part of M24b. -/
lemma capped_split_of_side_boundary {X X₁ X₂ : Chain V} {γ : Finset V} {c : ℤ}
    (hsum : X₁ + X₂ = X) (hXc : bdry X = 0) (hb1 : bdry X₁ = c • bdryGen γ) :
    bdry (X₁ - Finsupp.single γ c) = 0 ∧ bdry (X₂ + Finsupp.single γ c) = 0 ∧
      (X₁ - Finsupp.single γ c) + (X₂ + Finsupp.single γ c) = X := by
  have hbs : bdry (Finsupp.single γ c) = c • bdryGen γ := bdry_single γ c
  have hb2 : bdry X₂ = -(c • bdryGen γ) := by
    have h : bdry X₁ + bdry X₂ = 0 := by rw [← map_add, hsum, hXc]
    rw [hb1] at h; exact eq_neg_of_add_eq_zero_right h
  refine ⟨?_, ?_, ?_⟩
  · rw [map_sub, hb1, hbs, sub_self]
  · rw [map_add, hb2, hbs, neg_add_cancel]
  · rw [← hsum]; abel

end Taut
