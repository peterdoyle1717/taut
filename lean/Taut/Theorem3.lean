import Taut.Theorem2Aleph

/-!
# Theorem 3: free sticker balls (the `FreelyShellable` reassembly)

Per Peter's "sticker ball" reframe (codex 019ecbfa): the induction carries
`FreelyShellable` (a free sticker ball — startable at any tet), and the case-2
reassembly is a direct concatenation rather than a topological obstruction. This
file builds the free-shelling reassembly tools and discharges the branch holes of
`theorem3_core`.

This installment: **L1** — the free case-1 stick (a free sticker ball plus a
`GlueStep` tet is a free sticker ball, given the bridge-start relative shelling) —
and **base_free** — the minimal-sphere base case as a free sticker ball (reusing
the Aleph base lemmas, finishing with `freelyShellable_singleton`).
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- **L1 (free case-1 stick).** A free sticker ball `τ` (boundary `B`) plus a fresh
`GlueStep` tet `t` is a free sticker ball with `t` adjoined. For an old target the
shelling is `(old shelling from target) ++ [t]`; for target `t` the shelling is
`t :: (a shelling of τ onto the post-glue boundary `B'` starting from `tetFaces t`)`
— that bridge-start relative shelling is the hypothesis `hstart_t` (supplied by the
geometry at the call site). -/
lemma FreelyShellable.insert_of_glueStep {τ B B' : Finset (Finset V)} {t : Finset V}
    (hfree : FreelyShellable τ B) (hg : GlueStep t B B') (ht : t ∉ τ)
    (hstart_t : ∃ l : List (Finset V), l.toFinset = τ ∧ l.Nodup ∧
      ShellFrom (tetFaces t) l B') :
    FreelyShellable (insert t τ) B' := by
  intro s hs
  rw [Finset.mem_insert] at hs
  rcases hs with rfl | hsτ
  · -- target is the new tet (`rcases rfl` substituted the binder `t := s`)
    obtain ⟨l, hlτ, hnodup, hsf⟩ := hstart_t
    refine ⟨s :: l, rfl, ?_, ?_, hg.card4, hsf⟩
    · rw [List.toFinset_cons, hlτ]
    · exact List.nodup_cons.mpr ⟨fun hc => ht (hlτ ▸ List.mem_toFinset.mpr hc), hnodup⟩
  · -- target is an old tet `s ∈ τ`
    obtain ⟨l, hhead, hlτ, hnodup, hsh⟩ := hfree s hsτ
    refine ⟨l ++ [t], ?_, ?_, ?_, IsShelling_snoc hsh hg⟩
    · cases l with
      | nil => exact absurd hsh (by simp [IsShelling])
      | cons a r => rw [List.cons_append]; exact hhead
    · rw [List.toFinset_append, hlτ]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_singleton]
      tauto
    · refine hnodup.append (List.nodup_singleton t) ?_
      rw [List.disjoint_left]
      intro a ha
      simp only [List.mem_singleton]
      rintro rfl
      exact ht (hlτ ▸ List.mem_toFinset.mpr ha)

/-- **base_free** (the base hole of `theorem3_core`): a taut filling of a 2-sphere on
≤ 4 vertices is a free sticker ball — it is a single tetrahedron
(`freelyShellable_singleton`). Reuses the Aleph base lemmas verbatim; only the final
step changes from `isBall_singleton` to `freelyShellable_singleton`. -/
theorem base_free (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M)
    (hv : (vertsOf σ).card ≤ 4) : FreelyShellable M.support σ := by
  have hcard : (vertsOf σ).card = 4 := aleph_base_verts_card_eq_four hσ hv
  have hσeq : σ = (vertsOf σ).powersetCard 3 := aleph_base_sphere_eq_powersetCard3 hσ hcard
  have hsuppInfo := aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
  have hne := aleph_base_support_nonempty hσ hU hMX
  have hsupp : M.support = {vertsOf σ} :=
    aleph_base_support_eq_singleton_of_four_vertices hcard hsuppInfo hne
  rw [hσeq, hsupp]   -- hσeq first: σ occurs only as the 2nd arg, so no over-rewrite of `vertsOf σ`
  exact freelyShellable_singleton hcard

end Taut
