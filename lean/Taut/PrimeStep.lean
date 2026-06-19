import Taut.FlipGeom
import Taut.Theorem3
import Taut.StickerballRuleouts

/-!
# Prime step, case 1 (no flip edge present)

The `¬FlipEdgePresent` half of `theorem3_core`'s `prime_step`, per target `s`
(architect: codex assembly pass). With no degree-3 vertex, pick (via M25b's disjoint
eligible pair) an eligible tet `e ≠ s`, so `s` stays an OLD tet of `removeTet M e`.
When the flipped edge is absent, `removeTet M e` is a strictly smaller taut filling
of the flipped sphere `σe = (σ \ sharedFaces M e) ∪ exposedFaces M e` (its data
assembled from `isSphere2_flipBoundary_of_eligible`, `unitOn_flipBoundary_of_eligible`,
`isTaut_removeTet`, `simplicialChain_removeTet`, `nrm_removeTet_add_one_of_simplicial`).
The induction hypothesis makes it a free sticker ball; snoc `e` back onto the shelling
from `s` (`exists_shelling_insert_of_glueStep_old` + `glueStep_flipBoundary_of_eligible`).
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- Re-insert the removed tet: `insert e (removeTet M e).support = M.support`. -/
lemma support_insert_removeTet_of_mem {M : Chain V} {e : Finset V} (he : e ∈ M.support) :
    insert e (removeTet M e).support = M.support := by
  rw [support_removeTet_of_mem he, Finset.insert_erase he]

/-- An eligible tet's two exposed faces, as an explicit distinct pair. -/
lemma exposedFaces_eq_pair_of_eligible {M : Chain V} {e : Finset V} (he : EligibleTet M e) :
    ∃ f₃ f₄, f₃ ≠ f₄ ∧ exposedFaces M e = {f₃, f₄} :=
  Finset.card_eq_two.mp (exposedFaces_card_of_eligible he)

/-- The boundary obtained by deleting an eligible tet and exposing its other two
faces. In case 1 this is a sphere; in case 2 it is the non-manifold boundary
that splits along the already-present flip edge. -/
noncomputable def flipBoundary
    (σ : Finset (Finset V)) (M : Chain V) (e : Finset V) :
    Finset (Finset V) :=
  (σ \ sharedFaces M e) ∪ exposedFaces M e

/-- Case-2 split package for an already-present flip edge.

The two side chains are explicitly filters of `removeTet M e` by vertex-side
predicates, and the two side boundaries are the matching filters of
`flipBoundary σ M e`. The bridge fields are symmetric so a shelling can start on
whichever side contains the prescribed target tet. -/
structure PrimeFlipEdgeSplitFreePackage
    (σ : Finset (Finset V)) (X M : Chain V)
    (e f₃ f₄ : Finset V) : Type _ where
  A : Finset V
  B : Finset V
  σ₁ : Finset (Finset V)
  σ₂ : Finset (Finset V)
  M₁ : Chain V
  M₂ : Chain V
  Bmid₁₂ : Finset (Finset V)
  Bmid₂₁ : Finset (Finset V)
  cd_eq : A ∩ B = f₃ ∩ f₄
  cd_card : (f₃ ∩ f₄).card = 2
  σ₁_eq : σ₁ = (flipBoundary σ M e).filter (fun f => f ⊆ A)
  σ₂_eq : σ₂ = (flipBoundary σ M e).filter (fun f => f ⊆ B)
  M₁_eq : M₁ = (removeTet M e).filter (fun t => t ⊆ A)
  M₂_eq : M₂ = (removeTet M e).filter (fun t => t ⊆ B)
  sphere₁ : IsSphere2 σ₁
  sphere₂ : IsSphere2 σ₂
  unit₁ : UnitOn (bdry M₁) σ₁
  unit₂ : UnitOn (bdry M₂) σ₂
  closed₁ : bdry (bdry M₁) = 0
  closed₂ : bdry (bdry M₂) = 0
  taut₁ : IsTaut M₁
  taut₂ : IsTaut M₂
  simp₁ : SimplicialChain M₁
  simp₂ : SimplicialChain M₂
  smaller₁ : nrm M₁ < nrm M
  smaller₂ : nrm M₂ < nrm M
  e_not₁ : e ∉ M₁.support
  e_not₂ : e ∉ M₂.support
  side_coverage : ∀ t ∈ (removeTet M e).support, t ⊆ A ∨ t ⊆ B
  side_separation :
    ∀ t ∈ (removeTet M e).support, (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A)
  disjoint_supports : Disjoint M₁.support M₂.support
  support_decomp : M.support = insert e (M₁.support ∪ M₂.support)
  glue₁₂ : GlueStep e σ₁ Bmid₁₂
  glue₂₁ : GlueStep e σ₂ Bmid₂₁
  rel₂_over₁ : RelShelling M₂.support Bmid₁₂ σ
  rel₁_over₂ : RelShelling M₁.support Bmid₂₁ σ

/-! ## Case-2 side decomposition targets

The case-2 proof needs one genuinely topological construction: the already-present
flip edge cuts the post-removal boundary into two spherical sides.  The following
three lemmas isolate that construction from the algebraic bookkeeping used by
`flipEdgePresent_side_data`.
-/

theorem cut_filter_by_vertsOf_eq {σ : Finset (Finset V)} {γ : Finset V} {W : C2 σ}
    (hσ : IsSphere2 σ)
    (hγ3 : γ.card = 3)
    (hγe : γ.powersetCard 2 ⊆ edgesOf σ)
    (hγσ : γ ∉ σ)
    (hW : bd2 σ W = gammaChain σ γ) :
    σ.filter (fun f => f ⊆ vertsOf (insert γ (cutSet σ W))) = cutSet σ W := by
  ext f
  constructor
  · intro hf
    rw [mem_filter] at hf
    rcases hf with ⟨hfσ, hfsub⟩
    by_contra hfc
    have hfcomp : f ∈ cutSet σ (W + fun _ => 1) := by
      rw [cutSet_add_one_eq_sdiff]
      exact mem_sdiff.mpr ⟨hfσ, hfc⟩
    have hsubcomp : f ⊆ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := by
      intro v hv
      exact mem_vertsOf.mpr ⟨f, by simp [hfcomp], hv⟩
    have hsubγ : f ⊆ γ := by
      intro v hv
      have hv1 := hfsub hv
      have hv2 := hsubcomp hv
      have hvinter : v ∈ vertsOf (insert γ (cutSet σ W)) ∩ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := by
        exact mem_inter.mpr ⟨hv1, hv2⟩
      rw [← vertsOf_cut_inter hσ hW]
      exact hvinter
    have hfcard : f.card = 3 := hσ.pure f hfσ
    have hfgamma : f = γ := by
      apply Finset.eq_of_subset_of_card_le hsubγ
      rw [hfcard, hγ3]
    exact hγσ (hfgamma ▸ hfσ)
  · intro hf
    rw [mem_filter]
    constructor
    · exact cutSet_subset hf
    · intro v hv
      exact mem_vertsOf.mpr ⟨f, by simp [hf], hv⟩

theorem flipEdgePresent_cd_card {M : Chain V} {e f₃ f₄ : Finset V}
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄) :
    (f₃ ∩ f₄).card = 2 := by
  have hf3exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    exact mem_insert_self f₃ {f₄}
  have hf4exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    exact mem_insert_of_mem (mem_singleton_self f₄)
  have hf3tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf3exp
  have hf4tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf4exp
  exact tetFaces_pair_inter_card_eq_two he.1 hf3tet hf4tet hf₃₄

theorem flipEdgePresent_exposed_faces_missing {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hU : UnitOn X σ)
    (hMX : bdry M = X)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄) :
    f₃ ∉ σ ∧ f₄ ∉ σ := by
  have hUb : UnitOn (bdry M) σ := by
    rw [hMX]
    exact hU
  have hf₃exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    simp
  have hf₄exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    simp [hf₃₄]
  constructor
  · intro hf₃σ
    have hz : (bdry M) f₃ = 0 := bdry_apply_eq_zero_of_mem_exposedFaces hf₃exp
    have hmem : f₃ ∈ (bdry M).support := by
      rw [hUb.1]
      exact hf₃σ
    exact (Finsupp.mem_support_iff.mp hmem) hz
  · intro hf₄σ
    have hz : (bdry M) f₄ = 0 := bdry_apply_eq_zero_of_mem_exposedFaces hf₄exp
    have hmem : f₄ ∈ (bdry M).support := by
      rw [hUb.1]
      exact hf₄σ
    exact (Finsupp.mem_support_iff.mp hmem) hz

theorem flipEdgePresent_exposed_edges_in_sigma {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hU : UnitOn X σ)
    (hMX : bdry M = X)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    f₃.powersetCard 2 ⊆ edgesOf σ ∧ f₄.powersetCard 2 ⊆ edgesOf σ := by
  classical
  have hUb : UnitOn (bdry M) σ := by
    rw [hMX]
    exact hU
  unfold FlipEdgePresent at hFlip
  have edges_of_first {f g : Finset V} (hfg : f ≠ g)
      (hexpfg : exposedFaces M e = {f, g})
      (hflipfg : f ∩ g ∈ edgesOf σ) :
      f.powersetCard 2 ⊆ edgesOf σ := by
    intro a ha
    rw [Finset.mem_powersetCard] at ha
    obtain ⟨haf, hacard⟩ := ha
    have hfexp : f ∈ exposedFaces M e := by
      rw [hexpfg]
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    have hftet : f ∈ tetFaces e := exposedFaces_subset_tetFaces M e hfexp
    have hcd : (f ∩ g).card = 2 :=
      flipEdgePresent_cd_card (M := M) (e := e) (f₃ := f) (f₄ := g) he hexpfg hfg
    by_cases hag : a ⊆ g
    · have hsub : a ⊆ f ∩ g := Finset.subset_inter haf hag
      have haeq : a = f ∩ g := by
        apply Finset.eq_of_subset_of_card_le hsub
        rw [hcd, hacard]
      rw [haeq]
      exact hflipfg
    · have hae : a ⊆ e := haf.trans (Finset.mem_powersetCard.mp hftet).1
      have hTcard : ((tetFaces e).filter (fun F => a ⊆ F)).card = 2 :=
        tetFaces_edge_filter_card_eq_two he.1 hae hacard
      have hT_eq : (tetFaces e).filter (fun F => a ⊆ F)
          = (sharedFaces M e).filter (fun F => a ⊆ F) ∪
            (exposedFaces M e).filter (fun F => a ⊆ F) := by
        ext F
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hFt, hP⟩
          by_cases hFs : F ∈ sharedFaces M e
          · exact Or.inl ⟨hFs, hP⟩
          · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hFt, hFs⟩, hP⟩
        · rintro (⟨hFs, hP⟩ | ⟨hFe, hP⟩)
          · exact ⟨sharedFaces_subset_tetFaces M e hFs, hP⟩
          · exact ⟨exposedFaces_subset_tetFaces M e hFe, hP⟩
      have hdisj : Disjoint ((sharedFaces M e).filter (fun F => a ⊆ F))
          ((exposedFaces M e).filter (fun F => a ⊆ F)) := by
        rw [Finset.disjoint_left]
        intro F hFs hFe
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hFe).1).2 (Finset.mem_filter.mp hFs).1
      have hExpFilter_eq : (exposedFaces M e).filter (fun F => a ⊆ F) = {f} := by
        ext F
        simp only [Finset.mem_filter, hexpfg, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hF, haF⟩
          rcases hF with hF | hF
          · exact hF
          · exfalso
            rw [hF] at haF
            exact hag haF
        · intro hF
          constructor
          · exact Or.inl hF
          · rw [hF]
            exact haf
      have hExpCard : ((exposedFaces M e).filter (fun F => a ⊆ F)).card = 1 := by
        rw [hExpFilter_eq, Finset.card_singleton]
      have hsum : ((sharedFaces M e).filter (fun F => a ⊆ F)).card +
            ((exposedFaces M e).filter (fun F => a ⊆ F)).card = 2 := by
        rw [← Finset.card_union_of_disjoint hdisj, ← hT_eq, hTcard]
      have hShPos : 0 < ((sharedFaces M e).filter (fun F => a ⊆ F)).card := by
        omega
      obtain ⟨F, hF⟩ := Finset.card_pos.mp hShPos
      obtain ⟨hFsh, haF⟩ := Finset.mem_filter.mp hF
      have hFσ : F ∈ σ := by
        have hshared_eq := sharedFaces_eq_tetFaces_inter_sigma (M := M) (σ := σ) (e := e) hUb
        rw [hshared_eq] at hFsh
        exact (Finset.mem_inter.mp hFsh).2
      exact mem_edgesOf.mpr ⟨F, hFσ, haF, hacard⟩
  constructor
  · exact edges_of_first hf₃₄ hexp hFlip
  · have hexp_swap : exposedFaces M e = {f₄, f₃} := by
      rw [hexp, Finset.pair_comm]
    have hFlip_swap : f₄ ∩ f₃ ∈ edgesOf σ := by
      rw [Finset.inter_comm]
      exact hFlip
    exact edges_of_first (Ne.symm hf₃₄) hexp_swap hFlip_swap

theorem flipEdgePresent_removeTet_support_partition {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    (hAB : A ∩ B = f₃ ∩ f₄)
    (hcd : (f₃ ∩ f₄).card = 2)
    (hfaceCover : ∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B) :
    (∀ t ∈ (removeTet M e).support, t ⊆ A ∨ t ⊆ B) ∧
      (∀ t ∈ (removeTet M e).support,
        (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A)) := by
  classical
  let M' : Chain V := removeTet M e
  let τ : Finset (Finset V) := flipBoundary σ M e
  have hUb : UnitOn (bdry M) σ := by
    rw [hMX]
    exact hU
  have hUτ : UnitOn (bdry M') τ := by
    dsimp [M', τ, flipBoundary]
    exact unitOn_flipBoundary_of_eligible hUb hS he
  have hτ_faces : ∀ f ∈ τ, f.card = 3 := by
    intro f hf
    dsimp [τ, flipBoundary] at hf
    rw [Finset.mem_union] at hf
    rcases hf with hf_old | hf_exp
    · exact hσ.pure f (Finset.mem_sdiff.mp hf_old).1
    · exact (Finset.mem_powersetCard.mp (exposedFaces_subset_tetFaces M e hf_exp)).2
  have hbdsupp : ∀ s ∈ (bdry M').support, s.card = 3 := by
    intro s hs
    have hsτ : s ∈ τ := by
      rwa [hUτ.1] at hs
    exact hτ_faces s hsτ
  have hbd_supp : ∀ s ∈ (bdry M').support, s.card = 3 ∧ (s ⊆ A ∨ s ⊆ B) := by
    intro s hs
    have hsτ : s ∈ τ := by
      rwa [hUτ.1] at hs
    exact ⟨hτ_faces s hsτ, hfaceCover s (by simpa [τ] using hsτ)⟩
  have hAB2 : (A ∩ B).card = 2 := by
    rw [hAB]
    exact hcd
  let X_A : Chain V := (bdry M').filter (fun f => f ⊆ A)
  let X_B : Chain V := (bdry M').filter (fun f => ¬ f ⊆ A)
  have hXAc : bdry X_A = 0 := by
    dsimp [X_A]
    exact bdry_filter_subset_eq_zero_of_inter_card_two (X := bdry M') (A := A) (B := B)
      (bdry_bdry M') hbd_supp hAB2
  have hsumXA : X_A + X_B = bdry M' := by
    dsimp [X_A, X_B]
    exact Finsupp.filter_pos_add_filter_neg (bdry M') (fun f => f ⊆ A)
  have hXBc : bdry X_B = 0 := by
    have h := congrArg bdry hsumXA
    rw [map_add, hXAc, bdry_bdry, zero_add] at h
    exact h
  have hXA_supp : ∀ s ∈ X_A.support, s ⊆ A ∧ s.card = 2 + 1 := by
    intro s hs
    have hs' : s ∈ (bdry M').support ∧ s ⊆ A := by
      dsimp [X_A] at hs
      exact Finset.mem_filter.mp hs
    exact ⟨hs'.2, by simpa using hbdsupp s hs'.1⟩
  have hXB_supp : ∀ s ∈ X_B.support, s ⊆ B ∧ s.card = 2 + 1 := by
    intro s hs
    have hs' : s ∈ (bdry M').support ∧ ¬ s ⊆ A := by
      dsimp [X_B] at hs
      exact Finset.mem_filter.mp hs
    have hc := hbd_supp s hs'.1
    exact ⟨hc.2.resolve_left hs'.2, by simpa using hc.1⟩
  have hM't : IsTaut M' := isTaut_removeTet hT
  have hM1 : bdry M' = X_A + X_B := hsumXA.symm
  obtain ⟨p, q, hpq, hpqset⟩ := Finset.card_eq_two.mp hAB2
  have hp : p ∈ A ∩ B := by
    rw [hpqset]
    simp [hpq]
  have hq : q ∈ A ∩ B := by
    rw [hpqset]
    simp [hpq]
  have hC : (A ∩ B).card ≤ 2 + 1 := by
    rw [hAB2]
    norm_num
  have hpureM : ∀ s ∈ M'.support, s.card = 2 + 2 := by
    intro s hs
    have h := hM't.dim_pure hbdsupp s hs
    simpa using h
  have hdim2 : ∀ s ∈ M'.support, 2 ≤ s.card := by
    intro s hs
    rw [hpureM s hs]
    norm_num
  have hsuppAB : ∀ t ∈ M'.support, t ⊆ A ∪ B := by
    intro t ht
    refine (supp_subset_vert ht).trans ((hM't.vert_subset hdim2).trans ?_)
    rw [hM1]
    exact (vert_add_subset X_A X_B).trans (Finset.union_subset_union
      (vert_subset_of_supp fun s hs => (hXA_supp s hs).1)
      (vert_subset_of_supp fun s hs => (hXB_supp s hs).1))
  have hcoverM : ∀ t ∈ M'.support, t ⊆ A ∨ t ⊆ B := by
    intro t ht
    rcases hybrid_structure (A := A) (B := B) (n := 2) (by norm_num) hp hq hpq hC
        hXA_supp hXB_supp hXAc hXBc hM1 hM't hpureM hsuppAB ht with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨y₀, hy⟩ := Finset.card_eq_one.mp h1
      exact (no_extreme_hybrid (A := A) (B := B) (n := 2) (by norm_num) hp hq hpq hC
        hXA_supp hXB_supp hXAc hXBc hM1 hM't hpureM hsuppAB ht hy h2).elim
    · obtain ⟨x₀, hx⟩ := Finset.card_eq_one.mp h1
      have hM1' : bdry M' = X_B + X_A := by
        rw [hM1, add_comm]
      have hsuppBA : ∀ t' ∈ M'.support, t' ⊆ B ∪ A := by
        intro t' ht'
        rw [Finset.union_comm]
        exact hsuppAB t' ht'
      exact (no_extreme_hybrid (A := B) (B := A) (n := 2) (by norm_num)
        (Finset.inter_comm A B ▸ hq) (Finset.inter_comm A B ▸ hp) hpq.symm
        (Finset.inter_comm A B ▸ hC) hXB_supp hXA_supp hXBc hXAc hM1' hM't
        hpureM hsuppBA ht hx (Finset.inter_comm A B ▸ h2)).elim
  refine ⟨?_, ?_⟩
  · intro t ht
    exact hcoverM t ht
  · intro t ht
    have htcard : t.card = 4 := by
      have h := hpureM t ht
      simpa using h
    have hnotBoth : ¬ (t ⊆ A ∧ t ⊆ B) := by
      rintro ⟨hA, hB⟩
      have hsub : t ⊆ A ∩ B := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨hA hx, hB hx⟩
      have hle : t.card ≤ (A ∩ B).card := Finset.card_le_card hsub
      rw [hAB2, htcard] at hle
      norm_num at hle
    rcases hcoverM t ht with hA | hB
    · exact Or.inl ⟨hA, fun hB => hnotBoth ⟨hA, hB⟩⟩
    · exact Or.inr ⟨hB, fun hA => hnotBoth ⟨hA, hB⟩⟩

theorem flipEdgePresent_sharedFaces_indicator_boundary {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hMX : bdry M = X)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    bd2 σ (fun F : σ => if (F : Finset V) ∈ sharedFaces M e then (1 : ZMod 2) else 0)
      = gammaChain σ f₃ + gammaChain σ f₄ := by
  classical
  have hUb : UnitOn (bdry M) σ := by
    rw [hMX]
    exact hU
  funext a
  rw [bd2_apply]
  simp only [Pi.add_apply, gammaChain]
  let P : Finset V → Prop := fun F => (a : Finset V) ⊆ F
  have hshared_sub_sigma : sharedFaces M e ⊆ σ := by
    intro F hF
    rw [sharedFaces_eq_tetFaces_inter_sigma (M := M) (σ := σ) (e := e) hUb] at hF
    exact (Finset.mem_inter.mp hF).2
  have hleft : (∑ f : σ, (if ((a : Finset V) ⊆ (f : Finset V)) then (1 : ZMod 2) else 0) * if (f : Finset V) ∈ sharedFaces M e then (1 : ZMod 2) else 0)
      = (((sharedFaces M e).filter P).card : ZMod 2) := by
    simp only [P]
    rw [Finset.sum_coe_sort σ (fun F => (if ((a : Finset V) ⊆ F) then (1 : ZMod 2) else 0) * if F ∈ sharedFaces M e then (1 : ZMod 2) else 0)]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    rw [Finset.sum_boole]
    have hfin : ({x ∈ σ.filter (fun F => (a : Finset V) ⊆ F) | x ∈ sharedFaces M e}) = (sharedFaces M e).filter (fun F => (a : Finset V) ⊆ F) := by
      ext F
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hFσ, hPF⟩, hFsh⟩
        exact ⟨hFsh, hPF⟩
      · rintro ⟨hFsh, hPF⟩
        exact ⟨⟨hshared_sub_sigma hFsh, hPF⟩, hFsh⟩
    rw [hfin]
  have hright : (if ((a : Finset V) ⊆ f₃) then (1 : ZMod 2) else 0) + (if ((a : Finset V) ⊆ f₄) then (1 : ZMod 2) else 0)
      = (((exposedFaces M e).filter P).card : ZMod 2) := by
    rw [hexp]
    simp only [P]
    by_cases h3 : (a : Finset V) ⊆ f₃
    · by_cases h4 : (a : Finset V) ⊆ f₄
      · have hfilter : ({f₃, f₄} : Finset (Finset V)).filter (fun F => (a : Finset V) ⊆ F) = {f₃, f₄} := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro h
            exact h.1
          · intro h
            rcases h with rfl | rfl
            · exact ⟨Or.inl rfl, h3⟩
            · exact ⟨Or.inr rfl, h4⟩
        rw [if_pos h3, if_pos h4, hfilter, Finset.card_pair hf₃₄]
        decide
      · have hfilter : ({f₃, f₄} : Finset (Finset V)).filter (fun F => (a : Finset V) ⊆ F) = {f₃} := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hmem, hP⟩
            rcases hmem with rfl | rfl
            · exact rfl
            · exact False.elim (h4 hP)
          · intro hF
            rw [hF]
            exact ⟨Or.inl rfl, h3⟩
        rw [if_pos h3, if_neg h4, hfilter, Finset.card_singleton]
        decide
    · by_cases h4 : (a : Finset V) ⊆ f₄
      · have hfilter : ({f₃, f₄} : Finset (Finset V)).filter (fun F => (a : Finset V) ⊆ F) = {f₄} := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hmem, hP⟩
            rcases hmem with rfl | rfl
            · exact False.elim (h3 hP)
            · exact rfl
          · intro hF
            rw [hF]
            exact ⟨Or.inr rfl, h4⟩
        rw [if_neg h3, if_pos h4, hfilter, Finset.card_singleton]
        decide
      · have hfilter : ({f₃, f₄} : Finset (Finset V)).filter (fun F => (a : Finset V) ⊆ F) = ∅ := by
          ext F
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
          constructor
          · rintro ⟨hmem, hP⟩
            rcases hmem with rfl | rfl
            · exact False.elim (h3 hP)
            · exact False.elim (h4 hP)
          · intro hF
            cases hF
        rw [if_neg h3, if_neg h4, hfilter, Finset.card_empty]
        decide
  rw [hleft, hright]
  have hT_eq : (tetFaces e).filter P = ((sharedFaces M e).filter P) ∪ ((exposedFaces M e).filter P) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hFt, hPF⟩
      by_cases hFs : F ∈ sharedFaces M e
      · exact Or.inl ⟨hFs, hPF⟩
      · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hFt, hFs⟩, hPF⟩
    · rintro (⟨hFs, hPF⟩ | ⟨hFe, hPF⟩)
      · exact ⟨sharedFaces_subset_tetFaces M e hFs, hPF⟩
      · exact ⟨exposedFaces_subset_tetFaces M e hFe, hPF⟩
  have hdisj : Disjoint ((sharedFaces M e).filter P) ((exposedFaces M e).filter P) := by
    rw [Finset.disjoint_left]
    intro F hFs hFe
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hFe).1).2 (Finset.mem_filter.mp hFs).1
  by_cases hae : (a : Finset V) ⊆ e
  · have hTcard : ((tetFaces e).filter P).card = 2 := by
      exact tetFaces_edge_filter_card_eq_two (e := e) (a := (a : Finset V)) he.1 hae (card_of_mem_edgesOf a.2)
    have hsum : ((sharedFaces M e).filter P).card + ((exposedFaces M e).filter P).card = 2 := by
      rw [← Finset.card_union_of_disjoint hdisj, ← hT_eq, hTcard]
    have hmod : (((sharedFaces M e).filter P).card : ZMod 2) + (((exposedFaces M e).filter P).card : ZMod 2) = 0 := by
      rw [← Nat.cast_add, hsum]
      decide
    exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ hmod
  · have hSempty : ((sharedFaces M e).filter P).card = 0 := by
      rw [Finset.card_eq_zero]
      ext F
      simp only [Finset.mem_filter, Finset.notMem_empty]
      constructor
      · rintro ⟨hFs, hPF⟩
        have hFt : F ∈ tetFaces e := sharedFaces_subset_tetFaces M e hFs
        have hFe : F ⊆ e := (Finset.mem_powersetCard.mp hFt).1
        exact False.elim (hae (hPF.trans hFe))
      · intro hF
        cases hF
    have hEempty : ((exposedFaces M e).filter P).card = 0 := by
      rw [Finset.card_eq_zero]
      ext F
      simp only [Finset.mem_filter, Finset.notMem_empty]
      constructor
      · rintro ⟨hFe, hPF⟩
        have hFt : F ∈ tetFaces e := exposedFaces_subset_tetFaces M e hFe
        have hFe' : F ⊆ e := (Finset.mem_powersetCard.mp hFt).1
        exact False.elim (hae (hPF.trans hFe'))
      · intro hF
        cases hF
    rw [hSempty, hEempty]

theorem flipEdgePresent_cut_values_add_eq_one_of_not_shared {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hMX : bdry M = X)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    {W₃ W₄ : C2 σ}
    (hW₃ : bd2 σ W₃ = gammaChain σ f₃)
    (hW₄ : bd2 σ W₄ = gammaChain σ f₄)
    (hD₃ : Disjoint (sharedFaces M e) (cutSet σ W₃))
    (hD₄ : Disjoint (sharedFaces M e) (cutSet σ W₄))
    {g : Finset V} (hgσ : g ∈ σ) (hgnot : g ∉ sharedFaces M e) :
    W₃ ⟨g, hgσ⟩ + W₄ ⟨g, hgσ⟩ = 1 := by
  classical
  let S : C2 σ := fun F : σ => if (F : Finset V) ∈ sharedFaces M e then (1 : ZMod 2) else 0
  have hSbd : bd2 σ S = gammaChain σ f₃ + gammaChain σ f₄ := by
    simpa only [S] using
      flipEdgePresent_sharedFaces_indicator_boundary hσ hU hMX he hexp hf₃₄ hFlip
  have hcycle : bd2 σ (W₃ + W₄ + S) = 0 := by
    rw [map_add, map_add, hW₃, hW₄, hSbd]
    funext E
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero (gammaChain σ f₃ E + gammaChain σ f₄ E)
  have hUb : UnitOn (bdry M) σ := by
    rw [hMX]
    exact hU
  obtain ⟨s, hsShared⟩ : (sharedFaces M e).Nonempty := by
    apply Finset.card_pos.mp
    rw [he.2.2.1]
    norm_num
  have hsσ : s ∈ σ := by
    have htmp : s ∈ tetFaces e ∩ σ := by
      simpa only [sharedFaces_eq_tetFaces_inter_sigma hUb] using hsShared
    exact (Finset.mem_inter.mp htmp).2
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hW₃s0 : W₃ ⟨s, hsσ⟩ = 0 := by
    rcases hz (W₃ ⟨s, hsσ⟩) with h0 | h1
    · exact h0
    · exfalso
      exact Finset.disjoint_left.mp hD₃ hsShared (mem_cutSet.mpr ⟨hsσ, h1⟩)
  have hW₄s0 : W₄ ⟨s, hsσ⟩ = 0 := by
    rcases hz (W₄ ⟨s, hsσ⟩) with h0 | h1
    · exact h0
    · exfalso
      exact Finset.disjoint_left.mp hD₄ hsShared (mem_cutSet.mpr ⟨hsσ, h1⟩)
  have hSs : S ⟨s, hsσ⟩ = 1 := by
    dsimp [S]
    rw [if_pos hsShared]
  have hSg : S ⟨g, hgσ⟩ = 0 := by
    dsimp [S]
    rw [if_neg hgnot]
  have hZs : (W₃ + W₄ + S) ⟨s, hsσ⟩ = 1 := by
    simp only [Pi.add_apply]
    rw [hW₃s0, hW₄s0, hSs]
    norm_num
  have hZg : (W₃ + W₄ + S) ⟨g, hgσ⟩ = W₃ ⟨g, hgσ⟩ + W₄ ⟨g, hgσ⟩ := by
    simp only [Pi.add_apply]
    rw [hSg, add_zero]
  have hconst := bd2_ker_constant hσ.toClosedSurface hcycle ⟨s, hsσ⟩ ⟨g, hgσ⟩
  rw [hZs, hZg] at hconst
  exact hconst.symm

theorem flipBoundary_coverage_of_compatible_cut_chains {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V} {W₃ W₄ : C2 σ}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    (hW₃ : bd2 σ W₃ = gammaChain σ f₃)
    (hW₄ : bd2 σ W₄ = gammaChain σ f₄)
    (hD₃ : Disjoint (sharedFaces M e) (cutSet σ W₃))
    (hD₄ : Disjoint (sharedFaces M e) (cutSet σ W₄))
    (hAB : vertsOf (insert f₃ (cutSet σ W₃)) ∩ vertsOf (insert f₄ (cutSet σ W₄)) = f₃ ∩ f₄) :
    ∀ f ∈ flipBoundary σ M e,
      f ⊆ vertsOf (insert f₃ (cutSet σ W₃)) ∨ f ⊆ vertsOf (insert f₄ (cutSet σ W₄)) := by
  intro f hf
  classical
  unfold flipBoundary at hf
  rcases Finset.mem_union.mp hf with hOld | hExp
  · rcases Finset.mem_sdiff.mp hOld with ⟨hfσ, hfnot⟩
    have hsum := flipEdgePresent_cut_values_add_eq_one_of_not_shared
      hσ hU hMX he hexp hf₃₄ hFlip hW₃ hW₄ hD₃ hD₄ hfσ hfnot
    have hcases : W₃ ⟨f, hfσ⟩ = 1 ∨ W₄ ⟨f, hfσ⟩ = 1 := by
      have hz : ∀ x y : ZMod 2, x + y = 1 → x = 1 ∨ y = 1 := by decide
      exact hz _ _ hsum
    rcases hcases with hW3 | hW4
    · left
      intro x hx
      exact mem_vertsOf.mpr ⟨f, Finset.mem_insert_of_mem (mem_cutSet.mpr ⟨hfσ, hW3⟩), hx⟩
    · right
      intro x hx
      exact mem_vertsOf.mpr ⟨f, Finset.mem_insert_of_mem (mem_cutSet.mpr ⟨hfσ, hW4⟩), hx⟩
  · rw [hexp] at hExp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hExp
    rcases hExp with hff₃ | hff₄
    · left
      rw [hff₃]
      intro x hx
      exact mem_vertsOf.mpr ⟨f₃, Finset.mem_insert_self f₃ (cutSet σ W₃), hx⟩
    · right
      rw [hff₄]
      intro x hx
      exact mem_vertsOf.mpr ⟨f₄, Finset.mem_insert_self f₄ (cutSet σ W₄), hx⟩

theorem flipEdgePresent_exists_compatible_cut_chains {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    ∃ W₃ W₄ : C2 σ,
      bd2 σ W₃ = gammaChain σ f₃ ∧
      bd2 σ W₄ = gammaChain σ f₄ ∧
      vertsOf (insert f₃ (cutSet σ W₃)) ∩ vertsOf (insert f₄ (cutSet σ W₄)) = f₃ ∩ f₄ ∧
      Disjoint (sharedFaces M e) (cutSet σ W₃) ∧
      Disjoint (sharedFaces M e) (cutSet σ W₄) := by
  classical
  have hUb : UnitOn (bdry M) σ := by
    rw [hMX]
    exact hU
  have hf₃exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, true_or]
  have hf₄exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, or_true]
  have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
  have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
  have hf₃card : f₃.card = 3 := by
    exact (Finset.mem_powersetCard.mp hf₃tet).2
  have hf₄card : f₄.card = 3 := by
    exact (Finset.mem_powersetCard.mp hf₄tet).2
  have hedge := flipEdgePresent_exposed_edges_in_sigma hU hMX he hexp hf₃₄ hFlip
  have hshared_sigma : sharedFaces M e ⊆ σ := by
    intro s hs
    have hs' := hs
    rw [sharedFaces_eq_tetFaces_inter_sigma (M := M) (σ := σ) (e := e) hUb] at hs'
    exact (Finset.mem_inter.mp hs').2
  have orient : ∀ {γ : Finset V}, γ ∈ exposedFaces M e →
      ∀ U : C2 σ, bd2 σ U = gammaChain σ γ →
        ∃ W : C2 σ, bd2 σ W = gammaChain σ γ ∧
          Disjoint (sharedFaces M e) (cutSet σ W) := by
    intro γ hγexp U hUbd
    have hγtet : γ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hγexp
    obtain ⟨a, hae, hγeq⟩ := exists_erase_eq_of_mem_tetFaces he.1 hγtet
    have hγ_nshared : γ ∉ sharedFaces M e := (Finset.mem_sdiff.mp hγexp).2
    have ha_not_γ : a ∉ γ := by
      rw [hγeq]
      exact Finset.notMem_erase a e
    have face_eq_erase : ∀ {F : Finset V}, F ∈ tetFaces e → a ∈ e → a ∉ F → F = e.erase a := by
      intro F hFt hae' haF
      obtain ⟨hsubF, hcardF⟩ := Finset.mem_powersetCard.mp hFt
      have hsubErase : F ⊆ e.erase a := by
        intro y hy
        exact Finset.mem_erase.mpr ⟨by intro hya; subst y; exact haF hy, hsubF hy⟩
      have hcardErase : (e.erase a).card = 3 := by
        rw [Finset.card_erase_of_mem hae', he.1]
      exact Finset.eq_of_subset_of_card_le hsubErase (by rw [hcardF, hcardErase])
    have hcontains_a : ∀ s ∈ sharedFaces M e, a ∈ s := by
      intro s hs
      by_contra has
      have hs_eq : s = e.erase a := face_eq_erase (sharedFaces_subset_tetFaces M e hs) hae has
      have hsg : s = γ := hs_eq.trans hγeq.symm
      exact hγ_nshared (hsg ▸ hs)
    have hconst : ∀ s (hs : s ∈ sharedFaces M e) t (ht : t ∈ sharedFaces M e),
        U ⟨s, hshared_sigma hs⟩ = U ⟨t, hshared_sigma ht⟩ := by
      intro s hs t ht
      exact W_const_at hσ hUbd ha_not_γ (hcontains_a s hs) (hcontains_a t ht)
    obtain ⟨s0, hs0⟩ : (sharedFaces M e).Nonempty := by
      exact Finset.card_pos.mp (by rw [he.2.2.1]; omega)
    have hs0σ : s0 ∈ σ := hshared_sigma hs0
    by_cases hzero : U ⟨s0, hs0σ⟩ = 0
    · refine ⟨U, hUbd, ?_⟩
      rw [Finset.disjoint_left]
      intro s hss hsc
      obtain ⟨hsσ', hUs1⟩ := mem_cutSet.mp hsc
      have hsubtype : (⟨s, hsσ'⟩ : σ) = ⟨s, hshared_sigma hss⟩ := Subtype.ext rfl
      rw [hsubtype] at hUs1
      have hUs0 := hconst s hss s0 hs0
      rw [hUs0, hzero] at hUs1
      exact one_ne_zero hUs1.symm
    · refine ⟨U + fun _ => 1, bd2_W_add_one hσ hUbd, ?_⟩
      rw [Finset.disjoint_left]
      intro s hss hsc
      have hsσ : s ∈ σ := hshared_sigma hss
      have hsc0 : U ⟨s, hsσ⟩ = 0 := (mem_cutSet_add_one hsσ).mp hsc
      have hUs0 := hconst s hss s0 hs0
      have hUs0one : U ⟨s0, hs0σ⟩ = 1 := by
        rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (U ⟨s0, hs0σ⟩) with h0 | h1
        · exact False.elim (hzero h0)
        · exact h1
      have hUs : U ⟨s, hsσ⟩ = 1 := hUs0.trans hUs0one
      rw [hUs] at hsc0
      exact one_ne_zero hsc0
  rcases exists_cut hσ hf₃card hedge.1 with ⟨U₃, hU₃⟩
  rcases exists_cut hσ hf₄card hedge.2 with ⟨U₄, hU₄⟩
  rcases orient hf₃exp U₃ hU₃ with ⟨W₃, hW₃, hD₃⟩
  rcases orient hf₄exp U₄ hU₄ with ⟨W₄, hW₄, hD₄⟩
  have hshared_verts : vertsOf (sharedFaces M e) = e := by
    have hsub : sharedFaces M e ⊆ tetFaces e := sharedFaces_subset_tetFaces M e
    have hcard : (sharedFaces M e).card = 2 := he.2.2.1
    ext x
    rw [mem_vertsOf]
    constructor
    · rintro ⟨F, hFA, hxF⟩
      exact (Finset.mem_powersetCard.mp (hsub hFA)).1 hxF
    · intro hxe
      obtain ⟨F₁, F₂, hne, hpair⟩ := Finset.card_eq_two.mp hcard
      have hF₁A : F₁ ∈ sharedFaces M e := by
        rw [hpair]
        exact Finset.mem_insert_self F₁ {F₂}
      have hF₂A : F₂ ∈ sharedFaces M e := by
        rw [hpair]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self F₂)
      by_contra hxnot
      have hxF₁ : x ∉ F₁ := by
        intro hx
        exact hxnot ⟨F₁, hF₁A, hx⟩
      have hxF₂ : x ∉ F₂ := by
        intro hx
        exact hxnot ⟨F₂, hF₂A, hx⟩
      have face_eq_erase : ∀ {F : Finset V}, F ∈ tetFaces e → x ∉ F → F = e.erase x := by
        intro F hFt hxnotF
        obtain ⟨hsubF, hcardF⟩ := Finset.mem_powersetCard.mp hFt
        have hsubErase : F ⊆ e.erase x := by
          intro y hy
          exact Finset.mem_erase.mpr ⟨by intro hyx; subst hyx; exact hxnotF hy, hsubF hy⟩
        have hcardErase : (e.erase x).card = 3 := by
          rw [Finset.card_erase_of_mem hxe, he.1]
        exact Finset.eq_of_subset_of_card_le hsubErase (by rw [hcardF, hcardErase])
      have hF₁eq : F₁ = e.erase x := face_eq_erase (hsub hF₁A) hxF₁
      have hF₂eq : F₂ = e.erase x := face_eq_erase (hsub hF₂A) hxF₂
      exact hne (hF₁eq.trans hF₂eq.symm)
  have exists_shared_of_mem_e : ∀ {v : V}, v ∈ e → ∃ s, s ∈ sharedFaces M e ∧ v ∈ s := by
    intro v hv
    have hv' : v ∈ vertsOf (sharedFaces M e) := by
      simpa only [hshared_verts] using hv
    exact mem_vertsOf.mp hv'
  have W₃_zero_shared : ∀ {s : Finset V} (hs : s ∈ sharedFaces M e),
      W₃ ⟨s, hshared_sigma hs⟩ = 0 := by
    intro s hs
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (W₃ ⟨s, hshared_sigma hs⟩) with h0 | h1
    · exact h0
    · exfalso
      exact Finset.disjoint_left.mp hD₃ hs (mem_cutSet.mpr ⟨hshared_sigma hs, h1⟩)
  have W₄_zero_shared : ∀ {s : Finset V} (hs : s ∈ sharedFaces M e),
      W₄ ⟨s, hshared_sigma hs⟩ = 0 := by
    intro s hs
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (W₄ ⟨s, hshared_sigma hs⟩) with h0 | h1
    · exact h0
    · exfalso
      exact Finset.disjoint_left.mp hD₄ hs (mem_cutSet.mpr ⟨hshared_sigma hs, h1⟩)
  refine ⟨W₃, W₄, hW₃, hW₄, ?_, hD₃, hD₄⟩
  apply Finset.Subset.antisymm
  · intro v hv
    rw [Finset.mem_inter] at hv
    obtain ⟨F₃, hF₃, hvF₃⟩ := mem_vertsOf.mp hv.1
    obtain ⟨F₄, hF₄, hvF₄⟩ := mem_vertsOf.mp hv.2
    rw [Finset.mem_inter]
    rcases Finset.mem_insert.mp hF₃ with rfl | hF₃cut
    · by_cases hvf₄ : v ∈ f₄
      · exact ⟨hvF₃, hvf₄⟩
      · exfalso
        obtain ⟨hF₄σ, hW₄F₄⟩ := mem_cutSet.mp ((Finset.mem_insert.mp hF₄).resolve_left (fun h => hvf₄ (h ▸ hvF₄)))
        have hve : v ∈ e := (Finset.mem_powersetCard.mp hf₃tet).1 hvF₃
        obtain ⟨s, hs, hvs⟩ := exists_shared_of_mem_e hve
        have hkey : W₄ ⟨F₄, hF₄σ⟩ = W₄ ⟨s, hshared_sigma hs⟩ :=
          W_const_at hσ hW₄ hvf₄ hvF₄ hvs
        rw [hW₄F₄, W₄_zero_shared hs] at hkey
        exact one_ne_zero hkey
    · obtain ⟨hF₃σ, hW₃F₃⟩ := mem_cutSet.mp hF₃cut
      rcases Finset.mem_insert.mp hF₄ with rfl | hF₄cut
      · by_cases hvf₃ : v ∈ f₃
        · exact ⟨hvf₃, hvF₄⟩
        · exfalso
          have hve : v ∈ e := (Finset.mem_powersetCard.mp hf₄tet).1 hvF₄
          obtain ⟨s, hs, hvs⟩ := exists_shared_of_mem_e hve
          have hkey : W₃ ⟨F₃, hF₃σ⟩ = W₃ ⟨s, hshared_sigma hs⟩ :=
            W_const_at hσ hW₃ hvf₃ hvF₃ hvs
          rw [hW₃F₃, W₃_zero_shared hs] at hkey
          exact one_ne_zero hkey
      · obtain ⟨hF₄σ, hW₄F₄⟩ := mem_cutSet.mp hF₄cut
        by_cases hvf₃ : v ∈ f₃
        · by_cases hvf₄ : v ∈ f₄
          · exact ⟨hvf₃, hvf₄⟩
          · exfalso
            have hve : v ∈ e := (Finset.mem_powersetCard.mp hf₃tet).1 hvf₃
            obtain ⟨s, hs, hvs⟩ := exists_shared_of_mem_e hve
            have hkey : W₄ ⟨F₄, hF₄σ⟩ = W₄ ⟨s, hshared_sigma hs⟩ :=
              W_const_at hσ hW₄ hvf₄ hvF₄ hvs
            rw [hW₄F₄, W₄_zero_shared hs] at hkey
            exact one_ne_zero hkey
        · by_cases hvf₄ : v ∈ f₄
          · exfalso
            have hve : v ∈ e := (Finset.mem_powersetCard.mp hf₄tet).1 hvf₄
            obtain ⟨s, hs, hvs⟩ := exists_shared_of_mem_e hve
            have hkey : W₃ ⟨F₃, hF₃σ⟩ = W₃ ⟨s, hshared_sigma hs⟩ :=
              W_const_at hσ hW₃ hvf₃ hvF₃ hvs
            rw [hW₃F₃, W₃_zero_shared hs] at hkey
            exact one_ne_zero hkey
          · exfalso
            have hF₃not : F₃ ∉ sharedFaces M e := by
              intro hs
              exact Finset.disjoint_left.mp hD₃ hs hF₃cut
            have hcomp := flipEdgePresent_cut_values_add_eq_one_of_not_shared
              hσ hU hMX he hexp hf₃₄ hFlip hW₃ hW₄ hD₃ hD₄ hF₃σ hF₃not
            have hkey₄ : W₄ ⟨F₃, hF₃σ⟩ = W₄ ⟨F₄, hF₄σ⟩ :=
              W_const_at hσ hW₄ hvf₄ hvF₃ hvF₄
            rw [hW₃F₃, hkey₄, hW₄F₄] at hcomp
            exact (by decide : ¬ ((1 : ZMod 2) + 1 = 1)) hcomp
  · intro v hv
    rw [Finset.mem_inter] at hv ⊢
    exact ⟨mem_vertsOf.mpr ⟨f₃, Finset.mem_insert_self _ _, hv.1⟩,
      mem_vertsOf.mpr ⟨f₄, Finset.mem_insert_self _ _, hv.2⟩⟩

theorem flipEdgePresent_compatible_triangle_cuts {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    ∃ A B : Finset V, ∃ W₃ W₄ : C2 σ,
      bd2 σ W₃ = gammaChain σ f₃ ∧
      bd2 σ W₄ = gammaChain σ f₄ ∧
      A ∩ B = f₃ ∩ f₄ ∧
      (∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B) ∧
      (flipBoundary σ M e).filter (fun f => f ⊆ A) = insert f₃ (cutSet σ W₃) ∧
      (flipBoundary σ M e).filter (fun f => f ⊆ B) = insert f₄ (cutSet σ W₄) := by
  classical
  have hcd : (f₃ ∩ f₄).card = 2 :=
    flipEdgePresent_cd_card (M := M) (e := e) (f₃ := f₃) (f₄ := f₄) he hexp hf₃₄
  have hf₃exp : f₃ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, true_or]
  have hf₄exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]
    simp only [mem_insert, mem_singleton, or_true]
  have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
  have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
  have hf₃card : f₃.card = 3 := (Finset.mem_powersetCard.mp hf₃tet).2
  have hf₄card : f₄.card = 3 := (Finset.mem_powersetCard.mp hf₄tet).2
  have hmissing : f₃ ∉ σ ∧ f₄ ∉ σ :=
    flipEdgePresent_exposed_faces_missing (σ := σ) (X := X) (M := M) (e := e) (f₃ := f₃) (f₄ := f₄) hU hMX he hexp hf₃₄
  have hedges : f₃.powersetCard 2 ⊆ edgesOf σ ∧ f₄.powersetCard 2 ⊆ edgesOf σ :=
    flipEdgePresent_exposed_edges_in_sigma (σ := σ) (X := X) (M := M) (e := e) (f₃ := f₃) (f₄ := f₄) hU hMX he hexp hf₃₄ hFlip
  obtain ⟨W₃, W₄, hW₃, hW₄, hABraw, hdisj₃, hdisj₄⟩ :=
    flipEdgePresent_exists_compatible_cut_chains (σ := σ) (X := X) (M := M) (e := e)
      (f₃ := f₃) (f₄ := f₄) hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
  let A : Finset V := vertsOf (insert f₃ (cutSet σ W₃))
  let B : Finset V := vertsOf (insert f₄ (cutSet σ W₄))
  have hAB : A ∩ B = f₃ ∩ f₄ := by
    simpa [A, B] using hABraw
  have hcover : ∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B := by
    simpa [A, B] using
      flipBoundary_coverage_of_compatible_cut_chains (σ := σ) (X := X) (M := M) (e := e)
        (f₃ := f₃) (f₄ := f₄) hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
        hW₃ hW₄ hdisj₃ hdisj₄ hABraw
  have hcut₃ : σ.filter (fun f => f ⊆ A) = cutSet σ W₃ := by
    ext f
    constructor
    · intro hf
      obtain ⟨hfσ, hfA⟩ := Finset.mem_filter.mp hf
      by_contra hnot
      have hW0 : W₃ ⟨f, hfσ⟩ = 0 := by
        rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (W₃ ⟨f, hfσ⟩) with h0 | h1
        · exact h0
        · exact False.elim (hnot (mem_cutSet.mpr ⟨hfσ, h1⟩))
      have hfcomp : f ∈ cutSet σ (W₃ + fun _ => 1) := (mem_cutSet_add_one hfσ).mpr hW0
      have hfcompVerts : f ⊆ vertsOf (insert f₃ (cutSet σ (W₃ + fun _ => 1))) := by
        intro x hx
        exact mem_vertsOf.mpr ⟨f, Finset.mem_insert_of_mem hfcomp, hx⟩
      have hinter := vertsOf_cut_inter hσ hW₃
      have hfsubγ : f ⊆ f₃ := by
        rw [← hinter]
        exact Finset.subset_inter (by simpa [A] using hfA) hfcompVerts
      have hfeq : f = f₃ := by
        apply Finset.eq_of_subset_of_card_le hfsubγ
        rw [hf₃card, hσ.pure f hfσ]
      rw [hfeq] at hfσ
      exact hmissing.1 hfσ
    · intro hfcut
      obtain ⟨hfσ, _⟩ := mem_cutSet.mp hfcut
      exact Finset.mem_filter.mpr ⟨hfσ, by
        intro x hx
        exact mem_vertsOf.mpr ⟨f, Finset.mem_insert_of_mem hfcut, hx⟩⟩
  have hcut₄ : σ.filter (fun f => f ⊆ B) = cutSet σ W₄ := by
    ext f
    constructor
    · intro hf
      obtain ⟨hfσ, hfB⟩ := Finset.mem_filter.mp hf
      by_contra hnot
      have hW0 : W₄ ⟨f, hfσ⟩ = 0 := by
        rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (W₄ ⟨f, hfσ⟩) with h0 | h1
        · exact h0
        · exact False.elim (hnot (mem_cutSet.mpr ⟨hfσ, h1⟩))
      have hfcomp : f ∈ cutSet σ (W₄ + fun _ => 1) := (mem_cutSet_add_one hfσ).mpr hW0
      have hfcompVerts : f ⊆ vertsOf (insert f₄ (cutSet σ (W₄ + fun _ => 1))) := by
        intro x hx
        exact mem_vertsOf.mpr ⟨f, Finset.mem_insert_of_mem hfcomp, hx⟩
      have hinter := vertsOf_cut_inter hσ hW₄
      have hfsubγ : f ⊆ f₄ := by
        rw [← hinter]
        exact Finset.subset_inter (by simpa [B] using hfB) hfcompVerts
      have hfeq : f = f₄ := by
        apply Finset.eq_of_subset_of_card_le hfsubγ
        rw [hf₄card, hσ.pure f hfσ]
      rw [hfeq] at hfσ
      exact hmissing.2 hfσ
    · intro hfcut
      obtain ⟨hfσ, _⟩ := mem_cutSet.mp hfcut
      exact Finset.mem_filter.mpr ⟨hfσ, by
        intro x hx
        exact mem_vertsOf.mpr ⟨f, Finset.mem_insert_of_mem hfcut, hx⟩⟩
  have hf₃subA : f₃ ⊆ A := by
    intro x hx
    exact mem_vertsOf.mpr ⟨f₃, Finset.mem_insert_self _ _, hx⟩
  have hf₄subB : f₄ ⊆ B := by
    intro x hx
    exact mem_vertsOf.mpr ⟨f₄, Finset.mem_insert_self _ _, hx⟩
  have hf₄notA : ¬ f₄ ⊆ A := by
    intro hsub
    have hsubcd : f₄ ⊆ f₃ ∩ f₄ := by
      rw [← hAB]
      exact Finset.subset_inter hsub hf₄subB
    have hle := Finset.card_le_card hsubcd
    rw [hf₄card, hcd] at hle
    omega
  have hf₃notB : ¬ f₃ ⊆ B := by
    intro hsub
    have hsubcd : f₃ ⊆ f₃ ∩ f₄ := by
      rw [← hAB]
      exact Finset.subset_inter hf₃subA hsub
    have hle := Finset.card_le_card hsubcd
    rw [hf₃card, hcd] at hle
    omega
  have hfilter₃ : (flipBoundary σ M e).filter (fun f => f ⊆ A) = insert f₃ (cutSet σ W₃) := by
    ext f
    constructor
    · intro hf
      rw [Finset.mem_filter] at hf
      unfold flipBoundary at hf
      rw [Finset.mem_union, Finset.mem_sdiff] at hf
      rcases hf.1 with hold | hex
      · have hfσfilter : f ∈ σ.filter (fun f => f ⊆ A) := Finset.mem_filter.mpr ⟨hold.1, hf.2⟩
        have hfcut : f ∈ cutSet σ W₃ := by
          rw [← hcut₃]
          exact hfσfilter
        exact Finset.mem_insert_of_mem hfcut
      · rw [hexp] at hex
        rw [Finset.mem_insert, Finset.mem_singleton] at hex
        rcases hex with rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact False.elim (hf₄notA hf.2)
    · intro hf
      rw [Finset.mem_insert] at hf
      rw [Finset.mem_filter]
      rcases hf with rfl | hfcut
      · constructor
        · unfold flipBoundary
          rw [Finset.mem_union]
          exact Or.inr hf₃exp
        · exact hf₃subA
      · have hfσfilter : f ∈ σ.filter (fun f => f ⊆ A) := by
          rw [hcut₃]
          exact hfcut
        obtain ⟨hfσ, hfsub⟩ := Finset.mem_filter.mp hfσfilter
        constructor
        · unfold flipBoundary
          rw [Finset.mem_union, Finset.mem_sdiff]
          refine Or.inl ⟨hfσ, ?_⟩
          intro hsh
          exact (Finset.disjoint_left.mp hdisj₃) hsh hfcut
        · exact hfsub
  have hfilter₄ : (flipBoundary σ M e).filter (fun f => f ⊆ B) = insert f₄ (cutSet σ W₄) := by
    ext f
    constructor
    · intro hf
      rw [Finset.mem_filter] at hf
      unfold flipBoundary at hf
      rw [Finset.mem_union, Finset.mem_sdiff] at hf
      rcases hf.1 with hold | hex
      · have hfσfilter : f ∈ σ.filter (fun f => f ⊆ B) := Finset.mem_filter.mpr ⟨hold.1, hf.2⟩
        have hfcut : f ∈ cutSet σ W₄ := by
          rw [← hcut₄]
          exact hfσfilter
        exact Finset.mem_insert_of_mem hfcut
      · rw [hexp] at hex
        rw [Finset.mem_insert, Finset.mem_singleton] at hex
        rcases hex with rfl | rfl
        · exact False.elim (hf₃notB hf.2)
        · exact Finset.mem_insert_self _ _
    · intro hf
      rw [Finset.mem_insert] at hf
      rw [Finset.mem_filter]
      rcases hf with rfl | hfcut
      · constructor
        · unfold flipBoundary
          rw [Finset.mem_union]
          exact Or.inr hf₄exp
        · exact hf₄subB
      · have hfσfilter : f ∈ σ.filter (fun f => f ⊆ B) := by
          rw [hcut₄]
          exact hfcut
        obtain ⟨hfσ, hfsub⟩ := Finset.mem_filter.mp hfσfilter
        constructor
        · unfold flipBoundary
          rw [Finset.mem_union, Finset.mem_sdiff]
          refine Or.inl ⟨hfσ, ?_⟩
          intro hsh
          exact (Finset.disjoint_left.mp hdisj₄) hsh hfcut
        · exact hfsub
  exact ⟨A, B, W₃, W₄, hW₃, hW₄, hAB, hcover, hfilter₃, hfilter₄⟩

theorem flipEdgePresent_boundary_side_package {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    ∃ A B : Finset V,
      A ∩ B = f₃ ∩ f₄ ∧
      (f₃ ∩ f₄).card = 2 ∧
      IsSphere2 ((flipBoundary σ M e).filter (fun f => f ⊆ A)) ∧
      IsSphere2 ((flipBoundary σ M e).filter (fun f => f ⊆ B)) ∧
      (∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B) ∧
      f₃ ⊆ A ∧ ¬ f₃ ⊆ B ∧ f₄ ⊆ B ∧ ¬ f₄ ⊆ A := by
  classical
  have hcd : (f₃ ∩ f₄).card = 2 := flipEdgePresent_cd_card he hexp hf₃₄
  have hmiss := flipEdgePresent_exposed_faces_missing hU hMX he hexp hf₃₄
  have hedges := flipEdgePresent_exposed_edges_in_sigma hU hMX he hexp hf₃₄ hFlip
  have hf₃card : f₃.card = 3 := by
    have hf₃mem : f₃ ∈ exposedFaces M e := by
      rw [hexp]
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃mem
    exact (Finset.mem_powersetCard.mp hf₃tet).2
  have hf₄card : f₄.card = 3 := by
    have hf₄mem : f₄ ∈ exposedFaces M e := by
      rw [hexp]
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
    have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄mem
    exact (Finset.mem_powersetCard.mp hf₄tet).2
  obtain ⟨A, B, W₃, W₄, hW₃, hW₄, hAB, hcover, hAeq, hBeq⟩ :=
    flipEdgePresent_compatible_triangle_cuts hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
  have hf₃flip : f₃ ∈ flipBoundary σ M e := by
    simp only [flipBoundary, Finset.mem_union]; right; rw [hexp]
    exact Finset.mem_insert_self f₃ _
  have hf₄flip : f₄ ∈ flipBoundary σ M e := by
    simp only [flipBoundary, Finset.mem_union]; right; rw [hexp]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
  refine ⟨A, B, hAB, hcd, ?_, ?_, hcover, ?_, ?_, ?_, ?_⟩
  · rw [hAeq]
    exact isSphere2_cut hσ hf₃card hedges.1 hmiss.1 hW₃
  · rw [hBeq]
    exact isSphere2_cut hσ hf₄card hedges.2 hmiss.2 hW₄
  · -- f₃ ⊆ A : the A-side filter is `insert f₃ (cutSet σ W₃)`, so `f₃` is in it
    have hmem : f₃ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ A) := by
      rw [hAeq]; exact Finset.mem_insert_self f₃ _
    exact (Finset.mem_filter.mp hmem).2
  · -- ¬ f₃ ⊆ B : else f₃ ∈ insert f₄ (cutSet σ W₄), but f₃ ≠ f₄ and f₃ ∉ σ ⊇ cutSet
    intro hf₃B
    have hmem : f₃ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ B) :=
      Finset.mem_filter.mpr ⟨hf₃flip, hf₃B⟩
    rw [hBeq, Finset.mem_insert] at hmem
    rcases hmem with h | h
    · exact hf₃₄ h
    · exact hmiss.1 (cutSet_subset h)
  · -- f₄ ⊆ B
    have hmem : f₄ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ B) := by
      rw [hBeq]; exact Finset.mem_insert_self f₄ _
    exact (Finset.mem_filter.mp hmem).2
  · -- ¬ f₄ ⊆ A
    intro hf₄A
    have hmem : f₄ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ A) :=
      Finset.mem_filter.mpr ⟨hf₄flip, hf₄A⟩
    rw [hAeq, Finset.mem_insert] at hmem
    rcases hmem with h | h
    · exact hf₃₄ h.symm
    · exact hmiss.2 (cutSet_subset h)


/-- **Case-2 edge split, geometry.** The already-present flip edge
`f₃ ∩ f₄` determines two vertex sides `A,B`, intersecting exactly in that edge,
such that the two filters of `flipBoundary σ M e` are 2-spheres, and every
remaining tetrahedron lies wholly on exactly one side.  This is the edge-split
analogue of `isSphere2_cut`. -/
theorem flipEdgePresent_side_sets {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    ∃ A B : Finset V,
      A ∩ B = f₃ ∩ f₄ ∧
      (f₃ ∩ f₄).card = 2 ∧
      IsSphere2 ((flipBoundary σ M e).filter (fun f => f ⊆ A)) ∧
      IsSphere2 ((flipBoundary σ M e).filter (fun f => f ⊆ B)) ∧
      (∀ t ∈ (removeTet M e).support, t ⊆ A ∨ t ⊆ B) ∧
      (∀ t ∈ (removeTet M e).support,
        (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A)) ∧
      f₃ ⊆ A ∧ ¬ f₃ ⊆ B ∧ f₄ ⊆ B ∧ ¬ f₄ ⊆ A ∧
      (∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B) := by
  rcases flipEdgePresent_boundary_side_package hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip with
    ⟨A, B, hAB, hcd, hsphereA, hsphereB, hfaceCover, hf₃A, hf₃notB, hf₄B, hf₄notA⟩
  rcases flipEdgePresent_removeTet_support_partition hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip hAB hcd hfaceCover with ⟨hcover, hsep⟩
  exact ⟨A, B, hAB, hcd, hsphereA, hsphereB, hcover, hsep, hf₃A, hf₃notB, hf₄B, hf₄notA, hfaceCover⟩

theorem bdry_filter_eq_filter_bdry_of_side_sep {V : Type*} [LinearOrder V] {M : Chain V} {A B : Finset V}
    (hpure : ∀ t ∈ M.support, t.card = 4)
    (hsep : ∀ t ∈ M.support,
      (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A))
    (hAB2 : (A ∩ B).card = 2) :
    bdry (M.filter (fun t => t ⊆ A)) = (bdry M).filter (fun f => f ⊆ A) := by
  classical
  ext f
  rw [Finsupp.filter_apply]
  by_cases hfA : f ⊆ A
  · rw [if_pos hfA]
    refine bdry_filter_apply_eq_bdry_of_no_cross (X := M) (P := fun t => t ⊆ A) (u := f) ?_
    intro t ht htA
    by_contra hbg
    obtain ⟨w, hw, hfw⟩ := exists_facet_of_bdryGen_ne_zero hbg
    have htB : t ⊆ B := by
      rcases hsep t ht with hside | hside
      · exact False.elim (htA hside.1)
      · exact hside.1
    have hfB : f ⊆ B := by
      rw [hfw]
      exact (Finset.erase_subset w t).trans htB
    have hfInter : f ⊆ A ∩ B := Finset.subset_inter hfA hfB
    have hcardf : f.card = 3 := by
      rw [hfw, Finset.card_erase_of_mem hw, hpure t ht]
    have hle : f.card ≤ (A ∩ B).card := Finset.card_le_card hfInter
    rw [hAB2] at hle
    omega
  · rw [if_neg hfA]
    rw [bdry_apply_eq_sum]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at ht
    by_cases hgen : bdryGen t f = 0
    · rw [hgen, mul_zero]
    · exfalso
      obtain ⟨w, hw, hfw⟩ := exists_facet_of_bdryGen_ne_zero hgen
      have hfsubA : f ⊆ A := by
        rw [hfw]
        exact (Finset.erase_subset w t).trans ht.2
      exact hfA hfsubA

theorem flipEdgePresent_side_supports {V : Type*} [LinearOrder V] {M : Chain V} {e A B : Finset V}
    (he : EligibleTet M e)
    (hcover : ∀ t ∈ (removeTet M e).support, t ⊆ A ∨ t ⊆ B)
    (hsep : ∀ t ∈ (removeTet M e).support,
      (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A)) :
    Disjoint ((removeTet M e).filter (fun t => t ⊆ A)).support
      ((removeTet M e).filter (fun t => t ⊆ B)).support ∧
    M.support =
      insert e
        (((removeTet M e).filter (fun t => t ⊆ A)).support ∪
          ((removeTet M e).filter (fun t => t ⊆ B)).support) := by
  classical
  let R := removeTet M e
  constructor
  · rw [Finset.disjoint_left]
    intro t htA htB
    simp only [Finsupp.support_filter, mem_filter] at htA htB
    rcases htA with ⟨htR, htA⟩
    rcases htB with ⟨htR', htB⟩
    rcases hsep t htR with h | h
    · exact h.2 htB
    · exact h.2 htA
  · have hR : R.support = (R.filter (fun t => t ⊆ A)).support ∪ (R.filter (fun t => t ⊆ B)).support := by
      ext t
      constructor
      · intro htR
        rw [mem_union]
        rcases hcover t htR with htA | htB
        · left
          simp only [Finsupp.support_filter, mem_filter]
          exact ⟨htR, htA⟩
        · right
          simp only [Finsupp.support_filter, mem_filter]
          exact ⟨htR, htB⟩
      · intro ht
        rw [mem_union] at ht
        rcases ht with htA | htB
        · simp only [Finsupp.support_filter, mem_filter] at htA
          exact htA.1
        · simp only [Finsupp.support_filter, mem_filter] at htB
          exact htB.1
    have hins := support_insert_removeTet_of_mem he.2.1
    rw [← hins]
    simp only [R] at hR
    rw [hR]

theorem flipEdgePresent_side_taut_simp_norm {V : Type*} [LinearOrder V] {M : Chain V} {e A B : Finset V}
    (hT : IsTaut M) (hS : SimplicialChain M) (he : EligibleTet M e) :
    IsTaut ((removeTet M e).filter (fun t => t ⊆ A)) ∧
      IsTaut ((removeTet M e).filter (fun t => t ⊆ B)) ∧
      SimplicialChain ((removeTet M e).filter (fun t => t ⊆ A)) ∧
      SimplicialChain ((removeTet M e).filter (fun t => t ⊆ B)) ∧
      nrm ((removeTet M e).filter (fun t => t ⊆ A)) < nrm M ∧
      nrm ((removeTet M e).filter (fun t => t ⊆ B)) < nrm M ∧
      e ∉ ((removeTet M e).filter (fun t => t ⊆ A)).support ∧
      e ∉ ((removeTet M e).filter (fun t => t ⊆ B)).support := by
  let R := removeTet M e
  have hTR : IsTaut R := isTaut_removeTet hT
  have hTA : IsTaut (R.filter (fun t => t ⊆ A)) := hTR.subChain (subChain_filter _ R)
  have hTB : IsTaut (R.filter (fun t => t ⊆ B)) := hTR.subChain (subChain_filter _ R)
  have hSR : SimplicialChain R := simplicialChain_removeTet hS
  have hSA : SimplicialChain (R.filter (fun t => t ⊆ A)) := by
    intro t
    rw [Finsupp.filter_apply]
    by_cases ht : t ⊆ A
    · simp [ht]
      exact hSR t
    · simp [ht]
  have hSB : SimplicialChain (R.filter (fun t => t ⊆ B)) := by
    intro t
    rw [Finsupp.filter_apply]
    by_cases ht : t ⊆ B
    · simp [ht]
      exact hSR t
    · simp [ht]
  have hdropR : nrm R < nrm M := by
    have hEq : nrm R + 1 = nrm M := nrm_removeTet_add_one_of_simplicial hS he.2.1
    omega
  have hleA : nrm (R.filter (fun t => t ⊆ A)) ≤ nrm R := by
    have hsum := nrm_filter_add_nrm_filter_neg (fun t => t ⊆ A) R
    omega
  have hleB : nrm (R.filter (fun t => t ⊆ B)) ≤ nrm R := by
    have hsum := nrm_filter_add_nrm_filter_neg (fun t => t ⊆ B) R
    omega
  have hdropA : nrm (R.filter (fun t => t ⊆ A)) < nrm M := lt_of_le_of_lt hleA hdropR
  have hdropB : nrm (R.filter (fun t => t ⊆ B)) < nrm M := lt_of_le_of_lt hleB hdropR
  have hsuppR : R.support = M.support.erase e := support_removeTet_of_mem he.2.1
  have hnotR : e ∉ R.support := by
    rw [hsuppR]
    simp
  have hnotA : e ∉ (R.filter (fun t => t ⊆ A)).support := by
    intro heA
    rw [Finsupp.support_filter] at heA
    exact hnotR ((Finset.mem_filter.mp heA).1)
  have hnotB : e ∉ (R.filter (fun t => t ⊆ B)).support := by
    intro heB
    rw [Finsupp.support_filter] at heB
    exact hnotR ((Finset.mem_filter.mp heB).1)
  exact ⟨hTA, hTB, hSA, hSB, hdropA, hdropB, hnotA, hnotB⟩

theorem flipEdgePresent_side_units {V : Type*} [LinearOrder V]
    {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hAB : A ∩ B = f₃ ∩ f₄)
    (hcd : (f₃ ∩ f₄).card = 2)
    (hsep : ∀ t ∈ (removeTet M e).support,
      (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A)) :
    UnitOn (bdry ((removeTet M e).filter (fun t => t ⊆ A)))
        ((flipBoundary σ M e).filter (fun f => f ⊆ A)) ∧
      UnitOn (bdry ((removeTet M e).filter (fun t => t ⊆ B)))
        ((flipBoundary σ M e).filter (fun f => f ⊆ B)) := by
  have hUb : UnitOn (bdry M) σ := by
    simpa only [hMX] using hU
  have hUflip : UnitOn (bdry (removeTet M e)) (flipBoundary σ M e) := by
    simpa only [flipBoundary] using unitOn_flipBoundary_of_eligible hUb hS he
  have hpure : ∀ t ∈ (removeTet M e).support, t.card = 4 := by
    intro t ht
    have hMinfo : ∀ t ∈ M.support, t.card = 4 ∧ t ⊆ vertsOf σ :=
      aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
    have hR : (removeTet M e).support = M.support.erase e :=
      support_removeTet_of_mem he.2.1
    rw [hR] at ht
    exact (hMinfo t (Finset.mem_of_mem_erase ht)).1
  have hAB2 : (A ∩ B).card = 2 := by
    rw [hAB]
    exact hcd
  have hbdA : bdry ((removeTet M e).filter (fun t => t ⊆ A)) =
      (bdry (removeTet M e)).filter (fun f => f ⊆ A) := by
    exact bdry_filter_eq_filter_bdry_of_side_sep hpure hsep hAB2
  have hsepBA : ∀ t ∈ (removeTet M e).support,
      (t ⊆ B ∧ ¬ t ⊆ A) ∨ (t ⊆ A ∧ ¬ t ⊆ B) := by
    intro t ht
    rcases hsep t ht with hA | hB
    · exact Or.inr hA
    · exact Or.inl hB
  have hBA2 : (B ∩ A).card = 2 := by
    rw [Finset.inter_comm]
    exact hAB2
  have hbdB : bdry ((removeTet M e).filter (fun t => t ⊆ B)) =
      (bdry (removeTet M e)).filter (fun f => f ⊆ B) := by
    exact bdry_filter_eq_filter_bdry_of_side_sep (M := removeTet M e) (A := B) (B := A) hpure hsepBA hBA2
  constructor
  · unfold UnitOn
    constructor
    · rw [hbdA, Finsupp.support_filter, hUflip.1]
    · intro s hs
      rw [Finset.mem_filter] at hs
      rw [hbdA, Finsupp.filter_apply, if_pos hs.2]
      exact hUflip.2 s hs.1
  · unfold UnitOn
    constructor
    · rw [hbdB, Finsupp.support_filter, hUflip.1]
    · intro s hs
      rw [Finset.mem_filter] at hs
      rw [hbdB, Finsupp.filter_apply, if_pos hs.2]
      exact hUflip.2 s hs.1


/-- **Case-2 edge split, algebra.** Once the side vertex sets are known with
coverage and exact-side separation, the filtered side chains are closed, taut,
simplicial, strictly smaller, disjoint, and decompose the original support.
Intended proof ingredients:
`unitOn_flipBoundary_of_eligible`, `bdry_filter_subset_eq_zero_of_inter_card_two`,
`IsTaut.splits`, `nrm_filter_add_nrm_filter_neg`, `simplicialChain_removeTet`,
and `support_flipBoundary_of_eligible`. -/
theorem flipEdgePresent_side_algebra {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    (hAB : A ∩ B = f₃ ∩ f₄)
    (hcd : (f₃ ∩ f₄).card = 2)
    (hcover : ∀ t ∈ (removeTet M e).support, t ⊆ A ∨ t ⊆ B)
    (hsep : ∀ t ∈ (removeTet M e).support,
      (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A)) :
    UnitOn (bdry ((removeTet M e).filter (fun t => t ⊆ A)))
        ((flipBoundary σ M e).filter (fun f => f ⊆ A)) ∧
      UnitOn (bdry ((removeTet M e).filter (fun t => t ⊆ B)))
        ((flipBoundary σ M e).filter (fun f => f ⊆ B)) ∧
      bdry (bdry ((removeTet M e).filter (fun t => t ⊆ A))) = 0 ∧
      bdry (bdry ((removeTet M e).filter (fun t => t ⊆ B))) = 0 ∧
      IsTaut ((removeTet M e).filter (fun t => t ⊆ A)) ∧
      IsTaut ((removeTet M e).filter (fun t => t ⊆ B)) ∧
      SimplicialChain ((removeTet M e).filter (fun t => t ⊆ A)) ∧
      SimplicialChain ((removeTet M e).filter (fun t => t ⊆ B)) ∧
      nrm ((removeTet M e).filter (fun t => t ⊆ A)) < nrm M ∧
      nrm ((removeTet M e).filter (fun t => t ⊆ B)) < nrm M ∧
      e ∉ ((removeTet M e).filter (fun t => t ⊆ A)).support ∧
      e ∉ ((removeTet M e).filter (fun t => t ⊆ B)).support ∧
      Disjoint ((removeTet M e).filter (fun t => t ⊆ A)).support
        ((removeTet M e).filter (fun t => t ⊆ B)).support ∧
      M.support =
        insert e
          (((removeTet M e).filter (fun t => t ⊆ A)).support ∪
            ((removeTet M e).filter (fun t => t ⊆ B)).support) := by
  obtain ⟨hUA, hUB⟩ := flipEdgePresent_side_units hσ hU hMX hT hS he hAB hcd hsep
  obtain ⟨hTA, hTB, hSA, hSB, hnA, hnB, heA, heB⟩ := flipEdgePresent_side_taut_simp_norm (M := M) (e := e) (A := A) (B := B) hT hS he
  obtain ⟨hdisj, hsupp⟩ := flipEdgePresent_side_supports (M := M) (e := e) (A := A) (B := B) he hcover hsep
  refine ⟨hUA, hUB, ?_, ?_, hTA, hTB, hSA, hSB, hnA, hnB, heA, heB, hdisj, hsupp⟩
  · exact bdry_bdry _
  · exact bdry_bdry _

/-! ## The pseudomanifold carry (LEMMA B + LEMMA C)

Both remaining geometry holes need "a boundary triangle of the smaller filling lies
in exactly one tet", which is the pseudomanifold property — false for a bare freely
shellable complex, true once we carry `IsPseudomanifold` through the induction.  The
two pieces here are the engine: `removeTet_isPseudomanifold` (the smaller filling is a
pseudomanifold, using the IH on each side of a split) and
`faceCount_removeTet_sharedFace_eq_zero` (the eligible tet's shared faces vanish on
removal — the clean-glue input for the prime step). -/

/-- **LEMMA B (removeTet is a pseudomanifold).** For an eligible `u` in a taut
filling `M` of the sphere `σ`, the smaller filling `removeTet M u` is a
pseudomanifold, using the strong-induction hypothesis (every strictly smaller
single-sphere taut filling is a pseudomanifold). The "two pieces joined along an
edge" case (flip edge present) is handled by applying the IH to each side and
gluing the two pseudomanifolds with `isPseudomanifold_union_of_sideSep`. -/
lemma removeTet_isPseudomanifold {σ : Finset (Finset V)} {X M : Chain V} {u : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hu : EligibleTet M u)
    (IHpm : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      IsPseudomanifold M'.support) :
    IsPseudomanifold (removeTet M u).support := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  obtain ⟨f₃, f₄, hf₃₄, hexp⟩ := exposedFaces_eq_pair_of_eligible hu
  by_cases hFlip : FlipEdgePresent σ f₃ f₄
  · -- case 2: removeTet M u splits into two smaller single-sphere taut fillings
    obtain ⟨A, B, hAB, hcd, hsph₁, hsph₂, hcover, hsep, hf₃A, hf₃notB, hf₄B, hf₄notA, _⟩ :=
      flipEdgePresent_side_sets hσ hU hXc hMX hT hS hu hexp hf₃₄ hFlip
    obtain ⟨hu₁, hu₂, hc₁, hc₂, hT₁, hT₂, hS₁, hS₂, hsm₁, hsm₂, hen₁, hen₂, hdisj, hsupp⟩ :=
      flipEdgePresent_side_algebra hσ hU hXc hMX hT hS hu hexp hf₃₄ hFlip hAB hcd hcover hsep
    have hPM₁ : IsPseudomanifold ((removeTet M u).filter (fun t => t ⊆ A)).support :=
      IHpm _ (bdry ((removeTet M u).filter (fun t => t ⊆ A)))
        ((removeTet M u).filter (fun t => t ⊆ A)) hsm₁ hsph₁ hu₁ hc₁ rfl hT₁ hS₁
    have hPM₂ : IsPseudomanifold ((removeTet M u).filter (fun t => t ⊆ B)).support :=
      IHpm _ (bdry ((removeTet M u).filter (fun t => t ⊆ B)))
        ((removeTet M u).filter (fun t => t ⊆ B)) hsm₂ hsph₂ hu₂ hc₂ rfl hT₂ hS₂
    rw [Finsupp.support_filter] at hPM₁ hPM₂
    refine isPseudomanifold_union_of_sideSep hcover ?_ hPM₁ hPM₂
    rw [hAB]; exact hcd.le
  · -- case 1: removeTet M u is itself a smaller single-sphere taut filling
    have hσe := isSphere2_flipBoundary_of_eligible hσ hUb hS hu hexp hf₃₄ hFlip
    have hUe := unitOn_flipBoundary_of_eligible hUb hS hu
    have hTe : IsTaut (removeTet M u) := isTaut_removeTet hT
    have hSe : SimplicialChain (removeTet M u) := simplicialChain_removeTet hS
    have hlt : nrm (removeTet M u) < nrm M := by
      have h := nrm_removeTet_add_one_of_simplicial hS hu.2.1; omega
    exact IHpm _ (bdry (removeTet M u)) (removeTet M u) hlt hσe hUe (bdry_bdry _) rfl hTe hSe

/-- **LEMMA C (triangle rule-out).** The shared faces of an eligible tet `e` vanish
when `e` is removed: a shared face `r` lies in NO tet of `removeTet M e`.  If it
lay in some `w ≠ e`, then removing the disjoint eligible `u` (boundary faces
disjoint from `e`'s, from `aleph_disjoint_eligible_pair`) keeps both `e` and `w`,
so `r` lies in ≥ 2 tets of `removeTet M u`; by parity it is ≥ 3, contradicting
`removeTet M u` being a pseudomanifold (LEMMA B). -/
lemma faceCount_removeTet_sharedFace_eq_zero {σ : Finset (Finset V)} {X M : Chain V}
    {e u r : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (he : EligibleTet M e) (hu : EligibleTet M u)
    (hdisj : Disjoint (sharedFaces M e) (sharedFaces M u))
    (hPMu : IsPseudomanifold (removeTet M u).support)
    (hr : r ∈ sharedFaces M e) :
    faceCount (removeTet M e).support r = 0 := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  -- r is a triangle, a face of e, on the boundary
  have hrt : r ∈ tetFaces e := sharedFaces_subset_tetFaces M e hr
  have hr3 : r.card = 3 := (Finset.mem_powersetCard.mp hrt).2
  have hre : r ⊆ e := (Finset.mem_powersetCard.mp hrt).1
  have hrbd : r ∈ (bdry M).support := (Finset.mem_inter.mp hr).2
  -- r is not a face of u (disjoint shared faces)
  have hrnu : r ∉ sharedFaces M u := fun h => (Finset.disjoint_left.mp hdisj) hr h
  have hru_not : ¬ r ⊆ u := by
    intro hru
    have : r ∈ tetFaces u := Finset.mem_powersetCard.mpr ⟨hru, hr3⟩
    exact hrnu (Finset.mem_inter.mpr ⟨this, hrbd⟩)
  -- support facts
  have hSu : SimplicialChain (removeTet M u) := simplicialChain_removeTet hS
  have hsuppU : (removeTet M u).support = M.support.erase u := support_removeTet_of_mem hu.2.1
  have hPureU : ∀ t ∈ (removeTet M u).support, t.card = 4 := by
    intro t ht; rw [hsuppU] at ht; exact hPure t (Finset.mem_of_mem_erase ht)
  -- r is a boundary face of removeTet M u (it's in σ \ sharedFaces M u ⊆ flipBoundary)
  have hUe : UnitOn (bdry (removeTet M u)) ((σ \ sharedFaces M u) ∪ exposedFaces M u) :=
    unitOn_flipBoundary_of_eligible hUb hS hu
  have hrσ : r ∈ σ := hUb.1 ▸ hrbd
  have hrflip : r ∈ (σ \ sharedFaces M u) ∪ exposedFaces M u :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hrσ, hrnu⟩)
  have hrbdU : bdry (removeTet M u) r = 1 ∨ bdry (removeTet M u) r = -1 :=
    hUe.2 r hrflip
  -- now rule out any w ≠ e with r ⊆ w
  apply faceCount_eq_zero
  intro w hw hrw
  rw [support_removeTet_of_mem he.2.1] at hw
  have hwne : w ≠ e := (Finset.mem_erase.mp hw).1
  have hwM : w ∈ M.support := (Finset.mem_erase.mp hw).2
  -- e, w are both ≠ u, hence both in removeTet M u
  have heu : e ≠ u := fun h => hru_not (h ▸ hre)
  have hwu : w ≠ u := fun h => hru_not (h ▸ hrw)
  have heU : e ∈ (removeTet M u).support := by
    rw [hsuppU]; exact Finset.mem_erase.mpr ⟨heu, he.2.1⟩
  have hwU : w ∈ (removeTet M u).support := by
    rw [hsuppU]; exact Finset.mem_erase.mpr ⟨hwu, hwM⟩
  -- faceCount (removeTet M u).support r ≥ 2
  have hpair : ({e, w} : Finset (Finset V)) ⊆ (removeTet M u).support.filter (fun t => r ⊆ t) := by
    intro s hs
    rw [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨heU, hre⟩
    · exact Finset.mem_filter.mpr ⟨hwU, hrw⟩
  have h2le : 2 ≤ faceCount (removeTet M u).support r := by
    have hcard := Finset.card_le_card hpair
    rw [Finset.card_pair (Ne.symm hwne)] at hcard
    exact hcard
  -- parity: faceCount ≠ 2
  have hne2 : faceCount (removeTet M u).support r ≠ 2 :=
    faceCount_ne_two_of_boundary hSu hPureU hr3 hrbdU
  -- so ≥ 3, contradicting PM
  have h3 : 3 ≤ faceCount (removeTet M u).support r := by omega
  exact not_isPseudomanifold_of_faceCount hr3 h3 hPMu

/-! ## PM-carry: a taut filling of a 2-sphere is a pseudomanifold

A standalone strong induction mirroring the free-shelling induction
(`base_free`/`deg3_step_free`/`prime_step_free` assembled by `theorem3_core`),
but carrying `IsPseudomanifold M.support` instead of `FreelyShellable`. This
provides the triangle-incidence half of a faithful stickerball directly to
downstream proofs. -/

/-- **prime_isPM** (PM no-degree-3 step): a no-degree-3 taut filling of a 2-sphere
is a pseudomanifold, given that every strictly smaller single-sphere taut filling
is one. Pick a disjoint eligible pair `e, u` (M25b); each `removeTet` is a PM by
the recursion (`removeTet_isPseudomanifold`); re-insert `e` via
`isPseudomanifold_insert`, discharging the clean-glue obligation by the triangle
rule-out (`faceCount_removeTet_sharedFace_eq_zero`) on shared faces and by the
unit boundary (`faceCount_eq_one_of_boundary`) on exposed faces. -/
lemma prime_isPM (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) (hNo3 : NoDegree3Vertex σ)
    (IHpm : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      IsPseudomanifold M'.support) :
    IsPseudomanifold M.support := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hPure : ∀ t ∈ M.support, t.card = 4 :=
    fun t ht => (aleph_base_taut_support_card4_subset_verts hσ hU hMX hT t ht).1
  obtain ⟨e, u, hne, he, hu, hdisj⟩ :=
    aleph_disjoint_eligible_pair hσ hUb hS hT hPure hNo3
  have hPMu : IsPseudomanifold (removeTet M u).support :=
    removeTet_isPseudomanifold hσ hU hXc hMX hT hS hu IHpm
  -- re-insert e onto the smaller PM (removeTet M e)
  have hPMe : IsPseudomanifold (removeTet M e).support :=
    removeTet_isPseudomanifold hσ hU hXc hMX hT hS he IHpm
  rw [← support_insert_removeTet_of_mem he.2.1]
  refine isPseudomanifold_insert hPMe ?_ ?_
  · -- e ∉ (removeTet M e).support
    rw [support_removeTet_of_mem he.2.1]
    exact Finset.notMem_erase e M.support
  · -- clean glue: every triangle of e lies in ≤ 1 tet of removeTet M e
    intro f hf3 hfe
    have hftet : f ∈ tetFaces e := Finset.mem_powersetCard.mpr ⟨hfe, hf3⟩
    by_cases hsh : f ∈ sharedFaces M e
    · -- shared face: vanishes on removal
      have h0 : faceCount (removeTet M e).support f = 0 :=
        faceCount_removeTet_sharedFace_eq_zero hσ hU hXc hMX hT hS hPure he hu hdisj hPMu hsh
      omega
    · -- exposed face: it is a unit boundary face of removeTet M e, so exactly one tet
      have hexpf : f ∈ exposedFaces M e := Finset.mem_sdiff.mpr ⟨hftet, hsh⟩
      have hUe : UnitOn (bdry (removeTet M e)) ((σ \ sharedFaces M e) ∪ exposedFaces M e) :=
        unitOn_flipBoundary_of_eligible hUb hS he
      have hfflip : f ∈ (σ \ sharedFaces M e) ∪ exposedFaces M e :=
        Finset.mem_union_right _ hexpf
      have hbd : bdry (removeTet M e) f = 1 ∨ bdry (removeTet M e) f = -1 :=
        hUe.2 f hfflip
      have hSe : SimplicialChain (removeTet M e) := simplicialChain_removeTet hS
      have hPureE : ∀ t ∈ (removeTet M e).support, t.card = 4 := by
        intro t ht
        rw [support_removeTet_of_mem he.2.1] at ht
        exact hPure t (Finset.mem_of_mem_erase ht)
      have h1 : faceCount (removeTet M e).support f = 1 :=
        faceCount_eq_one_of_boundary hSe hPureE hPMe hf3 hbd
      omega

/-- **PM-carry: every taut filling of a combinatorial 2-sphere is a
pseudomanifold.** A standalone strong induction parallel to `theorem3_core`,
carrying `IsPseudomanifold M.support` (each triangle in ≤ 2 tets). Base case
(≤ 4 vertices) by `base_isPM`; degree-3 vertex by `deg3_isPM`; otherwise by
`prime_isPM`; the strong induction hypothesis is threaded to both non-base
steps. This exposes the triangle-incidence half of a faithful stickerball to
downstream proofs without modifying the free-shelling induction. -/
theorem taut_isPseudomanifold {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : IsPseudomanifold M.support := by
  suffices H : ∀ N, ∀ (σ : Finset (Finset V)) (X M : Chain V), nrm M = N → IsSphere2 σ →
      UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
      IsPseudomanifold M.support by
    exact H (nrm M) σ X M rfl hσ hU hXc hMX hT hS
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro σ X M hN hσ hU hXc hMX hT hS
    by_cases hv : (vertsOf σ).card ≤ 4
    · exact base_isPM σ X M hσ hU hMX hT hS hv
    · push_neg at hv
      by_cases hd3 : HasDegree3Vertex σ
      · refine deg3_isPM σ X M hσ hv hU hXc hMX hT hS hd3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'
      · have hno3 : NoDegree3Vertex σ := fun v hvv hcard => hd3 ⟨v, hvv, hcard⟩
        refine prime_isPM σ X M hσ hU hXc hMX hT hS hno3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'

/-- **Shared faces of the eligible tet straddle the cut.** Each of the two
boundary-shared faces of `e` contains both the A-apex (`f₃ \ f₄`) and the B-apex
(`f₄ \ f₃`) of `e`; since the A-apex lies in `A \ B` and the B-apex in `B \ A`
(the apexes are off the flip edge `A ∩ B = f₃ ∩ f₄`), each shared face is neither
`⊆ A` nor `⊆ B`. -/
theorem sharedFaces_straddle {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ A B : Finset V}
    (hU : UnitOn X σ) (hMX : bdry M = X) (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hAB : A ∩ B = f₃ ∩ f₄) (hcd : (f₃ ∩ f₄).card = 2)
    (hf₃A : f₃ ⊆ A) (hf₄B : f₄ ⊆ B) :
    ∀ s ∈ sharedFaces M e, ¬ s ⊆ A ∧ ¬ s ⊆ B := by
  classical
  -- f₃, f₄ are faces of e (card 3, ⊆ e).
  have hf₃tet : f₃ ∈ tetFaces e := by
    apply exposedFaces_subset_tetFaces M e; rw [hexp]; exact Finset.mem_insert_self f₃ _
  have hf₄tet : f₄ ∈ tetFaces e := by
    apply exposedFaces_subset_tetFaces M e; rw [hexp]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
  have hf₃e : f₃ ⊆ e := (Finset.mem_powersetCard.mp hf₃tet).1
  have hf₄e : f₄ ⊆ e := (Finset.mem_powersetCard.mp hf₄tet).1
  have hf₃c : f₃.card = 3 := (Finset.mem_powersetCard.mp hf₃tet).2
  have hf₄c : f₄.card = 3 := (Finset.mem_powersetCard.mp hf₄tet).2
  have he4 : e.card = 4 := he.1
  -- e = f₃ ∪ f₄.
  have hunioncard : (f₃ ∪ f₄).card + (f₃ ∩ f₄).card = f₃.card + f₄.card :=
    Finset.card_union_add_card_inter f₃ f₄
  have hunion : f₃ ∪ f₄ = e := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hf₃e hf₄e)
    rw [he4]; rw [hf₃c, hf₄c, hcd] at hunioncard; omega
  -- The A-apex `a ∈ f₃ \ f₄` and B-apex `b ∈ f₄ \ f₃`.
  have hf₃sub : ¬ f₃ ⊆ f₄ := by
    intro h
    have : f₃ = f₄ := Finset.eq_of_subset_of_card_le h (hf₄c.trans hf₃c.symm).le
    exact hf₃₄ this
  obtain ⟨a, ha⟩ : (f₃ \ f₄).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact hf₃sub
  have hf₄sub : ¬ f₄ ⊆ f₃ := by
    intro h
    have : f₄ = f₃ := Finset.eq_of_subset_of_card_le h (hf₃c.trans hf₄c.symm).le
    exact hf₃₄ this.symm
  obtain ⟨b, hb⟩ : (f₄ \ f₃).Nonempty := by
    rw [Finset.sdiff_nonempty]; exact hf₄sub
  rw [Finset.mem_sdiff] at ha hb
  -- a ∈ A \ B : a ∈ f₃ ⊆ A; a ∉ B since a ∉ f₃ ∩ f₄ = A ∩ B.
  have haA : a ∈ A := hf₃A ha.1
  have haB : a ∉ B := by
    intro haB'
    have : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨haA, haB'⟩
    rw [hAB, Finset.mem_inter] at this
    exact ha.2 this.2
  -- b ∈ B \ A : b ∈ f₄ ⊆ B; b ∉ A since b ∉ f₃ ∩ f₄ = A ∩ B.
  have hbB : b ∈ B := hf₄B hb.1
  have hbA : b ∉ A := by
    intro hbA'
    have : b ∈ A ∩ B := Finset.mem_inter.mpr ⟨hbA', hbB⟩
    rw [hAB, Finset.mem_inter] at this
    exact hb.2 this.1
  intro s hs
  have hstet : s ∈ tetFaces e := sharedFaces_subset_tetFaces M e hs
  have hse : s ⊆ e := (Finset.mem_powersetCard.mp hstet).1
  have hsc : s.card = 3 := (Finset.mem_powersetCard.mp hstet).2
  -- s ≠ f₃ and s ≠ f₄ (shared faces are not exposed faces).
  have hsnotexp : s ∉ exposedFaces M e := by
    rw [exposedFaces, Finset.mem_sdiff]; push_neg; intro _; exact hs
  rw [hexp, Finset.mem_insert, Finset.mem_singleton] at hsnotexp
  push_neg at hsnotexp
  obtain ⟨hsf₃, hsf₄⟩ := hsnotexp
  -- s contains both apexes a and b.
  have has : a ∈ s := by
    by_contra haS
    -- then s ⊆ e \ {a} = f₄ (since e = f₃ ∪ f₄ and a is the only vertex of f₃ \ f₄).
    -- Show s = f₄ by s ⊆ f₄ and equal cards.
    have hsf₄sub : s ⊆ f₄ := by
      intro x hx
      have hxe : x ∈ e := hse hx
      rw [← hunion, Finset.mem_union] at hxe
      rcases hxe with hxf₃ | hxf₄
      · -- x ∈ f₃; if x ∈ f₄ done, else x ∈ f₃\f₄ = {a}, so x = a, contra haS
        by_cases hxf₄ : x ∈ f₄
        · exact hxf₄
        · exfalso
          have hxa : x = a := by
            have hxd : x ∈ f₃ \ f₄ := Finset.mem_sdiff.mpr ⟨hxf₃, hxf₄⟩
            -- f₃ \ f₄ has card 1, contains a and x.
            have hcard1 : (f₃ \ f₄).card = 1 := by
              have hpart : (f₃ \ f₄).card + (f₃ ∩ f₄).card = f₃.card :=
                Finset.card_sdiff_add_card_inter f₃ f₄
              rw [hf₃c, hcd] at hpart; omega
            rw [Finset.card_eq_one] at hcard1
            obtain ⟨w, hw⟩ := hcard1
            have : x ∈ ({w} : Finset V) := hw ▸ hxd
            have ha' : a ∈ ({w} : Finset V) := hw ▸ (Finset.mem_sdiff.mpr ha)
            rw [Finset.mem_singleton] at this ha'
            rw [this, ha']
          rw [hxa] at hx; exact haS hx
      · exact hxf₄
    exact hsf₄ (Finset.eq_of_subset_of_card_le hsf₄sub (hf₄c.trans hsc.symm).le)
  have hbs : b ∈ s := by
    by_contra hbS
    have hsf₃sub : s ⊆ f₃ := by
      intro x hx
      have hxe : x ∈ e := hse hx
      rw [← hunion, Finset.mem_union] at hxe
      rcases hxe with hxf₃ | hxf₄
      · exact hxf₃
      · by_cases hxf₃ : x ∈ f₃
        · exact hxf₃
        · exfalso
          have hxb : x = b := by
            have hxd : x ∈ f₄ \ f₃ := Finset.mem_sdiff.mpr ⟨hxf₄, hxf₃⟩
            have hcard1 : (f₄ \ f₃).card = 1 := by
              have hpart : (f₄ \ f₃).card + (f₄ ∩ f₃).card = f₄.card :=
                Finset.card_sdiff_add_card_inter f₄ f₃
              rw [hf₄c, Finset.inter_comm, hcd] at hpart; omega
            rw [Finset.card_eq_one] at hcard1
            obtain ⟨w, hw⟩ := hcard1
            have : x ∈ ({w} : Finset V) := hw ▸ hxd
            have hb' : b ∈ ({w} : Finset V) := hw ▸ (Finset.mem_sdiff.mpr hb)
            rw [Finset.mem_singleton] at this hb'
            rw [this, hb']
          rw [hxb] at hx; exact hbS hx
    exact hsf₃ (Finset.eq_of_subset_of_card_le hsf₃sub (hf₃c.trans hsc.symm).le)
  -- s contains b ∉ A, so ¬ s ⊆ A; and a ∉ B, so ¬ s ⊆ B.
  exact ⟨fun hsA => hbA (hsA hbs), fun hsB => haB (hsB has)⟩

/-- **Side reconstruction of `σ` (B-side).** Erasing the exposed face `f₄` from the
B-side flip boundary and adjoining the faces of `σ` that are not contained in `B`
recovers the original sphere `σ`. The two shared faces of `e` straddle the cut, so
they are not ⊆ B; hence they survive in `σ.filter (¬·⊆B)`, exactly compensating
for their absence from `flipBoundary`. -/
theorem flipEdgePresent_side_reconstruct {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) (hAB : A ∩ B = f₃ ∩ f₄) (hcd : (f₃ ∩ f₄).card = 2)
    (hf₄flip : f₄ ∈ flipBoundary σ M e) (hf₄notA : ¬ f₄ ⊆ A) (hf₄B : f₄ ⊆ B)
    (hf₃A : f₃ ⊆ A) (hf₃notB : ¬ f₃ ⊆ B) :
    σ = ((flipBoundary σ M e).filter (fun f => f ⊆ B)).erase f₄ ∪
      σ.filter (fun f => ¬ f ⊆ B) := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hsh_eq : sharedFaces M e = tetFaces e ∩ σ := by simp only [sharedFaces, hUb.1]
  have hshared_sub : sharedFaces M e ⊆ σ := by rw [hsh_eq]; exact Finset.inter_subset_right
  have hf₄notσ : f₄ ∉ σ := by
    have hmem : f₄ ∈ exposedFaces M e := by
      rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
    rw [exposedFaces, hsh_eq, Finset.mem_sdiff, Finset.mem_inter] at hmem
    intro hf₄σ
    exact hmem.2 ⟨hmem.1, hf₄σ⟩
  have hstraddle := sharedFaces_straddle hU hMX he hexp hf₃₄ hAB hcd hf₃A hf₄B
  ext g
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, flipBoundary,
    Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hgσ
    by_cases hgB : g ⊆ B
    · -- g ⊆ B: g ∈ σ₂.erase f₄
      left
      have hgshared : g ∉ sharedFaces M e := fun hc => (hstraddle g hc).2 hgB
      have hgne4 : g ≠ f₄ := fun hc => hf₄notσ (hc ▸ hgσ)
      exact ⟨hgne4, Or.inl ⟨hgσ, hgshared⟩, hgB⟩
    · -- ¬ g ⊆ B: g ∈ K₂
      right; exact ⟨hgσ, hgB⟩
  · rintro (⟨hgne4, hgflip, hgB⟩ | ⟨hgσ, _⟩)
    · -- g ∈ σ₂.erase f₄ ⟹ g ∈ σ
      rcases hgflip with ⟨hgσ, _⟩ | hgexp
      · exact hgσ
      · -- g ∈ {f₃, f₄}: f₄ excluded by hgne4; f₃ excluded by g ⊆ B vs ¬ f₃ ⊆ B
        rw [hexp, Finset.mem_insert, Finset.mem_singleton] at hgexp
        rcases hgexp with hgf₃ | hgf₄
        · exact absurd (hgf₃ ▸ hgB) hf₃notB
        · exact absurd hgf₄ hgne4
    · exact hgσ

/-- **Side reconstruction of `σ` (A-side).** Symmetric to
`flipEdgePresent_side_reconstruct`, with `f₃` and `A`. -/
theorem flipEdgePresent_side_reconstruct_left {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) (hAB : A ∩ B = f₃ ∩ f₄) (hcd : (f₃ ∩ f₄).card = 2)
    (hf₃flip : f₃ ∈ flipBoundary σ M e) (hf₃notB : ¬ f₃ ⊆ B) (hf₃A : f₃ ⊆ A)
    (hf₄notA : ¬ f₄ ⊆ A) (hf₄B : f₄ ⊆ B) :
    σ = ((flipBoundary σ M e).filter (fun f => f ⊆ A)).erase f₃ ∪
      σ.filter (fun f => ¬ f ⊆ A) := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hsh_eq : sharedFaces M e = tetFaces e ∩ σ := by simp only [sharedFaces, hUb.1]
  have hshared_sub : sharedFaces M e ⊆ σ := by rw [hsh_eq]; exact Finset.inter_subset_right
  have hf₃notσ : f₃ ∉ σ := by
    have hmem : f₃ ∈ exposedFaces M e := by
      rw [hexp]; exact Finset.mem_insert_self f₃ _
    rw [exposedFaces, hsh_eq, Finset.mem_sdiff, Finset.mem_inter] at hmem
    intro hf₃σ
    exact hmem.2 ⟨hmem.1, hf₃σ⟩
  have hstraddle := sharedFaces_straddle hU hMX he hexp hf₃₄ hAB hcd hf₃A hf₄B
  ext g
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, flipBoundary,
    Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hgσ
    by_cases hgA : g ⊆ A
    · left
      have hgshared : g ∉ sharedFaces M e := fun hc => (hstraddle g hc).1 hgA
      have hgne3 : g ≠ f₃ := fun hc => hf₃notσ (hc ▸ hgσ)
      exact ⟨hgne3, Or.inl ⟨hgσ, hgshared⟩, hgA⟩
    · right; exact ⟨hgσ, hgA⟩
  · rintro (⟨hgne3, hgflip, hgA⟩ | ⟨hgσ, _⟩)
    · rcases hgflip with ⟨hgσ, _⟩ | hgexp
      · exact hgσ
      · rw [hexp, Finset.mem_insert, Finset.mem_singleton] at hgexp
        rcases hgexp with hgf₃ | hgf₄
        · exact absurd hgf₃ hgne3
        · exact absurd (hgf₄ ▸ hgA) hf₄notA
    · exact hgσ

/-- **Bridge glue onto the A-side.** Gluing the eligible tet `e` onto the A-side
flip boundary `σ₁ = flipBoundary.filter(⊆A)` is a `GlueStep`: `e` shares exactly the
single A-exposed face `f₃` with `σ₁`, and the resulting boundary is
`insert f₄ (σ.filter(¬·⊆B))` — the B-exposed face together with the σ-faces that are
not B-side. The two shared faces of `e` straddle the cut (so they survive in
`σ.filter(¬·⊆B)` but are absent from `σ₁`). -/
theorem glueStep_bridge_left {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hAB : A ∩ B = f₃ ∩ f₄) (hcd : (f₃ ∩ f₄).card = 2)
    (hf₃A : f₃ ⊆ A) (hf₃notB : ¬ f₃ ⊆ B) (hf₄B : f₄ ⊆ B) (hf₄notA : ¬ f₄ ⊆ A)
    (hcover : ∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B) :
    GlueStep e ((flipBoundary σ M e).filter (fun f => f ⊆ A))
      (insert f₄ (σ.filter (fun f => ¬ f ⊆ B))) := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hsh_eq : sharedFaces M e = tetFaces e ∩ σ := by simp only [sharedFaces, hUb.1]
  have hexp_mem : ∀ x, x ∈ exposedFaces M e ↔ (x ∈ tetFaces e ∧ x ∉ σ) := by
    intro x; simp only [exposedFaces, hsh_eq, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hstraddle := sharedFaces_straddle hU hMX he hexp hf₃₄ hAB hcd hf₃A hf₄B
  have hshared_sub : sharedFaces M e ⊆ σ := by
    rw [hsh_eq]; exact Finset.inter_subset_right
  have hf₃exp : f₃ ∈ exposedFaces M e := by rw [hexp]; exact Finset.mem_insert_self f₃ _
  have hf₄exp : f₄ ∈ exposedFaces M e := by
    rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
  have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃exp
  have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄exp
  have hf₃notσ : f₃ ∉ σ := ((hexp_mem f₃).mp hf₃exp).2
  have hf₄notσ : f₄ ∉ σ := ((hexp_mem f₄).mp hf₄exp).2
  -- Faces of `e` are the shared faces together with `{f₃, f₄}`.
  have htetFaces : ∀ x ∈ tetFaces e, x ∈ sharedFaces M e ∨ x = f₃ ∨ x = f₄ := by
    intro x hx
    by_cases hxσ : x ∈ σ
    · exact Or.inl (by rw [hsh_eq]; exact Finset.mem_inter.mpr ⟨hx, hxσ⟩)
    · have : x ∈ exposedFaces M e := (hexp_mem x).mpr ⟨hx, hxσ⟩
      rw [hexp, Finset.mem_insert, Finset.mem_singleton] at this
      exact Or.inr this
  refine ⟨he.1, ?_, ?_⟩
  · -- shared: tetFaces e ∩ σ₁ = {f₃}, card 1.
    left
    have heq : tetFaces e ∩ (flipBoundary σ M e).filter (fun f => f ⊆ A) = {f₃} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hxtet, hxflip, hxA⟩
        rcases htetFaces x hxtet with hxsh | hxf₃ | hxf₄
        · exact absurd hxA (hstraddle x hxsh).1
        · exact hxf₃
        · exact absurd (hxf₄ ▸ hxA) hf₄notA
      · rintro rfl
        refine ⟨hf₃tet, ?_, hf₃A⟩
        simp only [flipBoundary, Finset.mem_union]; right; rw [hexp]
        exact Finset.mem_insert_self _ _
    rw [heq, Finset.card_singleton]
  · -- newBdry: insert f₄ K₂ = (σ₁ \ tetFaces e) ∪ (tetFaces e \ σ₁).
    -- Membership characterizations (kept folded to avoid fragile simp normal forms).
    have hmemflip : ∀ g, g ∈ flipBoundary σ M e ↔ (g ∈ σ ∧ g ∉ sharedFaces M e) ∨
        g = f₃ ∨ g = f₄ := by
      intro g
      simp only [flipBoundary, Finset.mem_union, Finset.mem_sdiff, hexp, Finset.mem_insert,
        Finset.mem_singleton]
    have hmemσ₁ : ∀ g, g ∈ (flipBoundary σ M e).filter (fun f => f ⊆ A) ↔
        ((g ∈ σ ∧ g ∉ sharedFaces M e) ∨ g = f₃ ∨ g = f₄) ∧ g ⊆ A := by
      intro g; rw [Finset.mem_filter, hmemflip]
    have hf₃σ₁ : f₃ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ A) :=
      (hmemσ₁ f₃).mpr ⟨Or.inr (Or.inl rfl), hf₃A⟩
    ext g
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_sdiff, hmemσ₁ g]
    constructor
    · rintro (rfl | ⟨hgσ, hgnotB⟩)
      · -- g = f₄: f₄ ∈ tetFaces e, f₄ ∉ σ₁ (¬ f₄ ⊆ A)
        right
        refine ⟨hf₄tet, ?_⟩
        rintro ⟨_, hf₄A⟩; exact hf₄notA hf₄A
      · -- g ∈ σ, ¬ g ⊆ B
        by_cases hgtet : g ∈ tetFaces e
        · -- g a face of e: shared (straddle ⟹ ¬⊆A ⟹ ∉σ₁); f₃,f₄ ∉ σ — but g ∈ σ
          right
          refine ⟨hgtet, ?_⟩
          rcases htetFaces g hgtet with hgsh | hgf₃ | hgf₄
          · rintro ⟨_, hgA⟩; exact (hstraddle g hgsh).1 hgA
          · exact absurd (hgf₃ ▸ hgσ) hf₃notσ
          · exact absurd (hgf₄ ▸ hgσ) hf₄notσ
        · -- g ∉ tetFaces e: g ∈ σ \ shared, and g ⊆ A (¬⊆B + cover); left branch
          left
          have hgnotsh : g ∉ sharedFaces M e := fun hc => hgtet (sharedFaces_subset_tetFaces M e hc)
          have hgflip : g ∈ flipBoundary σ M e := (hmemflip g).mpr (Or.inl ⟨hgσ, hgnotsh⟩)
          have hgA : g ⊆ A := (hcover g hgflip).resolve_right hgnotB
          exact ⟨⟨Or.inl ⟨hgσ, hgnotsh⟩, hgA⟩, hgtet⟩
    · rintro (⟨⟨hgflip, hgA⟩, hgtet⟩ | ⟨hgtet, hgnotσ₁⟩)
      · -- g ∈ σ₁ \ tetFaces e: g ∈ σ (flip-disjunct, f₃/f₄ ruled out by ∉ tetFaces), ¬ g ⊆ B
        right
        have hgσ : g ∈ σ := by
          rcases hgflip with ⟨hgσ, _⟩ | hgf₃ | hgf₄
          · exact hgσ
          · exact absurd (hgf₃ ▸ hf₃tet) hgtet
          · exact absurd (hgf₄ ▸ hf₄tet) hgtet
        have hgnotB : ¬ g ⊆ B := by
          intro hgB
          have hsub : g ⊆ A ∩ B := Finset.subset_inter hgA hgB
          have hgc : g.card ≤ (A ∩ B).card := Finset.card_le_card hsub
          rw [hAB, hcd] at hgc
          have hg3 : g.card = 3 := hσ.pure g hgσ
          omega
        exact ⟨hgσ, hgnotB⟩
      · -- g ∈ tetFaces e \ σ₁: shared (⟹ g ∈ K₂) or f₃ (∈ σ₁, contra) or f₄ (left).
        rcases htetFaces g hgtet with hgsh | hgf₃ | hgf₄
        · right; exact ⟨hshared_sub hgsh, (hstraddle g hgsh).2⟩
        · exact absurd (hgf₃ ▸ (hmemσ₁ f₃).mp hf₃σ₁) hgnotσ₁
        · left; exact hgf₄

/-- **Bridge glue onto the B-side.** Mirror of `glueStep_bridge_left` with the two
sides (and the two exposed faces) swapped. -/
theorem glueStep_bridge_right {σ : Finset (Finset V)} {X M : Chain V}
    {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hAB : A ∩ B = f₃ ∩ f₄) (hcd : (f₃ ∩ f₄).card = 2)
    (hf₃A : f₃ ⊆ A) (hf₃notB : ¬ f₃ ⊆ B) (hf₄B : f₄ ⊆ B) (hf₄notA : ¬ f₄ ⊆ A)
    (hcover : ∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B) :
    GlueStep e ((flipBoundary σ M e).filter (fun f => f ⊆ B))
      (insert f₃ (σ.filter (fun f => ¬ f ⊆ A))) := by
  refine glueStep_bridge_left (f₃ := f₄) (f₄ := f₃) (A := B) (B := A)
    hσ hU hXc hMX hT hS he ?_ (Ne.symm hf₃₄) ?_ ?_ hf₄B hf₄notA hf₃A hf₃notB ?_
  · rw [hexp]; exact Finset.pair_comm f₃ f₄
  · rw [Finset.inter_comm, hAB, Finset.inter_comm]
  · rw [Finset.inter_comm]; exact hcd
  · intro f hf; exact (hcover f hf).symm

/-- **Case-2 edge split, bridge shellings.** After gluing `e` onto either
spherical side, the other side shelling transports through the disjoint ambient
boundary. The coverage and exact-side separation hypotheses rule out degenerate
choices of `A,B` that do not partition the post-removal support. Intended proof
ingredients: `GlueStep.union_disjoint` and `ShellFrom_union_disjoint`. -/
theorem flipEdgePresent_side_bridge
    {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ A B : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    (hAB : A ∩ B = f₃ ∩ f₄)
    (hcd : (f₃ ∩ f₄).card = 2)
    (hsphere₁ : IsSphere2 ((flipBoundary σ M e).filter (fun f => f ⊆ A)))
    (hsphere₂ : IsSphere2 ((flipBoundary σ M e).filter (fun f => f ⊆ B)))
    (hfree₁ :
      FreelyShellable ((removeTet M e).filter (fun t => t ⊆ A)).support
        ((flipBoundary σ M e).filter (fun f => f ⊆ A)))
    (hfree₂ :
      FreelyShellable ((removeTet M e).filter (fun t => t ⊆ B)).support
        ((flipBoundary σ M e).filter (fun f => f ⊆ B)))
    (hf₃A : f₃ ⊆ A)
    (hf₃notB : ¬ f₃ ⊆ B)
    (hf₄B : f₄ ⊆ B)
    (hf₄notA : ¬ f₄ ⊆ A)
    (hcover : ∀ t ∈ (removeTet M e).support, t ⊆ A ∨ t ⊆ B)
    (hsep : ∀ t ∈ (removeTet M e).support,
      (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A))
    (huniq₂ : ∃! t, t ∈ ((removeTet M e).filter (fun t => t ⊆ B)).support ∧ f₄ ⊆ t)
    (huniq₁ : ∃! t, t ∈ ((removeTet M e).filter (fun t => t ⊆ A)).support ∧ f₃ ⊆ t)
    (hrecon₂ : σ = ((flipBoundary σ M e).filter (fun f => f ⊆ B)).erase f₄ ∪
      σ.filter (fun f => ¬ f ⊆ B))
    (hrecon₁ : σ = ((flipBoundary σ M e).filter (fun f => f ⊆ A)).erase f₃ ∪
      σ.filter (fun f => ¬ f ⊆ A))
    (hfaceCover : ∀ f ∈ flipBoundary σ M e, f ⊆ A ∨ f ⊆ B) :
    ∃ Bmid₁₂ Bmid₂₁ : Finset (Finset V),
      GlueStep e ((flipBoundary σ M e).filter (fun f => f ⊆ A)) Bmid₁₂ ∧
      GlueStep e ((flipBoundary σ M e).filter (fun f => f ⊆ B)) Bmid₂₁ ∧
      RelShelling ((removeTet M e).filter (fun t => t ⊆ B)).support Bmid₁₂ σ ∧
      RelShelling ((removeTet M e).filter (fun t => t ⊆ A)).support Bmid₂₁ σ := by
  classical
  -- Abbreviations matching the Codex recipe.
  set σ₁ := (flipBoundary σ M e).filter (fun f => f ⊆ A) with hσ₁def
  set σ₂ := (flipBoundary σ M e).filter (fun f => f ⊆ B) with hσ₂def
  set K₂ := σ.filter (fun f => ¬ f ⊆ B) with hK₂def
  set K₁ := σ.filter (fun f => ¬ f ⊆ A) with hK₁def
  refine ⟨insert f₄ K₂, insert f₃ K₁, ?_, ?_, ?_, ?_⟩
  · -- glue₁₂ : GlueStep e σ₁ (insert f₄ K₂)
    rw [hσ₁def, hK₂def]
    exact glueStep_bridge_left hσ hU hXc hMX hT hS he hexp hf₃₄ hAB hcd hf₃A hf₃notB hf₄B
      hf₄notA hfaceCover
  · -- glue₂₁ : GlueStep e σ₂ (insert f₃ K₁)
    rw [hσ₂def, hK₁def]
    exact glueStep_bridge_right hσ hU hXc hMX hT hS he hexp hf₃₄ hAB hcd hf₃A hf₃notB hf₄B
      hf₄notA hfaceCover
  · -- rel₂_over₁ : RelShelling side₂.support (insert f₄ K₂) σ
    refine FreelyShellable.relShelling_over_insert_boundary_face hfree₂ ?_ huniq₂ ?_ hrecon₂
    · -- f₄.card = 3
      have hf₄mem : f₄ ∈ exposedFaces M e := by
        rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
      have hf₄tet : f₄ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₄mem
      exact (Finset.mem_powersetCard.mp hf₄tet).2
    · -- hKdisj : every side₂ tet's faces avoid K₂
      intro t ht
      rw [Finset.disjoint_left]
      intro g hgT hgK
      -- g ⊆ t (face of t), t ⊆ B (side₂), so g ⊆ B; but g ∈ K₂ means ¬ g ⊆ B
      have htB : t ⊆ B := by
        rw [Finsupp.support_filter, Finset.mem_filter] at ht; exact ht.2
      have hgt : g ⊆ t := (Finset.mem_powersetCard.mp hgT).1
      have hgB : g ⊆ B := hgt.trans htB
      have hgnotB : ¬ g ⊆ B := by
        rw [hK₂def, Finset.mem_filter] at hgK; exact hgK.2
      exact hgnotB hgB
  · -- rel₁_over₂ : RelShelling side₁.support (insert f₃ K₁) σ
    refine FreelyShellable.relShelling_over_insert_boundary_face hfree₁ ?_ huniq₁ ?_ hrecon₁
    · -- f₃.card = 3
      have hf₃mem : f₃ ∈ exposedFaces M e := by
        rw [hexp]; exact Finset.mem_insert_self f₃ _
      have hf₃tet : f₃ ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf₃mem
      exact (Finset.mem_powersetCard.mp hf₃tet).2
    · -- hKdisj : every side₁ tet's faces avoid K₁
      intro t ht
      rw [Finset.disjoint_left]
      intro g hgT hgK
      have htA : t ⊆ A := by
        rw [Finsupp.support_filter, Finset.mem_filter] at ht; exact ht.2
      have hgt : g ⊆ t := (Finset.mem_powersetCard.mp hgT).1
      have hgA : g ⊆ A := hgt.trans htA
      have hgnotA : ¬ g ⊆ A := by
        rw [hK₁def, Finset.mem_filter] at hgK; exact hgK.2
      exact hgnotA hgA

/-- The single genuine case-2 geometry target.

Given an eligible tet whose exposed faces are `f₃,f₄` and whose flip edge
`f₃ ∩ f₄` is already present in the original sphere, produce the two side
vertex sets `A,B`, the filtered smaller taut fillings, the two spherical side
boundaries, the support decomposition, and the symmetric bridge shellings. -/
noncomputable def flipEdgePresent_side_data
    {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    (IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M →
      IsSphere2 σ' → UnitOn X' σ' → bdry X' = 0 → bdry M' = X' →
      IsTaut M' → SimplicialChain M' → FreelyShellable M'.support σ') :
    PrimeFlipEdgeSplitFreePackage σ X M e f₃ f₄ := by
  classical
  let hsets := flipEdgePresent_side_sets hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
  let A := Classical.choose hsets
  let hsetsB := Classical.choose_spec hsets
  let B := Classical.choose hsetsB
  let hside := Classical.choose_spec hsetsB
  rcases hside with
    ⟨hAB, hcd, hsphere₁, hsphere₂, hcover, hsep, hf₃A, hf₃notB, hf₄B, hf₄notA, hfaceCover⟩
  have halg :=
    flipEdgePresent_side_algebra hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip hAB hcd
      hcover hsep
  have hunit₁ := halg.1
  have hunit₂ := halg.2.1
  have hclosed₁ := halg.2.2.1
  have hclosed₂ := halg.2.2.2.1
  have htaut₁ := halg.2.2.2.2.1
  have htaut₂ := halg.2.2.2.2.2.1
  have hsimp₁ := halg.2.2.2.2.2.2.1
  have hsimp₂ := halg.2.2.2.2.2.2.2.1
  have hsmaller₁ := halg.2.2.2.2.2.2.2.2.1
  have hsmaller₂ := halg.2.2.2.2.2.2.2.2.2.1
  have he_not₁ := halg.2.2.2.2.2.2.2.2.2.2.1
  have he_not₂ := halg.2.2.2.2.2.2.2.2.2.2.2.1
  have hdisj := halg.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsupport := halg.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hfree₁ :
      FreelyShellable ((removeTet M e).filter (fun t => t ⊆ A)).support
        ((flipBoundary σ M e).filter (fun f => f ⊆ A)) :=
    IH _ (bdry ((removeTet M e).filter (fun t => t ⊆ A)))
      ((removeTet M e).filter (fun t => t ⊆ A))
      hsmaller₁ hsphere₁ hunit₁ hclosed₁ rfl htaut₁ hsimp₁
  have hfree₂ :
      FreelyShellable ((removeTet M e).filter (fun t => t ⊆ B)).support
        ((flipBoundary σ M e).filter (fun f => f ⊆ B)) :=
    IH _ (bdry ((removeTet M e).filter (fun t => t ⊆ B)))
      ((removeTet M e).filter (fun t => t ⊆ B))
      hsmaller₂ hsphere₂ hunit₂ hclosed₂ rfl htaut₂ hsimp₂
  -- Discharge the four bridge hypotheses (uniqueness of the consuming tet on each
  -- side, and the side-reconstruction of `σ`).
  have hf₃card : f₃.card = 3 := by
    have hmem : f₃ ∈ exposedFaces M e := by
      rw [hexp]; exact Finset.mem_insert_self f₃ _
    exact (Finset.mem_powersetCard.mp (exposedFaces_subset_tetFaces M e hmem)).2
  have hf₄card : f₄.card = 3 := by
    have hmem : f₄ ∈ exposedFaces M e := by
      rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
    exact (Finset.mem_powersetCard.mp (exposedFaces_subset_tetFaces M e hmem)).2
  have hf₃flip : f₃ ∈ flipBoundary σ M e := by
    simp only [flipBoundary, Finset.mem_union]; right; rw [hexp]
    exact Finset.mem_insert_self f₃ _
  have hf₄flip : f₄ ∈ flipBoundary σ M e := by
    simp only [flipBoundary, Finset.mem_union]; right; rw [hexp]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
  have huniq₂ : ∃! t, t ∈ ((removeTet M e).filter (fun t => t ⊆ B)).support ∧ f₄ ⊆ t := by
    have hPM₂ : IsPseudomanifold ((removeTet M e).filter (fun t => t ⊆ B)).support :=
      taut_isPseudomanifold hsphere₂ hunit₂ hclosed₂ rfl htaut₂ hsimp₂
    have hpure₂ : ∀ t ∈ ((removeTet M e).filter (fun t => t ⊆ B)).support, t.card = 4 :=
      fun t ht => (aleph_base_taut_support_card4_subset_verts hsphere₂ hunit₂ rfl htaut₂ t ht).1
    have hf₄σ₂ : f₄ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ B) :=
      Finset.mem_filter.mpr ⟨hf₄flip, hf₄B⟩
    have hbd₂ : bdry ((removeTet M e).filter (fun t => t ⊆ B)) f₄ = 1 ∨
        bdry ((removeTet M e).filter (fun t => t ⊆ B)) f₄ = -1 := hunit₂.2 f₄ hf₄σ₂
    have hfc : faceCount ((removeTet M e).filter (fun t => t ⊆ B)).support f₄ = 1 :=
      faceCount_eq_one_of_boundary hsimp₂ hpure₂ hPM₂ hf₄card hbd₂
    rw [faceCount, Finset.card_eq_one] at hfc
    obtain ⟨t₀, ht₀⟩ := hfc
    refine ⟨t₀, ?_, ?_⟩
    · have : t₀ ∈ ((removeTet M e).filter (fun t => t ⊆ B)).support.filter (fun t => f₄ ⊆ t) := by
        rw [ht₀]; exact Finset.mem_singleton_self t₀
      rw [Finset.mem_filter] at this; exact this
    · intro y hy
      have : y ∈ ((removeTet M e).filter (fun t => t ⊆ B)).support.filter (fun t => f₄ ⊆ t) :=
        Finset.mem_filter.mpr hy
      rw [ht₀, Finset.mem_singleton] at this; exact this
  have huniq₁ : ∃! t, t ∈ ((removeTet M e).filter (fun t => t ⊆ A)).support ∧ f₃ ⊆ t := by
    have hPM₁ : IsPseudomanifold ((removeTet M e).filter (fun t => t ⊆ A)).support :=
      taut_isPseudomanifold hsphere₁ hunit₁ hclosed₁ rfl htaut₁ hsimp₁
    have hpure₁ : ∀ t ∈ ((removeTet M e).filter (fun t => t ⊆ A)).support, t.card = 4 :=
      fun t ht => (aleph_base_taut_support_card4_subset_verts hsphere₁ hunit₁ rfl htaut₁ t ht).1
    have hf₃σ₁ : f₃ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ A) :=
      Finset.mem_filter.mpr ⟨hf₃flip, hf₃A⟩
    have hbd₁ : bdry ((removeTet M e).filter (fun t => t ⊆ A)) f₃ = 1 ∨
        bdry ((removeTet M e).filter (fun t => t ⊆ A)) f₃ = -1 := hunit₁.2 f₃ hf₃σ₁
    have hfc : faceCount ((removeTet M e).filter (fun t => t ⊆ A)).support f₃ = 1 :=
      faceCount_eq_one_of_boundary hsimp₁ hpure₁ hPM₁ hf₃card hbd₁
    rw [faceCount, Finset.card_eq_one] at hfc
    obtain ⟨t₀, ht₀⟩ := hfc
    refine ⟨t₀, ?_, ?_⟩
    · have : t₀ ∈ ((removeTet M e).filter (fun t => t ⊆ A)).support.filter (fun t => f₃ ⊆ t) := by
        rw [ht₀]; exact Finset.mem_singleton_self t₀
      rw [Finset.mem_filter] at this; exact this
    · intro y hy
      have : y ∈ ((removeTet M e).filter (fun t => t ⊆ A)).support.filter (fun t => f₃ ⊆ t) :=
        Finset.mem_filter.mpr hy
      rw [ht₀, Finset.mem_singleton] at this; exact this
  have hrecon₂ : σ = ((flipBoundary σ M e).filter (fun f => f ⊆ B)).erase f₄ ∪
      σ.filter (fun f => ¬ f ⊆ B) :=
    flipEdgePresent_side_reconstruct hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip hAB hcd
      hf₄flip hf₄notA hf₄B hf₃A hf₃notB
  have hrecon₁ : σ = ((flipBoundary σ M e).filter (fun f => f ⊆ A)).erase f₃ ∪
      σ.filter (fun f => ¬ f ⊆ A) :=
    flipEdgePresent_side_reconstruct_left hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip hAB hcd
      hf₃flip hf₃notB hf₃A hf₄notA hf₄B
  let hbridge := flipEdgePresent_side_bridge hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
    hAB hcd hsphere₁ hsphere₂ hfree₁ hfree₂ hf₃A hf₃notB hf₄B hf₄notA hcover hsep
    huniq₂ huniq₁ hrecon₂ hrecon₁ hfaceCover
  let Bmid₁₂ := Classical.choose hbridge
  let hbridge₂ := Classical.choose_spec hbridge
  let Bmid₂₁ := Classical.choose hbridge₂
  let hbridge_props := Classical.choose_spec hbridge₂
  have hglue₁₂ := hbridge_props.1
  have hglue₂₁ := hbridge_props.2.1
  have hrel₂_over₁ := hbridge_props.2.2.1
  have hrel₁_over₂ := hbridge_props.2.2.2
  exact
    { A := A
      B := B
      σ₁ := (flipBoundary σ M e).filter (fun f => f ⊆ A)
      σ₂ := (flipBoundary σ M e).filter (fun f => f ⊆ B)
      M₁ := (removeTet M e).filter (fun t => t ⊆ A)
      M₂ := (removeTet M e).filter (fun t => t ⊆ B)
      Bmid₁₂ := Bmid₁₂
      Bmid₂₁ := Bmid₂₁
      cd_eq := hAB
      cd_card := hcd
      σ₁_eq := rfl
      σ₂_eq := rfl
      M₁_eq := rfl
      M₂_eq := rfl
      sphere₁ := hsphere₁
      sphere₂ := hsphere₂
      unit₁ := hunit₁
      unit₂ := hunit₂
      closed₁ := hclosed₁
      closed₂ := hclosed₂
      taut₁ := htaut₁
      taut₂ := htaut₂
      simp₁ := hsimp₁
      simp₂ := hsimp₂
      smaller₁ := hsmaller₁
      smaller₂ := hsmaller₂
      e_not₁ := he_not₁
      e_not₂ := he_not₂
      side_coverage := hcover
      side_separation := hsep
      disjoint_supports := hdisj
      support_decomp := hsupport
      glue₁₂ := hglue₁₂
      glue₂₁ := hglue₂₁
      rel₂_over₁ := hrel₂_over₁
      rel₁_over₂ := hrel₁_over₂ }

/-- The public case-2 package theorem is only a named reduction to the clean
AlephProver target `flipEdgePresent_side_data`. -/
noncomputable def prime_flipEdge_split_free_package
    {σ : Finset (Finset V)} {X M : Chain V} {e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ)
    (hU : UnitOn X σ)
    (hXc : bdry X = 0)
    (hMX : bdry M = X)
    (hT : IsTaut M)
    (hS : SimplicialChain M)
    (he : EligibleTet M e)
    (hexp : exposedFaces M e = {f₃, f₄})
    (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄)
    (IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M →
      IsSphere2 σ' → UnitOn X' σ' → bdry X' = 0 → bdry M' = X' →
      IsTaut M' → SimplicialChain M' → FreelyShellable M'.support σ') :
    PrimeFlipEdgeSplitFreePackage σ X M e f₃ f₄ :=
  flipEdgePresent_side_data hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip IH

/-- **Prime step, case 1 (no flip edge), per target.** -/
theorem exists_shelling_prime_case1 {σ : Finset (Finset V)} {X M : Chain V}
    {s e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M)
    (IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      FreelyShellable M'.support σ')
    (he : EligibleTet M e) (hne_es : e ≠ s) (hs : s ∈ M.support)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hFlip : ¬ FlipEdgePresent σ f₃ f₄) :
    ∃ l : List (Finset V), l.head? = some s ∧ l.toFinset = M.support ∧ l.Nodup ∧
      IsShelling l σ := by
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hs_old : s ∈ (removeTet M e).support := by
    rw [support_removeTet_of_mem he.2.1]
    exact Finset.mem_erase.mpr ⟨Ne.symm hne_es, hs⟩
  have he_not_old : e ∉ (removeTet M e).support := by
    rw [support_removeTet_of_mem he.2.1]; simp
  have hσe : IsSphere2 ((σ \ sharedFaces M e) ∪ exposedFaces M e) :=
    isSphere2_flipBoundary_of_eligible hσ hUb hS he hexp hf₃₄ hFlip
  have hUe : UnitOn (bdry (removeTet M e)) ((σ \ sharedFaces M e) ∪ exposedFaces M e) :=
    unitOn_flipBoundary_of_eligible hUb hS he
  have hTe : IsTaut (removeTet M e) := isTaut_removeTet hT
  have hSe : SimplicialChain (removeTet M e) := simplicialChain_removeTet hS
  have hlt : nrm (removeTet M e) < nrm M := by
    have h := nrm_removeTet_add_one_of_simplicial hS he.2.1; omega
  have hfree_e : FreelyShellable (removeTet M e).support
      ((σ \ sharedFaces M e) ∪ exposedFaces M e) :=
    IH _ (bdry (removeTet M e)) (removeTet M e) hlt hσe hUe (bdry_bdry _) rfl hTe hSe
  have hg : GlueStep e ((σ \ sharedFaces M e) ∪ exposedFaces M e) σ :=
    glueStep_flipBoundary_of_eligible hUb he
  obtain ⟨l, hhead, hfin, hnodup, hsh⟩ :=
    FreelyShellable.exists_shelling_insert_of_glueStep_old hfree_e hg he_not_old hs_old
  refine ⟨l, hhead, ?_, hnodup, hsh⟩
  rw [hfin, support_removeTet_of_mem he.2.1, Finset.insert_erase he.2.1]

set_option maxHeartbeats 800000 in
/-- **Prime step, case 2 (flip edge present), per target.** When the flipped edge
`cd = f₃ ∩ f₄` is already present, removing `e` splits the configuration along `cd`
into two strictly smaller taut fillings bridged through `e`; the free shelling from
`s` concatenates the side containing `s` (free by IH), `[e]`, and the transported
other side (`PrimeFlipEdgeSplitFreePackage` + `ShellFrom_union_disjoint`).  Geometry
to be supplied (`prime_flipEdge_split_free_package` / `flipEdgePresent_side_data`). -/
theorem exists_shelling_prime_case2 {σ : Finset (Finset V)} {X M : Chain V}
    {s e f₃ f₄ : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M)
    (IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      FreelyShellable M'.support σ')
    (he : EligibleTet M e) (hne_es : e ≠ s) (hs : s ∈ M.support)
    (hexp : exposedFaces M e = {f₃, f₄}) (hf₃₄ : f₃ ≠ f₄)
    (hFlip : FlipEdgePresent σ f₃ f₄) :
    ∃ l : List (Finset V), l.head? = some s ∧ l.toFinset = M.support ∧ l.Nodup ∧
      IsShelling l σ := by
  classical
  let P := prime_flipEdge_split_free_package hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip IH
  have hsP : s ∈ insert e (P.M₁.support ∪ P.M₂.support) := by
    rw [← P.support_decomp]
    exact hs
  have hs12 : s ∈ P.M₁.support ∪ P.M₂.support := by
    rw [Finset.mem_insert] at hsP
    rcases hsP with hse | hs12
    · exact False.elim (hne_es hse.symm)
    · exact hs12
  rw [Finset.mem_union] at hs12
  rcases hs12 with hs₁ | hs₂
  · have hfree₁ : FreelyShellable P.M₁.support P.σ₁ :=
      IH _ (bdry P.M₁) P.M₁ P.smaller₁ P.sphere₁ P.unit₁ P.closed₁ rfl P.taut₁ P.simp₁
    obtain ⟨l₁, hhead₁, hfin₁, hnodup₁, hsh₁⟩ := hfree₁ s hs₁
    obtain ⟨l₂, hfin₂, hnodup₂, hsf₂⟩ := P.rel₂_over₁
    refine ⟨(l₁ ++ [e]) ++ l₂, ?_, ?_, ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil]
      · rw [List.head?_append_of_ne_nil]
        · exact hhead₁
        · intro hnil
          rw [hnil] at hhead₁
          simp at hhead₁
      · simp
    · rw [List.toFinset_append, List.toFinset_append, hfin₁, hfin₂, P.support_decomp]
      ext t
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_singleton]
      tauto
    · have hel₁ : e ∉ l₁ := fun he_l₁ => P.e_not₁ (hfin₁ ▸ List.mem_toFinset.mpr he_l₁)
      have hel₂ : e ∉ l₂ := fun he_l₂ => P.e_not₂ (hfin₂ ▸ List.mem_toFinset.mpr he_l₂)
      have hdl : l₁.Disjoint l₂ := by
        intro t ht₁ ht₂
        exact Finset.disjoint_left.mp P.disjoint_supports
          (hfin₁ ▸ List.mem_toFinset.mpr ht₁) (hfin₂ ▸ List.mem_toFinset.mpr ht₂)
      refine (hnodup₁.append (List.nodup_singleton e) ?_).append hnodup₂ ?_
      · rw [List.disjoint_left]
        intro t ht
        simp only [List.mem_singleton]
        rintro rfl
        exact hel₁ ht
      · rw [List.disjoint_left]
        intro t ht
        rw [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht₁ | rfl
        · exact List.disjoint_left.mp hdl ht₁
        · exact hel₂
    · exact IsShelling_append (IsShelling_snoc hsh₁ P.glue₁₂) hsf₂
  · have hfree₂ : FreelyShellable P.M₂.support P.σ₂ :=
      IH _ (bdry P.M₂) P.M₂ P.smaller₂ P.sphere₂ P.unit₂ P.closed₂ rfl P.taut₂ P.simp₂
    obtain ⟨l₂, hhead₂, hfin₂, hnodup₂, hsh₂⟩ := hfree₂ s hs₂
    obtain ⟨l₁, hfin₁, hnodup₁, hsf₁⟩ := P.rel₁_over₂
    refine ⟨(l₂ ++ [e]) ++ l₁, ?_, ?_, ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil]
      · rw [List.head?_append_of_ne_nil]
        · exact hhead₂
        · intro hnil
          rw [hnil] at hhead₂
          simp at hhead₂
      · simp
    · rw [List.toFinset_append, List.toFinset_append, hfin₂, hfin₁, P.support_decomp]
      ext t
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_singleton]
      tauto
    · have hel₂ : e ∉ l₂ := fun he_l₂ => P.e_not₂ (hfin₂ ▸ List.mem_toFinset.mpr he_l₂)
      have hel₁ : e ∉ l₁ := fun he_l₁ => P.e_not₁ (hfin₁ ▸ List.mem_toFinset.mpr he_l₁)
      have hdl : l₂.Disjoint l₁ := by
        intro t ht₂ ht₁
        exact Finset.disjoint_left.mp P.disjoint_supports
          (hfin₁ ▸ List.mem_toFinset.mpr ht₁) (hfin₂ ▸ List.mem_toFinset.mpr ht₂)
      refine (hnodup₂.append (List.nodup_singleton e) ?_).append hnodup₁ ?_
      · rw [List.disjoint_left]
        intro t ht
        simp only [List.mem_singleton]
        rintro rfl
        exact hel₂ ht
      · rw [List.disjoint_left]
        intro t ht
        rw [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht₂ | rfl
        · exact List.disjoint_left.mp hdl ht₂
        · exact hel₁
    · exact IsShelling_append (IsShelling_snoc hsh₂ P.glue₂₁) hsf₁

/-- **prime_step** (the `theorem3_core` hole): a no-degree-3 taut filling is a free
sticker ball.  Per target `s`, pick (via M25b) an eligible tet `e ≠ s` so `s` stays
old, then dispatch on whether the flipped edge is present (case 2, split) or absent
(case 1, snoc). -/
theorem prime_step_free (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hbig : 4 < (vertsOf σ).card) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hNo3 : NoDegree3Vertex σ)
    (IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      FreelyShellable M'.support σ' ∧ IsPseudomanifold M'.support) :
    FreelyShellable M.support σ ∧ IsPseudomanifold M.support := by
  classical
  refine ⟨?_, prime_isPM σ X M hσ hU hXc hMX hT hS hNo3
    (fun σ' X' M' hlt h1 h2 h3 h4 h5 h6 => (IH σ' X' M' hlt h1 h2 h3 h4 h5 h6).2)⟩
  -- the free-shelling half feeds the case helpers an `IH` projected to `FreelyShellable`
  have IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      FreelyShellable M'.support σ' :=
    fun σ' X' M' hlt h1 h2 h3 h4 h5 h6 => (IH σ' X' M' hlt h1 h2 h3 h4 h5 h6).1
  intro s hs
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hPure : ∀ t ∈ M.support, t.card = 4 :=
    fun t ht => (aleph_base_taut_support_card4_subset_verts hσ hU hMX hT t ht).1
  obtain ⟨e₁, e₂, hne12, he₁, he₂, _hdisj⟩ :=
    aleph_disjoint_eligible_pair hσ hUb hS hT hPure hNo3
  obtain ⟨e, he, hne_es⟩ : ∃ e, EligibleTet M e ∧ e ≠ s := by
    by_cases hse1 : s = e₁
    · exact ⟨e₂, he₂, by rw [hse1]; exact Ne.symm hne12⟩
    · exact ⟨e₁, he₁, fun h => hse1 h.symm⟩
  obtain ⟨f₃, f₄, hf₃₄, hexp⟩ := exposedFaces_eq_pair_of_eligible he
  by_cases hFlip : FlipEdgePresent σ f₃ f₄
  · exact exists_shelling_prime_case2 hσ hU hXc hMX hT hS IH he hne_es hs hexp hf₃₄ hFlip
  · exact exists_shelling_prime_case1 hσ hU hMX hT hS IH he hne_es hs hexp hf₃₄ hFlip

/-! ## Theorem 3 / Theorem 2 (assembled)

`theorem3_core` (the strong induction) applied to the three discharged reduction
steps `base_free`, `deg3_step_free`, `prime_step_free`. Theorem 2 (`IsBall`) is the
corollary via `FreelyShellable.isBall_of_mem` and support-nonemptiness. -/

/-- **Theorem 3**: a taut filling of a combinatorial 2-sphere is a *free* sticker
ball. -/
theorem theorem3 {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : FreelyShellable M.support σ :=
  (theorem3_core base_free deg3_step_free prime_step_free hσ hU hXc hMX hT hS).1

/-- **Theorem 2**: a taut filling of a combinatorial 2-sphere `σ` is a
shelling-certified ball with boundary `σ` (it arises from a triangulation of `B³`). -/
theorem theorem2 {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : IsBall M.support σ := by
  obtain ⟨t, ht⟩ := aleph_base_support_nonempty hσ hU hMX
  exact (theorem3 hσ hU hXc hMX hT hS).isBall_of_mem ht

end Taut
