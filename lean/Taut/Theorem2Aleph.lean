import Taut.Theorem23
import Taut.Degree3
import Taut.OrientedBridge

/-!
# Theorem 2 (core): two of three holes closed by Aleph Prover

`theorem2_core` (in `Taut.Theorem23`) reduces "a taut filling of a combinatorial
2-sphere is a ball" to three reduction steps. This file records machine-found
proofs (Aleph Prover, alephprover.logicalintelligence.com) of two of them —
`aleph_base` (minimal-sphere base case) and `aleph_deg3_split` (degree-3 /
connected-sum reduction) — together with M25b (`aleph_disjoint_eligible_pair`).

Provenance: the proofs and the auxiliary `aleph_*` / `degree3_*` / `cut*` lemma
names are Aleph Prover's, reproduced verbatim. Each was VERIFIED locally — it
compiles against the project's own definitions with a complete proof, reducing to
`[propext, Classical.choice, Quot.sound]`.

`theorem2_modulo_prime_step` discharges these two holes, leaving Theorem 2's core
dependent on a single remaining step `prime_step` (the no-degree-3 inductive step,
whose hard core is the M22b relative-shelling reassembly — not closed here).
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

theorem aleph_base_boundary_vert_eq {σ : Finset (Finset V)} {X M : Chain V} (hU : UnitOn X σ) (hMX : bdry M = X) :
    vert (bdry M) = vertsOf σ := by
  rw [hMX, vert, hU.1, vertsOf]

theorem aleph_base_sphere_eq_powersetCard3 {σ : Finset (Finset V)} (hσ : IsSphere2 σ) (hcard : (vertsOf σ).card = 4) :
    σ = (vertsOf σ).powersetCard 3 := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro f hf
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      exact mem_vertsOf.mpr ⟨f, hf, hx⟩
    · exact hσ.pure f hf
  · rw [Finset.card_powersetCard, hcard]
    norm_num
    have htwo := two_mul_card_verts hσ
    rw [hcard] at htwo
    omega

theorem aleph_base_support_eq_singleton_of_four_vertices {M : Chain V} {T : Finset V} (hTcard : T.card = 4)
    (hsupp : ∀ t ∈ M.support, t.card = 4 ∧ t ⊆ T)
    (hne : M.support.Nonempty) : M.support = {T} := by
  classical
  obtain ⟨u, hu⟩ := hne
  have huT : u = T := by
    have hprops := hsupp u hu
    exact Finset.eq_of_subset_of_card_le hprops.2 (by
      rw [hprops.1, hTcard])
  have hTmem : T ∈ M.support := by
    simpa [huT] using hu
  ext x
  constructor
  · intro hx
    have hprops := hsupp x hx
    have hxT : x = T := by
      exact Finset.eq_of_subset_of_card_le hprops.2 (by
        rw [hprops.1, hTcard])
    simpa [hxT]
  · intro hx
    have hxT : x = T := by
      simpa using hx
    rw [hxT]
    exact hTmem

theorem aleph_base_support_nonempty {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) : M.support.Nonempty := by
  classical
  rcases hσ.nonempty with ⟨f, hf⟩
  have hXne : X f ≠ 0 := by
    rcases hU.2 f hf with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  by_contra hnon
  rw [Finset.not_nonempty_iff_eq_empty] at hnon
  have hM0 : M = 0 := by
    exact Finsupp.support_eq_empty.mp hnon
  have hX0 : X = 0 := by
    rw [← hMX, hM0]
    simp [bdry]
  have hXf0 : X f = 0 := by
    rw [hX0]
    rfl
  exact hXne hXf0

theorem aleph_base_taut_support_card4_subset_verts {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M) :
    ∀ t ∈ M.support, t.card = 4 ∧ t ⊆ vertsOf σ := by
  intro t ht
  have hbpur : ∀ s ∈ (bdry M).support, s.card = 3 := by
    intro s hs
    have hsX : s ∈ X.support := by
      rw [hMX] at hs
      exact hs
    have hsσ : s ∈ σ := by
      simpa only [hU.1] using hsX
    exact hσ.pure s hsσ
  have hcard_all : ∀ t ∈ M.support, t.card = 3 + 1 := hT.dim_pure hbpur
  have hcard : t.card = 4 := by
    have := hcard_all t ht
    omega
  have hdim2 : ∀ t ∈ M.support, 2 ≤ t.card := by
    intro u hu
    have hu_card : u.card = 4 := by
      have := hcard_all u hu
      omega
    omega
  have hvsub : vert M ⊆ vert (bdry M) := hT.vert_subset hdim2
  have htvert : t ⊆ vert M := supp_subset_vert ht
  constructor
  · exact hcard
  · intro v hv
    have hvb : v ∈ vert (bdry M) := hvsub (htvert hv)
    rw [aleph_base_boundary_vert_eq hU hMX] at hvb
    exact hvb

theorem aleph_base_verts_card_eq_four {σ : Finset (Finset V)} (hσ : IsSphere2 σ) (hv : (vertsOf σ).card ≤ 4) :
    (vertsOf σ).card = 4 := by
  classical
  rcases hσ.nonempty with ⟨f, hf⟩
  have hfcard : f.card = 3 := hσ.pure f hf
  have hfpos : 0 < f.card := by omega
  rcases Finset.card_pos.mp hfpos with ⟨v, hvf⟩
  have hvV : v ∈ vertsOf σ := by
    exact mem_vertsOf.mpr ⟨f, hf, hvf⟩
  have hlink3 : 3 ≤ (linkVerts σ v).card := three_le_card_linkVerts hσ hvV
  have hsub : linkVerts σ v ⊆ (vertsOf σ).erase v := by
    intro x hx
    have hx' := mem_linkVerts.mp hx
    rcases hx' with ⟨hxne, g, hg, hvg, hxg⟩
    exact Finset.mem_erase.mpr ⟨hxne, mem_vertsOf.mpr ⟨g, hg, hxg⟩⟩
  have hcardle : (linkVerts σ v).card ≤ ((vertsOf σ).erase v).card := Finset.card_le_card hsub
  have herase : ((vertsOf σ).erase v).card = (vertsOf σ).card - 1 := Finset.card_erase_of_mem hvV
  have hlow : 4 ≤ (vertsOf σ).card := by omega
  omega


/-- M26 hole `base`: the minimal 2-sphere (≤ 4 vertices, i.e. a tetrahedron
boundary) has a single-tet taut filling, which is a ball. -/
theorem aleph_base (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M)
    (hv : (vertsOf σ).card ≤ 4) : IsBall M.support σ := by
  let T := vertsOf σ
  have hcard : T.card = 4 := aleph_base_verts_card_eq_four hσ hv
  have hσeq : σ = T.powersetCard 3 := aleph_base_sphere_eq_powersetCard3 hσ hcard
  have hsuppInfo : ∀ t ∈ M.support, t.card = 4 ∧ t ⊆ T := aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
  have hne : M.support.Nonempty := aleph_base_support_nonempty hσ hU hMX
  have hsupp : M.support = {T} := aleph_base_support_eq_singleton_of_four_vertices hcard hsuppInfo hne
  rw [hsupp, hσeq]
  exact isBall_singleton hcard


noncomputable def cutChain (σ : Finset (Finset V)) (W : C2 σ) (X : Chain V) : Chain V :=
  X.filter (fun f => f ∈ cutSet σ W)

noncomputable def cappedCutLeft (σ : Finset (Finset V)) (W : C2 σ) (X : Chain V)
    (γ : Finset V) (c : ℤ) : Chain V :=
  cutChain σ W X - Finsupp.single γ c

noncomputable def cappedCutRight (σ : Finset (Finset V)) (W : C2 σ) (X : Chain V)
    (γ : Finset V) (c : ℤ) : Chain V :=
  cutChain σ (W + fun _ => 1) X + Finsupp.single γ c

theorem capped_cut_splits_unit (σ : Finset (Finset V)) (X : Chain V) {γ : Finset V} {W : C2 σ}
    (hσ : IsSphere2 σ) (hγ3 : γ.card = 3) (hγe : γ.powersetCard 2 ⊆ edgesOf σ)
    (hγσ : γ ∉ σ) (hW : bd2 σ W = gammaChain σ γ) (hU : UnitOn X σ)
    (hXc : bdry X = 0) :
    ∃ c : ℤ,
      UnitOn (cappedCutLeft σ W X γ c) (insert γ (cutSet σ W)) ∧
      bdry (cappedCutLeft σ W X γ c) = 0 ∧
      UnitOn (cappedCutRight σ W X γ c) (insert γ (cutSet σ (W + fun _ => 1))) ∧
      bdry (cappedCutRight σ W X γ c) = 0 ∧
      cappedCutLeft σ W X γ c + cappedCutRight σ W X γ c = X := by
  classical
  have bdryGen_facet_natAbs : ∀ {f e : Finset V}, f.card = 3 → e.card = 2 → e ⊆ f → (bdryGen f e).natAbs = 1 := by
    intro f e hf3 he2 hef
    obtain ⟨z, hzf, hze⟩ : ∃ z ∈ f, z ∉ e := by
      by_contra hno
      push_neg at hno
      have hfsub : f ⊆ e := by intro z hz; exact hno z hz
      have := Finset.card_le_card hfsub
      omega
    have heeq : e = f.erase z := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro u hu
        exact Finset.mem_erase.mpr ⟨fun hzu => hze (hzu ▸ hu), hef hu⟩
      · rw [Finset.card_erase_of_mem hzf, hf3, he2]
    have hb : bdryGen f (f.erase z) = sgn z f := by
      rw [bdryGen, Finset.sum_apply']
      rw [Finset.sum_eq_single_of_mem z hzf]
      · rw [Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
      · intro y hy hyz
        rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hyz ((Finset.erase_inj f hy).mp h)), smul_zero]
    rw [heeq, hb, natAbs_sgn]
  have hsum : cutChain σ W X + cutChain σ (W + fun _ => 1) X = X := by
    unfold cutChain
    rw [cutSet_add_one_eq_sdiff W]
    ext s
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hs : s ∈ cutSet σ W
    · rw [if_pos hs]
      have hnot : ¬ s ∈ σ \ cutSet σ W := by intro hsd; exact (Finset.mem_sdiff.mp hsd).2 hs
      rw [if_neg hnot, add_zero]
    · rw [if_neg hs]
      by_cases hsσ : s ∈ σ
      · have hsd : s ∈ σ \ cutSet σ W := Finset.mem_sdiff.mpr ⟨hsσ, hs⟩
        rw [if_pos hsd, zero_add]
      · have hsdnot : ¬ s ∈ σ \ cutSet σ W := by intro hsd; exact hsσ (Finset.mem_sdiff.mp hsd).1
        have hXs : X s = 0 := by
          have hnotX : s ∉ X.support := by rw [hU.1]; exact hsσ
          exact Finsupp.notMem_support_iff.mp hnotX
        rw [if_neg hsdnot, zero_add, hXs]
  have hCsupp : ∀ e ∈ (bdry (cutChain σ W X)).support, e ∈ γ.powersetCard 2 := by
    intro e heSupp
    have hbe : bdry (cutChain σ W X) e ≠ 0 := Finsupp.mem_support_iff.mp heSupp
    have hbeSum : (∑ t ∈ (cutChain σ W X).support, cutChain σ W X t * bdryGen t e) ≠ 0 := by
      rwa [bdry_apply_eq_sum] at hbe
    obtain ⟨t, ht, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hbeSum
    have hgenne : bdryGen t e ≠ 0 := fun h0 => htne (by rw [h0, mul_zero])
    obtain ⟨w, hw, he_eq⟩ := exists_facet_of_bdryGen_ne_zero hgenne
    have htCut : t ∈ cutSet σ W := by rw [cutChain, Finsupp.support_filter, Finset.mem_filter] at ht; exact ht.2
    have htσ : t ∈ σ := cutSet_subset htCut
    have hcarde : e.card = 2 := by rw [he_eq, Finset.card_erase_of_mem hw, hσ.pure t htσ]
    have hsubγ : e ⊆ γ := by
      by_contra heγ
      have heEdge : e ∈ edgesOf σ := by
        refine mem_edgesOf.mpr ⟨t, htσ, ?_, hcarde⟩
        rw [he_eq]
        exact Finset.erase_subset w t
      have htW : W ⟨t, htσ⟩ = 1 := by obtain ⟨_, hWt⟩ := mem_cutSet.mp htCut; exact hWt
      have htEdgeSub : e ⊆ t := by rw [he_eq]; exact Finset.erase_subset w t
      have hvanish : ∀ s ∈ X.support, ¬ s ∈ cutSet σ W → bdryGen s e = 0 := by
        intro s hsX hsCut
        by_contra hbg
        obtain ⟨w2, hw2, hes⟩ := exists_facet_of_bdryGen_ne_zero hbg
        have hsσ : s ∈ σ := by rw [← hU.1]; exact hsX
        have hse : e ⊆ s := by rw [hes]; exact Finset.erase_subset w2 s
        have hWst : W ⟨s, hsσ⟩ = W ⟨t, htσ⟩ := W_eq_of_share_edge hσ hW heEdge heγ hse htEdgeSub
        have hsMem : s ∈ cutSet σ W := mem_cutSet.mpr ⟨hsσ, by rw [hWst, htW]⟩
        exact hsCut hsMem
      have heq := bdry_filter_apply_eq_bdry_of_no_cross (X := X) (P := fun f => f ∈ cutSet σ W) (u := e) hvanish
      have hcoeff0 : bdry (cutChain σ W X) e = 0 := by unfold cutChain; rw [heq, hXc]; rfl
      exact hbe hcoeff0
    exact Finset.mem_powersetCard.mpr ⟨hsubγ, hcarde⟩
  obtain ⟨c, hc⟩ := closed_one_chain_supported_on_triangle hγ3 (bdry_bdry _) hCsupp
  have hcpm : c = 1 ∨ c = -1 := by
    obtain ⟨a, haγ⟩ : γ.Nonempty := Finset.card_pos.mp (by rw [hγ3]; omega)
    let e0 : Finset V := γ.erase a
    have he0sub : e0 ⊆ γ := Finset.erase_subset a γ
    have he0card : e0.card = 2 := by rw [Finset.card_erase_of_mem haγ, hγ3]
    have he0pow : e0 ∈ γ.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨he0sub, he0card⟩
    have he0edge : e0 ∈ edgesOf σ := hγe he0pow
    obtain ⟨f₁, hf₁σ, f₂, hf₂σ, hne, he₁, he₂, huniq⟩ := exists_two_faces hσ.toClosedSurface he0edge
    have hpar := edge_cut_parity hW he0edge hf₁σ hf₂σ hne he₁ he₂ huniq
    rw [if_pos he0sub] at hpar
    have hone : W ⟨f₁, hf₁σ⟩ = 1 ∨ W ⟨f₂, hf₂σ⟩ = 1 := by
      have key : ∀ x y : ZMod 2, x + y = 1 → x = 1 ∨ y = 1 := by decide
      exact key _ _ hpar
    have hbdry_single_side : (bdry (cutChain σ W X) e0).natAbs = 1 := by
      rcases hone with hW1 | hW2
      · have hf₁cut : f₁ ∈ cutSet σ W := mem_cutSet.mpr ⟨hf₁σ, hW1⟩
        have hW2zero : W ⟨f₂, hf₂σ⟩ = 0 := by
          have key : ∀ x y : ZMod 2, x = 1 → x + y = 1 → y = 0 := by decide
          exact key _ _ hW1 hpar
        have hf₂not : f₂ ∉ cutSet σ W := by
          intro hcut
          obtain ⟨_, hh⟩ := mem_cutSet.mp hcut
          rw [hW2zero] at hh
          exact zero_ne_one hh
        have hval : bdry (cutChain σ W X) e0 = X f₁ * bdryGen f₁ e0 := by
          rw [bdry_apply_eq_sum]
          have hf₁X : f₁ ∈ X.support := by rw [hU.1]; exact hf₁σ
          have hf₁supp : f₁ ∈ (cutChain σ W X).support := by rw [cutChain, Finsupp.support_filter, Finset.mem_filter]; exact ⟨hf₁X, hf₁cut⟩
          rw [Finset.sum_eq_single_of_mem f₁ hf₁supp]
          · unfold cutChain; rw [Finsupp.filter_apply, if_pos hf₁cut]
          · intro t ht htne
            have htcut : t ∈ cutSet σ W := by rw [cutChain, Finsupp.support_filter, Finset.mem_filter] at ht; exact ht.2
            by_cases hgen : bdryGen t e0 = 0
            · rw [hgen, mul_zero]
            · obtain ⟨w, hw, heq⟩ := exists_facet_of_bdryGen_ne_zero hgen
              have htσ : t ∈ σ := cutSet_subset htcut
              have he0t : e0 ⊆ t := by rw [heq]; exact Finset.erase_subset w t
              rcases huniq t htσ he0t with rfl | rfl
              · exact (htne rfl).elim
              · exact (hf₂not htcut).elim
        rw [hval, Int.natAbs_mul]
        have hxabs : (X f₁).natAbs = 1 := by rcases hU.2 f₁ hf₁σ with hx | hx <;> rw [hx] <;> rfl
        rw [hxabs, bdryGen_facet_natAbs (hσ.pure f₁ hf₁σ) he0card he₁]
      · have hf₂cut : f₂ ∈ cutSet σ W := mem_cutSet.mpr ⟨hf₂σ, hW2⟩
        have hW1zero : W ⟨f₁, hf₁σ⟩ = 0 := by
          have key : ∀ x y : ZMod 2, y = 1 → x + y = 1 → x = 0 := by decide
          exact key _ _ hW2 hpar
        have hf₁not : f₁ ∉ cutSet σ W := by
          intro hcut
          obtain ⟨_, hh⟩ := mem_cutSet.mp hcut
          rw [hW1zero] at hh
          exact zero_ne_one hh
        have hval : bdry (cutChain σ W X) e0 = X f₂ * bdryGen f₂ e0 := by
          rw [bdry_apply_eq_sum]
          have hf₂X : f₂ ∈ X.support := by rw [hU.1]; exact hf₂σ
          have hf₂supp : f₂ ∈ (cutChain σ W X).support := by rw [cutChain, Finsupp.support_filter, Finset.mem_filter]; exact ⟨hf₂X, hf₂cut⟩
          rw [Finset.sum_eq_single_of_mem f₂ hf₂supp]
          · unfold cutChain; rw [Finsupp.filter_apply, if_pos hf₂cut]
          · intro t ht htne
            have htcut : t ∈ cutSet σ W := by rw [cutChain, Finsupp.support_filter, Finset.mem_filter] at ht; exact ht.2
            by_cases hgen : bdryGen t e0 = 0
            · rw [hgen, mul_zero]
            · obtain ⟨w, hw, heq⟩ := exists_facet_of_bdryGen_ne_zero hgen
              have htσ : t ∈ σ := cutSet_subset htcut
              have he0t : e0 ⊆ t := by rw [heq]; exact Finset.erase_subset w t
              rcases huniq t htσ he0t with rfl | rfl
              · exact (hf₁not htcut).elim
              · exact (htne rfl).elim
        rw [hval, Int.natAbs_mul]
        have hxabs : (X f₂).natAbs = 1 := by rcases hU.2 f₂ hf₂σ with hx | hx <;> rw [hx] <;> rfl
        rw [hxabs, bdryGen_facet_natAbs (hσ.pure f₂ hf₂σ) he0card he₂]
    have hgamma_abs : (bdryGen γ e0).natAbs = 1 := bdryGen_facet_natAbs hγ3 he0card he0sub
    have heval := congrArg (fun M : Chain V => M e0) hc
    change bdry (cutChain σ W X) e0 = (c • bdryGen γ) e0 at heval
    rw [Finsupp.smul_apply, smul_eq_mul] at heval
    have hcabs : c.natAbs = 1 := by
      rw [heval, Int.natAbs_mul, hgamma_abs, Nat.mul_one] at hbdry_single_side
      exact hbdry_single_side
    omega
  have hsplit := capped_split_of_side_boundary (X := X) (X₁ := cutChain σ W X) (X₂ := cutChain σ (W + fun _ => 1) X) hsum hXc hc
  have hUnitL : UnitOn (cappedCutLeft σ W X γ c) (insert γ (cutSet σ W)) := by
    unfold UnitOn
    constructor
    · ext s
      constructor
      · intro hsupp
        rw [Finsupp.mem_support_iff] at hsupp
        by_cases hγs : γ = s
        · rw [← hγs]
          exact Finset.mem_insert_self γ (cutSet σ W)
        · have hsCut : s ∈ cutSet σ W := by
            unfold cappedCutLeft cutChain at hsupp
            rw [Finsupp.sub_apply, Finsupp.filter_apply, Finsupp.single_apply, if_neg hγs, sub_zero] at hsupp
            have hsuppX : s ∈ (X.filter fun f => f ∈ cutSet σ W).support := Finsupp.mem_support_iff.mpr hsupp
            rw [Finsupp.support_filter, Finset.mem_filter] at hsuppX
            exact hsuppX.2
          exact Finset.mem_insert_of_mem hsCut
      · intro hmem
        rw [Finsupp.mem_support_iff]
        rcases Finset.mem_insert.mp hmem with hsγ | hsCut
        · rw [hsγ]
          unfold cappedCutLeft cutChain
          have hγnotcut : γ ∉ cutSet σ W := fun h => hγσ (cutSet_subset h)
          rw [Finsupp.sub_apply, Finsupp.filter_apply, if_neg hγnotcut, Finsupp.single_eq_same, zero_sub]
          rcases hcpm with rfl | rfl <;> norm_num
        · unfold cappedCutLeft cutChain
          have hγs : γ ≠ s := by intro h; exact hγσ (by rw [h]; exact cutSet_subset hsCut)
          have hsX : s ∈ X.support := by rw [hU.1]; exact cutSet_subset hsCut
          have hXne : X s ≠ 0 := Finsupp.mem_support_iff.mp hsX
          rw [Finsupp.sub_apply, Finsupp.filter_apply, if_pos hsCut, Finsupp.single_apply, if_neg hγs, sub_zero]
          exact hXne
    · intro s hs
      rcases Finset.mem_insert.mp hs with hsγ | hsCut
      · rw [hsγ]
        unfold cappedCutLeft cutChain
        have hγnotcut : γ ∉ cutSet σ W := fun h => hγσ (cutSet_subset h)
        rw [Finsupp.sub_apply, Finsupp.filter_apply, if_neg hγnotcut, Finsupp.single_eq_same, zero_sub]
        rcases hcpm with rfl | rfl <;> norm_num
      · unfold cappedCutLeft cutChain
        have hγs : γ ≠ s := by intro h; exact hγσ (by rw [h]; exact cutSet_subset hsCut)
        rw [Finsupp.sub_apply, Finsupp.filter_apply, if_pos hsCut, Finsupp.single_apply, if_neg hγs, sub_zero]
        exact hU.2 s (cutSet_subset hsCut)
  have hUnitR : UnitOn (cappedCutRight σ W X γ c) (insert γ (cutSet σ (W + fun _ => 1))) := by
    unfold UnitOn
    constructor
    · ext s
      constructor
      · intro hsupp
        rw [Finsupp.mem_support_iff] at hsupp
        by_cases hγs : γ = s
        · rw [← hγs]
          exact Finset.mem_insert_self γ (cutSet σ (W + fun _ => 1))
        · have hsCut : s ∈ cutSet σ (W + fun _ => 1) := by
            unfold cappedCutRight cutChain at hsupp
            rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.single_apply, if_neg hγs, add_zero] at hsupp
            have hsuppX : s ∈ (X.filter fun f => f ∈ cutSet σ (W + fun _ => 1)).support := Finsupp.mem_support_iff.mpr hsupp
            rw [Finsupp.support_filter, Finset.mem_filter] at hsuppX
            exact hsuppX.2
          exact Finset.mem_insert_of_mem hsCut
      · intro hmem
        rw [Finsupp.mem_support_iff]
        rcases Finset.mem_insert.mp hmem with hsγ | hsCut
        · rw [hsγ]
          unfold cappedCutRight cutChain
          have hγnotcut : γ ∉ cutSet σ (W + fun _ => 1) := fun h => hγσ (cutSet_subset h)
          rw [Finsupp.add_apply, Finsupp.filter_apply, if_neg hγnotcut, Finsupp.single_eq_same, zero_add]
          rcases hcpm with rfl | rfl <;> norm_num
        · unfold cappedCutRight cutChain
          have hγs : γ ≠ s := by intro h; exact hγσ (by rw [h]; exact cutSet_subset hsCut)
          have hsX : s ∈ X.support := by rw [hU.1]; exact cutSet_subset hsCut
          have hXne : X s ≠ 0 := Finsupp.mem_support_iff.mp hsX
          rw [Finsupp.add_apply, Finsupp.filter_apply, if_pos hsCut, Finsupp.single_apply, if_neg hγs, add_zero]
          exact hXne
    · intro s hs
      rcases Finset.mem_insert.mp hs with hsγ | hsCut
      · rw [hsγ]
        unfold cappedCutRight cutChain
        have hγnotcut : γ ∉ cutSet σ (W + fun _ => 1) := fun h => hγσ (cutSet_subset h)
        rw [Finsupp.add_apply, Finsupp.filter_apply, if_neg hγnotcut, Finsupp.single_eq_same, zero_add]
        rcases hcpm with rfl | rfl <;> norm_num
      · unfold cappedCutRight cutChain
        have hγs : γ ≠ s := by intro h; exact hγσ (by rw [h]; exact cutSet_subset hsCut)
        rw [Finsupp.add_apply, Finsupp.filter_apply, if_pos hsCut, Finsupp.single_apply, if_neg hγs, add_zero]
        exact hU.2 s (cutSet_subset hsCut)
  refine ⟨c, hUnitL, ?_, hUnitR, ?_, ?_⟩
  · simpa [cappedCutLeft] using hsplit.1
  · simpa [cappedCutRight] using hsplit.2.1
  · simpa [cappedCutLeft, cappedCutRight] using hsplit.2.2

theorem degree3_cut_setup (σ : Finset (Finset V)) (hσ : IsSphere2 σ) (hbig : 4 < (vertsOf σ).card)
    (hd3 : HasDegree3Vertex σ) :
    ∃ (v : V) (W : C2 σ),
      v ∈ vertsOf σ ∧ (linkVerts σ v).card = 3 ∧
      (linkVerts σ v).powersetCard 2 ⊆ edgesOf σ ∧ linkVerts σ v ∉ σ ∧
      bd2 σ W = gammaChain σ (linkVerts σ v) ∧
      IsSphere2 (insert (linkVerts σ v) (cutSet σ W)) ∧
      IsSphere2 (insert (linkVerts σ v) (cutSet σ (W + fun _ => 1))) := by
  rcases hd3 with ⟨v, hv, h3⟩
  rcases degree3_link_triangle_cut_data hσ hv h3 hbig with ⟨hγ3, hγe, hγσ⟩
  rcases exists_cut hσ hγ3 hγe with ⟨W, hW⟩
  refine ⟨v, W, hv, hγ3, hγe, hγσ, hW, ?_, ?_⟩
  · exact isSphere2_cut hσ hγ3 hγe hγσ hW
  · exact isSphere2_cut hσ hγ3 hγe hγσ (bd2_W_add_one hσ hW)

theorem norm_lt_filter_neg_of_filter_support_singleton (M : Chain V) (P : Finset V → Prop) [DecidablePred P] {T : Finset V}
    (hP : (M.filter P).support = {T}) :
    nrm (M.filter (fun t => ¬ P t)) < nrm M := by
  have hpos_nonzero : M.filter P ≠ 0 := by
    intro hzero
    rw [hzero] at hP
    simp at hP
  have hpos : 0 < nrm (M.filter P) := by
    have hnz : nrm (M.filter P) ≠ 0 := by
      intro hn
      exact hpos_nonzero (nrm_eq_zero_iff.mp hn)
    exact Nat.pos_of_ne_zero hnz
  have hsum := nrm_filter_add_nrm_filter_neg P M
  omega

def starTet (σ : Finset (Finset V)) (v : V) : Finset V := insert v (linkVerts σ v)

theorem starTet_card_of_degree3 (σ : Finset (Finset V)) {v : V} (h3 : (linkVerts σ v).card = 3) :
    (starTet σ v).card = 4 := by
  rw [starTet, Finset.card_insert_of_notMem]
  · omega
  · rw [linkVerts]
    exact Finset.notMem_erase _ _

theorem degree3_cut_star_side_glue (σ : Finset (Finset V)) {v : V} {W : C2 σ}
    (hσ : IsSphere2 σ) (hbig : 4 < (vertsOf σ).card) (hv : v ∈ vertsOf σ)
    (h3 : (linkVerts σ v).card = 3)
    (hW : bd2 σ W = gammaChain σ (linkVerts σ v)) :
    (insert (linkVerts σ v) (cutSet σ W) = tetFaces (starTet σ v) ∧
      GlueStep (starTet σ v) (insert (linkVerts σ v) (cutSet σ (W + fun _ => 1))) σ) ∨
    (insert (linkVerts σ v) (cutSet σ (W + fun _ => 1)) = tetFaces (starTet σ v) ∧
      GlueStep (starTet σ v) (insert (linkVerts σ v) (cutSet σ W)) σ) := by
  classical
  let γ := linkVerts σ v
  let T := starTet σ v
  have hdata := degree3_link_triangle_cut_data hσ hv h3 hbig
  have hγ3 : γ.card = 3 := by simpa [γ] using hdata.1
  have hγe : γ.powersetCard 2 ⊆ edgesOf σ := by simpa [γ] using hdata.2.1
  have hγσ : γ ∉ σ := by simpa [γ] using hdata.2.2
  have hvγ : v ∉ γ := by
    simp [γ, linkVerts]
  obtain ⟨F, hFσ, hvF⟩ := mem_vertsOf.mp hv
  have hTcard : T.card = 4 := by
    simpa [T, starTet, γ] using starTet_card_of_degree3 σ (v := v) h3
  have star_side_eq (U : C2 σ) (hU : bd2 σ U = gammaChain σ γ)
      (hUF : U ⟨F, hFσ⟩ = 1) :
      insert γ (cutSet σ U) = tetFaces T := by
    let τ : Finset (Finset V) := insert γ (cutSet σ U)
    change τ = tetFaces T
    have hτ : IsSphere2 τ := by
      dsimp [τ]
      exact isSphere2_cut hσ hγ3 hγe hγσ hU
    have hUlink : bd2 σ U = gammaChain σ (linkVerts σ v) := by simpa [γ] using hU
    have htetra : ∀ f, f ∈ tetFaces T → f ∈ τ := by
      intro f hf
      obtain ⟨w, hwT, rfl⟩ := exists_erase_eq_of_mem_tetFaces hTcard hf
      by_cases hwv : w = v
      · subst w
        have hTv : T.erase v = γ := by
          simp [T, starTet, γ, hvγ]
        dsimp [τ]
        rw [hTv]
        exact Finset.mem_insert_self γ (cutSet σ U)
      · have hwγ : w ∈ γ := by
          have : w ∈ insert v γ := by simpa [T, starTet] using hwT
          rw [Finset.mem_insert] at this
          exact this.resolve_left hwv
        have hcard2 : (γ.erase w).card = 2 := by
          rw [Finset.card_erase_of_mem hwγ, hγ3]
        obtain ⟨x, y, hxy, hpair⟩ := Finset.card_eq_two.mp hcard2
        have hxγ : x ∈ γ := Finset.mem_of_mem_erase (hpair ▸ Finset.mem_insert_self x {y})
        have hyγ : y ∈ γ := Finset.mem_of_mem_erase (hpair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        obtain ⟨_, hface⟩ := linkGraph_complete_of_linkVerts_card_three hσ
          (by simpa [γ] using hxγ) (by simpa [γ] using hyγ) hxy h3
        have heq : T.erase w = ({v, x, y} : Finset V) := by
          dsimp [T, starTet, γ]
          rw [Finset.erase_insert_of_ne (Ne.symm hwv), hpair]
        dsimp [τ]
        rw [heq]
        refine Finset.mem_insert_of_mem (mem_cutSet.mpr ⟨hface, ?_⟩)
        have key : U (⟨{v, x, y}, hface⟩ : σ) = U (⟨F, hFσ⟩ : σ) :=
          W_const_at hσ hUlink hvγ (by simp) hvF
        rw [key, hUF]
    apply Finset.Subset.antisymm
    · intro g hgτ
      rw [tetFaces, Finset.mem_powersetCard]
      refine ⟨?_, hτ.pure g hgτ⟩
      set S : Set τ := {f | (f : Finset V) ⊆ T}
      have hclosed : ∀ u ∈ S, ∀ z, (dualGraph τ).Adj u z → z ∈ S := by
        rintro u huT z ⟨_, e, he, heu, hez⟩
        have huT' : (u : Finset V) ⊆ T := huT
        have heT : e ⊆ T := heu.trans huT'
        have he2 : e.card = 2 := card_of_mem_edgesOf he
        have hTe : (T \ e).card = 2 := by rw [Finset.card_sdiff_of_subset heT, hTcard, he2]
        obtain ⟨w₁, w₂, hw12, hwe⟩ := Finset.card_eq_two.mp hTe
        have hw1 : w₁ ∈ T \ e := hwe ▸ Finset.mem_insert_self w₁ {w₂}
        have hw2 : w₂ ∈ T \ e := hwe ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂)
        have hw1e : w₁ ∉ e := (Finset.mem_sdiff.mp hw1).2
        have hw2e : w₂ ∉ e := (Finset.mem_sdiff.mp hw2).2
        have hf1T : insert w₁ e ⊆ T := Finset.insert_subset (Finset.mem_sdiff.mp hw1).1 heT
        have hf2T : insert w₂ e ⊆ T := Finset.insert_subset (Finset.mem_sdiff.mp hw2).1 heT
        have hf1τ : insert w₁ e ∈ τ := htetra _
          (Finset.mem_powersetCard.mpr ⟨hf1T, by rw [Finset.card_insert_of_notMem hw1e, he2]⟩)
        have hf2τ : insert w₂ e ∈ τ := htetra _
          (Finset.mem_powersetCard.mpr ⟨hf2T, by rw [Finset.card_insert_of_notMem hw2e, he2]⟩)
        have hins_ne : insert w₁ e ≠ insert w₂ e := by
          intro hc
          have hm : w₁ ∈ insert w₂ e := hc ▸ Finset.mem_insert_self w₁ e
          rw [Finset.mem_insert] at hm
          exact hm.elim (fun h => hw12 h) (fun h => hw1e h)
        have hfilter2 : (τ.filter (fun h => e ⊆ h)).card = 2 := hτ.closed e he
        have hpair_sub : ({insert w₁ e, insert w₂ e} : Finset (Finset V))
            ⊆ τ.filter (fun h => e ⊆ h) := by
          intro h hh; rw [Finset.mem_insert, Finset.mem_singleton] at hh
          rcases hh with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hf1τ, Finset.subset_insert _ _⟩
          · exact Finset.mem_filter.mpr ⟨hf2τ, Finset.subset_insert _ _⟩
        have hfeq : τ.filter (fun h => e ⊆ h) = {insert w₁ e, insert w₂ e} :=
          (Finset.eq_of_subset_of_card_le hpair_sub
            (le_of_eq (hfilter2.trans (Finset.card_pair hins_ne).symm))).symm
        have hmemg : (z : Finset V) ∈ τ.filter (fun h => e ⊆ h) :=
          Finset.mem_filter.mpr ⟨z.2, hez⟩
        rw [hfeq, Finset.mem_insert, Finset.mem_singleton] at hmemg
        show (z : Finset V) ⊆ T
        rcases hmemg with h | h
        · rw [h]; exact hf1T
        · rw [h]; exact hf2T
      have hbase : (⟨γ, by dsimp [τ]; exact Finset.mem_insert_self γ (cutSet σ U)⟩ : τ) ∈ S := by
        show (γ : Finset V) ⊆ T
        simp [T, starTet, γ]
      obtain ⟨p⟩ := dualGraph_preconnected hτ.toClosedSurface
        (⟨γ, by dsimp [τ]; exact Finset.mem_insert_self γ (cutSet σ U)⟩ : τ) ⟨g, hgτ⟩
      exact walk_mem_of_adj_closed' hclosed p hbase
    · exact htetra
  have glue_of_star (U : C2 σ) (hstar : insert γ (cutSet σ U) = tetFaces T)
      (B : Finset (Finset V)) (hB : B = insert γ (σ \ cutSet σ U)) : GlueStep T B σ := by
    refine ⟨hTcard, ?_, ?_⟩
    · left
      have hshared : tetFaces T ∩ B = {γ} := by
        ext s
        simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hsT, hsB⟩
          rw [hB, Finset.mem_insert] at hsB
          rcases hsB with hsγ | hscomp
          · exact hsγ
          · exfalso
            rcases Finset.mem_sdiff.mp hscomp with ⟨hsσ, hsncut⟩
            have hsStar : s ∈ insert γ (cutSet σ U) := by rwa [hstar]
            rw [Finset.mem_insert] at hsStar
            rcases hsStar with hsg | hscut
            · exact hγσ (hsg ▸ hsσ)
            · exact hsncut hscut
        · intro hsγ
          subst s
          constructor
          · rw [← hstar]
            exact Finset.mem_insert_self γ (cutSet σ U)
          · rw [hB]
            exact Finset.mem_insert_self γ (σ \ cutSet σ U)
      rw [hshared]
      simp
    · ext s
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hsσ
        by_cases hscut : s ∈ cutSet σ U
        · right
          refine ⟨?_, ?_⟩
          · rw [← hstar]
            exact Finset.mem_insert_of_mem hscut
          · rw [hB, Finset.mem_insert]
            intro hsB
            rcases hsB with hsγ | hscomp
            · exact hγσ (hsγ ▸ hsσ)
            · exact (Finset.mem_sdiff.mp hscomp).2 hscut
        · left
          refine ⟨?_, ?_⟩
          · rw [hB]
            exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hsσ, hscut⟩)
          · intro hsT
            have hsStar : s ∈ insert γ (cutSet σ U) := by rwa [hstar]
            rw [Finset.mem_insert] at hsStar
            rcases hsStar with hsγ | hscut'
            · exact hγσ (hsγ ▸ hsσ)
            · exact hscut hscut'
      · intro hs
        rcases hs with hs | hs
        · rcases hs with ⟨hsB, hsnotT⟩
          rw [hB, Finset.mem_insert] at hsB
          rcases hsB with hsγ | hscomp
          · exfalso
            apply hsnotT
            rw [← hstar]
            exact hsγ ▸ Finset.mem_insert_self γ (cutSet σ U)
          · exact (Finset.mem_sdiff.mp hscomp).1
        · rcases hs with ⟨hsT, hsnotB⟩
          have hsStar : s ∈ insert γ (cutSet σ U) := by rwa [hstar]
          rw [Finset.mem_insert] at hsStar
          rcases hsStar with hsγ | hscut
          · exfalso
            apply hsnotB
            rw [hB]
            exact hsγ ▸ Finset.mem_insert_self γ (σ \ cutSet σ U)
          · exact cutSet_subset hscut
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (W ⟨F, hFσ⟩) with hWF0 | hWF1
  · right
    have hWadd : bd2 σ (W + fun _ => 1) = gammaChain σ γ := by
      simpa [γ] using bd2_W_add_one hσ hW
    have hWFadd : ((W + fun _ => 1) : C2 σ) ⟨F, hFσ⟩ = 1 := by
      show W ⟨F, hFσ⟩ + 1 = 1
      rw [hWF0]
      decide
    have hstar := star_side_eq (W + fun _ => 1) hWadd hWFadd
    refine ⟨?_, ?_⟩
    · simpa [γ, T] using hstar
    · have hcomp : cutSet σ W = σ \ cutSet σ (W + fun _ => 1) := by
        rw [cutSet_add_one_eq_sdiff W]
        exact (Finset.sdiff_sdiff_eq_self (cutSet_subset : cutSet σ W ⊆ σ)).symm
      have hg : GlueStep T (insert γ (cutSet σ W)) σ :=
        glue_of_star (W + fun _ => 1) hstar (insert γ (cutSet σ W)) (by rw [hcomp])
      simpa [γ, T] using hg
  · left
    have hWγ : bd2 σ W = gammaChain σ γ := by simpa [γ] using hW
    have hstar := star_side_eq W hWγ hWF1
    refine ⟨?_, ?_⟩
    · simpa [γ, T] using hstar
    · have hg : GlueStep T (insert γ (cutSet σ (W + fun _ => 1))) σ :=
        glue_of_star W hstar (insert γ (cutSet σ (W + fun _ => 1))) (by rw [cutSet_add_one_eq_sdiff W])
      simpa [γ, T] using hg

theorem star_filter_support_singleton (Mstar Y : Chain V) (T : Finset V) (hT4 : T.card = 4)
    (hU : UnitOn Y (tetFaces T)) (hbd : bdry Mstar = Y) (hMt : IsTaut Mstar)
    (hSupp : ∀ t ∈ Mstar.support, t ⊆ T) :
    Mstar.support = {T} := by
  classical
  have h_all : ∀ t ∈ Mstar.support, t = T := by
    intro t ht
    have hbdsupp : ∀ s ∈ (bdry Mstar).support, s.card = 3 := by
      intro s hs
      rw [hbd, hU.1] at hs
      exact (Finset.mem_powersetCard.mp hs).2
    have hcardt : t.card = 4 := by
      simpa using (hMt.dim_pure hbdsupp t ht)
    exact Finset.eq_of_subset_of_card_le (hSupp t ht) (by omega)
  have hnonempty : Mstar.support.Nonempty := by
    have hcardfaces : (tetFaces T).card = 4 := card_tetFaces hT4
    have hfaces_nonempty : (tetFaces T).Nonempty := by
      exact Finset.card_pos.mp (by rw [hcardfaces]; norm_num)
    rcases hfaces_nonempty with ⟨s, hs⟩
    have hYs : s ∈ Y.support := by
      rw [hU.1]
      exact hs
    have hYne : Y ≠ 0 := by
      intro hY0
      rw [hY0] at hYs
      simpa using hYs
    have hMne : Mstar ≠ 0 := by
      intro hM0
      apply hYne
      rw [← hbd, hM0]
      simp
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hMne
    rw [← Finsupp.support_eq_empty]
    exact hempty
  ext t
  constructor
  · intro ht
    have htT : t = T := h_all t ht
    rw [htT]
    exact Finset.mem_singleton_self T
  · intro ht
    rw [Finset.mem_singleton] at ht
    rw [ht]
    rcases hnonempty with ⟨u, hu⟩
    have huT : u = T := h_all u hu
    rw [← huT]
    exact hu

theorem support_eq_insert_of_filter_support_singleton (M : Chain V) (P : Finset V → Prop) [DecidablePred P] {T : Finset V}
    (hP : (M.filter P).support = {T}) :
    M.support = insert T (M.filter (fun t => ¬ P t)).support := by
  ext s
  constructor
  · intro hs
    by_cases hPs : P s
    · have hsfil : s ∈ (M.filter P).support := by
        simpa using And.intro hs hPs
      rw [hP] at hsfil
      have hsT : s = T := by
        simpa using hsfil
      simp [hsT]
    · have hsfil : s ∈ (M.filter (fun t => ¬ P t)).support := by
        simpa using And.intro hs hPs
      exact mem_insert_of_mem hsfil
  · intro hs
    simp at hs
    rcases hs with hsT | hsfil
    · have hTin : T ∈ (M.filter P).support := by
        rw [hP]
        simp
      have hTnz : ¬ M T = 0 := by
        have hTin' : ¬ M T = 0 ∧ P T := by
          simpa using hTin
        exact hTin'.1
      simpa [hsT] using hTnz
    · simpa using hsfil.1

theorem ball_reassemble_of_filter_support_singleton (M : Chain V) (P : Finset V → Prop) [DecidablePred P] {T : Finset V}
    {B σ : Finset (Finset V)} (hP : (M.filter P).support = {T})
    (hglue : GlueStep T B σ) :
    IsBall (M.filter (fun t => ¬ P t)).support B → IsBall M.support σ := by
  intro hball
  have hTmem : T ∈ (M.filter P).support := by
    rw [hP]
    simp
  have hTne : (M.filter P) T ≠ 0 := by
    exact Finsupp.mem_support_iff.mp hTmem
  have hPT : P T := by
    by_contra hnot
    have hzero : (M.filter P) T = 0 := by
      simp [Finsupp.filter, hnot]
    exact hTne hzero
  have hTnot : T ∉ (M.filter (fun t => ¬ P t)).support := by
    intro h
    have hne : (M.filter (fun t => ¬ P t)) T ≠ 0 := Finsupp.mem_support_iff.mp h
    have hzero : (M.filter (fun t => ¬ P t)) T = 0 := by
      simp [Finsupp.filter, hPT]
    exact hne hzero
  rw [support_eq_insert_of_filter_support_singleton M P hP]
  exact IsBall.insert_of_glueStep hball hglue hTnot

theorem taut_splits_for_capped_cut (σ : Finset (Finset V)) (X M : Chain V) {γ : Finset V} {W : C2 σ} {c : ℤ}
    (hσ : IsSphere2 σ)
    (hσL : IsSphere2 (insert γ (cutSet σ W)))
    (hσR : IsSphere2 (insert γ (cutSet σ (W + fun _ => 1))))
    (hγ3 : γ.card = 3) (hγe : γ.powersetCard 2 ⊆ edgesOf σ)
    (hW : bd2 σ W = gammaChain σ γ)
    (hUL : UnitOn (cappedCutLeft σ W X γ c) (insert γ (cutSet σ W)))
    (hXLc : bdry (cappedCutLeft σ W X γ c) = 0)
    (hUR : UnitOn (cappedCutRight σ W X γ c) (insert γ (cutSet σ (W + fun _ => 1))))
    (hXRc : bdry (cappedCutRight σ W X γ c) = 0)
    (hXsum : cappedCutLeft σ W X γ c + cappedCutRight σ W X γ c = X)
    (hMX : bdry M = X) (hT : IsTaut M) :
    bdry (M.filter (fun t => t ⊆ vertsOf (insert γ (cutSet σ W)))) = cappedCutLeft σ W X γ c ∧
    bdry (M.filter (fun t => ¬ t ⊆ vertsOf (insert γ (cutSet σ W)))) = cappedCutRight σ W X γ c ∧
    IsTaut (M.filter (fun t => t ⊆ vertsOf (insert γ (cutSet σ W)))) ∧
    IsTaut (M.filter (fun t => ¬ t ⊆ vertsOf (insert γ (cutSet σ W)))) ∧
    (∀ t ∈ (M.filter (fun t => t ⊆ vertsOf (insert γ (cutSet σ W)))).support,
      t ⊆ vertsOf (insert γ (cutSet σ W))) ∧
    (∀ t ∈ (M.filter (fun t => ¬ t ⊆ vertsOf (insert γ (cutSet σ W)))).support,
      t ⊆ vertsOf (insert γ (cutSet σ (W + fun _ => 1)))) ∧
    M.filter (fun t => t ⊆ vertsOf (insert γ (cutSet σ W))) +
      M.filter (fun t => ¬ t ⊆ vertsOf (insert γ (cutSet σ W))) = M := by
  classical
  let A : Finset V := vertsOf (insert γ (cutSet σ W))
  let B : Finset V := vertsOf (insert γ (cutSet σ (W + fun _ => 1)))
  have hXsupp : ∀ s ∈ (cappedCutLeft σ W X γ c).support, s ⊆ A ∧ s.card = 2 + 1 := by
    intro s hs
    have hsτ : s ∈ insert γ (cutSet σ W) := by
      rw [hUL.1] at hs
      exact hs
    constructor
    · intro x hx
      exact mem_vertsOf.mpr ⟨s, hsτ, hx⟩
    · exact hσL.pure s hsτ
  have hYsupp : ∀ s ∈ (cappedCutRight σ W X γ c).support, s ⊆ B ∧ s.card = 2 + 1 := by
    intro s hs
    have hsτ : s ∈ insert γ (cutSet σ (W + fun _ => 1)) := by
      rw [hUR.1] at hs
      exact hs
    constructor
    · intro x hx
      exact mem_vertsOf.mpr ⟨s, hsτ, hx⟩
    · exact hσR.pure s hsτ
  have hAB : A ∩ B = γ := by
    dsimp [A, B]
    exact vertsOf_cut_inter hσ hW
  have hC : (A ∩ B).card ≤ 2 + 1 := by
    rw [hAB, hγ3]
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_pair_of_one_lt_card (s := A ∩ B) (by
    rw [hAB, hγ3]
    omega)
  have hM1 : bdry M = cappedCutLeft σ W X γ c + cappedCutRight σ W X γ c :=
    hMX.trans hXsum.symm
  have hbdsupp : ∀ s ∈ (bdry M).support, s.card = 2 + 1 := by
    intro s hs
    rw [hM1] at hs
    rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
    · exact (hXsupp s h).2
    · exact (hYsupp s h).2
  have hpure : ∀ s ∈ M.support, s.card = 2 + 2 :=
    fun s hs => hT.dim_pure hbdsupp s hs
  have hdim2 : ∀ s ∈ M.support, 2 ≤ s.card := by
    intro s hs
    rw [hpure s hs]
    omega
  have hsuppAB : ∀ t ∈ M.support, t ⊆ A ∪ B := by
    intro t ht
    refine (supp_subset_vert ht).trans ((hT.vert_subset hdim2).trans ?_)
    rw [hM1]
    exact (vert_add_subset (cappedCutLeft σ W X γ c) (cappedCutRight σ W X γ c)).trans
      (Finset.union_subset_union
        (vert_subset_of_supp fun s hs => (hXsupp s hs).1)
        (vert_subset_of_supp fun s hs => (hYsupp s hs).1))
  have hdich : ∀ t ∈ M.support, t ⊆ A ∨ t ⊆ B := by
    intro t ht
    rcases hybrid_structure (A := A) (B := B) (n := 2) (M := M)
        (X := cappedCutLeft σ W X γ c) (Y := cappedCutRight σ W X γ c)
        (by omega) hp hq hpq hC hXsupp hYsupp hXLc hXRc hM1 hT hpure hsuppAB ht with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨y₀, hy⟩ := Finset.card_eq_one.mp h1
      exact (no_extreme_hybrid (A := A) (B := B) (n := 2) (M := M)
        (X := cappedCutLeft σ W X γ c) (Y := cappedCutRight σ W X γ c)
        (by omega) hp hq hpq hC hXsupp hYsupp hXLc hXRc hM1 hT hpure hsuppAB ht hy h2).elim
    · obtain ⟨x₀, hx⟩ := Finset.card_eq_one.mp h1
      have hM1' : bdry M = cappedCutRight σ W X γ c + cappedCutLeft σ W X γ c := by
        rw [hM1, add_comm]
      have hsuppBA : ∀ t' ∈ M.support, t' ⊆ B ∪ A := by
        intro t' ht'
        rw [Finset.union_comm]
        exact hsuppAB t' ht'
      exact (no_extreme_hybrid (A := B) (B := A) (n := 2) (M := M)
        (X := cappedCutRight σ W X γ c) (Y := cappedCutLeft σ W X γ c)
        (by omega) (Finset.inter_comm A B ▸ hq) (Finset.inter_comm A B ▸ hp) hpq.symm
        (Finset.inter_comm A B ▸ hC) hYsupp hXsupp hXRc hXLc hM1' hT hpure hsuppBA ht hx
        (Finset.inter_comm A B ▸ h2)).elim
  have hs := IsTaut.splits (A := A) (B := B) (n := 2) (M := M)
    (by omega) (p := p) (q := q) hp hq hpq hC hXsupp hYsupp hXLc hXRc hT hM1
  rcases hs with ⟨hbdL, hbdR, htL, htR, hsumM⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbdL
  · exact hbdR
  · exact htL
  · exact htR
  · intro t ht
    rw [Finsupp.support_filter, Finset.mem_filter] at ht
    exact ht.2
  · intro t ht
    rw [Finsupp.support_filter, Finset.mem_filter] at ht
    exact (hdich t ht.1).resolve_left ht.2
  · exact hsumM

theorem vertsOf_tetFaces_eq (T : Finset V) (hT4 : T.card = 4) : vertsOf (tetFaces T) = T := by
  ext x
  constructor
  · intro hx
    rw [mem_vertsOf] at hx
    rcases hx with ⟨f, hf, hxf⟩
    exact (Finset.mem_powersetCard.mp hf).1 hxf
  · intro hx
    rw [mem_vertsOf]
    have herasecard : (T.erase x).card = 3 := by
      rw [Finset.card_erase_of_mem hx, hT4]
    have hpos : 0 < (T.erase x).card := by omega
    rcases Finset.card_pos.mp hpos with ⟨y, hy⟩
    have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
    have hyT : y ∈ T := (Finset.mem_erase.mp hy).2
    refine ⟨T.erase y, ?_, ?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro z hz
        exact Finset.mem_of_mem_erase hz
      · rw [Finset.card_erase_of_mem hyT, hT4]
    · exact Finset.mem_erase.mpr ⟨Ne.symm hyne, hx⟩

theorem degree3_reassemble_from_cut_split (σ : Finset (Finset V)) (X M : Chain V) {v : V} {W : C2 σ} {c : ℤ}
    (hσ : IsSphere2 σ) (hbig : 4 < (vertsOf σ).card) (hv : v ∈ vertsOf σ)
    (h3 : (linkVerts σ v).card = 3)
    (hW : bd2 σ W = gammaChain σ (linkVerts σ v))
    (hσL : IsSphere2 (insert (linkVerts σ v) (cutSet σ W)))
    (hσR : IsSphere2 (insert (linkVerts σ v) (cutSet σ (W + fun _ => 1))))
    (hUL : UnitOn (cappedCutLeft σ W X (linkVerts σ v) c) (insert (linkVerts σ v) (cutSet σ W)))
    (hXLc : bdry (cappedCutLeft σ W X (linkVerts σ v) c) = 0)
    (hUR : UnitOn (cappedCutRight σ W X (linkVerts σ v) c) (insert (linkVerts σ v) (cutSet σ (W + fun _ => 1))))
    (hXRc : bdry (cappedCutRight σ W X (linkVerts σ v) c) = 0)
    (hML : bdry (M.filter (fun t => t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W)))) =
      cappedCutLeft σ W X (linkVerts σ v) c)
    (hMR : bdry (M.filter (fun t => ¬ t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W)))) =
      cappedCutRight σ W X (linkVerts σ v) c)
    (hTL : IsTaut (M.filter (fun t => t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W)))))
    (hTR : IsTaut (M.filter (fun t => ¬ t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W)))))
    (hSuppL : ∀ t ∈ (M.filter (fun t => t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W)))).support,
      t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W)))
    (hSuppR : ∀ t ∈ (M.filter (fun t => ¬ t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W)))).support,
      t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ (W + fun _ => 1))))
    (hMsum : M.filter (fun t => t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W))) +
      M.filter (fun t => ¬ t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W))) = M)
    (hS : SimplicialChain M) :
    ∃ (σ' : Finset (Finset V)) (X' M' : Chain V),
      IsSphere2 σ' ∧ UnitOn X' σ' ∧ bdry X' = 0 ∧ bdry M' = X' ∧ IsTaut M' ∧
      SimplicialChain M' ∧ nrm M' < nrm M ∧
      (IsBall M'.support σ' → IsBall M.support σ) := by
  classical
  let γ : Finset V := linkVerts σ v
  let A : Finset V := vertsOf (insert γ (cutSet σ W))
  let ML : Chain V := M.filter (fun t => t ⊆ A)
  let MR : Chain V := M.filter (fun t => ¬ t ⊆ A)
  have hsplit := degree3_cut_star_side_glue σ hσ hbig hv h3 hW
  rcases hsplit with hcase | hcase
  · rcases hcase with ⟨hstar, hglue⟩
    refine ⟨insert γ (cutSet σ (W + fun _ => 1)), cappedCutRight σ W X γ c, MR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [γ]
      exact hσR
    · dsimp [γ]
      exact hUR
    · dsimp [γ]
      exact hXRc
    · dsimp [MR, A, γ]
      exact hMR
    · dsimp [MR, A, γ]
      exact hTR
    · intro t
      dsimp [MR, A, γ]
      rw [Finsupp.filter_apply]
      by_cases ht : ¬ t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W))
      · rw [if_pos ht]
        exact hS t
      · rw [if_neg ht]
        exact Or.inr (Or.inl rfl)
    · have hT4 : (starTet σ v).card = 4 := starTet_card_of_degree3 σ h3
      have hULtet : UnitOn (cappedCutLeft σ W X γ c) (tetFaces (starTet σ v)) := by
        dsimp [γ]
        rw [← hstar]
        exact hUL
      have hSuppLT : ∀ t ∈ ML.support, t ⊆ starTet σ v := by
        intro t ht
        have htA : t ⊆ vertsOf (insert γ (cutSet σ W)) := hSuppL t (by simpa only [ML, A] using ht)
        dsimp [γ] at htA
        rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4] at htA
        exact htA
      have hMLsupp : ML.support = {starTet σ v} := by
        exact star_filter_support_singleton ML (cappedCutLeft σ W X γ c) (starTet σ v) hT4 hULtet (by simpa only [ML, A, γ] using hML) (by simpa only [ML, A, γ] using hTL) hSuppLT
      have hlt : nrm (M.filter (fun t => ¬ t ⊆ A)) < nrm M :=
        norm_lt_filter_neg_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
      simpa only [MR] using hlt
    · intro hball
      have hT4 : (starTet σ v).card = 4 := starTet_card_of_degree3 σ h3
      have hULtet : UnitOn (cappedCutLeft σ W X γ c) (tetFaces (starTet σ v)) := by
        dsimp [γ]
        rw [← hstar]
        exact hUL
      have hSuppLT : ∀ t ∈ ML.support, t ⊆ starTet σ v := by
        intro t ht
        have htA : t ⊆ vertsOf (insert γ (cutSet σ W)) := hSuppL t (by simpa only [ML, A] using ht)
        dsimp [γ] at htA
        rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4] at htA
        exact htA
      have hMLsupp : ML.support = {starTet σ v} := by
        exact star_filter_support_singleton ML (cappedCutLeft σ W X γ c) (starTet σ v) hT4 hULtet (by simpa only [ML, A, γ] using hML) (by simpa only [ML, A, γ] using hTL) hSuppLT
      have hreasm : IsBall (M.filter (fun t => ¬ t ⊆ A)).support (insert γ (cutSet σ (W + fun _ => 1))) → IsBall M.support σ :=
        ball_reassemble_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp hglue
      exact hreasm (by simpa only [MR] using hball)
  · rcases hcase with ⟨hstar, hglue⟩
    refine ⟨insert γ (cutSet σ W), cappedCutLeft σ W X γ c, ML, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [γ]
      exact hσL
    · dsimp [γ]
      exact hUL
    · dsimp [γ]
      exact hXLc
    · dsimp [ML, A, γ]
      exact hML
    · dsimp [ML, A, γ]
      exact hTL
    · intro t
      dsimp [ML, A, γ]
      rw [Finsupp.filter_apply]
      by_cases ht : t ⊆ vertsOf (insert (linkVerts σ v) (cutSet σ W))
      · rw [if_pos ht]
        exact hS t
      · rw [if_neg ht]
        exact Or.inr (Or.inl rfl)
    · have hT4 : (starTet σ v).card = 4 := starTet_card_of_degree3 σ h3
      have hURtet : UnitOn (cappedCutRight σ W X γ c) (tetFaces (starTet σ v)) := by
        dsimp [γ]
        rw [← hstar]
        exact hUR
      have hSuppRT : ∀ t ∈ MR.support, t ⊆ starTet σ v := by
        intro t ht
        have htA : t ⊆ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := hSuppR t (by simpa only [MR, A] using ht)
        dsimp [γ] at htA
        rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4] at htA
        exact htA
      have hMRsupp : MR.support = {starTet σ v} := by
        exact star_filter_support_singleton MR (cappedCutRight σ W X γ c) (starTet σ v) hT4 hURtet (by simpa only [MR, A, γ] using hMR) (by simpa only [MR, A, γ] using hTR) hSuppRT
      have hlt : nrm (M.filter (fun t => ¬ (¬ t ⊆ A))) < nrm M :=
        norm_lt_filter_neg_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
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
      rw [hML_eq]
      exact hlt
    · intro hball
      have hT4 : (starTet σ v).card = 4 := starTet_card_of_degree3 σ h3
      have hURtet : UnitOn (cappedCutRight σ W X γ c) (tetFaces (starTet σ v)) := by
        dsimp [γ]
        rw [← hstar]
        exact hUR
      have hSuppRT : ∀ t ∈ MR.support, t ⊆ starTet σ v := by
        intro t ht
        have htA : t ⊆ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := hSuppR t (by simpa only [MR, A] using ht)
        dsimp [γ] at htA
        rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4] at htA
        exact htA
      have hMRsupp : MR.support = {starTet σ v} := by
        exact star_filter_support_singleton MR (cappedCutRight σ W X γ c) (starTet σ v) hT4 hURtet (by simpa only [MR, A, γ] using hMR) (by simpa only [MR, A, γ] using hTR) hSuppRT
      have hreasm : IsBall (M.filter (fun t => ¬ (¬ t ⊆ A))).support (insert γ (cutSet σ W)) → IsBall M.support σ :=
        ball_reassemble_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp hglue
      apply hreasm
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
      rw [← hML_eq]
      exact hball


/-- M26 hole `deg3_split`: a 2-sphere with a degree-3 vertex (> 4 vertices) splits,
along the link triangle, into a strictly smaller taut filling whose ball reassembles
to the original (connected-sum reduction). -/
theorem aleph_deg3_split (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hbig : 4 < (vertsOf σ).card) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hd3 : HasDegree3Vertex σ) :
    ∃ (σ' : Finset (Finset V)) (X' M' : Chain V),
      IsSphere2 σ' ∧ UnitOn X' σ' ∧ bdry X' = 0 ∧ bdry M' = X' ∧ IsTaut M' ∧
      SimplicialChain M' ∧ nrm M' < nrm M ∧
      (IsBall M'.support σ' → IsBall M.support σ) := by
  obtain ⟨v, W, hv, hγ3, hγe, hγσ, hW, hσL, hσR⟩ := degree3_cut_setup σ hσ hbig hd3
  obtain ⟨c, hUL, hXLc, hUR, hXRc, hXsum⟩ := capped_cut_splits_unit σ X hσ hγ3 hγe hγσ hW hU hXc
  obtain ⟨hML, hMR, hTL, hTR, hSuppL, hSuppR, hMsum⟩ := taut_splits_for_capped_cut σ X M hσ hσL hσR hγ3 hγe hW hUL hXLc hUR hXRc hXsum hMX hT
  exact degree3_reassemble_from_cut_split σ X M hσ hbig hv hγ3 hW hσL hσR hUL hXLc hUR hXRc hML hMR hTL hTR hSuppL hSuppR hMsum hS


noncomputable def alephChosenFiber {V : Type*} [LinearOrder V] {M : Chain V} {σ : Finset (Finset V)}
    (f : {α // α ∈ σ} → {t // t ∈ M.support}) (τ : {t // t ∈ M.support}) :
    Finset {α // α ∈ σ} :=
  (Finset.univ : Finset {α // α ∈ σ}).filter (fun α => f α = τ)

noncomputable def alephChosenFaceFiber {V : Type*} [LinearOrder V] {M : Chain V} {σ : Finset (Finset V)}
    (f : {α // α ∈ σ} → {t // t ∈ M.support}) (τ : {t // t ∈ M.support}) :
    Finset (Finset V) :=
  (alephChosenFiber f τ).image (fun α : {α // α ∈ σ} => (α : Finset V))

open Finset in
theorem aleph_chosenFaceFiber_subset_sharedFaces {M : Chain V} {σ : Finset (Finset V)}
    (hU : UnitOn (bdry M) σ)
    (f : {α // α ∈ σ} → {t // t ∈ M.support})
    (hfspec : ∀ α : {α // α ∈ σ}, ProperBoundaryFaceTet M (α : Finset V) ((f α) : Finset V))
    (τ : {t // t ∈ M.support}) :
    alephChosenFaceFiber f τ ⊆ sharedFaces M (τ : Finset V) := by
  unfold alephChosenFaceFiber alephChosenFiber
  intro s hs
  rw [mem_image] at hs
  rcases hs with ⟨α, hα, rfl⟩
  rw [mem_filter] at hα
  rcases hα with ⟨hαuniv, hαeq⟩
  rw [sharedFaces]
  rw [mem_inter]
  constructor
  · have hproper := hfspec α
    rw [hαeq] at hproper
    exact hproper.2.1
  · rw [hU.1]
    exact α.property

open Finset in
theorem aleph_chosenFaceFibers_disjoint {M : Chain V} {σ : Finset (Finset V)}
    (f : {α // α ∈ σ} → {t // t ∈ M.support}) {τ₁ τ₂ : {t // t ∈ M.support}}
    (hne : τ₁ ≠ τ₂) :
    Disjoint (alephChosenFaceFiber f τ₁) (alephChosenFaceFiber f τ₂) := by
  rw [Finset.disjoint_left]
  intro s hs1 hs2
  unfold alephChosenFaceFiber at hs1 hs2
  simp only [Finset.mem_image, alephChosenFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
  rcases hs1 with ⟨α1, hα1f, hα1s⟩
  rcases hs2 with ⟨α2, hα2f, hα2s⟩
  have hsub : α1 = α2 := by
    apply Subtype.ext
    exact hα1s.trans hα2s.symm
  apply hne
  calc
    τ₁ = f α1 := hα1f.symm
    _ = f α2 := by rw [hsub]
    _ = τ₂ := hα2f

open Finset in
theorem aleph_chosenFiber_card_le_sharedFaces {M : Chain V} {σ : Finset (Finset V)}
    (hU : UnitOn (bdry M) σ)
    (f : {α // α ∈ σ} → {t // t ∈ M.support})
    (hfspec : ∀ α : {α // α ∈ σ}, ProperBoundaryFaceTet M (α : Finset V) ((f α) : Finset V))
    (τ : {t // t ∈ M.support}) :
    (alephChosenFiber f τ).card ≤ (sharedFaces M (τ : Finset V)).card := by
  have hsub : alephChosenFaceFiber f τ ⊆ sharedFaces M (τ : Finset V) :=
    aleph_chosenFaceFiber_subset_sharedFaces hU f hfspec τ
  have hcard : (alephChosenFaceFiber f τ).card = (alephChosenFiber f τ).card := by
    unfold alephChosenFaceFiber
    rw [Finset.card_image_of_injective]
    intro a b h
    exact Subtype.ext h
  calc
    (alephChosenFiber f τ).card = (alephChosenFaceFiber f τ).card := hcard.symm
    _ ≤ (sharedFaces M (τ : Finset V)).card := Finset.card_le_card hsub

open Finset in
theorem aleph_deg_eq_card_filter_of_unitOn {X : Chain V} {σ : Finset (Finset V)} (hU : UnitOn X σ) (x : V) :
    deg x X = (σ.filter (fun s => x ∈ s)).card := by
  rw [deg]
  apply UnitOn.nrm_eq
  refine ⟨?_, ?_⟩
  · rw [nbhd, Finsupp.support_filter, hU.1]
  · intro s hs
    rw [Finset.mem_filter] at hs
    rw [nbhd_apply, if_pos hs.2]
    exact hU.2 s hs.1

open Finset in
theorem aleph_double_fiber_eligible {M : Chain V} {σ : Finset (Finset V)}
    (hU : UnitOn (bdry M) σ) (hPure : ∀ t ∈ M.support, t.card = 4)
    (hShared2 : ∀ t ∈ M.support, (sharedFaces M t).card ≤ 2)
    (f : {α // α ∈ σ} → {t // t ∈ M.support})
    (hfspec : ∀ α : {α // α ∈ σ}, ProperBoundaryFaceTet M (α : Finset V) ((f α) : Finset V))
    (τ : {t // t ∈ M.support})
    (h2 : (alephChosenFiber f τ).card = 2) :
    EligibleTet M (τ : Finset V) ∧ sharedFaces M (τ : Finset V) = alephChosenFaceFiber f τ := by
  classical
  let F := alephChosenFaceFiber f τ
  have hFsub : F ⊆ sharedFaces M (τ : Finset V) := by
    dsimp [F]
    exact aleph_chosenFaceFiber_subset_sharedFaces hU f hfspec τ
  have hFcard : F.card = 2 := by
    dsimp [F]
    rw [alephChosenFaceFiber]
    rw [Finset.card_image_of_injective]
    · exact h2
    · intro a b hab
      exact Subtype.ext hab
  have hSharedCardLe : (sharedFaces M (τ : Finset V)).card ≤ F.card := by
    rw [hFcard]
    exact hShared2 (τ : Finset V) τ.property
  have hEqF : F = sharedFaces M (τ : Finset V) := by
    exact Finset.eq_of_subset_of_card_le hFsub hSharedCardLe
  have hEq : sharedFaces M (τ : Finset V) = F := hEqF.symm
  constructor
  · constructor
    · exact hPure (τ : Finset V) τ.property
    · constructor
      · exact τ.property
      · constructor
        · rw [hEq, hFcard]
        · intro s hs
          rw [hEq] at hs
          dsimp [F, alephChosenFaceFiber] at hs
          rcases Finset.mem_image.mp hs with ⟨α, hαmem, rfl⟩
          have hfα : f α = τ := by
            dsimp [alephChosenFiber] at hαmem
            exact (Finset.mem_filter.mp hαmem).2
          have hspec := hfspec α
          rw [hfα] at hspec
          exact hspec.2.2
  · exact hEq

open Finset in
theorem aleph_incident_faces_card_ge_three {σ : Finset (Finset V)} (hσ : IsSphere2 σ) {v : V} (hv : v ∈ vertsOf σ) :
    3 ≤ (σ.filter (fun f => v ∈ f)).card := by
  classical
  obtain ⟨f, hf, hvf⟩ := mem_vertsOf.mp hv
  have hf3 : f.card = 3 := hσ.pure f hf
  have he2 : (f.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvf, hf3]
  obtain ⟨x, y, hxy, hpair⟩ := Finset.card_eq_two.mp he2
  have hxe : x ∈ f.erase v := by rw [hpair]; simp
  have hye : y ∈ f.erase v := by rw [hpair]; simp
  have hxf : x ∈ f := Finset.mem_of_mem_erase hxe
  have hyf : y ∈ f := Finset.mem_of_mem_erase hye
  have hxv : x ≠ v := Finset.ne_of_mem_erase hxe
  have hyv : y ≠ v := Finset.ne_of_mem_erase hye
  have hvx_sub : ({v, x} : Finset V) ⊆ f := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hvf
    · rw [Finset.mem_singleton] at hu
      exact hu ▸ hxf
  have hvy_sub : ({v, y} : Finset V) ⊆ f := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hvf
    · rw [Finset.mem_singleton] at hu
      exact hu ▸ hyf
  have hedge_x : ({v, x} : Finset V) ∈ edgesOf σ :=
    mem_edgesOf.mpr ⟨f, hf, hvx_sub, Finset.card_pair (Ne.symm hxv)⟩
  obtain ⟨fx₁, hfx₁, fx₂, hfx₂, hfx_ne, hfxe₁, hfxe₂, huniq_x⟩ :=
    exists_two_faces hσ.toClosedSurface hedge_x
  obtain ⟨fx, hfx, hvx_fx, hfx_ne_f⟩ :
      ∃ fx ∈ σ, ({v, x} : Finset V) ⊆ fx ∧ fx ≠ f := by
    rcases huniq_x f hf hvx_sub with rfl | rfl
    · exact ⟨fx₂, hfx₂, hfxe₂, hfx_ne.symm⟩
    · exact ⟨fx₁, hfx₁, hfxe₁, hfx_ne⟩
  have hedge_y : ({v, y} : Finset V) ∈ edgesOf σ :=
    mem_edgesOf.mpr ⟨f, hf, hvy_sub, Finset.card_pair (Ne.symm hyv)⟩
  obtain ⟨fy₁, hfy₁, fy₂, hfy₂, hfy_ne, hfye₁, hfye₂, huniq_y⟩ :=
    exists_two_faces hσ.toClosedSurface hedge_y
  obtain ⟨fy, hfy, hvy_fy, hfy_ne_f⟩ :
      ∃ fy ∈ σ, ({v, y} : Finset V) ⊆ fy ∧ fy ≠ f := by
    rcases huniq_y f hf hvy_sub with rfl | rfl
    · exact ⟨fy₂, hfy₂, hfye₂, hfy_ne.symm⟩
    · exact ⟨fy₁, hfy₁, hfye₁, hfy_ne⟩
  have hf_eq : f = insert v {x, y} := by
    rw [← hpair, Finset.insert_erase hvf]
  have hfx_ne_fy : fx ≠ fy := by
    intro hxyf
    have hfy_sub_fx : f ⊆ fx := by
      rw [hf_eq]
      intro u hu
      rcases Finset.mem_insert.mp hu with huv | hu
      · rw [huv]
        exact hvx_fx (Finset.mem_insert_self v _)
      · rcases Finset.mem_insert.mp hu with hux | hu
        · rw [hux]
          exact hvx_fx (by simp)
        · rw [Finset.mem_singleton] at hu
          rw [hu, hxyf]
          exact hvy_fy (by simp)
    have hfx3 : fx.card = 3 := hσ.pure fx hfx
    have hf_eq_fx : f = fx :=
      Finset.eq_of_subset_of_card_le hfy_sub_fx (by rw [hfx3, hf3])
    exact hfx_ne_f hf_eq_fx.symm
  have hf_mem : f ∈ σ.filter (fun g => v ∈ g) :=
    Finset.mem_filter.mpr ⟨hf, hvf⟩
  have hfx_v : v ∈ fx := hvx_fx (Finset.mem_insert_self v _)
  have hfx_mem : fx ∈ σ.filter (fun g => v ∈ g) :=
    Finset.mem_filter.mpr ⟨hfx, hfx_v⟩
  have hfy_v : v ∈ fy := hvy_fy (Finset.mem_insert_self v _)
  have hfy_mem : fy ∈ σ.filter (fun g => v ∈ g) :=
    Finset.mem_filter.mpr ⟨hfy, hfy_v⟩
  calc
    3 = ({f, fx, fy} : Finset (Finset V)).card :=
      (Finset.card_eq_three.mpr ⟨f, fx, fy, hfx_ne_f.symm, hfy_ne_f.symm,
        hfx_ne_fy, rfl⟩).symm
    _ ≤ (σ.filter (fun g => v ∈ g)).card := by
      refine Finset.card_le_card ?_
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hf_mem
      · rcases Finset.mem_insert.mp hg with rfl | hg
        · exact hfx_mem
        · rw [Finset.mem_singleton] at hg
          exact hg ▸ hfy_mem

open Finset in
theorem aleph_card_gap_two {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M) (hT : IsTaut M) :
    M.support.card + 2 ≤ σ.card := by
  classical
  rcases hσ.vertsOf_nonempty with ⟨v, hv⟩
  have hdeg_card : deg v (bdry M) = (σ.filter (fun s => v ∈ s)).card :=
    aleph_deg_eq_card_filter_of_unitOn hU v
  have hdeg_ge : 3 ≤ deg v (bdry M) := by
    rw [hdeg_card]
    exact aleph_incident_faces_card_ge_three hσ hv
  have hprop := Zvol_add_deg_le v (bdry_bdry M)
  have hvol : Zvol (bdry M) = nrm M := hT.symm
  have hnrm_bdry : nrm (bdry M) = σ.card := UnitOn.nrm_eq hU
  have hnrmM : nrm M = M.support.card := nrm_eq_support_card_of_simplicial hS
  omega

/-- **Per-vertex degree gap.** Strengthening of `aleph_card_gap_two`: for *every* vertex `v`,
`M.support.card + deg v (bdry M) ≤ σ.card`.  Same proof as `aleph_card_gap_two` but without picking a
minimum-degree vertex — `Zvol_add_deg_le v` (Prop 2) on the closed chain `bdry M`, rewritten through
`IsTaut` (`Zvol (bdry M) = nrm M`), `nrm M = |M.support|`, and `nrm (bdry M) = σ.card`.  This supplies
the `deg v` bound the eligible-tet family count needs. -/
theorem aleph_card_gap_deg {M : Chain V} {σ : Finset (Finset V)}
    (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M) (hT : IsTaut M) (v : V) :
    M.support.card + deg v (bdry M) ≤ σ.card := by
  have hprop := Zvol_add_deg_le v (bdry_bdry M)
  have hvol : Zvol (bdry M) = nrm M := hT.symm
  have hnrm_bdry : nrm (bdry M) = σ.card := UnitOn.nrm_eq hU
  have hnrmM : nrm M = M.support.card := nrm_eq_support_card_of_simplicial hS
  omega

open Finset in
open scoped BigOperators in
theorem aleph_two_double_fibers (α β : Type*) [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)
    (hmap : ∀ a ∈ s, f a ∈ t)
    (hcard : t.card + 2 ≤ s.card)
    (hfiber_le2 : ∀ b ∈ t, (s.filter (fun a => f a = b)).card ≤ 2) :
    ∃ b₁ ∈ t, ∃ b₂ ∈ t, b₁ ≠ b₂ ∧
      (s.filter (fun a => f a = b₁)).card = 2 ∧
      (s.filter (fun a => f a = b₂)).card = 2 := by
  classical
  let g : β → ℕ := fun b => (s.filter (fun a => f a = b)).card
  let D : Finset β := t.filter (fun b => g b = 2)
  have hsum : s.card = ∑ b ∈ t, g b := by
    dsimp [g]
    exact Finset.card_eq_sum_card_fiberwise (by
      intro a ha
      exact hmap a ha)
  have hterm_le : ∀ b ∈ t, g b ≤ 1 + if g b = 2 then 1 else 0 := by
    intro b hb
    have hle2 : g b ≤ 2 := by
      dsimp [g]
      exact hfiber_le2 b hb
    by_cases h2 : g b = 2
    · simpa [h2]
    · have hle1 : g b ≤ 1 := by omega
      simpa [h2] using hle1
  have hsum_rhs : (∑ b ∈ t, (1 + if g b = 2 then 1 else 0)) = t.card + D.card := by
    dsimp [D]
    rw [Finset.sum_add_distrib]
    rw [Finset.card_eq_sum_ones t]
    rw [Finset.card_filter]
  have hsum_le : s.card ≤ t.card + D.card := by
    calc
      s.card = ∑ b ∈ t, g b := hsum
      _ ≤ ∑ b ∈ t, (1 + if g b = 2 then 1 else 0) := by
        exact Finset.sum_le_sum (by
          intro b hb
          exact hterm_le b hb)
      _ = t.card + D.card := hsum_rhs
  have hDcard : 2 ≤ D.card := by
    omega
  have hDcard_lt : 1 < D.card := by omega
  obtain ⟨b₁, hb₁D, b₂, hb₂D, hne⟩ := (Finset.one_lt_card.mp hDcard_lt)
  have hb₁D' : b₁ ∈ t ∧ g b₁ = 2 := by
    simpa [D] using hb₁D
  have hb₂D' : b₂ ∈ t ∧ g b₂ = 2 := by
    simpa [D] using hb₂D
  rcases hb₁D' with ⟨hb₁t, hb₁eq⟩
  rcases hb₂D' with ⟨hb₂t, hb₂eq⟩
  refine ⟨b₁, hb₁t, b₂, hb₂t, hne, ?_, ?_⟩
  · simpa [g] using hb₁eq
  · simpa [g] using hb₂eq


/-- M25b: a no-degree-3 taut filling has two distinct eligible tets whose shared
boundary-face pairs are disjoint (needed by case-1's multiplicity-2 argument). -/
theorem aleph_disjoint_eligible_pair {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M) (hT : IsTaut M)
    (hPure : ∀ t ∈ M.support, t.card = 4) (hNo3 : NoDegree3Vertex σ) :
    ∃ t₁ t₂, t₁ ≠ t₂ ∧ EligibleTet M t₁ ∧ EligibleTet M t₂ ∧
      Disjoint (sharedFaces M t₁) (sharedFaces M t₂) := by
  classical
  have hcov : ∀ α ∈ σ, ∃ t, ProperBoundaryFaceTet M α t := fun α hα =>
    exists_properBoundaryFaceTet hS hPure (hU.2 α hα)
  let f : {α // α ∈ σ} → {t // t ∈ M.support} := fun α =>
    ⟨Classical.choose (hcov α.1 α.2), (Classical.choose_spec (hcov α.1 α.2)).1⟩
  have hfspec : ∀ α : {α // α ∈ σ}, ProperBoundaryFaceTet M (α : Finset V) ((f α) : Finset V) := fun α =>
    Classical.choose_spec (hcov α.1 α.2)
  have hShared2 : ∀ t ∈ M.support, (sharedFaces M t).card ≤ 2 := by
    intro t ht
    exact sharedFaces_card_le_two_of_noDegree3 hσ hU hNo3 (hPure t ht)
  have hgap : M.support.card + 2 ≤ σ.card := aleph_card_gap_two hσ hU hS hT
  have hmap : ∀ a ∈ (Finset.univ : Finset {α // α ∈ σ}), f a ∈ (Finset.univ : Finset {t // t ∈ M.support}) := by
    intro a ha
    exact Finset.mem_univ _
  have hcard : (Finset.univ : Finset {t // t ∈ M.support}).card + 2 ≤ (Finset.univ : Finset {α // α ∈ σ}).card := by
    rw [Finset.card_univ, Finset.card_univ, Fintype.card_coe, Fintype.card_coe]
    exact hgap
  have hfiber_le2 : ∀ b ∈ (Finset.univ : Finset {t // t ∈ M.support}),
      ((Finset.univ : Finset {α // α ∈ σ}).filter (fun a => f a = b)).card ≤ 2 := by
    intro b hb
    have hle_shared : (alephChosenFiber f b).card ≤ (sharedFaces M (b : Finset V)).card :=
      aleph_chosenFiber_card_le_sharedFaces hU f hfspec b
    have hle2 : (sharedFaces M (b : Finset V)).card ≤ 2 := hShared2 (b : Finset V) b.property
    exact le_trans hle_shared hle2
  rcases aleph_two_double_fibers {α // α ∈ σ} {t // t ∈ M.support}
      (Finset.univ : Finset {α // α ∈ σ}) (Finset.univ : Finset {t // t ∈ M.support}) f
      hmap hcard hfiber_le2 with ⟨τ₁, hτ₁mem, τ₂, hτ₂mem, hne, hτ₁card, hτ₂card⟩
  have hτ₁dbl : (alephChosenFiber f τ₁).card = 2 := by
    simpa only [alephChosenFiber] using hτ₁card
  have hτ₂dbl : (alephChosenFiber f τ₂).card = 2 := by
    simpa only [alephChosenFiber] using hτ₂card
  rcases aleph_double_fiber_eligible hU hPure hShared2 f hfspec τ₁ hτ₁dbl with ⟨helig₁, hshared₁⟩
  rcases aleph_double_fiber_eligible hU hPure hShared2 f hfspec τ₂ hτ₂dbl with ⟨helig₂, hshared₂⟩
  refine ⟨(τ₁ : Finset V), (τ₂ : Finset V), ?_, helig₁, helig₂, ?_⟩
  · intro hval
    apply hne
    exact Subtype.ext hval
  · rw [hshared₁, hshared₂]
    exact aleph_chosenFaceFibers_disjoint f hne


/-- **Theorem 2's core, reduced to the prime step.** With `aleph_base` and
`aleph_deg3_split` discharging two of `theorem2_core`'s three hypotheses, a taut
filling of a 2-sphere is a ball provided the no-degree-3 step `prime_step` holds. -/
theorem theorem2_modulo_prime_step
    (prime_step : ∀ (σ : Finset (Finset V)) (X M : Chain V), IsSphere2 σ →
      4 < (vertsOf σ).card → UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M →
      SimplicialChain M → NoDegree3Vertex σ →
      (∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
        UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
        IsBall M'.support σ') →
      IsBall M.support σ)
    {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ) (hU : UnitOn X σ)
    (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M) :
    IsBall M.support σ :=
  theorem2_core aleph_base aleph_deg3_split prime_step hσ hU hXc hMX hT hS

end Taut
