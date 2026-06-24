import Taut.Theorem2

/-!
# Eligible tets

For the Theorem-2 induction we need, in a no-degree-3 taut filling, an *eligible*
tet — one sharing two oriented faces with the boundary.
The route (paper §"Filling a triangulation of the 2-sphere", the 2-to-1 count):

* every boundary face `α` (`∂M α = ±1`) is a *properly oriented* face of some tet
  of `M` — `∂M α` is a sum of `{-1,0,1}` tet contributions, so one of them equals
  `∂M α`. The tet is chosen, not unique;
* the choice map `σ → M.support` has fibers `⊆ sharedFaces`, hence (no deg-3)
  `≤ 2`; a *double* fiber is an eligible tet;
* a count + Prop 2 (`Zvol_add_deg_le`) forces a double fiber to exist.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

lemma tetContribution_apply (M : Chain V) (t α : Finset V) :
    tetContribution M t α = M t * bdryGen t α := by
  rw [tetContribution, bdry_single, Finsupp.smul_apply, smul_eq_mul]

lemma bdryGen_apply_mem_pm (t α : Finset V) :
    bdryGen t α = -1 ∨ bdryGen t α = 0 ∨ bdryGen t α = 1 := by
  by_cases h : ∃ x ∈ t, α = t.erase x
  · obtain ⟨x, hx, rfl⟩ := h
    rw [bdryGen_apply_erase_of_mem hx]
    rcases mul_self_eq_one_iff.mp (sgn_mul_self x t) with h1 | h1
    · exact Or.inr (Or.inr h1)
    · exact Or.inl h1
  · push_neg at h
    refine Or.inr (Or.inl ?_)
    rw [bdryGen, Finset.sum_apply']
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (h x hx), smul_zero]

/-- `α` is a *properly oriented boundary face* of the tet `t`: a genuine tet of
`M` whose contribution at `α` accounts for the whole boundary coefficient. -/
def ProperBoundaryFaceTet (M : Chain V) (α t : Finset V) : Prop :=
  t ∈ M.support ∧ α ∈ tetFaces t ∧ (bdry M) α = tetContribution M t α

/-- **Every boundary face is properly oriented by some tet.** `∂M α = ±1` is a
sum of `{-1,0,1}` tet contributions, so one of them equals `∂M α`. -/
lemma exists_properBoundaryFaceTet {M : Chain V} (hS : SimplicialChain M)
    (hPure : ∀ t ∈ M.support, t.card = 4) {α : Finset V}
    (hαpm : (bdry M) α = 1 ∨ (bdry M) α = -1) :
    ∃ t, ProperBoundaryFaceTet M α t := by
  have hbound : ∀ t ∈ M.support, M t * bdryGen t α = -1 ∨ M t * bdryGen t α = 0
      ∨ M t * bdryGen t α = 1 := by
    intro t _
    rcases hS t with hm | hm | hm <;> rcases bdryGen_apply_mem_pm t α with hg | hg | hg <;>
      rw [hm, hg] <;> decide
  have hsum : bdry M α = ∑ t ∈ M.support, M t * bdryGen t α := bdry_apply_eq_sum M α
  have hkey : ∃ t ∈ M.support, M t * bdryGen t α = bdry M α := by
    by_contra hcon
    push_neg at hcon
    rcases hαpm with hp | hp
    · have hle : (∑ t ∈ M.support, M t * bdryGen t α) ≤ 0 := by
        refine Finset.sum_nonpos fun t ht => ?_
        rcases hbound t ht with h | h | h
        · rw [h]; decide
        · rw [h]
        · exact absurd (h.trans hp.symm) (hcon t ht)
      rw [← hsum, hp] at hle; exact absurd hle (by decide)
    · have hge : (0 : ℤ) ≤ ∑ t ∈ M.support, M t * bdryGen t α := by
        refine Finset.sum_nonneg fun t ht => ?_
        rcases hbound t ht with h | h | h
        · exact absurd (h.trans hp.symm) (hcon t ht)
        · rw [h]
        · rw [h]; decide
      rw [← hsum, hp] at hge; exact absurd hge (by decide)
  obtain ⟨t, ht, hval⟩ := hkey
  refine ⟨t, ht, ?_, ?_⟩
  · have hgne : bdryGen t α ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hval
      rcases hαpm with hp | hp <;> rw [hp] at hval <;> exact absurd hval.symm (by decide)
    obtain ⟨w, hw, hαe⟩ := exists_facet_of_bdryGen_ne_zero hgne
    exact hαe ▸ erase_mem_tetFaces (hPure t ht) hw
  · rw [tetContribution_apply, hval]

/-- **One eligible tet exists**, given the no-degree-3 face bound
`sharedFaces ≤ 2`. Two boundary faces collide under the face→tet choice map
(there are more faces than tets, by Prop 2), so their common tet has two shared,
coefficient-matched faces — an eligible tet. -/
theorem exists_eligibleTet {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M) (hT : IsTaut M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hShared2 : ∀ t ∈ M.support, (sharedFaces M t).card ≤ 2) :
    ∃ t, EligibleTet M t := by
  classical
  have hcov : ∀ α ∈ σ, ∃ t, ProperBoundaryFaceTet M α t := fun α hα =>
    exists_properBoundaryFaceTet hS hPure (hU.2 α hα)
  let f : {α // α ∈ σ} → {t // t ∈ M.support} := fun α =>
    ⟨Classical.choose (hcov α.1 α.2), (Classical.choose_spec (hcov α.1 α.2)).1⟩
  have hfspec : ∀ α : {α // α ∈ σ}, ProperBoundaryFaceTet M α.1 (f α).1 := fun α =>
    Classical.choose_spec (hcov α.1 α.2)
  -- Prop 2: more boundary faces than tets
  have hcard : M.support.card < σ.card := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ vert (bdry M) := by
      obtain ⟨s, hs⟩ := hσ.nonempty
      obtain ⟨y, hy⟩ : s.Nonempty := by rw [← Finset.card_pos, hσ.pure s hs]; omega
      exact ⟨y, mem_vert.mpr ⟨s, hU.1 ▸ hs, hy⟩⟩
    have hdeg : 1 ≤ deg x (bdry M) := Nat.pos_of_ne_zero fun h => (deg_eq_zero_iff.mp h) hx
    have h2 := Zvol_add_deg_le x (bdry_bdry M)
    rw [← hT, UnitOn.nrm_eq hU, nrm_eq_support_card_of_simplicial hS] at h2
    omega
  obtain ⟨α₁, _, α₂, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset {α // α ∈ σ}))
      (t := (Finset.univ : Finset {t // t ∈ M.support})) (f := f)
      (by rw [Finset.card_univ, Finset.card_univ, Fintype.card_coe, Fintype.card_coe]; exact hcard)
      (fun a _ => Finset.mem_univ _)
  have ht : (f α₁).1 ∈ M.support := (f α₁).2
  have hαne : (α₁ : Finset V) ≠ (α₂ : Finset V) := fun h => hne (Subtype.ext h)
  have htt : (f α₁).1 = (f α₂).1 := congrArg Subtype.val heq
  have hα₁sh : (α₁ : Finset V) ∈ sharedFaces M (f α₁).1 :=
    Finset.mem_inter.mpr ⟨(hfspec α₁).2.1, hU.1 ▸ α₁.2⟩
  have hα₂sh : (α₂ : Finset V) ∈ sharedFaces M (f α₁).1 :=
    Finset.mem_inter.mpr ⟨htt ▸ (hfspec α₂).2.1, hU.1 ▸ α₂.2⟩
  have hsub : ({(α₁ : Finset V), (α₂ : Finset V)} : Finset (Finset V)) ⊆ sharedFaces M (f α₁).1 := by
    intro s hs; rw [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl; exacts [hα₁sh, hα₂sh]
  have hc2 : (sharedFaces M (f α₁).1).card = 2 := by
    have hge : 2 ≤ (sharedFaces M (f α₁).1).card :=
      (Finset.card_pair hαne).symm.le.trans (Finset.card_le_card hsub)
    have := hShared2 _ ht; omega
  refine ⟨(f α₁).1, hPure _ ht, ht, hc2, fun s hs => ?_⟩
  have hsharedEq : sharedFaces M (f α₁).1 = {(α₁ : Finset V), (α₂ : Finset V)} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hc2, Finset.card_pair hαne])).symm
  rw [hsharedEq, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact (hfspec α₁).2.2
  · rw [htt]; exact (hfspec α₂).2.2

/-! ## The no-degree-3 face bound

The hard combinatorial step: a tet with three boundary faces forces a degree-3
vertex. Those three faces of `t` share a common vertex `d`; the three σ-faces
make the other three vertices of `t` a 3-cycle in the link of `d`; 2-regularity
(`link_two_regular`) pins each cycle vertex's neighbours to the cycle, and
`linkConn` then traps the whole link inside it — so `d` has link exactly 3. -/

/-- A vertex of `σ` whose link has exactly three vertices (degree 3). -/
def HasDegree3Vertex (σ : Finset (Finset V)) : Prop :=
  ∃ v ∈ vertsOf σ, (linkVerts σ v).card = 3

/-- `σ` has no degree-3 vertex (the primality consequence the count needs). -/
def NoDegree3Vertex (σ : Finset (Finset V)) : Prop :=
  ∀ v ∈ vertsOf σ, (linkVerts σ v).card ≠ 3

lemma walk_mem_of_adj_closed {G : SimpleGraph V} {S : Finset V}
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) {a x : V} (w : G.Walk a x) :
    a ∈ S → x ∈ S := by
  induction w with
  | nil => exact id
  | cons hadj _ ih => exact fun ha => ih (hclosed _ ha _ hadj)

/-- **Three boundary faces force a degree-3 vertex.** If three of an eligible
tet's four faces lie on `σ`, the shared vertex `d` of those faces has link
exactly the opposite triangle. -/
lemma exists_degree3Vertex_of_three_sharedFaces {σ : Finset (Finset V)}
    {M : Chain V} {t : Finset V} (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ)
    (ht4 : t.card = 4) (h3 : 3 ≤ (sharedFaces M t).card) :
    HasDegree3Vertex σ := by
  classical
  obtain ⟨d, hd, hdshared⟩ :
      ∃ d ∈ t, ∀ x ∈ t, x ≠ d → t.erase x ∈ sharedFaces M t := by
    have hexp1 : (exposedFaces M t).card ≤ 1 := by
      rw [exposedFaces, Finset.card_sdiff_of_subset (sharedFaces_subset_tetFaces M t),
        card_tetFaces ht4]; omega
    rcases Finset.eq_empty_or_nonempty (exposedFaces M t) with hemp | ⟨F, hF⟩
    · obtain ⟨d, hd⟩ : t.Nonempty := Finset.card_pos.mp (by rw [ht4]; omega)
      refine ⟨d, hd, fun x hx _ => ?_⟩
      by_contra hns
      have : t.erase x ∈ exposedFaces M t :=
        Finset.mem_sdiff.mpr ⟨erase_mem_tetFaces ht4 hx, hns⟩
      rw [hemp] at this; exact absurd this (by simp)
    · obtain ⟨e, he, hFe⟩ :=
        exists_erase_eq_of_mem_tetFaces ht4 (exposedFaces_subset_tetFaces M t hF)
      refine ⟨e, he, fun x hx hxe => ?_⟩
      by_contra hns
      have hxexp : t.erase x ∈ exposedFaces M t :=
        Finset.mem_sdiff.mpr ⟨erase_mem_tetFaces ht4 hx, hns⟩
      have h1card : (exposedFaces M t).card = 1 :=
        le_antisymm hexp1 (Finset.card_pos.mpr ⟨F, hF⟩)
      obtain ⟨G, hG⟩ := Finset.card_eq_one.mp h1card
      have hxeq : t.erase x = t.erase e := by
        rw [hG, Finset.mem_singleton] at hxexp hF; rw [hxexp, ← hF, hFe]
      apply hxe
      by_contra hxene
      have : x ∈ t.erase e := Finset.mem_erase.mpr ⟨hxene, hx⟩
      rw [← hxeq] at this; exact Finset.notMem_erase x t this
  have hface : ∀ x ∈ t, x ≠ d → t.erase x ∈ σ := fun x hx hxd => by
    have := hdshared x hx hxd
    rw [sharedFaces, Finset.mem_inter] at this; exact hU.1 ▸ this.2
  have hcardL : (t.erase d).card = 3 := by rw [Finset.card_erase_of_mem hd, ht4]
  have hdv : d ∈ vertsOf σ := by
    obtain ⟨x, hx⟩ : (t.erase d).Nonempty := Finset.card_pos.mp (by rw [hcardL]; omega)
    have hxt := Finset.mem_of_mem_erase hx
    have hxd := Finset.ne_of_mem_erase hx
    exact mem_vertsOf.mpr ⟨t.erase x, hface x hxt hxd, Finset.mem_erase.mpr ⟨Ne.symm hxd, hd⟩⟩
  have hcyc : ∀ y ∈ t.erase d, ∀ z ∈ t.erase d, y ≠ z → (linkGraph σ d).Adj y z := by
    intro y hy z hz hyz
    have hyt := Finset.mem_of_mem_erase hy
    have hzt := Finset.mem_of_mem_erase hz
    have hyd := Finset.ne_of_mem_erase hy
    have hzd := Finset.ne_of_mem_erase hz
    have hsub : ({d, y, z} : Finset V) ⊆ t := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl; exacts [hd, hyt, hzt]
    have hc3 : ({d, y, z} : Finset V).card = 3 :=
      Finset.card_eq_three.mpr ⟨d, y, z, fun h => hyd h.symm, fun h => hzd h.symm, hyz, rfl⟩
    obtain ⟨w, hwt, hweq⟩ :=
      exists_erase_eq_of_mem_tetFaces ht4 (Finset.mem_powersetCard.mpr ⟨hsub, hc3⟩)
    have hwd : w ≠ d := by
      rintro rfl
      exact (Finset.notMem_erase w t) (hweq ▸ Finset.mem_insert_self w {y, z})
    exact ⟨hyz, by rw [hweq]; exact hface w hwt hwd⟩
  have hL_sub_link : t.erase d ⊆ linkVerts σ d := by
    intro y hy
    have hyt := Finset.mem_of_mem_erase hy
    have hyd := Finset.ne_of_mem_erase hy
    obtain ⟨x, hx, hxd, hxy⟩ : ∃ x ∈ t, x ≠ d ∧ x ≠ y := by
      have h2 : 2 ≤ ((t.erase d).erase y).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hyd, hyt⟩), hcardL]
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < ((t.erase d).erase y).card)
      exact ⟨x, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx),
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx), Finset.ne_of_mem_erase hx⟩
    exact mem_linkVerts.mpr ⟨hyd, t.erase x, hface x hx hxd,
      Finset.mem_erase.mpr ⟨Ne.symm hxd, hd⟩, Finset.mem_erase.mpr ⟨Ne.symm hxy, hyt⟩⟩
  have hadj_mem : ∀ {u v}, (linkGraph σ d).Adj u v → v ∈ linkVerts σ d := by
    intro u v hadjuv
    obtain ⟨_, hf⟩ := hadjuv
    have hc3 := hσ.pure _ hf
    have hvd : v ≠ d := by
      intro h
      have hsub : ({d, u, v} : Finset V) ⊆ {d, u} := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
        rcases ha with rfl | rfl | rfl
        exacts [Or.inl rfl, Or.inr rfl, Or.inl h]
      have hle : ({d, u, v} : Finset V).card ≤ 2 := (Finset.card_le_card hsub).trans
        ((Finset.card_insert_le d {u}).trans (by simp))
      omega
    exact mem_linkVerts.mpr ⟨hvd, {d, u, v}, hf, by simp, by simp⟩
  have hclosed : ∀ u ∈ t.erase d, ∀ v, (linkGraph σ d).Adj u v → v ∈ t.erase d := by
    intro u hu v hadjuv
    have hreg := link_two_regular hσ (hL_sub_link hu)
    have hsub : (t.erase d).erase u
        ⊆ (linkVerts σ d).filter (fun w => (linkGraph σ d).Adj u w) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨hL_sub_link (Finset.mem_of_mem_erase hz),
        hcyc u hu z (Finset.mem_of_mem_erase hz) (Ne.symm (Finset.ne_of_mem_erase hz))⟩
    have hNeq : (linkVerts σ d).filter (fun w => (linkGraph σ d).Adj u w)
        = (t.erase d).erase u :=
      (Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_erase_of_mem hu, hcardL, hreg])).symm
    have : v ∈ (linkVerts σ d).filter (fun w => (linkGraph σ d).Adj u w) :=
      Finset.mem_filter.mpr ⟨hadj_mem hadjuv, hadjuv⟩
    rw [hNeq] at this; exact Finset.mem_of_mem_erase this
  have hlink_sub : linkVerts σ d ⊆ t.erase d := by
    intro x hx
    obtain ⟨y₀, hy₀⟩ : (t.erase d).Nonempty := Finset.card_pos.mp (by rw [hcardL]; omega)
    obtain ⟨w⟩ := hσ.linkConn d hdv y₀ (hL_sub_link hy₀) x hx
    exact walk_mem_of_adj_closed hclosed w hy₀
  exact ⟨d, hdv, by rw [Finset.Subset.antisymm hlink_sub hL_sub_link, hcardL]⟩

/-- **The no-degree-3 face bound** (discharges `exists_eligibleTet`'s hypothesis):
if `σ` has no degree-3 vertex, no tet has more than two boundary faces. -/
lemma sharedFaces_card_le_two_of_noDegree3 {σ : Finset (Finset V)} {M : Chain V}
    {t : Finset V} (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ)
    (hNo3 : NoDegree3Vertex σ) (ht4 : t.card = 4) :
    (sharedFaces M t).card ≤ 2 := by
  by_contra h
  obtain ⟨v, hv, hcard⟩ := exists_degree3Vertex_of_three_sharedFaces hσ hU ht4 (by omega)
  exact hNo3 v hv hcard

/-- **One eligible tet exists in a no-degree-3 taut filling**: the
`sharedFaces ≤ 2` bound is discharged from `NoDegree3Vertex σ`.
(Deriving `NoDegree3Vertex` from primality is separate.) -/
theorem exists_eligibleTet_of_noDegree3 {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M) (hT : IsTaut M)
    (hPure : ∀ t ∈ M.support, t.card = 4) (hNo3 : NoDegree3Vertex σ) :
    ∃ t, EligibleTet M t :=
  exists_eligibleTet hσ hU hS hT hPure
    (fun t ht => sharedFaces_card_le_two_of_noDegree3 hσ hU hNo3 (hPure t ht))

/-! ## Route-Y bridge scaffolding: coefficient-free geometric eligibility

For removing `SimplicialChain` from the Theorem-2 endpoint via the paper's minimal-counterexample
argument (`text/tautxy/tautxy_formalizable.tex`, `th2`), the eligibility used for *counting* must be
coefficient-free: the count is on support tetrahedra, and a high-multiplicity tet must still be
counted. The Lean `EligibleTet` bakes in an orientation conjunct that, under `UnitOn`, already forces
`M t = ±1` (verified), so it is the wrong notion for the counting step. `GeomEligible` drops that
conjunct. See `notes/taut-to-simplicial-strategy.md`. -/

/-- **Geometric eligibility** (coefficient-free): a support tetrahedron `t` of `M` sharing exactly two
faces with the boundary `∂M` (under `UnitOn`, exactly two faces with `σ`). No coefficient conclusion
is part of this predicate — `t` may have any multiplicity. This is the paper's "shares two faces with
`σ`"; `EligibleTet` is this *plus* an orientation condition. -/
def GeomEligible (M : Chain V) (t : Finset V) : Prop :=
  t.card = 4 ∧ t ∈ M.support ∧ (sharedFaces M t).card = 2

/-- The Lean `EligibleTet` is strictly stronger than geometric eligibility. -/
lemma EligibleTet.geomEligible {M : Chain V} {t : Finset V} (h : EligibleTet M t) :
    GeomEligible M t :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- A geometrically-eligible tet has exactly two exposed (interior) faces. -/
lemma GeomEligible.exposedFaces_card {M : Chain V} {t : Finset V} (h : GeomEligible M t) :
    (exposedFaces M t).card = 2 := by
  rw [exposedFaces, Finset.card_sdiff_of_subset (sharedFaces_subset_tetFaces M t),
    card_tetFaces h.1, h.2.2]

/-- **Avoidance / pigeonhole** (route-neutral): a Finset `E` strictly larger than a forbidden Finset
`F` has a member outside `F`. Applied with `E` an eligible family of supports and `F` the bounded set
of supports touched by a local move/cut, this picks an available `u ∈ E \ F`. -/
lemma exists_mem_not_mem_of_card_lt {α : Type*} [DecidableEq α] {E F : Finset α}
    (h : F.card < E.card) : ∃ u ∈ E, u ∉ F :=
  Finset.not_subset.mp (fun hsub => not_le.mpr h (Finset.card_le_card hsub))

/-- **Same-boundary minimality** (route-Y step 5, the strict-norm contradiction shape): a taut filling
`M` is optimal for its own boundary — no chain `N` with the same boundary has smaller norm. The
Case-1/Case-2 contradictions are instances (a same-boundary chain of strictly smaller norm cannot
exist). Immediate from `IsTaut M : nrm M = Zvol (bdry M)` and `Zvol_le`. -/
lemma IsTaut.le_nrm_of_bdry_eq {M N : Chain V} (hM : IsTaut M) (hbd : bdry N = bdry M) :
    nrm M ≤ nrm N :=
  calc nrm M = Zvol (bdry M) := hM
    _ ≤ nrm N := Zvol_le hbd

/-- Contrapositive packaging of `IsTaut.le_nrm_of_bdry_eq`: no strictly-smaller same-boundary fill. -/
lemma IsTaut.not_nrm_lt_of_bdry_eq {M N : Chain V} (hM : IsTaut M) (hbd : bdry N = bdry M) :
    ¬ nrm N < nrm M :=
  fun h => absurd (hM.le_nrm_of_bdry_eq hbd) (not_le.mpr h)

omit [LinearOrder V] in
/-- The number of distinct support tetrahedra is at most the norm (each contributes `≥ 1`).
Replaces the `SimplicialChain`-only `nrm = support.card` in the counting argument. -/
lemma card_support_le_nrm (M : Chain V) : M.support.card ≤ nrm M := by
  show M.support.card ≤ ∑ s ∈ M.support, (M s).natAbs
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun s hs => Int.natAbs_pos.mpr (Finsupp.mem_support_iff.mp hs)

/-- **The counting lemma** (route-Y, `SimplicialChain`-free): a taut filling of a 2-sphere with no
degree-3 vertex contains a family `E` of pairwise-disjoint (in shared faces) geometrically-eligible
support tetrahedra, of cardinality at least `deg x (∂M)` for every vertex `x`.

Construction: each boundary face is covered by some support tet (`bdry M α ≠ 0` forces a contributing
tet — no orientation/`SimplicialChain` needed); choosing one such tet per face gives `c : σ →
M.support` with fibres `⊆ sharedFaces`, hence `≤ 2`. The fibre-2 tets are exactly the eligible family:
their fibre equals their shared faces (so `GeomEligible`, and pairwise-disjoint shared faces since
fibres of a function are disjoint), and the fibre count `σ.card ≤ E.card + support.card` combines with
`support.card ≤ nrm M = Zvol(∂M) ≤ σ.card − deg x (∂M)` (Prop 2) to give `deg x (∂M) ≤ E.card`. -/
theorem exists_disjoint_geomEligible_family {M : Chain V} {σ : Finset (Finset V)}
    (hU : UnitOn (bdry M) σ) (hT : IsTaut M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hShared2 : ∀ t ∈ M.support, (sharedFaces M t).card ≤ 2) (x : V) :
    ∃ E : Finset (Finset V), E ⊆ M.support ∧ (∀ t ∈ E, GeomEligible M t) ∧
      (↑E : Set (Finset V)).PairwiseDisjoint (fun e => sharedFaces M e) ∧
      deg x (bdry M) ≤ E.card := by
  classical
  -- (1) weak covering: every boundary face is a face of some support tet (no orientation needed)
  have hcov : ∀ α, α ∈ σ → ∃ t, t ∈ M.support ∧ α ∈ tetFaces t := by
    intro α hα
    have hαsupp : α ∈ (bdry M).support := by rw [hU.1]; exact hα
    have hne : (bdry M) α ≠ 0 := Finsupp.mem_support_iff.mp hαsupp
    rw [bdry_apply_eq_sum] at hne
    obtain ⟨t, ht, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hbg : bdryGen t α ≠ 0 := fun h => hterm (by rw [h, mul_zero])
    obtain ⟨w, hw, hαe⟩ := exists_facet_of_bdryGen_ne_zero hbg
    exact ⟨t, ht, hαe ▸ erase_mem_tetFaces (hPure t ht) hw⟩
  -- (2) the covering map (total, junk off σ)
  let f : Finset V → Finset V := fun α => if h : α ∈ σ then (hcov α h).choose else ∅
  have hf_mem : ∀ α ∈ σ, f α ∈ M.support := fun α hα => by
    simp only [f, dif_pos hα]; exact (hcov α hα).choose_spec.1
  have hf_face : ∀ α ∈ σ, α ∈ sharedFaces M (f α) := fun α hα =>
    Finset.mem_inter.mpr ⟨by simp only [f, dif_pos hα]; exact (hcov α hα).choose_spec.2,
      by rw [hU.1]; exact hα⟩
  -- (3) the eligible family = fibre-2 tets
  set E : Finset (Finset V) :=
    M.support.filter (fun t => (σ.filter (fun a => f a = t)).card = 2) with hE_def
  -- fibre ⊆ sharedFaces
  have hfib_sub : ∀ t, σ.filter (fun a => f a = t) ⊆ sharedFaces M t := by
    intro t α hα
    rw [Finset.mem_filter] at hα
    rw [← hα.2]; exact hf_face α hα.1
  -- each E-tet: sharedFaces = fibre, and GeomEligible
  have hElig : ∀ t ∈ E, sharedFaces M t = σ.filter (fun a => f a = t) ∧ GeomEligible M t := by
    intro t ht
    rw [hE_def, Finset.mem_filter] at ht
    obtain ⟨htsupp, htfib2⟩ := ht
    have hsub := hfib_sub t
    have hcard2 : (sharedFaces M t).card = 2 := by
      have h := hShared2 t htsupp
      have hge : 2 ≤ (sharedFaces M t).card := htfib2 ▸ Finset.card_le_card hsub
      omega
    exact ⟨(Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, htfib2])).symm,
      hPure t htsupp, htsupp, hcard2⟩
  refine ⟨E, Finset.filter_subset _ _, fun t ht => (hElig t ht).2, ?_, ?_⟩
  · -- pairwise-disjoint shared faces (fibres of a function are disjoint)
    intro t₁ h₁ t₂ h₂ hne
    simp only [Finset.mem_coe] at h₁ h₂
    show Disjoint (sharedFaces M t₁) (sharedFaces M t₂)
    rw [(hElig t₁ h₁).1, (hElig t₂ h₂).1, Finset.disjoint_left]
    intro α hα₁ hα₂
    rw [Finset.mem_filter] at hα₁ hα₂
    exact hne (hα₁.2.symm.trans hα₂.2)
  · -- cardinality: deg x (∂M) ≤ E.card
    have hsum : σ.card = ∑ t ∈ M.support, (σ.filter (fun a => f a = t)).card :=
      Finset.card_eq_sum_card_fiberwise hf_mem
    have hbound : σ.card ≤ E.card + M.support.card := by
      rw [hsum]
      have hle : ∑ t ∈ M.support, (σ.filter (fun a => f a = t)).card
          ≤ ∑ t ∈ M.support, (1 + if (σ.filter (fun a => f a = t)).card = 2 then 1 else 0) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have h2 : (σ.filter (fun a => f a = t)).card ≤ 2 :=
          (Finset.card_le_card (hfib_sub t)).trans (hShared2 t ht)
        by_cases hc : (σ.filter (fun a => f a = t)).card = 2
        · simp [hc]
        · simp only [hc, if_false, add_zero]; omega
      have heq : ∑ t ∈ M.support, (1 + if (σ.filter (fun a => f a = t)).card = 2 then 1 else 0)
          = M.support.card + E.card := by
        rw [Finset.sum_add_distrib, ← Finset.card_eq_sum_ones, ← Finset.card_filter, ← hE_def]
      omega
    have hdeg : M.support.card + deg x (bdry M) ≤ σ.card := by
      have h2 := Zvol_add_deg_le x (bdry_bdry M)
      rw [UnitOn.nrm_eq hU] at h2
      have hTeq : nrm M = Zvol (bdry M) := hT
      have h3 := card_support_le_nrm M
      omega
    omega

/-- **Avoidance step** (route-Y steps 1–2): given a forbidden Finset `F` of supports strictly smaller
than `deg x (∂M)`, the counting family supplies a geometrically-eligible support `u ∉ F`. The caller
sets `F` to the supports touched by the local cut/flip/removal and chooses `x` of large enough degree.
This is the source of the backup tet `u` in the minimal-counterexample assembly. -/
theorem exists_geomEligible_not_mem {M : Chain V} {σ : Finset (Finset V)}
    (hU : UnitOn (bdry M) σ) (hT : IsTaut M)
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hShared2 : ∀ t ∈ M.support, (sharedFaces M t).card ≤ 2)
    (x : V) (F : Finset (Finset V)) (hF : F.card < deg x (bdry M)) :
    ∃ u, u ∈ M.support ∧ GeomEligible M u ∧ u ∉ F := by
  obtain ⟨E, hEsub, hElig, _, hcard⟩ := exists_disjoint_geomEligible_family hU hT hPure hShared2 x
  obtain ⟨u, huE, huF⟩ := exists_mem_not_mem_of_card_lt (lt_of_lt_of_le hF hcard)
  exact ⟨u, hEsub huE, hElig u huE, huF⟩

end Taut
