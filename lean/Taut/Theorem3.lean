import Taut.Theorem2Aleph
import Taut.Stickerball

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

/-- **Old-target snoc** (L1's old-target half, extracted, with no `hstart_t`): if `τ`
is a free sticker ball and a fresh tet `e` glues onto its boundary, then for any OLD
target `s ∈ τ` there is a shelling of `insert e τ` starting at `s` — namely `(τ's
shelling from s) ++ [e]`.  This is the only half `prime_step`/`deg3_step` need: by
the M25b disjoint-eligible-pair, the removed tet is always chosen `≠ s`, so the
target is always old and the removed tet always glues last. -/
lemma FreelyShellable.exists_shelling_insert_of_glueStep_old
    {τ B B' : Finset (Finset V)} {e s : Finset V}
    (hfree : FreelyShellable τ B) (hg : GlueStep e B B') (heτ : e ∉ τ) (hsτ : s ∈ τ) :
    ∃ l : List (Finset V), l.head? = some s ∧ l.toFinset = insert e τ ∧ l.Nodup ∧
      IsShelling l B' := by
  obtain ⟨l, hhead, hlτ, hnodup, hsh⟩ := hfree s hsτ
  refine ⟨l ++ [e], ?_, ?_, ?_, IsShelling_snoc hsh hg⟩
  · cases l with
    | nil => exact absurd hsh (by simp [IsShelling])
    | cons a r => rw [List.cons_append]; exact hhead
  · rw [List.toFinset_append, hlτ]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_singleton]
    tauto
  · refine hnodup.append (List.nodup_singleton e) ?_
    rw [List.disjoint_left]
    intro a ha
    simp only [List.mem_singleton]
    rintro rfl
    exact heτ (hlτ ▸ List.mem_toFinset.mpr ha)

/-- **base_isPM** (PM base case, ≤ 4 vertices): a taut filling of a 2-sphere on
≤ 4 vertices is a single tetrahedron, hence a pseudomanifold. Mirrors `base_free`,
but ends in `isPseudomanifold_singleton` instead of `freelyShellable_singleton`. -/
lemma base_isPM (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M)
    (hv : (vertsOf σ).card ≤ 4) : IsPseudomanifold M.support := by
  have hcard : (vertsOf σ).card = 4 := aleph_base_verts_card_eq_four hσ hv
  have hsuppInfo := aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
  have hne := aleph_base_support_nonempty hσ hU hMX
  have hsupp : M.support = {vertsOf σ} :=
    aleph_base_support_eq_singleton_of_four_vertices hcard hsuppInfo hne
  rw [hsupp]
  exact isPseudomanifold_singleton (vertsOf σ)

/-- **base_free** (the base hole of `theorem3_core`): a taut filling of a 2-sphere on
≤ 4 vertices is a free sticker ball — it is a single tetrahedron
(`freelyShellable_singleton`). Reuses the Aleph base lemmas verbatim; only the final
step changes from `isBall_singleton` to `freelyShellable_singleton`. -/
theorem base_free (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M) (hS : SimplicialChain M)
    (hv : (vertsOf σ).card ≤ 4) :
    FreelyShellable M.support σ ∧ IsPseudomanifold M.support := by
  refine ⟨?_, base_isPM σ X M hσ hU hMX hT hS hv⟩
  have hcard : (vertsOf σ).card = 4 := aleph_base_verts_card_eq_four hσ hv
  have hσeq : σ = (vertsOf σ).powersetCard 3 := aleph_base_sphere_eq_powersetCard3 hσ hcard
  have hsuppInfo := aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
  have hne := aleph_base_support_nonempty hσ hU hMX
  have hsupp : M.support = {vertsOf σ} :=
    aleph_base_support_eq_singleton_of_four_vertices hcard hsuppInfo hne
  rw [hσeq, hsupp]   -- hσeq first: σ occurs only as the 2nd arg, so no over-rewrite of `vertsOf σ`
  exact freelyShellable_singleton hcard

/-- Degree-3 bridge-start shelling for the star target, with the missing anchor
data made explicit.

The false version tried to derive this from `FreelyShellable τ B` and the star
`GlueStep` alone.  The actual degree-3 use also needs a first remainder tet `t₀`
that glues to the star across the interface face `γ`, plus the fact that the
remaining tets avoid both `γ` and the exposed star faces `K`.  The transport is:
free shell `τ` from `t₀`, glue `t₀` after the star, then replace the carried
interface face by the exposed star boundary piece for the rest of the shelling. -/
lemma degree3_star_start_shellFrom (σ B τ : Finset (Finset V)) {v : V}
    {γ t₀ : Finset V} {K : Finset (Finset V)}
    (hfree : FreelyShellable τ B) (ht₀ : t₀ ∈ τ)
    (hglue₀ : GlueStep t₀ (tetFaces (starTet σ v)) ((tetFaces t₀).erase γ ∪ K))
    (hrest_disj : ∀ t ∈ τ, t ≠ t₀ → Disjoint (tetFaces t) (insert γ K))
    (hfinal : σ = B.erase γ ∪ K) :
    ∃ l : List (Finset V), l.toFinset = τ ∧ l.Nodup ∧
      ShellFrom (tetFaces (starTet σ v)) l σ := by
  obtain ⟨l, hhead, hlτ, hnodup, hsh⟩ := hfree t₀ ht₀
  cases l with
  | nil =>
      simp at hhead
  | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst a
      simp only [IsShelling] at hsh
      have htail_disj : ∀ t ∈ rest, Disjoint (tetFaces t) (insert γ K) := by
        intro t ht
        exact hrest_disj t (hlτ ▸ List.mem_toFinset.mpr (List.mem_cons.mpr (Or.inr ht)))
          (by
            intro h
            subst t
            exact (List.nodup_cons.mp hnodup).1 ht)
      have htransport :
          ShellFrom ((tetFaces t₀).erase γ ∪ K) rest (B.erase γ ∪ K) :=
        ShellFrom_erase_union_disjoint hsh.2 htail_disj
      refine ⟨t₀ :: rest, hlτ, hnodup, ?_⟩
      simp only [ShellFrom]
      exact ⟨(tetFaces t₀).erase γ ∪ K, hglue₀, hfinal ▸ htransport⟩

/-- If the `W` capped side is the degree-3 star, then the opposite capped side has
no apex vertex.  The two capped sides overlap only in the link triangle `γ`, and
`v` is not a vertex of its own link. -/
lemma degree3_apex_notMem_right_verts_of_left_star {σ : Finset (Finset V)}
    {v : V} {W : C2 σ} {γ : Finset V}
    (hσ : IsSphere2 σ) (h3 : (linkVerts σ v).card = 3)
    (hγ : γ = linkVerts σ v)
    (hW : bd2 σ W = gammaChain σ γ)
    (hstar : insert γ (cutSet σ W) = tetFaces (starTet σ v)) :
    v ∉ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := by
  classical
  intro hvR
  have hT4 : (starTet σ v).card = 4 := starTet_card_of_degree3 σ h3
  have hvT : v ∈ starTet σ v := by simp [starTet]
  have hvL : v ∈ vertsOf (insert γ (cutSet σ W)) := by
    rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4]
    exact hvT
  have hvinter : v ∈ vertsOf (insert γ (cutSet σ W)) ∩
      vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := by
    exact Finset.mem_inter.mpr ⟨hvL, hvR⟩
  have hinter := vertsOf_cut_inter hσ hW
  rw [hinter] at hvinter
  have hvγ : v ∉ γ := by simp [hγ, linkVerts]
  exact hvγ hvinter

/-- If the `W + 1` capped side is the degree-3 star, then the opposite capped side
has no apex vertex. -/
lemma degree3_apex_notMem_left_verts_of_right_star {σ : Finset (Finset V)}
    {v : V} {W : C2 σ} {γ : Finset V}
    (hσ : IsSphere2 σ) (h3 : (linkVerts σ v).card = 3)
    (hγ : γ = linkVerts σ v)
    (hW : bd2 σ W = gammaChain σ γ)
    (hstar : insert γ (cutSet σ (W + fun _ => 1)) = tetFaces (starTet σ v)) :
    v ∉ vertsOf (insert γ (cutSet σ W)) := by
  classical
  intro hvL
  have hT4 : (starTet σ v).card = 4 := starTet_card_of_degree3 σ h3
  have hvT : v ∈ starTet σ v := by simp [starTet]
  have hvR : v ∈ vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := by
    rw [hstar, vertsOf_tetFaces_eq (starTet σ v) hT4]
    exact hvT
  have hvinter : v ∈ vertsOf (insert γ (cutSet σ W)) ∩
      vertsOf (insert γ (cutSet σ (W + fun _ => 1))) := by
    exact Finset.mem_inter.mpr ⟨hvL, hvR⟩
  have hinter := vertsOf_cut_inter hσ hW
  rw [hinter] at hvinter
  have hvγ : v ∉ γ := by simp [hγ, linkVerts]
  exact hvγ hvinter

/-- **Degree-3 anchor target.** In the degree-3 cut context, once one side is the
star tetrahedron and the other capped side is a freely shellable remainder, the
remainder has an anchor tetrahedron `t₀` adjacent to the star through the capped
interface face `γ`. The remaining tetrahedra avoid both `γ` and the exposed star
faces `K`, and erasing the cap from the capped side while restoring `K` recovers
the original sphere.

This is intentionally packaged as a single Prop-shaped geometry target for
AlephProver; `deg3_step_free` uses it for both symmetric cut branches. -/
lemma degree3_hanchor (sigma sigmaR : Finset (Finset V)) (MR : Chain V)
    (M : Chain V) (sideVerts : Finset V) (useInside : Bool)
    (v : V) (W : C2 sigma) (γ : Finset V)
    (hsigma : IsSphere2 sigma) (hbig : 4 < (vertsOf sigma).card)
    (hv : v ∈ vertsOf sigma)
    (hγ : γ = linkVerts sigma v) (hγ3 : (linkVerts sigma v).card = 3)
    (hW : bd2 sigma W = gammaChain sigma (linkVerts sigma v))
    (hσR : IsSphere2 sigmaR)
    (hUR : UnitOn (bdry MR) sigmaR)
    (hfreeR : FreelyShellable MR.support sigmaR)
    (hSimpR : SimplicialChain MR)
    (hTautR : IsTaut MR)
    (hPMR : IsPseudomanifold MR.support)
    (hStarNotMR : starTet sigma v ∉ MR.support)
    (hvNotMR : ∀ t ∈ MR.support, v ∉ t)
    (hsideVerts : sideVerts = vertsOf (insert γ (cutSet sigma W)))
    (hMR_actual :
      MR = M.filter (fun t => if useInside then t ⊆ sideVerts else ¬ t ⊆ sideVerts))
    (hsigmaR_cut :
      sigmaR = insert γ (cutSet sigma W) ∨
      sigmaR = insert γ (cutSet sigma (W + fun _ => 1))) :
    ∃ t₀ K,
      t₀ ∈ MR.support ∧
      GlueStep t₀ (tetFaces (starTet sigma v)) ((tetFaces t₀).erase γ ∪ K) ∧
      (∀ t ∈ MR.support, t ≠ t₀ → Disjoint (tetFaces t) (insert γ K)) ∧
      sigma = sigmaR.erase γ ∪ K := by
  -- Residual degree-3 geometry target: find the first non-star tetrahedron
  -- meeting the capped face `γ`, with the exposed star faces carried as `K`.
  sorry

/-- **deg3 clean-glue (PM version).** The clean-glue obligation for inserting the
degree-3 star tet onto the remainder side `R`. A triangle `f` of `starTet σ v`
either contains the apex `v` — then no remainder tet contains it (`hvNotR`), so it
lies in zero remainder tets — or it is the link triangle `γ`, which is a boundary
face of `R` (it is in `σR` and `R`'s boundary is unit on `σR`), so it lies in
exactly one remainder tet by `faceCount_eq_one_of_boundary`. -/
lemma deg3_clean_glue_of_remainder {σ : Finset (Finset V)} {R : Chain V}
    {v : V} {γ : Finset V}
    (hγ : γ = linkVerts σ v) (hT4 : (starTet σ v).card = 4)
    (hURγ : bdry R γ = 1 ∨ bdry R γ = -1)
    (hPMR : IsPseudomanifold R.support) (hSR : SimplicialChain R)
    (hPureR : ∀ t ∈ R.support, t.card = 4)
    (hvNotR : ∀ t ∈ R.support, v ∉ t) :
    ∀ f, f.card = 3 → f ⊆ starTet σ v → faceCount R.support f ≤ 1 := by
  classical
  intro f hf3 hfstar
  by_cases hvf : v ∈ f
  · -- v ∈ f: no remainder tet can contain f (it would contain v)
    have h0 : faceCount R.support f = 0 := by
      apply faceCount_eq_zero
      intro t ht hft
      exact hvNotR t ht (hft hvf)
    omega
  · -- v ∉ f: f ⊆ insert v γ and v ∉ f force f = γ, a unit boundary face
    have hfγ : f ⊆ γ := by
      intro x hx
      have hx' : x ∈ insert v γ := by
        have : f ⊆ insert v γ := by rw [hγ] at *; simpa [starTet, hγ] using hfstar
        exact this hx
      rcases Finset.mem_insert.mp hx' with rfl | hxγ
      · exact absurd hx hvf
      · exact hxγ
    have hγcard : γ.card = 3 := by
      rw [hγ]
      have : (starTet σ v).card = 4 := hT4
      simpa [starTet, hγ, Finset.card_insert_of_notMem
        (by simp [hγ, linkVerts] : v ∉ linkVerts σ v)] using this
    have hfeqγ : f = γ := Finset.eq_of_subset_of_card_le hfγ (by rw [hγcard, hf3])
    subst hfeqγ
    have h1 : faceCount R.support f = 1 :=
      faceCount_eq_one_of_boundary hSR hPureR hPMR hf3 hURγ
    omega

/-- **deg3_isPM** (PM degree-3 step): a taut filling of a 2-sphere with a degree-3
vertex is a pseudomanifold, given that every strictly smaller single-sphere taut
filling is one. Mirrors the *setup* of `deg3_step_free` (the cut, the ML/MR
filters, the star-side dichotomy, `hsupport`/`hTnot`/`hvNotR`), but instead of the
star-shelling glue it applies the IH to the remainder to get a PM, then re-inserts
the star tet with `isPseudomanifold_insert`, discharging the clean-glue obligation
by `deg3_clean_glue_of_remainder`. Does NOT use `degree3_hanchor`. -/
lemma deg3_isPM (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hbig : 4 < (vertsOf σ).card) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hd3 : HasDegree3Vertex σ)
    (IHpm : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      IsPseudomanifold M'.support) :
    IsPseudomanifold M.support := by
  classical
  obtain ⟨v, W, hv, hγ3, hγe, hγσ, hW, hσL, hσR⟩ :=
    degree3_cut_setup σ hσ hbig hd3
  let γ : Finset V := linkVerts σ v
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
  -- γ lies in both candidate remainder spheres
  have hγL : γ ∈ insert γ (cutSet σ W) := Finset.mem_insert_self _ _
  have hγR : γ ∈ insert γ (cutSet σ (W + fun _ => 1)) := Finset.mem_insert_self _ _
  rcases hsplit with hcase | hcase
  · -- left side is the star; remainder is MR (the ¬⊆A side, sphere σR)
    rcases hcase with ⟨hstar, _hglue⟩
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
      IHpm (insert γ (cutSet σ (W + fun _ => 1))) (bdry MR) MR hlt hσRdef hURMR
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
    have hsupport : M.support = insert (starTet σ v) MR.support := by
      simpa only [MR] using
        support_eq_insert_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
    rw [hsupport]
    refine isPseudomanifold_insert hPMR hTnot ?_
    exact deg3_clean_glue_of_remainder rfl hT4 hURγ hPMR hSimpR hPureMR hvNotMR
  · -- right side is the star; remainder is ML (the ⊆A side, sphere σL)
    rcases hcase with ⟨hstar, _hglue⟩
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
      IHpm (insert γ (cutSet σ W)) (bdry ML) ML hlt hσLdef hULML
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
    have hsupport : M.support = insert (starTet σ v) ML.support := by
      have hsupport' :
          M.support = insert (starTet σ v)
            (M.filter (fun t => ¬ (¬ t ⊆ A))).support :=
        support_eq_insert_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
      rwa [← hML_eq] at hsupport'
    rw [hsupport]
    refine isPseudomanifold_insert hPML hTnot ?_
    exact deg3_clean_glue_of_remainder rfl hT4 hURγ hPML hSimpL hPureML hvNotML

/-- Degree-3 step for the free-shelling induction: cut off the degree-3 star,
apply the induction hypothesis to the non-star side, then glue the star tetrahedron
back onto that freely shellable remainder. -/
theorem deg3_step_free (sigma : Finset (Finset V)) (X M : Chain V)
    (hsigma : IsSphere2 sigma) (hbig : 4 < (vertsOf sigma).card)
    (hU : UnitOn X sigma) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hd3 : HasDegree3Vertex sigma)
    (IH : ∀ (sigma' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M →
      IsSphere2 sigma' → UnitOn X' sigma' → bdry X' = 0 → bdry M' = X' →
      IsTaut M' → SimplicialChain M' →
      FreelyShellable M'.support sigma' ∧ IsPseudomanifold M'.support) :
    FreelyShellable M.support sigma ∧ IsPseudomanifold M.support := by
  classical
  refine ⟨?_, deg3_isPM sigma X M hsigma hbig hU hXc hMX hT hS hd3
    (fun σ' X' M' hlt h1 h2 h3 h4 h5 h6 => (IH σ' X' M' hlt h1 h2 h3 h4 h5 h6).2)⟩
  obtain ⟨v, W, hv, hγ3, hγe, hγσ, hW, hσL, hσR⟩ :=
    degree3_cut_setup sigma hsigma hbig hd3
  let γ : Finset V := linkVerts sigma v
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
    have hIHR : FreelyShellable MR.support (insert γ (cutSet sigma (W + fun _ => 1))) ∧
        IsPseudomanifold MR.support :=
      IH (insert γ (cutSet sigma (W + fun _ => 1)))
        (cappedCutRight sigma W X γ c) MR hlt
        (by dsimp [γ]; exact hσR) (by dsimp [γ]; exact hUR)
        (by dsimp [γ]; exact hXRc) (by dsimp [MR, A, γ]; exact hMR)
        (by dsimp [MR, A, γ]; exact hTR) hSimpR
    have hfreeR : FreelyShellable MR.support (insert γ (cutSet sigma (W + fun _ => 1))) :=
      hIHR.1
    have hPMR : IsPseudomanifold MR.support := hIHR.2
    have hPT : (starTet sigma v) ⊆ A := by
      have hTin : starTet sigma v ∈ ML.support := by
        rw [hMLsupp]
        simp
      have hTin' : ¬ M (starTet sigma v) = 0 ∧ (starTet sigma v) ⊆ A := by
        simpa [ML] using hTin
      exact hTin'.2
    have hTnot : starTet sigma v ∉ MR.support := by
      intro hmem
      have hne : MR (starTet sigma v) ≠ 0 := Finsupp.mem_support_iff.mp hmem
      have hzero : MR (starTet sigma v) = 0 := by
        simp [MR, hPT]
      exact hne hzero
    have hvNotMR : ∀ t ∈ MR.support, v ∉ t := by
      have hvNotSigmaR : v ∉ vertsOf (insert γ (cutSet sigma (W + fun _ => 1))) :=
        degree3_apex_notMem_right_verts_of_left_star (σ := sigma) (v := v) (W := W)
          (γ := γ) hsigma hγ3 rfl (by simpa [γ] using hW) hstar
      have hbdMR : bdry MR = cappedCutRight sigma W X γ c := by
        dsimp [MR, A, γ]
        exact hMR
      have hTRMR : IsTaut MR := by
        dsimp [MR, A, γ]
        exact hTR
      have hsuppInfo :
          ∀ t ∈ MR.support,
            t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet sigma (W + fun _ => 1))) :=
        aleph_base_taut_support_card4_subset_verts hσR hUR hbdMR hTRMR
      intro t ht hvt
      exact hvNotSigmaR ((hsuppInfo t ht).2 hvt)
    have hsupport : M.support = insert (starTet sigma v) MR.support := by
      simpa only [MR] using
        support_eq_insert_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
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
        hfreeR hSimpR (by dsimp only [MR, A, γ]; exact hTR) hPMR hTnot hvNotMR rfl
        (by simp [MR])
        (Or.inr rfl)
    obtain ⟨t₀, K, ht₀, hglue₀, hrest_disj, hfinal⟩ := hanchor
    have hstart : ∃ l : List (Finset V), l.toFinset = MR.support ∧ l.Nodup ∧
        ShellFrom (tetFaces (starTet sigma v)) l sigma :=
      degree3_star_start_shellFrom sigma (insert γ (cutSet sigma (W + fun _ => 1)))
        MR.support hfreeR ht₀ hglue₀ hrest_disj hfinal
    rw [hsupport]
    intro s hs
    by_cases hsstar : s = starTet sigma v
    · subst s
      have hfreeInsert : FreelyShellable (insert (starTet sigma v) MR.support) sigma :=
        FreelyShellable.insert_of_glueStep hfreeR hglue hTnot hstart
      exact hfreeInsert (starTet sigma v) (Finset.mem_insert_self _ _)
    · rw [Finset.mem_insert] at hs
      rcases hs with hsnew | hsold
      · exact False.elim (hsstar hsnew)
      · exact FreelyShellable.exists_shelling_insert_of_glueStep_old hfreeR hglue hTnot hsold
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
    have hIHL : FreelyShellable ML.support (insert γ (cutSet sigma W)) ∧
        IsPseudomanifold ML.support :=
      IH (insert γ (cutSet sigma W)) (cappedCutLeft sigma W X γ c) ML hlt
        (by dsimp [γ]; exact hσL) (by dsimp [γ]; exact hUL)
        (by dsimp [γ]; exact hXLc) (by dsimp [ML, A, γ]; exact hML)
        (by dsimp [ML, A, γ]; exact hTL) hSimpL
    have hfreeL : FreelyShellable ML.support (insert γ (cutSet sigma W)) := hIHL.1
    have hPML : IsPseudomanifold ML.support := hIHL.2
    have hPstar : ¬ (starTet sigma v) ⊆ A := by
      have hTin : starTet sigma v ∈ MR.support := by
        rw [hMRsupp]
        simp
      have hTin' : ¬ M (starTet sigma v) = 0 ∧ ¬ (starTet sigma v) ⊆ A := by
        simpa [MR] using hTin
      exact hTin'.2
    have hTnot : starTet sigma v ∉ ML.support := by
      intro hmem
      have hne : ML (starTet sigma v) ≠ 0 := Finsupp.mem_support_iff.mp hmem
      have hzero : ML (starTet sigma v) = 0 := by
        simp [ML, hPstar]
      exact hne hzero
    have hvNotML : ∀ t ∈ ML.support, v ∉ t := by
      have hvNotSigmaL : v ∉ vertsOf (insert γ (cutSet sigma W)) :=
        degree3_apex_notMem_left_verts_of_right_star (σ := sigma) (v := v) (W := W)
          (γ := γ) hsigma hγ3 rfl (by simpa [γ] using hW) hstar
      have hbdML : bdry ML = cappedCutLeft sigma W X γ c := by
        dsimp [ML, A, γ]
        exact hML
      have hTLML : IsTaut ML := by
        dsimp [ML, A, γ]
        exact hTL
      have hsuppInfo :
          ∀ t ∈ ML.support, t.card = 4 ∧ t ⊆ vertsOf (insert γ (cutSet sigma W)) :=
        aleph_base_taut_support_card4_subset_verts hσL hUL hbdML hTLML
      intro t ht hvt
      exact hvNotSigmaL ((hsuppInfo t ht).2 hvt)
    have hsupport : M.support = insert (starTet sigma v) ML.support := by
      have hsupport' :
          M.support = insert (starTet sigma v)
            (M.filter (fun t => ¬ (¬ t ⊆ A))).support := by
        exact support_eq_insert_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
      rwa [← hML_eq] at hsupport'
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
        hfreeL hSimpL (by dsimp only [ML, A, γ]; exact hTL) hPML hTnot hvNotML rfl
        (by simp [ML])
        (Or.inl rfl)
    obtain ⟨t₀, K, ht₀, hglue₀, hrest_disj, hfinal⟩ := hanchor
    have hstart : ∃ l : List (Finset V), l.toFinset = ML.support ∧ l.Nodup ∧
        ShellFrom (tetFaces (starTet sigma v)) l sigma :=
      degree3_star_start_shellFrom sigma (insert γ (cutSet sigma W)) ML.support
        hfreeL ht₀ hglue₀ hrest_disj hfinal
    rw [hsupport]
    intro s hs
    by_cases hsstar : s = starTet sigma v
    · subst s
      have hfreeInsert : FreelyShellable (insert (starTet sigma v) ML.support) sigma :=
        FreelyShellable.insert_of_glueStep hfreeL hglue hTnot hstart
      exact hfreeInsert (starTet sigma v) (Finset.mem_insert_self _ _)
    · rw [Finset.mem_insert] at hs
      rcases hs with hsnew | hsold
      · exact False.elim (hsstar hsnew)
      · exact FreelyShellable.exists_shelling_insert_of_glueStep_old hfreeL hglue hTnot hsold

end Taut
