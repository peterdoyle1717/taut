import Taut.Theorem2Aleph
import Taut.Stickerball

/-!
# Degree-3 geometry and the pseudomanifold base/step

The non-shelling half of the degree-3 reduction, shared by the clean shelling
route (`Theorem3Clean.lean`) and the pseudomanifold route (`taut_isPseudomanifold`):

* `base_isPM` / `deg3_isPM` — the `≤ 4`-vertex base case and the degree-3 step for
  `IsPseudomanifold M.support` (the PM strong induction is assembled in `PrimeStep`);
* `degree3_hanchor` — the degree-3 star-anchor existence target (a remainder tet
  exposing the link triangle `γ` lets the star tet glue back), consumed by the clean
  degree-3 step in `Theorem3Clean.lean`;
* `degree3_apex_notMem_*`, `deg3_clean_glue_of_remainder` — the apex / clean-glue
  side lemmas the degree-3 cut needs.

(The earlier weak free-shelling reassembly that lived here — `base_free`, the L1
free case-1 stick, `degree3_star_start_shellFrom`, and the `FreelyShellable`
helpers — has been removed; the public route is the clean one in
`Theorem3Clean.lean`.)
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-- **base_isPM** (PM base case, ≤ 4 vertices): a taut filling of a 2-sphere on
≤ 4 vertices is a single tetrahedron, hence a pseudomanifold. -/
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
the original sphere. -/
lemma degree3_hanchor (sigma sigmaR : Finset (Finset V)) (MR : Chain V)
    (M : Chain V) (sideVerts : Finset V) (useInside : Bool)
    (v : V) (W : C2 sigma) (γ : Finset V)
    (hsigma : IsSphere2 sigma) (hbig : 4 < (vertsOf sigma).card)
    (hv : v ∈ vertsOf sigma)
    (hγ : γ = linkVerts sigma v) (hγ3 : (linkVerts sigma v).card = 3)
    (hW : bd2 sigma W = gammaChain sigma (linkVerts sigma v))
    (hσR : IsSphere2 sigmaR)
    (hUR : UnitOn (bdry MR) sigmaR)
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
  classical
  set T := starTet sigma v with hT
  have hPureR : ∀ t ∈ MR.support, t.card = 4 := fun t ht =>
    (aleph_base_taut_support_card4_subset_verts hσR hUR rfl hTautR t ht).1
  have hγσR : γ ∈ sigmaR := by
    rcases hsigmaR_cut with h | h <;> rw [h] <;> exact Finset.mem_insert_self _ _
  have hγ3' : γ.card = 3 := by rw [hγ]; exact hγ3
  have hbd : bdry MR γ = 1 ∨ bdry MR γ = -1 := hUR.2 γ hγσR
  -- faceCount = 1: PM + pure + unit boundary ⟹ exactly one tet at γ.
  have hfc1 : faceCount MR.support γ = 1 :=
    faceCount_eq_one_of_boundary hSimpR hPureR hPMR hγ3' hbd
  have hfilt : (MR.support.filter (fun t => γ ⊆ t)).card = 1 := hfc1
  obtain ⟨t₀, ht₀set⟩ := Finset.card_eq_one.mp hfilt
  have ht₀mem : t₀ ∈ MR.support := by
    have : t₀ ∈ MR.support.filter (fun t => γ ⊆ t) := by
      rw [ht₀set]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).1
  have hγt₀ : γ ⊆ t₀ := by
    have : t₀ ∈ MR.support.filter (fun t => γ ⊆ t) := by
      rw [ht₀set]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).2
  have huniq : ∀ t ∈ MR.support, γ ⊆ t → t = t₀ := by
    intro t htmem hγt
    have : t ∈ MR.support.filter (fun t => γ ⊆ t) :=
      Finset.mem_filter.mpr ⟨htmem, hγt⟩
    rw [ht₀set] at this
    exact Finset.mem_singleton.mp this
  have ht₀card : t₀.card = 4 := hPureR t₀ ht₀mem
  have hstarcard : T.card = 4 := by rw [hT]; exact starTet_card_of_degree3 sigma hγ3
  have hTeq : T = insert v γ := by rw [hT, starTet, hγ]
  -- v ∉ γ: the apex is erased in linkVerts.
  have hvγ : v ∉ γ := by rw [hγ]; simp [linkVerts]
  -- γ ∉ σ (a degree-3 link triangle is not itself a face).
  have hγnotσ : γ ∉ sigma := by
    rw [hγ]
    exact linkVerts_not_mem_of_card_three_of_four_lt_verts hsigma hv hγ3 hbig
  -- γ ∈ tetFaces T and γ ∈ tetFaces t₀ (membership facts).
  have hmemTet : ∀ {s f : Finset V}, f ∈ tetFaces s ↔ f ⊆ s ∧ f.card = 3 := by
    intro s f; rw [tetFaces, Finset.mem_powersetCard]
  have hγstar : γ ∈ tetFaces T := hmemTet.mpr ⟨by rw [hTeq]; exact Finset.subset_insert _ _, hγ3'⟩
  have hγt₀face : γ ∈ tetFaces t₀ := hmemTet.mpr ⟨hγt₀, hγ3'⟩
  set K := tetFaces T \ tetFaces t₀ with hK
  -- **hinter**: the two tets share exactly the face γ.
  have hinter : tetFaces t₀ ∩ tetFaces T = {γ} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨hγt₀face, hγstar⟩, ?_⟩
    intro f hf
    rw [Finset.mem_inter] at hf
    obtain ⟨hft₀, hfstar⟩ := hf
    obtain ⟨hfsubt₀, hfc3⟩ := hmemTet.mp hft₀
    obtain ⟨hfsubstar, _⟩ := hmemTet.mp hfstar
    rw [hTeq] at hfsubstar
    by_cases hvf : v ∈ f
    · -- v ∈ f ⟹ v ∈ t₀, contradicting hvNotMR.
      exact absurd (hfsubt₀ hvf) (hvNotMR t₀ ht₀mem)
    · -- v ∉ f ⟹ f ⊆ γ ⟹ f = γ by card.
      have hfsubγ : f ⊆ γ := by
        intro x hx
        rcases Finset.mem_insert.mp (hfsubstar hx) with rfl | hxγ
        · exact absurd hx hvf
        · exact hxγ
      exact Finset.eq_of_subset_of_card_le hfsubγ (by rw [hγ3', hfc3])
  -- γ is the unique common face of t₀ and T.
  have hsdiff_t₀ : tetFaces t₀ \ tetFaces T = (tetFaces t₀).erase γ := by
    ext f
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨hft₀, hfstar⟩
      refine ⟨?_, hft₀⟩
      intro hfγ; subst hfγ; exact hfstar hγstar
    · rintro ⟨hfne, hft₀⟩
      refine ⟨hft₀, ?_⟩
      intro hfstar
      have : f ∈ tetFaces t₀ ∩ tetFaces T := Finset.mem_inter.mpr ⟨hft₀, hfstar⟩
      rw [hinter] at this
      exact hfne (Finset.mem_singleton.mp this)
  refine ⟨t₀, K, ht₀mem, ?glue, ?disj, ?recon⟩
  · refine ⟨ht₀card, ?_, ?_⟩
    · left
      have : tetFaces t₀ ∩ tetFaces T = {γ} := hinter
      rw [this]; exact Finset.card_singleton _
    · -- newBdry: B' = (B \ tetFaces t₀) ∪ (tetFaces t₀ \ B), B = tetFaces T.
      -- LHS is (tetFaces t₀).erase γ ∪ K; RHS is K ∪ (tetFaces t₀).erase γ.
      rw [hK, hsdiff_t₀, Finset.union_comm]
  · intro t htmem htne
    rw [Finset.disjoint_left]
    intro f hft hfins
    rcases Finset.mem_insert.mp hfins with hfγ | hfK
    · -- f = γ ⟹ γ ⊆ t ⟹ t = t₀, contra htne.
      subst hfγ
      obtain ⟨hfsubt, _⟩ := hmemTet.mp hft
      exact htne (huniq t htmem hfsubt)
    · -- f ∈ K ⟹ v ∈ f (K = star faces minus γ), but v ∉ t.
      have hfstar : f ∈ tetFaces T := (Finset.mem_sdiff.mp hfK).1
      have hfnt₀ : f ∉ tetFaces t₀ := (Finset.mem_sdiff.mp hfK).2
      obtain ⟨hfsubstar, hfc3⟩ := hmemTet.mp hfstar
      obtain ⟨hfsubt, _⟩ := hmemTet.mp hft
      -- v ∈ f: else f ⊆ γ ⟹ f = γ ∈ tetFaces t₀, contra hfnt₀.
      by_cases hvf : v ∈ f
      · exact hvNotMR t htmem (hfsubt hvf)
      · exfalso
        rw [hTeq] at hfsubstar
        have hfsubγ : f ⊆ γ := by
          intro x hx
          rcases Finset.mem_insert.mp (hfsubstar hx) with rfl | hxγ
          · exact absurd hx hvf
          · exact hxγ
        have hfeqγ : f = γ := Finset.eq_of_subset_of_card_le hfsubγ (by rw [hγ3', hfc3])
        rw [hfeqγ] at hfnt₀
        exact hfnt₀ hγt₀face
  · -- Determine which cut side is the star, then which is σR (the non-star side).
    have hsplit := degree3_cut_star_side_glue sigma hsigma hbig hv hγ3 hW
    -- γ ∉ both cut sides: γ is a non-face of σ.
    have hγnotL : γ ∉ cutSet sigma W := fun hc => hγnotσ (cutSet_subset hc)
    have hγnotR : γ ∉ cutSet sigma (W + fun _ => 1) := fun hc => hγnotσ (cutSet_subset hc)
    -- K = (tetFaces T).erase γ (γ is the unique common face of T and t₀).
    have hKerase : K = (tetFaces T).erase γ := by
      rw [hK]
      ext f
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro ⟨hfstar, hfnt₀⟩
        refine ⟨?_, hfstar⟩
        intro hfγ; subst hfγ; exact hfnt₀ hγt₀face
      · rintro ⟨hfne, hfstar⟩
        refine ⟨hfstar, ?_⟩
        intro hft₀
        have : f ∈ tetFaces t₀ ∩ tetFaces T := Finset.mem_inter.mpr ⟨hft₀, hfstar⟩
        rw [hinter] at this
        exact hfne (Finset.mem_singleton.mp this)
    have hsuppV : ∀ t ∈ MR.support, t ⊆ vertsOf sigmaR := fun t ht =>
      (aleph_base_taut_support_card4_subset_verts hσR hUR rfl hTautR t ht).2
    -- σR is not the star tet's boundary: else t₀ = T ∈ MR.support, contradicting hStarNotMR.
    have hstarNotσR : sigmaR ≠ tetFaces T := by
      intro hSR
      have ht₀V : t₀ ⊆ vertsOf sigmaR := hsuppV t₀ ht₀mem
      rw [hSR, vertsOf_tetFaces_eq T hstarcard] at ht₀V
      have ht₀T : t₀ = T := Finset.eq_of_subset_of_card_le ht₀V (by rw [hstarcard, ht₀card])
      rw [← ht₀T] at hStarNotMR
      exact hStarNotMR ht₀mem
    -- The two cut sides partition σ.
    have hunion : cutSet sigma W ∪ cutSet sigma (W + fun _ => 1) = sigma := by
      rw [cutSet_add_one_eq_sdiff, Finset.union_sdiff_of_subset cutSet_subset]
    -- erase γ from a γ-capped side recovers the bare cut side.
    have heraseL : (insert γ (cutSet sigma W)).erase γ = cutSet sigma W :=
      Finset.erase_insert hγnotL
    have heraseR : (insert γ (cutSet sigma (W + fun _ => 1))).erase γ
        = cutSet sigma (W + fun _ => 1) := Finset.erase_insert hγnotR
    -- Pair σR (non-star) with the star side, then sigmaR.erase γ ∪ K = σ.
    rcases hsplit with ⟨hstarEq, _⟩ | ⟨hstarEq, _⟩
    · -- Star side is the W-side: `insert γ (cutSet σ W) = tetFaces T`.
      rw [← hγ, ← hT] at hstarEq
      rcases hsigmaR_cut with hσRdef | hσRdef
      · -- σR = insert γ (cutSet σ W) = tetFaces T — ruled out.
        exact absurd (hσRdef.trans hstarEq) hstarNotσR
      · -- σR = insert γ (cutSet σ (W+1)); K = (tetFaces T).erase γ = cutSet σ W.
        rw [hσRdef, hKerase, ← hstarEq, heraseL, heraseR, Finset.union_comm, hunion]
    · -- Star side is the (W+1)-side: `insert γ (cutSet σ (W+1)) = tetFaces T`.
      rw [← hγ, ← hT] at hstarEq
      rcases hsigmaR_cut with hσRdef | hσRdef
      · -- σR = insert γ (cutSet σ W); K = (tetFaces T).erase γ = cutSet σ (W+1).
        rw [hσRdef, hKerase, ← hstarEq, heraseR, heraseL, hunion]
      · -- σR = insert γ (cutSet σ (W+1)) = tetFaces T — ruled out.
        exact absurd (hσRdef.trans hstarEq) hstarNotσR

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
filling is one. Cuts at the star, splits into the ML/MR filters with the star-side
dichotomy, applies the IH to the remainder to get a PM, then re-inserts the star
tet with `isPseudomanifold_insert`, discharging the clean-glue obligation by
`deg3_clean_glue_of_remainder`. Does NOT use `degree3_hanchor`. -/
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

end Taut
