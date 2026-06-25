import Taut.Theorem3Clean

/-!
# Theorem 4 (the flag-complex theorem)

Theorem 4 of "Taut fillings": a taut filling of a triangulated `S²` is a *flag complex*.
The combinatorial notion of "flag" is `IsFlagComplex`: every set `s` whose every edge is a
simplex of `τ` is itself a simplex of `τ`.

* `no_k5Clique_of_no_emptyK4_taut` replaces the paper's `S³ ⊄ B³` step: a `K₅` of edges in
  `M.support` would, via pseudomanifoldness, make every triangle inside it a *cancelled*
  (non-boundary) triangle, so the sub-chain `U := M ↾ s` of the `5` tets is closed;
  tautness (Prop 1) then forces `U = 0`, contradicting that `U` carries `5` tets.
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-! ## Flag-complex vocabulary -/

/-- `s` is (the vertex set of) a simplex of `τ`: either empty (the `(-1)`-simplex) or
contained in a facet. -/
def SimplexOf (τ : Finset (Finset V)) (s : Finset V) : Prop :=
  s = ∅ ∨ ∃ t ∈ τ, s ⊆ t

/-- `s` is a clique in the 1-skeleton of `τ`: its vertices are vertices of `τ` and each
of its edges (2-subsets) is a simplex of `τ`. -/
def CliqueInOneSkeleton (τ : Finset (Finset V)) (s : Finset V) : Prop :=
  s ⊆ vertsOf τ ∧ ∀ e, e ⊆ s → e.card = 2 → SimplexOf τ e

/-- `τ` is a *flag complex*: every clique of its 1-skeleton spans a simplex. -/
def IsFlagComplex (τ : Finset (Finset V)) : Prop :=
  ∀ s, CliqueInOneSkeleton τ s → SimplexOf τ s

/-- An *empty triangle* (`K₃`): three vertices, every edge a simplex, yet not a simplex. -/
def HasEmptyK3 (τ : Finset (Finset V)) : Prop :=
  ∃ s : Finset V, s.card = 3 ∧ (∀ e, e ⊆ s → e.card = 2 → SimplexOf τ e) ∧ ¬ SimplexOf τ s

/-- An *empty tetrahedron* (`K₄`): four vertices, every edge a simplex, yet not a simplex. -/
def HasEmptyK4 (τ : Finset (Finset V)) : Prop :=
  ∃ s : Finset V, s.card = 4 ∧ (∀ e, e ⊆ s → e.card = 2 → SimplexOf τ e) ∧ ¬ SimplexOf τ s

/-- A `K₅` of edges: five vertices, every edge a simplex (no spanning condition). -/
def HasK5Clique (τ : Finset (Finset V)) : Prop :=
  ∃ s : Finset V, s.card = 5 ∧ (∀ e, e ⊆ s → e.card = 2 → SimplexOf τ e)

/-- The three forbidden configurations are all absent. -/
def NoTaboo (τ : Finset (Finset V)) : Prop :=
  ¬ HasEmptyK3 τ ∧ ¬ HasEmptyK4 τ ∧ ¬ HasK5Clique τ

/-! ## (1) No taboo ⟹ flag (purely combinatorial) -/

/-- **No taboo configuration ⟹ flag complex.** Given a clique `s`, a case split on
`s.card` spans `s`: cards `0,1,2` directly; cards `3,4` would otherwise be an empty
`K₃`/`K₄`; card `≥ 5` produces a `5`-subclique, a forbidden `K₅`. -/
theorem NoTaboo.to_flag {τ : Finset (Finset V)} (h : NoTaboo τ) :
    IsFlagComplex τ := by
  obtain ⟨hK3, hK4, hK5⟩ := h
  intro s hs
  obtain ⟨hsub, hedges⟩ := hs
  by_cases hge5 : 5 ≤ s.card
  · exfalso
    obtain ⟨s', hs'sub, hs'card⟩ := Finset.exists_subset_card_eq hge5
    exact hK5 ⟨s', hs'card, fun e he hec => hedges e (he.trans hs'sub) hec⟩
  have hge5 : s.card ≤ 4 := by omega
  interval_cases hc : s.card
  · exact Or.inl (Finset.card_eq_zero.mp hc)
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    have hvmem : v ∈ vertsOf τ := hsub (hv ▸ Finset.mem_singleton_self v)
    obtain ⟨t, htτ, hvt⟩ := mem_vertsOf.mp hvmem
    exact Or.inr ⟨t, htτ, by rw [hv]; exact Finset.singleton_subset_iff.mpr hvt⟩
  · exact hedges s (Finset.Subset.refl s) hc
  · by_contra hns
    exact hK3 ⟨s, hc, hedges, hns⟩
  · by_contra hns
    exact hK4 ⟨s, hc, hedges, hns⟩

/-! ## (2) The K₅ obstruction (geometric crux) -/

private lemma fourSubset_mem_support {V : Type*} [LinearOrder V]
    {M : Chain V} {s q : Finset V}
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hK4 : ¬ HasEmptyK4 M.support)
    (hedges : ∀ e, e ⊆ s → e.card = 2 → SimplexOf M.support e)
    (hqs : q ⊆ s) (hq4 : q.card = 4) : q ∈ M.support := by
  have hqedges : ∀ e, e ⊆ q → e.card = 2 → SimplexOf M.support e :=
    fun e he hec => hedges e (he.trans hqs) hec
  have hsimp : SimplexOf M.support q := by
    by_contra hns
    exact hK4 ⟨q, hq4, hqedges, hns⟩
  rcases hsimp with hempty | ⟨t, htM, hqt⟩
  · rw [hempty] at hq4; simp at hq4
  · have : q = t := Finset.eq_of_subset_of_card_le hqt (by rw [hPure t htM, hq4])
    rwa [this]

private lemma two_tets_of_triangle {V : Type*} [LinearOrder V]
    {M : Chain V} {s f : Finset V}
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hK4 : ¬ HasEmptyK4 M.support)
    (hedges : ∀ e, e ⊆ s → e.card = 2 → SimplexOf M.support e)
    (hs5 : s.card = 5) (hfs : f ⊆ s) (hf3 : f.card = 3) :
    ∃ a b, a ∈ s ∧ b ∈ s ∧ a ∉ f ∧ b ∉ f ∧ a ≠ b ∧
      insert a f ∈ M.support ∧ insert b f ∈ M.support ∧
      insert a f ≠ insert b f := by
  have hsf2 : (s \ f).card = 2 := by
    rw [Finset.card_sdiff_of_subset hfs, hs5, hf3]
  obtain ⟨a, b, hab, hsf⟩ := Finset.card_eq_two.mp hsf2
  have hamem : a ∈ s \ f := hsf ▸ Finset.mem_insert_self a {b}
  have hbmem : b ∈ s \ f := hsf ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have has : a ∈ s := (Finset.mem_sdiff.mp hamem).1
  have hbs : b ∈ s := (Finset.mem_sdiff.mp hbmem).1
  have haf : a ∉ f := (Finset.mem_sdiff.mp hamem).2
  have hbf : b ∉ f := (Finset.mem_sdiff.mp hbmem).2
  have hca : (insert a f).card = 4 := by rw [Finset.card_insert_of_notMem haf, hf3]
  have hcb : (insert b f).card = 4 := by rw [Finset.card_insert_of_notMem hbf, hf3]
  have hsuba : insert a f ⊆ s := Finset.insert_subset has hfs
  have hsubb : insert b f ⊆ s := Finset.insert_subset hbs hfs
  have hmemA : insert a f ∈ M.support :=
    fourSubset_mem_support hPure hK4 hedges hsuba hca
  have hmemB : insert b f ∈ M.support :=
    fourSubset_mem_support hPure hK4 hedges hsubb hcb
  have hneq : insert a f ≠ insert b f := by
    intro heq
    have : a ∈ insert b f := heq ▸ Finset.mem_insert_self a f
    rcases Finset.mem_insert.mp this with h | h
    · exact hab h
    · exact haf h
  exact ⟨a, b, has, hbs, haf, hbf, hab, hmemA, hmemB, hneq⟩

/-- For a triangle `f ⊆ s` (card 3) of the `5`-clique `s`, every tet of `M.support`
that contains `f` is `⊆ s`.  `f` lies in two tets `insert a f, insert b f` both `⊆ s`,
and pseudomanifoldness (`hPM`) caps the count at two. -/
private lemma tet_containing_subset {V : Type*} [LinearOrder V]
    {M : Chain V} {s f : Finset V}
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hPM : IsPseudomanifold M.support)
    (hK4 : ¬ HasEmptyK4 M.support)
    (hedges : ∀ e, e ⊆ s → e.card = 2 → SimplexOf M.support e)
    (hs5 : s.card = 5) (hfs : f ⊆ s) (hf3 : f.card = 3) :
    ∀ t ∈ M.support, f ⊆ t → t ⊆ s := by
  obtain ⟨a, b, has, hbs, _, _, _, hmemA, hmemB, hneq⟩ :=
    two_tets_of_triangle hPure hK4 hedges hs5 hfs hf3
  have hsuba : insert a f ⊆ s := Finset.insert_subset has hfs
  have hsubb : insert b f ⊆ s := Finset.insert_subset hbs hfs
  set F := M.support.filter (fun t => f ⊆ t) with hF
  have hAF : insert a f ∈ F := by
    rw [hF, Finset.mem_filter]; exact ⟨hmemA, Finset.subset_insert a f⟩
  have hBF : insert b f ∈ F := by
    rw [hF, Finset.mem_filter]; exact ⟨hmemB, Finset.subset_insert b f⟩
  have hpairsub : ({insert a f, insert b f} : Finset (Finset V)) ⊆ F := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hAF
    · rw [Finset.mem_singleton.mp h]; exact hBF
  have hpaircard : ({insert a f, insert b f} : Finset (Finset V)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hneq]), Finset.card_singleton]
  have hFcard : F.card ≤ 2 := hPM f hf3
  have hFeq : F = ({insert a f, insert b f} : Finset (Finset V)) :=
    (Finset.eq_of_subset_of_card_le hpairsub (by rw [hpaircard]; exact hFcard)).symm
  intro t htM hft
  have htF : t ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨htM, hft⟩
  rw [hFeq] at htF
  rcases Finset.mem_insert.mp htF with h | h
  · rw [h]; exact hsuba
  · rw [Finset.mem_singleton.mp h]; exact hsubb

/-- **A triangle inside the `5`-clique is a cancelled (non-boundary) face.** Having
two bounding tets makes `faceCount = 2`; a `±1` boundary value is impossible there
(`faceCount_ne_two_of_boundary`), and `UnitOn X σ` then forces the boundary
coefficient to `0` (the face is off `σ`, so off `X.support`). -/
private lemma bdry_eq_zero_of_triangle {V : Type*} [LinearOrder V]
    {σ : Finset (Finset V)} {X M : Chain V} {s f : Finset V}
    (hU : UnitOn X σ) (hMX : bdry M = X)
    (hS : SimplicialChain M) (hPure : ∀ t ∈ M.support, t.card = 4)
    (hPM : IsPseudomanifold M.support)
    (hK4 : ¬ HasEmptyK4 M.support)
    (hedges : ∀ e, e ⊆ s → e.card = 2 → SimplexOf M.support e)
    (hs5 : s.card = 5) (hfs : f ⊆ s) (hf3 : f.card = 3) :
    bdry M f = 0 := by
  obtain ⟨a, b, _, _, _, _, _, hmemA, hmemB, hneq⟩ :=
    two_tets_of_triangle hPure hK4 hedges hs5 hfs hf3
  have hfc2 : faceCount M.support f = 2 := by
    have hpairsub : ({insert a f, insert b f} : Finset (Finset V)) ⊆
        M.support.filter (fun t => f ⊆ t) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h, Finset.mem_filter]; exact ⟨hmemA, Finset.subset_insert a f⟩
      · rw [Finset.mem_singleton.mp h, Finset.mem_filter]
        exact ⟨hmemB, Finset.subset_insert b f⟩
    have hpaircard : ({insert a f, insert b f} : Finset (Finset V)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hneq]), Finset.card_singleton]
    have hge : 2 ≤ faceCount M.support f := by
      unfold faceCount; rw [← hpaircard]; exact Finset.card_le_card hpairsub
    have hle : faceCount M.support f ≤ 2 := hPM f hf3
    omega
  have hne : bdry M f ≠ 1 ∧ bdry M f ≠ -1 := by
    constructor <;> intro hb
    · exact faceCount_ne_two_of_boundary hS hPure hf3 (Or.inl hb) hfc2
    · exact faceCount_ne_two_of_boundary hS hPure hf3 (Or.inr hb) hfc2
  have hXf : X f = 0 := by
    by_contra hXf0
    have hfσ : f ∈ σ := hU.1 ▸ Finsupp.mem_support_iff.mpr hXf0
    rcases hU.2 f hfσ with h | h
    · exact hne.1 (by rw [hMX, h])
    · exact hne.2 (by rw [hMX, h])
  rw [hMX]; exact hXf

/-- **The sub-chain on the `5`-clique is closed.** `U := M ↾ {t | t ⊆ s}` carries
exactly the (five) tets of `s`.  At a triangle `f ⊆ s` it agrees with `M` on the
two bounding tets (both `⊆ s`), so `bdry U f = bdry M f = 0`; at every other face the
local sum is empty.  Hence `bdry U = 0`. -/
private lemma bdry_filter_subset_eq_zero {V : Type*} [LinearOrder V]
    {σ : Finset (Finset V)} {X M : Chain V} {s : Finset V}
    (hU : UnitOn X σ) (hMX : bdry M = X)
    (hS : SimplicialChain M) (hPure : ∀ t ∈ M.support, t.card = 4)
    (hPM : IsPseudomanifold M.support)
    (hK4 : ¬ HasEmptyK4 M.support)
    (hedges : ∀ e, e ⊆ s → e.card = 2 → SimplexOf M.support e)
    (hs5 : s.card = 5) :
    bdry (M.filter (fun t => t ⊆ s)) = 0 := by
  classical
  set U := M.filter (fun t => t ⊆ s) with hUdef
  have hUapp : ∀ t, U t = if t ⊆ s then M t else 0 := by
    intro t; rw [hUdef, Finsupp.filter_apply]
  have hUsupp : U.support ⊆ M.support := by
    rw [hUdef, Finsupp.support_filter]; exact Finset.filter_subset _ _
  ext f
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_cases hcase : f ⊆ s ∧ f.card = 3
  · obtain ⟨hfs, hf3⟩ := hcase
    have hcont : ∀ t ∈ M.support, f ⊆ t → t ⊆ s :=
      tet_containing_subset hPure hPM hK4 hedges hs5 hfs hf3
    have hsumU : bdry U f = ∑ t ∈ U.support.filter (fun t => f ⊆ t), U t * bdryGen t f :=
      bdry_eq_sum_facets
    have hsumM : bdry M f = ∑ t ∈ M.support.filter (fun t => f ⊆ t), M t * bdryGen t f :=
      bdry_eq_sum_facets
    have hfilteq : U.support.filter (fun t => f ⊆ t) =
        M.support.filter (fun t => f ⊆ t) := by
      apply Finset.ext; intro t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨htU, hft⟩; exact ⟨hUsupp htU, hft⟩
      · rintro ⟨htM, hft⟩
        have htsub : t ⊆ s := hcont t htM hft
        have hUt : U t = M t := by rw [hUapp, if_pos htsub]
        refine ⟨?_, hft⟩
        rw [Finsupp.mem_support_iff, hUt]
        exact Finsupp.mem_support_iff.mp htM
    rw [hsumU, hfilteq]
    have hterms : ∀ t ∈ M.support.filter (fun t => f ⊆ t),
        U t * bdryGen t f = M t * bdryGen t f := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have htsub : t ⊆ s := hcont t ht.1 ht.2
      rw [hUapp, if_pos htsub]
    rw [Finset.sum_congr rfl hterms, ← hsumM]
    exact bdry_eq_zero_of_triangle hU hMX hS hPure hPM hK4 hedges hs5 hfs hf3
  · rw [show bdry U f = ∑ t ∈ U.support.filter (fun t => f ⊆ t), U t * bdryGen t f from
      bdry_eq_sum_facets]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_filter] at ht
    obtain ⟨htU, hft⟩ := ht
    have htM : t ∈ M.support := hUsupp htU
    have htsub : t ⊆ s := by
      have := hUapp t
      by_contra hns
      rw [if_neg hns] at this
      exact (Finsupp.mem_support_iff.mp htU) this
    have hfs : f ⊆ s := hft.trans htsub
    have hf3 : f.card ≠ 3 := fun h => hcase ⟨hfs, h⟩
    have hgen : bdryGen t f = 0 := by
      by_contra hg
      obtain ⟨w, hw, hfe⟩ := exists_facet_of_bdryGen_ne_zero hg
      have : f.card = 3 := by
        rw [hfe, Finset.card_erase_of_mem hw, hPure t htM]
      exact hf3 this
    rw [hgen, mul_zero]

/-- **The K₅ obstruction.** A taut, simplicial, pure filling of a combinatorial
`2`-sphere `σ` whose support has no empty `K₄` has no `K₅` of edges either.  A `K₅` of
edges `s` would make the sub-chain `U := M ↾ {t | t ⊆ s}` closed
(`bdry_filter_subset_eq_zero`); Proposition 1 (`IsTaut.subChain`) makes `U` taut, so
`nrm U = Zvol 0 = 0` forces `U = 0` — but `U` carries a tet of `s`. -/
theorem no_k5Clique_of_no_emptyK4_taut
    {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) (hPure : ∀ t ∈ M.support, t.card = 4)
    (hK4 : ¬ HasEmptyK4 M.support) : ¬ HasK5Clique M.support := by
  classical
  rintro ⟨s, hs5, hedges⟩
  have hPM : IsPseudomanifold M.support := taut_isPseudomanifold hσ hU hXc hMX hT hS
  set U := M.filter (fun t => t ⊆ s) with hUdef
  have hbU : bdry U = 0 :=
    bdry_filter_subset_eq_zero hU hMX hS hPure hPM hK4 hedges hs5
  have hsub : SubChain U M := subChain_filter _ M
  have hTU : IsTaut U := hT.subChain hsub
  have hZ0 : Zvol (0 : Chain V) = 0 := Nat.le_zero.mp (by
    simpa using Zvol_le (show bdry (0 : Chain V) = 0 by simp))
  have hnrmU : nrm U = 0 := by rw [IsTaut] at hTU; rw [hTU, hbU, hZ0]
  have hU0 : U = 0 := nrm_eq_zero_iff.mp hnrmU
  obtain ⟨q, hqs, hq4⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
  have hqM : q ∈ M.support := fourSubset_mem_support hPure hK4 hedges hqs hq4
  have hUq : U q = M q := by rw [hUdef, Finsupp.filter_apply, if_pos hqs]
  have hMq : M q ≠ 0 := Finsupp.mem_support_iff.mp hqM
  rw [hU0] at hUq
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hUq
  exact hMq hUq.symm

/-- Once `HasEmptyK3` / `HasEmptyK4` are ruled out for a taut filling `M` of a 2-sphere `σ`, the
support is a flag complex.  Composes `NoTaboo.to_flag` with `no_k5Clique_of_no_emptyK4_taut`
(which supplies `¬ HasK5Clique` from `¬ HasEmptyK4`), deriving purity from
`aleph_base_taut_support_card4_subset_verts`. -/
theorem theorem4_flag_from_no_emptyK3K4
    {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M)
    (hK3 : ¬ HasEmptyK3 M.support) (hK4 : ¬ HasEmptyK4 M.support) :
    IsFlagComplex M.support := by
  have hPure : ∀ t ∈ M.support, t.card = 4 := fun t ht =>
    (aleph_base_taut_support_card4_subset_verts hσ hU hMX hT t ht).1
  have hK5 : ¬ HasK5Clique M.support :=
    no_k5Clique_of_no_emptyK4_taut hσ hU hXc hMX hT hS hPure hK4
  exact NoTaboo.to_flag ⟨hK3, hK4, hK5⟩

/-! ### Persistence of the taboo configurations under removing a tet

In the minimal-counterexample induction (`no_emptyK3K4_of_taut`) we remove a tet — a degree-3
star or an eligible flip — and need the taboo configuration to survive in the smaller complex
`M.support.erase e` (= `(removeTet M e).support`). -/

omit [LinearOrder V] in
/-- `SimplexOf` is monotone in the complex. -/
lemma SimplexOf.mono {τ τ' : Finset (Finset V)} {s : Finset V}
    (h : τ ⊆ τ') (hs : SimplexOf τ s) : SimplexOf τ' s := by
  rcases hs with h0 | ⟨t, ht, hst⟩
  · exact Or.inl h0
  · exact Or.inr ⟨t, h ht, hst⟩

/-- Empty-K3 persists when erasing a tet `e` that is not the sole witness of any edge of the
witness triangle. -/
lemma hasEmptyK3_erase_of_witness {τ : Finset (Finset V)} {e s : Finset V}
    (hs3 : s.card = 3)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → ∃ t ∈ τ, t ≠ e ∧ x ⊆ t)
    (hno : ¬ SimplexOf τ s) : HasEmptyK3 (τ.erase e) := by
  refine ⟨s, hs3, ?_, ?_⟩
  · intro x hxs hx2
    obtain ⟨t, htτ, htne, hxt⟩ := hedges x hxs hx2
    exact Or.inr ⟨t, Finset.mem_erase.mpr ⟨htne, htτ⟩, hxt⟩
  · exact fun hcon => hno (hcon.mono (Finset.erase_subset _ _))

/-- Empty-K4 persists when erasing a tet `e` that is not the sole witness of any edge of the
witness `K4`. -/
lemma hasEmptyK4_erase_of_witness {τ : Finset (Finset V)} {e s : Finset V}
    (hs4 : s.card = 4)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → ∃ t ∈ τ, t ≠ e ∧ x ⊆ t)
    (hno : ¬ SimplexOf τ s) : HasEmptyK4 (τ.erase e) := by
  refine ⟨s, hs4, ?_, ?_⟩
  · intro x hxs hx2
    obtain ⟨t, htτ, htne, hxt⟩ := hedges x hxs hx2
    exact Or.inr ⟨t, Finset.mem_erase.mpr ⟨htne, htτ⟩, hxt⟩
  · exact fun hcon => hno (hcon.mono (Finset.erase_subset _ _))

lemma hasEmptyK3_removeTet_of_witness {M : Chain V} {e s : Finset V} (he : e ∈ M.support)
    (hs3 : s.card = 3)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → ∃ t ∈ M.support, t ≠ e ∧ x ⊆ t)
    (hno : ¬ SimplexOf M.support s) : HasEmptyK3 (removeTet M e).support := by
  rw [support_removeTet_of_mem he]
  exact hasEmptyK3_erase_of_witness hs3 hedges hno

lemma hasEmptyK4_removeTet_of_witness {M : Chain V} {e s : Finset V} (he : e ∈ M.support)
    (hs4 : s.card = 4)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → ∃ t ∈ M.support, t ≠ e ∧ x ⊆ t)
    (hno : ¬ SimplexOf M.support s) : HasEmptyK4 (removeTet M e).support := by
  rw [support_removeTet_of_mem he]
  exact hasEmptyK4_erase_of_witness hs4 hedges hno

/-! ### No-flip persistence

In the eligible-flip step of the induction we remove an eligible tet `e` whose two *shared*
(boundary) faces `g₃, g₄` get their common edge `g₃ ∩ g₄` deleted from the boundary.  A witness
edge `x` of a taboo configuration survives provided `x ≠ g₃ ∩ g₄` (the side condition `havoid`):
every other edge of `e` lies in an *exposed* (interior) face carried by a neighbouring tet `≠ e`. -/

/-- **An edge `x ⊆ e` that is not the shared diagonal lies in an exposed face.** The two
facets of `e` containing `x` (there are exactly two — `tetFaces_edge_filter_card_eq_two`)
cannot both be shared: if they were, they would exhaust `sharedFaces M e = {g₃, g₄}`, forcing
`x = g₃ ∩ g₄` (`inter_eq_edge_of_two_faces`), contrary to `hxne`.  So one of them is
exposed. -/
private lemma edge_in_exposed_of_ne_sharedInter {M : Chain V} {e g₃ g₄ x : Finset V}
    (he : EligibleTet M e) (hsh : sharedFaces M e = {g₃, g₄}) (hg : g₃ ≠ g₄)
    (hx2 : x.card = 2) (hxe : x ⊆ e) (hxne : x ≠ g₃ ∩ g₄) :
    ∃ f ∈ exposedFaces M e, x ⊆ f := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsubsh : (tetFaces e).filter (fun F => x ⊆ F) ⊆ sharedFaces M e := by
    intro F hF
    rw [Finset.mem_filter] at hF
    by_contra hns
    exact hcon F (Finset.mem_sdiff.mpr ⟨hF.1, hns⟩) hF.2
  have hfiltcard : ((tetFaces e).filter (fun F => x ⊆ F)).card = 2 :=
    tetFaces_edge_filter_card_eq_two he.1 hxe hx2
  have hsheq : (tetFaces e).filter (fun F => x ⊆ F) = sharedFaces M e :=
    Finset.eq_of_subset_of_card_le hsubsh (by rw [he.2.2.1, hfiltcard])
  have hg3mem : g₃ ∈ (tetFaces e).filter (fun F => x ⊆ F) := by
    rw [hsheq, hsh]; exact Finset.mem_insert_self g₃ {g₄}
  have hg4mem : g₄ ∈ (tetFaces e).filter (fun F => x ⊆ F) := by
    rw [hsheq, hsh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self g₄)
  have hxg3 : x ⊆ g₃ := (Finset.mem_filter.mp hg3mem).2
  have hxg4 : x ⊆ g₄ := (Finset.mem_filter.mp hg4mem).2
  have hg3card : g₃.card = 3 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hg3mem).1).2
  have hg4card : g₄.card = 3 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hg4mem).1).2
  exact hxne (inter_eq_edge_of_two_faces hg3card hg4card hg hx2 hxg3 hxg4).symm

/-- **A surviving witness for an edge `x` of an eligible tet's removal.** If the simplex edge
`x` is not the deleted diagonal `g₃ ∩ g₄`, then some tet `≠ e` of `M.support` carries `x`.
Edges `¬ ⊆ e` keep their original witness (which is automatically `≠ e`); edges `⊆ e` lie in
an exposed face `f`, whose `bdry M f = 0` forces a second tet `≠ e` of `f` (the `e`-term of
`bdry M f` is nonzero, so the sum cannot vanish without another nonzero term). -/
lemma edge_witness_ne_removed_of_not_sharedEdge {M : Chain V} {e g₃ g₄ x : Finset V}
    (he : EligibleTet M e) (hsh : sharedFaces M e = {g₃, g₄}) (hg : g₃ ≠ g₄)
    (hx : SimplexOf M.support x) (hx2 : x.card = 2) (hxne : x ≠ g₃ ∩ g₄) :
    ∃ t ∈ M.support, t ≠ e ∧ x ⊆ t := by
  classical
  have hxne0 : x ≠ ∅ := by
    intro h; rw [h, Finset.card_empty] at hx2; exact absurd hx2 (by decide)
  obtain ⟨t₀, ht₀, hxt₀⟩ := hx.resolve_left hxne0
  by_cases hxe : x ⊆ e
  · obtain ⟨f, hf, hxf⟩ := edge_in_exposed_of_ne_sharedInter he hsh hg hx2 hxe hxne
    have hftet : f ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf
    have hf3 : f.card = 3 := (Finset.mem_powersetCard.mp hftet).2
    have hfnsh : f ∉ sharedFaces M e := (Finset.mem_sdiff.mp hf).2
    have hfnb : f ∉ (bdry M).support := fun hb =>
      hfnsh (by rw [sharedFaces]; exact Finset.mem_inter.mpr ⟨hftet, hb⟩)
    have hbf0 : bdry M f = 0 := Finsupp.notMem_support_iff.mp hfnb
    have hfsube : f ⊆ e := (Finset.mem_powersetCard.mp hftet).1
    have heF : e ∈ M.support.filter (fun t => f ⊆ t) :=
      Finset.mem_filter.mpr ⟨he.2.1, hfsube⟩
    have hMe : M e ≠ 0 := Finsupp.mem_support_iff.mp he.2.1
    have hgene : bdryGen e f ≠ 0 := bdryGen_ne_zero_of_subset he.1 hf3 hfsube
    have htermE : M e * bdryGen e f ≠ 0 := mul_ne_zero hMe hgene
    have hsum0 : (∑ t ∈ M.support.filter (fun t => f ⊆ t), M t * bdryGen t f) = 0 := by
      rw [← bdry_eq_sum_facets]; exact hbf0
    have hexists : ∃ t ∈ M.support.filter (fun t => f ⊆ t),
        t ≠ e ∧ M t * bdryGen t f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hzero : (∑ t ∈ M.support.filter (fun t => f ⊆ t), M t * bdryGen t f) =
          M e * bdryGen e f :=
        Finset.sum_eq_single_of_mem e heF (fun t ht htne => hcon t ht htne)
      rw [hzero] at hsum0; exact htermE hsum0
    obtain ⟨t, htF, htne, htterm⟩ := hexists
    have htM : t ∈ M.support := (Finset.mem_filter.mp htF).1
    have hgent : bdryGen t f ≠ 0 := fun h0 => htterm (by rw [h0, mul_zero])
    obtain ⟨w, _, hfew⟩ := exists_facet_of_bdryGen_ne_zero hgent
    have hft : f ⊆ t := hfew ▸ Finset.erase_subset w t
    exact ⟨t, htM, htne, hxf.trans hft⟩
  · refine ⟨t₀, ht₀, ?_, hxt₀⟩
    intro hte
    exact hxe (hte ▸ hxt₀)

lemma hasEmptyK3_removeTet_of_avoids_sharedEdge {M : Chain V} {e g₃ g₄ s : Finset V}
    (he : EligibleTet M e) (hsh : sharedFaces M e = {g₃, g₄}) (hg : g₃ ≠ g₄)
    (hs3 : s.card = 3)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf M.support x)
    (havoid : ∀ x, x ⊆ s → x.card = 2 → x ≠ g₃ ∩ g₄)
    (hno : ¬ SimplexOf M.support s) :
    HasEmptyK3 (removeTet M e).support :=
  hasEmptyK3_removeTet_of_witness he.2.1 hs3
    (fun x hxs hx2 =>
      edge_witness_ne_removed_of_not_sharedEdge he hsh hg (hedges x hxs hx2) hx2
        (havoid x hxs hx2))
    hno

lemma hasEmptyK4_removeTet_of_avoids_sharedEdge {M : Chain V} {e g₃ g₄ s : Finset V}
    (he : EligibleTet M e) (hsh : sharedFaces M e = {g₃, g₄}) (hg : g₃ ≠ g₄)
    (hs4 : s.card = 4)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf M.support x)
    (havoid : ∀ x, x ⊆ s → x.card = 2 → x ≠ g₃ ∩ g₄)
    (hno : ¬ SimplexOf M.support s) :
    HasEmptyK4 (removeTet M e).support :=
  hasEmptyK4_removeTet_of_witness he.2.1 hs4
    (fun x hxs hx2 =>
      edge_witness_ne_removed_of_not_sharedEdge he hsh hg (hedges x hxs hx2) hx2
        (havoid x hxs hx2))
    hno

/-! ### Side localization of empty configurations

In the eligible-flip / edge-split step the support `τ` of a taboo configuration sits across a
separating edge `A ∩ B` (card 2): every tet lies in `A` or `B`, the two sides are bridged by tets
capping the seam edge, and a whole empty `K₃`/`K₄` witness must localize to a single side's filter.

* a card-`≥ 2` witness whose every edge is a simplex lies entirely in one side (`witness_subset_side`);
* once on side `P`, each edge transfers to `τ ↾ {t | t ⊆ P}`, seam edges via the bridging tet
  (`edge_simplexOf_filter_of_subset`). -/

/-- **A clique witness localizes to one side of a separating edge.** If every tet of `τ` lies in
`A` or `B`, and every `2`-subset of `s` (card `≥ 2`) is a simplex of `τ`, then `s ⊆ A` or `s ⊆ B`. -/
private lemma witness_subset_side {τ : Finset (Finset V)} {A B s : Finset V}
    (hcover : ∀ t ∈ τ, t ⊆ A ∨ t ⊆ B) (hs2 : 2 ≤ s.card)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf τ x) : s ⊆ A ∨ s ⊆ B := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnA, hnB⟩ := hcon
  obtain ⟨a, has, hanA⟩ := Finset.not_subset.mp hnA
  obtain ⟨b, hbs, hbnB⟩ := Finset.not_subset.mp hnB
  have hvAB : ∀ v ∈ s, v ∈ A ∨ v ∈ B := by
    intro v hv
    obtain ⟨w, hws, hwv⟩ :=
      (Finset.one_lt_card_iff_nontrivial.mp (show 1 < s.card by omega)).exists_ne v
    have hvw2 : ({v, w} : Finset V).card = 2 := Finset.card_pair (Ne.symm hwv)
    have hvwsub : ({v, w} : Finset V) ⊆ s := by
      intro y hy
      rcases Finset.mem_insert.mp hy with h | h
      · exact h ▸ hv
      · exact (Finset.mem_singleton.mp h) ▸ hws
    have hsimp : SimplexOf τ ({v, w} : Finset V) := hsedges _ hvwsub hvw2
    have hvw0 : ({v, w} : Finset V) ≠ ∅ := by
      intro h; rw [h, Finset.card_empty] at hvw2; exact absurd hvw2 (by decide)
    obtain ⟨t, htτ, hvwt⟩ := hsimp.resolve_left hvw0
    have hvt : v ∈ t := hvwt (Finset.mem_insert_self v {w})
    rcases hcover t htτ with htA | htB
    · exact Or.inl (htA hvt)
    · exact Or.inr (htB hvt)
  have haB : a ∈ B := (hvAB a has).resolve_left hanA
  have hbA : b ∈ A := (hvAB b hbs).resolve_right hbnB
  have hab : a ≠ b := by intro h; exact hanA (h ▸ hbA)
  have hab2 : ({a, b} : Finset V).card = 2 := Finset.card_pair hab
  have habsub : ({a, b} : Finset V) ⊆ s := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact h ▸ has
    · exact (Finset.mem_singleton.mp h) ▸ hbs
  have hsimp : SimplexOf τ ({a, b} : Finset V) := hsedges _ habsub hab2
  have hab0 : ({a, b} : Finset V) ≠ ∅ := by
    intro h; rw [h, Finset.card_empty] at hab2; exact absurd hab2 (by decide)
  obtain ⟨t, htτ, habt⟩ := hsimp.resolve_left hab0
  have hat : a ∈ t := habt (Finset.mem_insert_self a {b})
  have hbt : b ∈ t := habt (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  rcases hcover t htτ with htA | htB
  · exact hanA (htA hat)
  · exact hbnB (htB hbt)

/-- **An edge of a one-sided witness transfers to the side filter.** With `s ⊆ P` and every
`2`-subset of `s` a simplex of `τ`, every `2`-subset `x` of `s` is a simplex of `τ ↾ {t | t ⊆ P}`.
A witness tet on the other side `Q` forces `x = P ∩ Q`, so the bridging tet of `P` (hypothesis
`hbridge`) carries it. -/
private lemma edge_simplexOf_filter_of_subset {τ : Finset (Finset V)} {P Q s : Finset V}
    (hcover : ∀ t ∈ τ, t ⊆ P ∨ t ⊆ Q) (hPQ2 : (P ∩ Q).card = 2)
    (hbridge : ∃ t ∈ τ, t ⊆ P ∧ P ∩ Q ⊆ t) (hsP : s ⊆ P)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf τ x)
    {x : Finset V} (hxs : x ⊆ s) (hx2 : x.card = 2) :
    SimplexOf (τ.filter (fun t => t ⊆ P)) x := by
  classical
  have hx0 : x ≠ ∅ := by
    intro h; rw [h, Finset.card_empty] at hx2; exact absurd hx2 (by decide)
  obtain ⟨t, htτ, hxt⟩ := (hsedges x hxs hx2).resolve_left hx0
  rcases hcover t htτ with htP | htQ
  · exact Or.inr ⟨t, Finset.mem_filter.mpr ⟨htτ, htP⟩, hxt⟩
  · have hxPQ : x ⊆ P ∩ Q := Finset.subset_inter (hxs.trans hsP) (hxt.trans htQ)
    have hxeq : x = P ∩ Q :=
      Finset.eq_of_subset_of_card_le hxPQ (by rw [hPQ2, hx2])
    obtain ⟨t', ht'τ, ht'P, ht'PQ⟩ := hbridge
    exact Or.inr ⟨t', Finset.mem_filter.mpr ⟨ht'τ, ht'P⟩, hxeq ▸ ht'PQ⟩

/-- **Side localization of an empty `K₃`.** Across a separating edge `A ∩ B` (card 2) with both
sides bridged, an empty `K₃` of `τ` is an empty `K₃` of one side filter `τ ↾ {t | t ⊆ A}` or
`τ ↾ {t | t ⊆ B}`.  (`hsep` is supplied by the call site but unused here.) -/
lemma hasEmptyK3_side_of_edge_split {τ : Finset (Finset V)} {A B : Finset V}
    (hcover : ∀ t ∈ τ, t ⊆ A ∨ t ⊆ B)
    (_hsep : ∀ t ∈ τ, (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A))
    (hAB2 : (A ∩ B).card = 2)
    (hbridgeA : ∃ t ∈ τ, t ⊆ A ∧ A ∩ B ⊆ t)
    (hbridgeB : ∃ t ∈ τ, t ⊆ B ∧ A ∩ B ⊆ t)
    (h : HasEmptyK3 τ) :
    HasEmptyK3 (τ.filter (fun t => t ⊆ A)) ∨ HasEmptyK3 (τ.filter (fun t => t ⊆ B)) := by
  classical
  obtain ⟨s, hcard, hsedges, hsno⟩ := h
  have hs2 : 2 ≤ s.card := by omega
  rcases witness_subset_side hcover hs2 hsedges with hsA | hsB
  · refine Or.inl ⟨s, hcard, ?_, ?_⟩
    · exact fun x hxs hx2 =>
        edge_simplexOf_filter_of_subset (P := A) (Q := B) hcover hAB2 hbridgeA hsA hsedges hxs hx2
    · exact fun hc => hsno (hc.mono (Finset.filter_subset _ _))
  · have hAB2' : (B ∩ A).card = 2 := by rw [Finset.inter_comm]; exact hAB2
    have hbridgeB' : ∃ t ∈ τ, t ⊆ B ∧ B ∩ A ⊆ t := by
      rw [Finset.inter_comm]; exact hbridgeB
    refine Or.inr ⟨s, hcard, ?_, ?_⟩
    · exact fun x hxs hx2 =>
        edge_simplexOf_filter_of_subset (P := B) (Q := A)
          (fun t ht => (hcover t ht).symm) hAB2' hbridgeB' hsB hsedges hxs hx2
    · exact fun hc => hsno (hc.mono (Finset.filter_subset _ _))

/-- **Side localization of an empty `K₄`.** Identical argument to the `K₃` case (the witness card
plays no role beyond `2 ≤ s.card`). -/
lemma hasEmptyK4_side_of_edge_split {τ : Finset (Finset V)} {A B : Finset V}
    (hcover : ∀ t ∈ τ, t ⊆ A ∨ t ⊆ B)
    (_hsep : ∀ t ∈ τ, (t ⊆ A ∧ ¬ t ⊆ B) ∨ (t ⊆ B ∧ ¬ t ⊆ A))
    (hAB2 : (A ∩ B).card = 2)
    (hbridgeA : ∃ t ∈ τ, t ⊆ A ∧ A ∩ B ⊆ t)
    (hbridgeB : ∃ t ∈ τ, t ⊆ B ∧ A ∩ B ⊆ t)
    (h : HasEmptyK4 τ) :
    HasEmptyK4 (τ.filter (fun t => t ⊆ A)) ∨ HasEmptyK4 (τ.filter (fun t => t ⊆ B)) := by
  classical
  obtain ⟨s, hcard, hsedges, hsno⟩ := h
  have hs2 : 2 ≤ s.card := by omega
  rcases witness_subset_side hcover hs2 hsedges with hsA | hsB
  · refine Or.inl ⟨s, hcard, ?_, ?_⟩
    · exact fun x hxs hx2 =>
        edge_simplexOf_filter_of_subset (P := A) (Q := B) hcover hAB2 hbridgeA hsA hsedges hxs hx2
    · exact fun hc => hsno (hc.mono (Finset.filter_subset _ _))
  · have hAB2' : (B ∩ A).card = 2 := by rw [Finset.inter_comm]; exact hAB2
    have hbridgeB' : ∃ t ∈ τ, t ⊆ B ∧ B ∩ A ⊆ t := by
      rw [Finset.inter_comm]; exact hbridgeB
    refine Or.inr ⟨s, hcard, ?_, ?_⟩
    · exact fun x hxs hx2 =>
        edge_simplexOf_filter_of_subset (P := B) (Q := A)
          (fun t ht => (hcover t ht).symm) hAB2' hbridgeB' hsB hsedges hxs hx2
    · exact fun hc => hsno (hc.mono (Finset.filter_subset _ _))

/-! ## (5) Flip-avoidance counting -/

/-- The *octahedron* `2`-sphere: `6` vertices, no degree-3 vertex, every vertex of link-size `4`.
This is the one prime sphere with `maxdeg = 4` exactly, excluded as a special case in the empty-`K₄`
flip count (where the argument needs `maxdeg ≥ 5`). -/
def IsOctahedronSphere (σ : Finset (Finset V)) : Prop :=
  IsSphere2 σ ∧ (vertsOf σ).card = 6 ∧ NoDegree3Vertex σ ∧
    ∀ v ∈ vertsOf σ, (linkVerts σ v).card = 4

/-- **At most two members of a `sharedFaces`-disjoint eligible family hit a given pair of faces.**
The config-2 counting input: `≤ 2` eligible tets can carry a forbidden interior face `ABC`/`BCD`. -/
lemma disjoint_eligible_family_hit_two_faces_card_le_two
    {M : Chain V} {E : Finset (Finset V)} {p q : Finset V}
    (hpair : (↑E : Set (Finset V)).PairwiseDisjoint (fun e => sharedFaces M e))
    (_hpq : p ≠ q) :
    (E.filter (fun e => p ∈ sharedFaces M e ∨ q ∈ sharedFaces M e)).card ≤ 2 := by
  classical
  have key : ∀ r : Finset V, (E.filter (fun e => r ∈ sharedFaces M e)).card ≤ 1 := by
    intro r
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    exact (Finset.disjoint_left.mp
      (hpair (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) hab) ha.2) hb.2
  have hsub : E.filter (fun e => p ∈ sharedFaces M e ∨ q ∈ sharedFaces M e)
      ⊆ E.filter (fun e => p ∈ sharedFaces M e) ∪ E.filter (fun e => q ∈ sharedFaces M e) := by
    intro e he
    rw [Finset.mem_filter] at he
    rcases he.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he.1, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he.1, h⟩)
  calc (E.filter (fun e => p ∈ sharedFaces M e ∨ q ∈ sharedFaces M e)).card
      ≤ (E.filter (fun e => p ∈ sharedFaces M e)
          ∪ E.filter (fun e => q ∈ sharedFaces M e)).card := Finset.card_le_card hsub
    _ ≤ (E.filter (fun e => p ∈ sharedFaces M e)).card
          + (E.filter (fun e => q ∈ sharedFaces M e)).card := Finset.card_union_le _ _
    _ ≤ 2 := by have h1 := key p; have h2 := key q; omega

/-! ## Octahedron Euler bridge -/

/-- **The faces at `v` biject with the link vertices.**  For a `2`-sphere `σ`, the number
of faces containing a vertex `v` equals the number of vertices of its link. -/
lemma incident_faces_card_eq_linkVerts_card {σ : Finset (Finset V)} (hσ : IsSphere2 σ)
    {v : V} (_hv : v ∈ vertsOf σ) :
    (σ.filter (fun f => v ∈ f)).card = (linkVerts σ v).card := by
  classical
  set A := σ.filter (fun f => v ∈ f) with hA
  set B := linkVerts σ v with hB
  have claim1 : ∀ f ∈ A, (B.filter (fun x => x ∈ f)).card = 2 := by
    intro f hf
    have hfσ : f ∈ σ := (Finset.mem_filter.mp hf).1
    have hvf : v ∈ f := (Finset.mem_filter.mp hf).2
    have hset : B.filter (fun x => x ∈ f) = f.erase v := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hxB, hxf⟩
        exact ⟨(mem_linkVerts.mp hxB).1, hxf⟩
      · rintro ⟨hxv, hxf⟩
        exact ⟨mem_linkVerts.mpr ⟨hxv, f, hfσ, hvf, hxf⟩, hxf⟩
    rw [hset, Finset.card_erase_of_mem hvf, hσ.pure f hfσ]
  have claim2 : ∀ x ∈ B, (A.filter (fun f => x ∈ f)).card = 2 := by
    intro x hx
    have hxv : x ≠ v := (mem_linkVerts.mp hx).1
    have hedge : {v, x} ∈ edgesOf σ := (mem_linkVerts_iff_edge hσ hxv).mp hx
    have hset : A.filter (fun f => x ∈ f) = σ.filter (fun f => {v, x} ⊆ f) := by
      rw [hA, Finset.filter_filter]
      apply Finset.filter_congr
      intro f _
      constructor
      · rintro ⟨hvf, hxf⟩
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hvf, hxf⟩
      · intro hsub
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hsub
        exact hsub
    have hdeg := hσ.closed {v, x} hedge
    rw [edgeDeg] at hdeg
    rw [hset, hdeg]
  have hswap : ∑ f ∈ A, (B.filter (fun x => x ∈ f)).card
      = ∑ x ∈ B, (A.filter (fun f => x ∈ f)).card := by
    calc ∑ f ∈ A, (B.filter (fun x => x ∈ f)).card
        = ∑ f ∈ A, ∑ x ∈ B, (if x ∈ f then 1 else 0) := by simp_rw [Finset.card_filter]
      _ = ∑ x ∈ B, ∑ f ∈ A, (if x ∈ f then 1 else 0) := Finset.sum_comm
      _ = ∑ x ∈ B, (A.filter (fun f => x ∈ f)).card := by simp_rw [Finset.card_filter]
  have hleft : ∑ f ∈ A, (B.filter (fun x => x ∈ f)).card = 2 * A.card := by
    rw [Finset.sum_congr rfl claim1, Finset.sum_const, smul_eq_mul, mul_comm]
  have hright : ∑ x ∈ B, (A.filter (fun f => x ∈ f)).card = 2 * B.card := by
    rw [Finset.sum_congr rfl claim2, Finset.sum_const, smul_eq_mul, mul_comm]
  have h2 : 2 * A.card = 2 * B.card := by rw [← hleft, hswap, hright]
  omega

/-- **Vertex–face incidence double count: `∑_v (#faces at v) = 3f`** (every face is a
triangle, `hσ.pure`). -/
lemma sum_incident_faces_eq_three_mul_card {σ : Finset (Finset V)} (hσ : IsSphere2 σ) :
    ∑ v ∈ vertsOf σ, (σ.filter (fun f => v ∈ f)).card = 3 * σ.card := by
  classical
  have hcongr : ∀ f ∈ σ, ((vertsOf σ).filter (fun v => v ∈ f)).card = 3 := by
    intro f hf
    have hset : (vertsOf σ).filter (fun v => v ∈ f) = f := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro hvf
        exact ⟨mem_vertsOf.mpr ⟨f, hf, hvf⟩, hvf⟩
    rw [hset, hσ.pure f hf]
  calc ∑ v ∈ vertsOf σ, (σ.filter (fun f => v ∈ f)).card
      = ∑ v ∈ vertsOf σ, ∑ f ∈ σ, (if v ∈ f then 1 else 0) := by simp_rw [Finset.card_filter]
    _ = ∑ f ∈ σ, ∑ v ∈ vertsOf σ, (if v ∈ f then 1 else 0) := Finset.sum_comm
    _ = ∑ f ∈ σ, ((vertsOf σ).filter (fun v => v ∈ f)).card := by simp_rw [Finset.card_filter]
    _ = ∑ f ∈ σ, 3 := Finset.sum_congr rfl hcongr
    _ = 3 * σ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Euler bridge: a `2`-sphere whose every link has `4` vertices has exactly `6` vertices.**
This pins the octahedron: if every vertex link is a `4`-cycle then `4v = 3f` (Lemma B with
each summand `4`), together with `3f = 2e` and Euler `v + f = e + 2` forces `v = 6`. -/
lemma card_verts_eq_six_of_all_links_four {σ : Finset (Finset V)} (hσ : IsSphere2 σ)
    (h4 : ∀ v ∈ vertsOf σ, (linkVerts σ v).card = 4) :
    (vertsOf σ).card = 6 := by
  classical
  have h3F2E : 3 * σ.card = 2 * (edgesOf σ).card := three_mul_card_faces hσ
  have heuler : (vertsOf σ).card + σ.card = (edgesOf σ).card + 2 := hσ.euler
  have h4V3F : 4 * (vertsOf σ).card = 3 * σ.card := by
    have hlink : ∑ v ∈ vertsOf σ, (linkVerts σ v).card
        = ∑ v ∈ vertsOf σ, (σ.filter (fun f => v ∈ f)).card :=
      Finset.sum_congr rfl
        (fun v hv => (incident_faces_card_eq_linkVerts_card hσ hv).symm)
    have hfour : ∑ v ∈ vertsOf σ, (linkVerts σ v).card = 4 * (vertsOf σ).card := by
      rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hlink, sum_incident_faces_eq_three_mul_card hσ] at hfour
    omega
  omega

/-- **Max-degree ≥ 4.** In a no-degree-3 sphere, some boundary vertex has `deg ≥ 4` (indeed every
vertex does: link size `≥ 3` and `≠ 3`).  `deg v (bdry M) = (σ.filter (v∈·)).card =
(linkVerts σ v).card`. -/
theorem exists_boundary_vertex_deg_ge_four_of_noDegree3 {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hNo3 : NoDegree3Vertex σ) :
    ∃ v ∈ vertsOf σ, 4 ≤ deg v (bdry M) := by
  obtain ⟨v, hv⟩ := hσ.vertsOf_nonempty
  refine ⟨v, hv, ?_⟩
  have hdeg : deg v (bdry M) = (linkVerts σ v).card := by
    rw [aleph_deg_eq_card_filter_of_unitOn hU v, incident_faces_card_eq_linkVerts_card hσ hv]
  have h3 : 3 ≤ (linkVerts σ v).card := three_le_card_linkVerts hσ hv
  have hne3 : (linkVerts σ v).card ≠ 3 := hNo3 v hv
  omega

/-- **Max-degree ≥ 5 unless octahedron.** In a no-degree-3 sphere that is not the octahedron, some
boundary vertex has `deg ≥ 5`.  Contrapositive: if every vertex had `deg ≤ 4` then (with `deg ≥ 4`
from no-degree-3) every link size is exactly `4`, so `|verts| = 6` and `σ` is the octahedron. -/
theorem exists_boundary_vertex_deg_ge_five_of_not_octahedron {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hNo3 : NoDegree3Vertex σ)
    (hNotOct : ¬ IsOctahedronSphere σ) :
    ∃ v ∈ vertsOf σ, 5 ≤ deg v (bdry M) := by
  by_contra hcon
  push_neg at hcon
  have hall4 : ∀ v ∈ vertsOf σ, (linkVerts σ v).card = 4 := by
    intro v hv
    have hdeg : deg v (bdry M) = (linkVerts σ v).card := by
      rw [aleph_deg_eq_card_filter_of_unitOn hU v, incident_faces_card_eq_linkVerts_card hσ hv]
    have hlt5 : deg v (bdry M) < 5 := hcon v hv
    have h3 : 3 ≤ (linkVerts σ v).card := three_le_card_linkVerts hσ hv
    have hne3 : (linkVerts σ v).card ≠ 3 := hNo3 v hv
    omega
  exact hNotOct ⟨hσ, card_verts_eq_six_of_all_links_four hσ hall4, hNo3, hall4⟩

/-- **Four disjoint eligible tets** in a no-degree-3 taut filling (config-1 flip budget). -/
theorem aleph_four_disjoint_eligible_family {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (hT : IsTaut M) (hPure : ∀ t ∈ M.support, t.card = 4) (hNo3 : NoDegree3Vertex σ) :
    ∃ E : Finset (Finset V), E.card = 4 ∧
      (∀ e ∈ E, EligibleTet M e) ∧
      (↑E : Set (Finset V)).PairwiseDisjoint (fun e => sharedFaces M e) := by
  obtain ⟨v, hv, hdeg⟩ := exists_boundary_vertex_deg_ge_four_of_noDegree3 hσ hU hNo3
  exact aleph_disjoint_eligible_family hσ hU hS hT hPure hNo3 hv hdeg

/-- **Five disjoint eligible tets** in a no-degree-3, non-octahedron taut filling (config-2 budget). -/
theorem aleph_five_disjoint_eligible_family {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (hT : IsTaut M) (hPure : ∀ t ∈ M.support, t.card = 4) (hNo3 : NoDegree3Vertex σ)
    (hNotOct : ¬ IsOctahedronSphere σ) :
    ∃ E : Finset (Finset V), E.card = 5 ∧
      (∀ e ∈ E, EligibleTet M e) ∧
      (↑E : Set (Finset V)).PairwiseDisjoint (fun e => sharedFaces M e) := by
  obtain ⟨v, hv, hdeg⟩ := exists_boundary_vertex_deg_ge_five_of_not_octahedron hσ hU hNo3 hNotOct
  exact aleph_disjoint_eligible_family hσ hU hS hT hPure hNo3 hv hdeg

/-! ### Theorem 4 config-1 (K₃) good-flip pair -/

open Classical in
/-- For a family `E` of eligible tets with **pairwise disjoint** shared-face sets, at
most one of them can have its flip-edge `g₃ ∩ g₄` equal to a fixed edge `ab`: two such tets
would put `ab` in ≥ 4 faces of `σ`, contradicting `edgeDeg σ ab = 2`. -/
lemma disjoint_eligible_family_flipEdge_card_le_one
    {M : Chain V} {σ E : Finset (Finset V)} {ab : Finset V}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ)
    (helig : ∀ e ∈ E, EligibleTet M e)
    (hpair : (↑E : Set (Finset V)).PairwiseDisjoint (fun e => sharedFaces M e)) :
    (E.filter (fun e =>
      ∃ g₃ g₄, sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧ ab = g₃ ∩ g₄)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e₁ he₁ e₂ he₂
  by_contra hne
  rw [Finset.mem_filter] at he₁ he₂
  obtain ⟨he₁E, g₃, g₄, hsh₁, hne₁, hab₁⟩ := he₁
  obtain ⟨he₂E, h₃, h₄, hsh₂, hne₂, hab₂⟩ := he₂
  have hg₃sh : g₃ ∈ sharedFaces M e₁ := by rw [hsh₁]; exact Finset.mem_insert_self _ _
  have hg₄sh : g₄ ∈ sharedFaces M e₁ := by
    rw [hsh₁]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hh₃sh : h₃ ∈ sharedFaces M e₂ := by rw [hsh₂]; exact Finset.mem_insert_self _ _
  have hh₄sh : h₄ ∈ sharedFaces M e₂ := by
    rw [hsh₂]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hg₃tet : g₃ ∈ tetFaces e₁ := sharedFaces_subset_tetFaces M e₁ hg₃sh
  have hg₄tet : g₄ ∈ tetFaces e₁ := sharedFaces_subset_tetFaces M e₁ hg₄sh
  have he₁card : e₁.card = 4 := (helig e₁ he₁E).1
  have habcard : ab.card = 2 := by
    rw [hab₁]; exact tetFaces_pair_inter_card_eq_two he₁card hg₃tet hg₄tet hne₁
  have hab_g₃ : ab ⊆ g₃ := hab₁ ▸ Finset.inter_subset_left
  have hab_g₄ : ab ⊆ g₄ := hab₁ ▸ Finset.inter_subset_right
  have hab_h₃ : ab ⊆ h₃ := hab₂ ▸ Finset.inter_subset_left
  have hab_h₄ : ab ⊆ h₄ := hab₂ ▸ Finset.inter_subset_right
  have hmemσ : ∀ {g : Finset V}, g ∈ sharedFaces M e₁ ∨ g ∈ sharedFaces M e₂ → g ∈ σ := by
    intro g hg
    rcases hg with hg | hg
    · have := (Finset.mem_inter.mp hg).2; rwa [hU.1] at this
    · have := (Finset.mem_inter.mp hg).2; rwa [hU.1] at this
  have hg₃σ : g₃ ∈ σ := hmemσ (Or.inl hg₃sh)
  have hg₄σ : g₄ ∈ σ := hmemσ (Or.inl hg₄sh)
  have hh₃σ : h₃ ∈ σ := hmemσ (Or.inr hh₃sh)
  have hh₄σ : h₄ ∈ σ := hmemσ (Or.inr hh₄sh)
  have hdisj : Disjoint (sharedFaces M e₁) (sharedFaces M e₂) :=
    hpair (Finset.mem_coe.mpr he₁E) (Finset.mem_coe.mpr he₂E) hne
  rw [Finset.disjoint_left] at hdisj
  have hg₃h₃ : g₃ ≠ h₃ := fun h => hdisj hg₃sh (h ▸ hh₃sh)
  have hg₃h₄ : g₃ ≠ h₄ := fun h => hdisj hg₃sh (h ▸ hh₄sh)
  have hg₄h₃ : g₄ ≠ h₃ := fun h => hdisj hg₄sh (h ▸ hh₃sh)
  have hg₄h₄ : g₄ ≠ h₄ := fun h => hdisj hg₄sh (h ▸ hh₄sh)
  have habedge : ab ∈ edgesOf σ := mem_edgesOf.mpr ⟨g₃, hg₃σ, hab_g₃, habcard⟩
  have habdeg : (σ.filter (fun f => ab ⊆ f)).card = 2 := hσ.closed ab habedge
  have hsub : ({g₃, g₄, h₃, h₄} : Finset (Finset V)) ⊆ σ.filter (fun f => ab ⊆ f) := by
    intro f hf
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact ⟨hg₃σ, hab_g₃⟩
    · exact ⟨hg₄σ, hab_g₄⟩
    · exact ⟨hh₃σ, hab_h₃⟩
    · exact ⟨hh₄σ, hab_h₄⟩
  have hfour : ({g₃, g₄, h₃, h₄} : Finset (Finset V)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne₁, hg₃h₃, hg₃h₄]),
        Finset.card_insert_of_notMem (by simp [hg₄h₃, hg₄h₄]),
        Finset.card_insert_of_notMem (by simp [hne₂]), Finset.card_singleton]
  have : (4 : ℕ) ≤ 2 := by
    calc (4 : ℕ) = ({g₃, g₄, h₃, h₄} : Finset (Finset V)).card := hfour.symm
      _ ≤ (σ.filter (fun f => ab ⊆ f)).card := Finset.card_le_card hsub
      _ = 2 := habdeg
  omega

open Classical in
/-- **Config-1 (empty `K₃`) good flip.**  Given an empty triangle `s` (all three edges are
simplices of `M.support`) in a no-degree-3 taut filling, there is an eligible tet whose
flip edge `g₃ ∩ g₄` avoids every edge of `s`.  The aleph budget gives `4` disjoint eligible
tets; the previous lemma caps the number whose flip edge hits any one of `s`'s three edges
at one apiece, so at most `3` are bad and at least one survives. -/
theorem exists_good_flip_emptyK3
    {M : Chain V} {σ : Finset (Finset V)}
    (hσ : IsSphere2 σ) (hU : UnitOn (bdry M) σ) (hS : SimplicialChain M)
    (hT : IsTaut M) (hPure : ∀ t ∈ M.support, t.card = 4)
    (hNo3 : NoDegree3Vertex σ)
    {s : Finset V} (hs3 : s.card = 3)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf M.support x) :
    ∃ e g₃ g₄, EligibleTet M e ∧ sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧
      (∀ x, x ⊆ s → x.card = 2 → x ≠ g₃ ∩ g₄) := by
  obtain ⟨E, hEcard, hElig, hEpair⟩ :=
    aleph_four_disjoint_eligible_family hσ hU hS hT hPure hNo3
  set badE := E.filter (fun e =>
    ∃ g₃ g₄, sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧ g₃ ∩ g₄ ∈ s.powersetCard 2)
    with hbadE
  have hbadsub : badE ⊆ (s.powersetCard 2).biUnion (fun ab =>
      E.filter (fun e => ∃ g₃ g₄, sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧ ab = g₃ ∩ g₄)) := by
    intro e he
    rw [hbadE, Finset.mem_filter] at he
    obtain ⟨heE, g₃, g₄, hsh, hne, hmem⟩ := he
    rw [Finset.mem_biUnion]
    exact ⟨g₃ ∩ g₄, hmem, Finset.mem_filter.mpr ⟨heE, g₃, g₄, hsh, hne, rfl⟩⟩
  have hbadcard : badE.card ≤ 3 := by
    calc badE.card
        ≤ ((s.powersetCard 2).biUnion (fun ab =>
            E.filter (fun e => ∃ g₃ g₄, sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧ ab = g₃ ∩ g₄))).card :=
          Finset.card_le_card hbadsub
      _ ≤ ∑ ab ∈ s.powersetCard 2,
            (E.filter (fun e => ∃ g₃ g₄, sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧ ab = g₃ ∩ g₄)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _ab ∈ s.powersetCard 2, 1 :=
          Finset.sum_le_sum (fun ab _ =>
            disjoint_eligible_family_flipEdge_card_le_one hσ hU hElig hEpair)
      _ = (s.powersetCard 2).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = 3 := by rw [Finset.card_powersetCard, hs3]; decide
  have hbadsubE : badE ⊆ E := by rw [hbadE]; exact Finset.filter_subset _ _
  have hne : (E \ badE).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hbadsubE, hEcard]
    omega
  obtain ⟨e, he⟩ := hne
  rw [Finset.mem_sdiff] at he
  obtain ⟨heE, hebad⟩ := he
  have helig : EligibleTet M e := hElig e heE
  have hshcard : (sharedFaces M e).card = 2 := helig.2.2.1
  obtain ⟨g₃, g₄, hg, hsh⟩ := Finset.card_eq_two.mp hshcard
  refine ⟨e, g₃, g₄, helig, hsh, hg, ?_⟩
  intro x hxs hxcard hxeq
  apply hebad
  rw [hbadE, Finset.mem_filter]
  refine ⟨heE, g₃, g₄, hsh, hg, ?_⟩
  rw [← hxeq]
  exact Finset.mem_powersetCard.mpr ⟨hxs, hxcard⟩

/-- With no empty `K₃`, every triangular face of an empty `K₄` witness `s` is itself a simplex.
(Each of `s`'s `card`-3 subsets has all its edges among `s`'s edges, hence simplices; were it not a
simplex it would be an empty `K₃`.) -/
lemma emptyK4_face_simplex_of_no_emptyK3 {τ : Finset (Finset V)} {s f : Finset V}
    (hNoK3 : ¬ HasEmptyK3 τ) (_hs4 : s.card = 4)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf τ x)
    (hf : f ⊆ s) (hf3 : f.card = 3) :
    SimplexOf τ f := by
  by_contra hns
  exact hNoK3 ⟨f, hf3, fun x hxf hx2 => hsedges x (hxf.trans hf) hx2, hns⟩

/-! ### Theorem 4 config-2 (K₄) persistence route

Under `¬ HasEmptyK3`, removing ANY eligible tet `e` preserves an empty `K₄`.  A `K₄` edge `x ⊆ e`
that is the deleted diagonal still survives, because some `K₄` face through it is a simplex
(`emptyK4_face_simplex_of_no_emptyK3`) living in a tet `≠ e`.  No counting / octahedron / 5-family
is needed; every other edge already has a witness `≠ e` from
`edge_witness_ne_removed_of_not_sharedEdge`. -/

/-- **A `K₄` face through an edge `x ⊆ e` that escapes `e`.**  `s ⊄ e` (else `s` is a simplex),
so `insert v x` for `v ∈ s \ e` is a card-`3` subset of `s` containing `x` with `f ⊄ e`. -/
lemma exists_k4_face_through_edge_not_subset_tet {τ : Finset (Finset V)} {e s x : Finset V}
    (hs4 : s.card = 4) (hno : ¬ SimplexOf τ s) (he : e ∈ τ)
    (hx : x ⊆ s) (hx2 : x.card = 2) (hxe : x ⊆ e) :
    ∃ f, f ⊆ s ∧ f.card = 3 ∧ x ⊆ f ∧ ¬ f ⊆ e := by
  have hse : ¬ s ⊆ e := fun hse => hno (Or.inr ⟨e, he, hse⟩)
  have hne : (s \ e).Nonempty := Finset.sdiff_nonempty.mpr hse
  obtain ⟨v, hv⟩ := hne
  have hvs : v ∈ s := (Finset.mem_sdiff.mp hv).1
  have hve : v ∉ e := (Finset.mem_sdiff.mp hv).2
  refine ⟨insert v x, Finset.insert_subset hvs hx, ?_, Finset.subset_insert v x, ?_⟩
  · have hvx : v ∉ x := fun h => hve (hxe h)
    rw [Finset.card_insert_of_notMem hvx, hx2]
  · intro hfe
    exact hve (hfe (Finset.mem_insert_self v x))

/-- **A `K₄` edge `x ⊆ e` keeps a witness `≠ e` (no empty `K₃` case).**  Under `¬ HasEmptyK3` a
`K₄` face through `x` escaping `e` is a simplex, supplying a tet `t ≠ e` with `x ⊆ t`. -/
lemma k4_edge_has_witness_ne_removed_of_no_emptyK3 {M : Chain V} {e s x : Finset V}
    (hNoK3 : ¬ HasEmptyK3 M.support) (hs4 : s.card = 4)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf M.support x)
    (hno : ¬ SimplexOf M.support s) (he : e ∈ M.support)
    (hx : x ⊆ s) (hx2 : x.card = 2) (hxe : x ⊆ e) :
    ∃ t ∈ M.support, t ≠ e ∧ x ⊆ t := by
  obtain ⟨f, hfs, hf3, hxf, hfe⟩ :=
    exists_k4_face_through_edge_not_subset_tet hs4 hno he hx hx2 hxe
  have hsimp : SimplexOf M.support f :=
    emptyK4_face_simplex_of_no_emptyK3 hNoK3 hs4 hsedges hfs hf3
  rcases hsimp with hempty | ⟨t, htM, hft⟩
  · rw [hempty, Finset.card_empty] at hf3; exact absurd hf3 (by decide)
  · refine ⟨t, htM, ?_, hxf.trans hft⟩
    intro hte
    exact hfe (hte ▸ hft)

/-- **Every edge of a `K₄` witness keeps a witness `≠ e` past an eligible removal (no empty `K₃`).**
For the flip diagonal `x = g₃ ∩ g₄` (which lies `⊆ e`), route through the `K₄`-face argument;
every other edge already has a witness `≠ e` via `edge_witness_ne_removed_of_not_sharedEdge`. -/
lemma emptyK4_edge_witness_ne_removed_of_eligible {M : Chain V} {e s : Finset V}
    (hNoK3 : ¬ HasEmptyK3 M.support) (hs4 : s.card = 4)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf M.support x)
    (hno : ¬ SimplexOf M.support s) (he : EligibleTet M e) :
    ∀ x, x ⊆ s → x.card = 2 → ∃ t ∈ M.support, t ≠ e ∧ x ⊆ t := by
  obtain ⟨g₃, g₄, hg, hsh⟩ := Finset.card_eq_two.mp he.2.2.1
  intro x hxs hx2
  have hxsimp : SimplexOf M.support x := hsedges x hxs hx2
  by_cases hxflip : x = g₃ ∩ g₄
  · have hg₃sh : g₃ ∈ sharedFaces M e := by rw [hsh]; exact Finset.mem_insert_self _ _
    have hg₃e : g₃ ⊆ e :=
      (Finset.mem_powersetCard.mp (sharedFaces_subset_tetFaces M e hg₃sh)).1
    have hxe : x ⊆ e := hxflip ▸ Finset.inter_subset_left.trans hg₃e
    exact k4_edge_has_witness_ne_removed_of_no_emptyK3 hNoK3 hs4 hsedges hno he.2.1 hxs hx2 hxe
  · exact edge_witness_ne_removed_of_not_sharedEdge he hsh hg hxsimp hx2 hxflip

/-- **Empty-`K₄` persists past removing ANY eligible tet, under `¬ HasEmptyK3`.** -/
lemma hasEmptyK4_removeTet_of_eligible {M : Chain V} {e s : Finset V}
    (hNoK3 : ¬ HasEmptyK3 M.support) (hs4 : s.card = 4)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf M.support x)
    (hno : ¬ SimplexOf M.support s) (he : EligibleTet M e) :
    HasEmptyK4 (removeTet M e).support :=
  hasEmptyK4_removeTet_of_witness he.2.1 hs4
    (emptyK4_edge_witness_ne_removed_of_eligible hNoK3 hs4 hsedges hno he) hno

/-! ## (6) The nrm-induction: base case and degree-3 star transfer

The minimal-counterexample induction `no_emptyK3K4_of_taut` removes either a degree-3
star tet `T = insert v γ` (`v` of degree 3, `γ` its link triangle) or an eligible flip.
The degree-3 star transfer relies on: an empty configuration in the larger complex
`insert T τ` already lives in `τ`, because its witness avoids `v` — the only new vertex of `T`. -/

/-- **Base case of the nrm-induction.** For a minimal sphere (`≤ 4` vertices) the taut
filling's support is the single tet `T = vertsOf σ`, so any empty-`K₃`/`K₄` witness is `⊆ T`,
hence a simplex, contradicting `¬ SimplexOf`. -/
lemma base_no_emptyK3K4 {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hMX : bdry M = X) (hT : IsTaut M)
    (hv : (vertsOf σ).card ≤ 4) :
    ¬ HasEmptyK3 M.support ∧ ¬ HasEmptyK4 M.support := by
  classical
  set T := vertsOf σ with hTdef
  have hVc : T.card = 4 := aleph_base_verts_card_eq_four hσ hv
  have hsuppInfo : ∀ t ∈ M.support, t.card = 4 ∧ t ⊆ T :=
    aleph_base_taut_support_card4_subset_verts hσ hU hMX hT
  have hne : M.support.Nonempty := aleph_base_support_nonempty hσ hU hMX
  have hsupp1 : M.support = {T} :=
    aleph_base_support_eq_singleton_of_four_vertices hVc hsuppInfo hne
  have helper : ∀ s : Finset V, 2 ≤ s.card →
      (∀ e, e ⊆ s → e.card = 2 → SimplexOf M.support e) → SimplexOf M.support s := by
    intro s hs2 hedges
    have hsubT : s ⊆ T := by
      intro v hv
      obtain ⟨w, hws, hwv⟩ :=
        (Finset.one_lt_card_iff_nontrivial.mp (show 1 < s.card by omega)).exists_ne v
      have hvw2 : ({v, w} : Finset V).card = 2 := Finset.card_pair (Ne.symm hwv)
      have hvwsub : ({v, w} : Finset V) ⊆ s := by
        intro y hy
        rcases Finset.mem_insert.mp hy with h | h
        · exact h ▸ hv
        · exact (Finset.mem_singleton.mp h) ▸ hws
      have hsimp : SimplexOf M.support ({v, w} : Finset V) := hedges _ hvwsub hvw2
      have hvw0 : ({v, w} : Finset V) ≠ ∅ := by
        intro h; rw [h, Finset.card_empty] at hvw2; exact absurd hvw2 (by decide)
      obtain ⟨t, htM, hvwt⟩ := hsimp.resolve_left hvw0
      rw [hsupp1, Finset.mem_singleton] at htM
      have hvt : v ∈ t := hvwt (Finset.mem_insert_self v {w})
      exact htM ▸ hvt
    exact Or.inr ⟨T, by rw [hsupp1]; exact Finset.mem_singleton_self T, hsubT⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hcard, hedges, hno⟩
    exact hno (helper s (by omega) hedges)
  · rintro ⟨s, hcard, hedges, hno⟩
    exact hno (helper s (by omega) hedges)

/-- **A boundary face is a facet of some tet.** If `bdry R γ = ±1`, some tet `t` of `R.support`
has `γ ⊆ t`. -/
lemma exists_tet_of_boundary_face_nonzero {R : Chain V} {γ : Finset V}
    (hγ : bdry R γ = 1 ∨ bdry R γ = -1) : ∃ t ∈ R.support, γ ⊆ t := by
  classical
  have hsum : bdry R γ = ∑ t ∈ R.support, R t * bdryGen t γ := bdry_apply_eq_sum R γ
  have hne0 : bdry R γ ≠ 0 := by rcases hγ with h | h <;> rw [h] <;> decide
  have hsumne : (∑ t ∈ R.support, R t * bdryGen t γ) ≠ 0 := by rw [← hsum]; exact hne0
  obtain ⟨t, ht, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hgen : bdryGen t γ ≠ 0 := fun h0 => htne (by rw [h0, mul_zero])
  obtain ⟨w, hw, hγt⟩ := exists_facet_of_bdryGen_ne_zero hgen
  exact ⟨t, ht, hγt ▸ Finset.erase_subset w t⟩

/-- **Degree-3 star transfer for empty `K₃`.** Removing the star tet `T = insert v γ`
(`hRnoV`: `v` absent from every tet of the remainder `τ`; `hγbridge`: `γ` bridged by some tet
of `τ`) preserves an empty `K₃`: a witness in `insert T τ` cannot contain `v` (else it would lie
in `T`, a simplex), so each edge avoids `v` and, where it meets `T`, lands in `γ`. -/
lemma hasEmptyK3_insert_star_to_remainder {τ : Finset (Finset V)} {T γ : Finset V} {v : V}
    (hT : T = insert v γ) (hRnoV : ∀ t ∈ τ, v ∉ t)
    (hγbridge : ∃ t ∈ τ, γ ⊆ t) :
    HasEmptyK3 (insert T τ) → HasEmptyK3 τ := by
  classical
  rintro ⟨s, hs3, hsedges, hsno⟩
  have hsno' : ¬ SimplexOf τ s := fun h => hsno (h.mono (Finset.subset_insert T τ))
  have hvs : v ∉ s := by
    intro hvs
    have hsubT : s ⊆ T := by
      intro u hu
      by_cases huv : u = v
      · rw [huv, hT]; exact Finset.mem_insert_self v γ
      · have huvsub : ({v, u} : Finset V) ⊆ s := by
          intro y hy
          rcases Finset.mem_insert.mp hy with h | h
          · exact h ▸ hvs
          · exact (Finset.mem_singleton.mp h) ▸ hu
        have hvu2 : ({v, u} : Finset V).card = 2 := Finset.card_pair (Ne.symm huv)
        have hsimp : SimplexOf (insert T τ) ({v, u} : Finset V) :=
          hsedges _ huvsub hvu2
        have hvu0 : ({v, u} : Finset V) ≠ ∅ := by
          intro h; rw [h, Finset.card_empty] at hvu2; exact absurd hvu2 (by decide)
        obtain ⟨t, htmem, hvut⟩ := hsimp.resolve_left hvu0
        have hvt : v ∈ t := hvut (Finset.mem_insert_self v {u})
        have hut : u ∈ t := hvut (Finset.mem_insert_of_mem (Finset.mem_singleton_self u))
        have htT : t = T := by
          rcases Finset.mem_insert.mp htmem with h | h
          · exact h
          · exact absurd hvt (hRnoV t h)
        rw [htT, hT, Finset.mem_insert] at hut
        rcases hut with h | h
        · exact absurd h huv
        · rw [hT]; exact Finset.mem_insert_of_mem h
    exact hsno (Or.inr ⟨T, Finset.mem_insert_self T τ, hsubT⟩)
  have hsedges' : ∀ e, e ⊆ s → e.card = 2 → SimplexOf τ e := by
    intro e hes he2
    have hsimp : SimplexOf (insert T τ) e := hsedges e hes he2
    have he0 : e ≠ ∅ := by
      intro h; rw [h, Finset.card_empty] at he2; exact absurd he2 (by decide)
    obtain ⟨t, htmem, het⟩ := hsimp.resolve_left he0
    rcases Finset.mem_insert.mp htmem with htT | htτ
    · have hve : v ∉ e := fun h => hvs (hes h)
      have heγ : e ⊆ γ := by
        intro x hx
        have hxT : x ∈ insert v γ := hT ▸ htT ▸ het hx
        rcases Finset.mem_insert.mp hxT with h | h
        · exact absurd (h ▸ hx) hve
        · exact h
      obtain ⟨tγ, htγτ, hγtγ⟩ := hγbridge
      exact Or.inr ⟨tγ, htγτ, heγ.trans hγtγ⟩
    · exact Or.inr ⟨t, htτ, het⟩
  exact ⟨s, hs3, hsedges', hsno'⟩

/-- **Degree-3 star transfer for empty `K₄`.** Identical to the `K₃` case; the witness
card (`4` vs `3`) plays no role beyond the `card ≥ 2` used to pick a second vertex. -/
lemma hasEmptyK4_insert_star_to_remainder {τ : Finset (Finset V)} {T γ : Finset V} {v : V}
    (hT : T = insert v γ) (hRnoV : ∀ t ∈ τ, v ∉ t)
    (hγbridge : ∃ t ∈ τ, γ ⊆ t) :
    HasEmptyK4 (insert T τ) → HasEmptyK4 τ := by
  classical
  rintro ⟨s, hs4, hsedges, hsno⟩
  have hsno' : ¬ SimplexOf τ s := fun h => hsno (h.mono (Finset.subset_insert T τ))
  have hvs : v ∉ s := by
    intro hvs
    have hsubT : s ⊆ T := by
      intro u hu
      by_cases huv : u = v
      · rw [huv, hT]; exact Finset.mem_insert_self v γ
      · have huvsub : ({v, u} : Finset V) ⊆ s := by
          intro y hy
          rcases Finset.mem_insert.mp hy with h | h
          · exact h ▸ hvs
          · exact (Finset.mem_singleton.mp h) ▸ hu
        have hvu2 : ({v, u} : Finset V).card = 2 := Finset.card_pair (Ne.symm huv)
        have hsimp : SimplexOf (insert T τ) ({v, u} : Finset V) :=
          hsedges _ huvsub hvu2
        have hvu0 : ({v, u} : Finset V) ≠ ∅ := by
          intro h; rw [h, Finset.card_empty] at hvu2; exact absurd hvu2 (by decide)
        obtain ⟨t, htmem, hvut⟩ := hsimp.resolve_left hvu0
        have hvt : v ∈ t := hvut (Finset.mem_insert_self v {u})
        have hut : u ∈ t := hvut (Finset.mem_insert_of_mem (Finset.mem_singleton_self u))
        have htT : t = T := by
          rcases Finset.mem_insert.mp htmem with h | h
          · exact h
          · exact absurd hvt (hRnoV t h)
        rw [htT, hT, Finset.mem_insert] at hut
        rcases hut with h | h
        · exact absurd h huv
        · rw [hT]; exact Finset.mem_insert_of_mem h
    exact hsno (Or.inr ⟨T, Finset.mem_insert_self T τ, hsubT⟩)
  have hsedges' : ∀ e, e ⊆ s → e.card = 2 → SimplexOf τ e := by
    intro e hes he2
    have hsimp : SimplexOf (insert T τ) e := hsedges e hes he2
    have he0 : e ≠ ∅ := by
      intro h; rw [h, Finset.card_empty] at he2; exact absurd he2 (by decide)
    obtain ⟨t, htmem, het⟩ := hsimp.resolve_left he0
    rcases Finset.mem_insert.mp htmem with htT | htτ
    · have hve : v ∉ e := fun h => hvs (hes h)
      have heγ : e ⊆ γ := by
        intro x hx
        have hxT : x ∈ insert v γ := hT ▸ htT ▸ het hx
        rcases Finset.mem_insert.mp hxT with h | h
        · exact absurd (h ▸ hx) hve
        · exact h
      obtain ⟨tγ, htγτ, hγtγ⟩ := hγbridge
      exact Or.inr ⟨tγ, htγτ, heγ.trans hγtγ⟩
    · exact Or.inr ⟨t, htτ, het⟩
  exact ⟨s, hs4, hsedges', hsno'⟩

/-- **Degree-3 step for the empty-`K₃`/`K₄` ruleout.**  Mechanical adaptation of
`deg3_isPM`: cut off the degree-3 star, apply the induction hypothesis (now returning the
`¬ HasEmptyK3 ∧ ¬ HasEmptyK4` conjunction) to the non-star remainder, then transfer the
two ruleouts back across the re-glued star tetrahedron via
`hasEmptyK3/K4_insert_star_to_remainder`. -/
lemma deg3_no_emptyK3K4 (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hbig : 4 < (vertsOf σ).card) (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X)
    (hT : IsTaut M) (hS : SimplicialChain M) (hd3 : HasDegree3Vertex σ)
    (IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      ¬ HasEmptyK3 M'.support ∧ ¬ HasEmptyK4 M'.support) :
    ¬ HasEmptyK3 M.support ∧ ¬ HasEmptyK4 M.support := by
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
  · rcases hcase with ⟨hstar, _hglue⟩
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
    obtain ⟨hIH3, hIH4⟩ :=
      IH (insert γ (cutSet σ (W + fun _ => 1))) (bdry MR) MR hlt hσRdef hURMR
        (bdry_bdry _) rfl hTRMR hSimpR
    have hPT : (starTet σ v) ⊆ A := by
      have hTin : starTet σ v ∈ ML.support := by rw [hMLsupp]; simp
      have hTin' : ¬ M (starTet σ v) = 0 ∧ (starTet σ v) ⊆ A := by simpa [ML] using hTin
      exact hTin'.2
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
    have hURγ : bdry MR γ = 1 ∨ bdry MR γ = -1 := hURMR.2 γ hγR
    have hsupport : M.support = insert (starTet σ v) MR.support := by
      simpa only [MR] using
        support_eq_insert_of_filter_support_singleton M (fun t => t ⊆ A) hMLsupp
    obtain ⟨tγ, htγ, hγtγ⟩ := exists_tet_of_boundary_face_nonzero hURγ
    have hstar_eq : starTet σ v = insert v γ := rfl
    exact ⟨fun h3 => hIH3 (hasEmptyK3_insert_star_to_remainder hstar_eq hvNotMR ⟨tγ, htγ, hγtγ⟩ (hsupport ▸ h3)),
           fun h4 => hIH4 (hasEmptyK4_insert_star_to_remainder hstar_eq hvNotMR ⟨tγ, htγ, hγtγ⟩ (hsupport ▸ h4))⟩
  · rcases hcase with ⟨hstar, _hglue⟩
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
    obtain ⟨hIH3, hIH4⟩ :=
      IH (insert γ (cutSet σ W)) (bdry ML) ML hlt hσLdef hULML
        (bdry_bdry _) rfl hTLML hSimpL
    have hPstar : ¬ (starTet σ v) ⊆ A := by
      have hTin : starTet σ v ∈ MR.support := by rw [hMRsupp]; simp
      have hTin' : ¬ M (starTet σ v) = 0 ∧ ¬ (starTet σ v) ⊆ A := by simpa [MR] using hTin
      exact hTin'.2
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
    have hURγ : bdry ML γ = 1 ∨ bdry ML γ = -1 := hULML.2 γ hγL
    have hsupport : M.support = insert (starTet σ v) ML.support := by
      have hsupport' :
          M.support = insert (starTet σ v)
            (M.filter (fun t => ¬ (¬ t ⊆ A))).support :=
        support_eq_insert_of_filter_support_singleton M (fun t => ¬ t ⊆ A) hMRsupp
      rwa [← hML_eq] at hsupport'
    obtain ⟨tγ, htγ, hγtγ⟩ := exists_tet_of_boundary_face_nonzero hURγ
    have hstar_eq : starTet σ v = insert v γ := rfl
    exact ⟨fun h3 => hIH3 (hasEmptyK3_insert_star_to_remainder hstar_eq hvNotML ⟨tγ, htγ, hγtγ⟩ (hsupport ▸ h3)),
           fun h4 => hIH4 (hasEmptyK4_insert_star_to_remainder hstar_eq hvNotML ⟨tγ, htγ, hγtγ⟩ (hsupport ▸ h4))⟩

/-! ## (7) The prime (no-degree-3) step of the nrm-induction

When `σ` has no degree-3 vertex, the minimal-counterexample induction removes an eligible
flip rather than a degree-3 star.  Both empty-`K₃` and empty-`K₄` are ruled out by the same
two-case structure: if the flipped diagonal is already a flip edge of `σ` (`FlipEdgePresent`)
the support splits across the seam `A ∩ B = f₃ ∩ f₄` into two smaller taut fillings (each on a
single sphere), and an empty configuration localizes to one side (`hasEmptyK*_side_of_edge_split`)
where the IH kills it; otherwise the remainder `removeTet M e` is itself a single smaller taut
filling (sphere `flipBoundary σ M e`) and the IH applies directly. -/

/-- **Both sides of an already-present flip carry a bridging tet of the seam edge.** With the
flipped diagonal `A ∩ B = f₃ ∩ f₄` already a flip edge of `σ`, each exposed triangle is a
boundary face of its side (`hUA`/`hUB`), so it is a facet of some tet of `removeTet M e` lying
on that side; that tet contains the exposed triangle hence the seam edge `A ∩ B ⊆ f₃ ⊆ t`. -/
lemma side_edge_bridges_of_flip_present {σ : Finset (Finset V)} {M : Chain V} {e f₃ f₄ A B : Finset V}
    (he : EligibleTet M e) (hexp : exposedFaces M e = {f₃, f₄})
    (hAB : A ∩ B = f₃ ∩ f₄) (hf₃A : f₃ ⊆ A) (hf₄B : f₄ ⊆ B)
    (hUA : UnitOn (bdry ((removeTet M e).filter (fun t => t ⊆ A))) ((flipBoundary σ M e).filter (fun f => f ⊆ A)))
    (hUB : UnitOn (bdry ((removeTet M e).filter (fun t => t ⊆ B))) ((flipBoundary σ M e).filter (fun f => f ⊆ B))) :
    (∃ t ∈ (removeTet M e).support, t ⊆ A ∧ A ∩ B ⊆ t) ∧
    (∃ t ∈ (removeTet M e).support, t ⊆ B ∧ A ∩ B ⊆ t) := by
  classical
  refine ⟨?_, ?_⟩
  · have hf₃exp : f₃ ∈ exposedFaces M e := by rw [hexp]; exact Finset.mem_insert_self f₃ {f₄}
    have hf₃flip : f₃ ∈ flipBoundary σ M e := Finset.subset_union_right hf₃exp
    have hf₃σ₁ : f₃ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ A) :=
      Finset.mem_filter.mpr ⟨hf₃flip, hf₃A⟩
    have hbd : bdry ((removeTet M e).filter (fun t => t ⊆ A)) f₃ = 1 ∨
        bdry ((removeTet M e).filter (fun t => t ⊆ A)) f₃ = -1 := hUA.2 f₃ hf₃σ₁
    obtain ⟨t, ht, hf₃t⟩ := exists_tet_of_boundary_face_nonzero hbd
    rw [Finsupp.support_filter, Finset.mem_filter] at ht
    refine ⟨t, ht.1, ht.2, ?_⟩
    rw [hAB]
    exact Finset.inter_subset_left.trans hf₃t
  · have hf₄exp : f₄ ∈ exposedFaces M e := by
      rw [hexp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self f₄)
    have hf₄flip : f₄ ∈ flipBoundary σ M e := Finset.subset_union_right hf₄exp
    have hf₄σ₁ : f₄ ∈ (flipBoundary σ M e).filter (fun f => f ⊆ B) :=
      Finset.mem_filter.mpr ⟨hf₄flip, hf₄B⟩
    have hbd : bdry ((removeTet M e).filter (fun t => t ⊆ B)) f₄ = 1 ∨
        bdry ((removeTet M e).filter (fun t => t ⊆ B)) f₄ = -1 := hUB.2 f₄ hf₄σ₁
    obtain ⟨t, ht, hf₄t⟩ := exists_tet_of_boundary_face_nonzero hbd
    rw [Finsupp.support_filter, Finset.mem_filter] at ht
    refine ⟨t, ht.1, ht.2, ?_⟩
    rw [hAB]
    exact Finset.inter_subset_right.trans hf₄t

/-- **Prime (no-degree-3) step of the nrm-induction.** A minimal taut filling whose sphere has
no degree-3 vertex has neither an empty `K₃` nor an empty `K₄`: pick an eligible flip and split
on whether its diagonal is already a flip edge of `σ`.  Empty-`K₃` is handled first; empty-`K₄`
reuses it via `hasEmptyK4_removeTet_of_eligible`. -/
lemma prime_no_emptyK3K4 (σ : Finset (Finset V)) (X M : Chain V) (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) (hNo3 : NoDegree3Vertex σ)
    (IH : ∀ (σ' : Finset (Finset V)) (X' M' : Chain V), nrm M' < nrm M → IsSphere2 σ' →
      UnitOn X' σ' → bdry X' = 0 → bdry M' = X' → IsTaut M' → SimplicialChain M' →
      ¬ HasEmptyK3 M'.support ∧ ¬ HasEmptyK4 M'.support) :
    ¬ HasEmptyK3 M.support ∧ ¬ HasEmptyK4 M.support := by
  classical
  have hUb : UnitOn (bdry M) σ := by rw [hMX]; exact hU
  have hPure : ∀ t ∈ M.support, t.card = 4 :=
    fun t ht => (aleph_base_taut_support_card4_subset_verts hσ hU hMX hT t ht).1
  have hNoK3 : ¬ HasEmptyK3 M.support := by
    rintro ⟨s, hs3, hsedges, hno⟩
    obtain ⟨e, g₃, g₄, he, hsh, hg, havoid⟩ :=
      exists_good_flip_emptyK3 hσ hUb hS hT hPure hNo3 hs3 hsedges
    obtain ⟨f₃, f₄, hf₃₄, hexp⟩ := exposedFaces_eq_pair_of_eligible he
    have hR : HasEmptyK3 (removeTet M e).support :=
      hasEmptyK3_removeTet_of_avoids_sharedEdge he hsh hg hs3 hsedges havoid hno
    by_cases hFlip : FlipEdgePresent σ f₃ f₄
    · obtain ⟨A, B, hAB, hcd, hsphA, hsphB, hcover, hsep, hf₃A, hf₃nB, hf₄B, hf₄nA, hfc⟩ :=
        flipEdgePresent_side_sets hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
      obtain ⟨hUA, hUB, hXAc, hXBc, hTA, hTB, hSA, hSB, hnA, hnB, _, _, _, _⟩ :=
        flipEdgePresent_side_algebra hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip hAB hcd hcover hsep
      obtain ⟨hbridgeA, hbridgeB⟩ :=
        side_edge_bridges_of_flip_present he hexp hAB hf₃A hf₄B hUA hUB
      have hAB2 : (A ∩ B).card = 2 := by rw [hAB]; exact hcd
      rcases hasEmptyK3_side_of_edge_split hcover hsep hAB2 hbridgeA hbridgeB hR with hA | hB
      · exact (IH _ _ _ hnA hsphA hUA hXAc rfl hTA hSA).1
          (by rw [Finsupp.support_filter]; exact hA)
      · exact (IH _ _ _ hnB hsphB hUB hXBc rfl hTB hSB).1
          (by rw [Finsupp.support_filter]; exact hB)
    · have hσe := isSphere2_flipBoundary_of_eligible hσ hUb he hexp hf₃₄ hFlip
      have hUe := unitOn_flipBoundary_of_eligible hUb he
      have hnR : nrm (removeTet M e) < nrm M := by
        have h := nrm_removeTet_add_one_of_simplicial hS he.2.1; omega
      exact (IH _ _ _ hnR hσe hUe (bdry_bdry _) rfl (isTaut_removeTet hT)
        (simplicialChain_removeTet hS)).1 hR
  have hNoK4 : ¬ HasEmptyK4 M.support := by
    rintro ⟨s, hs4, hsedges, hno⟩
    obtain ⟨e, u, hne, he, hu, hdisj⟩ :=
      aleph_disjoint_eligible_pair hσ hUb hS hT hPure hNo3
    obtain ⟨f₃, f₄, hf₃₄, hexp⟩ := exposedFaces_eq_pair_of_eligible he
    have hR : HasEmptyK4 (removeTet M e).support :=
      hasEmptyK4_removeTet_of_eligible hNoK3 hs4 hsedges hno he
    by_cases hFlip : FlipEdgePresent σ f₃ f₄
    · obtain ⟨A, B, hAB, hcd, hsphA, hsphB, hcover, hsep, hf₃A, hf₃nB, hf₄B, hf₄nA, hfc⟩ :=
        flipEdgePresent_side_sets hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip
      obtain ⟨hUA, hUB, hXAc, hXBc, hTA, hTB, hSA, hSB, hnA, hnB, _, _, _, _⟩ :=
        flipEdgePresent_side_algebra hσ hU hXc hMX hT hS he hexp hf₃₄ hFlip hAB hcd hcover hsep
      obtain ⟨hbridgeA, hbridgeB⟩ :=
        side_edge_bridges_of_flip_present he hexp hAB hf₃A hf₄B hUA hUB
      have hAB2 : (A ∩ B).card = 2 := by rw [hAB]; exact hcd
      rcases hasEmptyK4_side_of_edge_split hcover hsep hAB2 hbridgeA hbridgeB hR with hA | hB
      · exact (IH _ _ _ hnA hsphA hUA hXAc rfl hTA hSA).2
          (by rw [Finsupp.support_filter]; exact hA)
      · exact (IH _ _ _ hnB hsphB hUB hXBc rfl hTB hSB).2
          (by rw [Finsupp.support_filter]; exact hB)
    · have hσe := isSphere2_flipBoundary_of_eligible hσ hUb he hexp hf₃₄ hFlip
      have hUe := unitOn_flipBoundary_of_eligible hUb he
      have hnR : nrm (removeTet M e) < nrm M := by
        have h := nrm_removeTet_add_one_of_simplicial hS he.2.1; omega
      exact (IH _ _ _ hnR hσe hUe (bdry_bdry _) rfl (isTaut_removeTet hT)
        (simplicialChain_removeTet hS)).2 hR
  exact ⟨hNoK3, hNoK4⟩

/-! ## (6) The induction and the Theorem-4 endpoint -/

/-- **No empty `K₃`/`K₄` in a taut filling of a 2-sphere.** Strong induction on `nrm M`, mirroring
`taut_isPseudomanifold`: base case (`≤ 4` vertices) by `base_no_emptyK3K4`; a degree-3 vertex by
`deg3_no_emptyK3K4`; otherwise by `prime_no_emptyK3K4`. -/
theorem no_emptyK3K4_of_taut {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : ¬ HasEmptyK3 M.support ∧ ¬ HasEmptyK4 M.support := by
  suffices H : ∀ N, ∀ (σ : Finset (Finset V)) (X M : Chain V), nrm M = N → IsSphere2 σ →
      UnitOn X σ → bdry X = 0 → bdry M = X → IsTaut M → SimplicialChain M →
      ¬ HasEmptyK3 M.support ∧ ¬ HasEmptyK4 M.support by
    exact H (nrm M) σ X M rfl hσ hU hXc hMX hT hS
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro σ X M hN hσ hU hXc hMX hT hS
    by_cases hv : (vertsOf σ).card ≤ 4
    · exact base_no_emptyK3K4 hσ hU hMX hT hv
    · push_neg at hv
      by_cases hd3 : HasDegree3Vertex σ
      · refine deg3_no_emptyK3K4 σ X M hσ hv hU hXc hMX hT hS hd3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'
      · have hno3 : NoDegree3Vertex σ := fun v hvv hcard => hd3 ⟨v, hvv, hcard⟩
        refine prime_no_emptyK3K4 σ X M hσ hU hXc hMX hT hS hno3 ?_
        intro σ' X' M' hlt hσ' hU' hX'c hM'X' hT' hS'
        exact IH (nrm M') (hN ▸ hlt) σ' X' M' rfl hσ' hU' hX'c hM'X' hT' hS'

/-- **Theorem 4 (the flag-complex theorem).** Any taut filling `M` of a combinatorial 2-sphere `σ` is a
flag complex: every clique of its 1-skeleton spans a simplex.  Combines `no_emptyK3K4_of_taut` (the
minimal-counterexample / edge-flip induction) with `theorem4_flag_from_no_emptyK3K4` (which adds the
`K₅` obstruction). -/
theorem theorem4_flag {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : IsFlagComplex M.support :=
  let ⟨hK3, hK4⟩ := no_emptyK3K4_of_taut hσ hU hXc hMX hT hS
  theorem4_flag_from_no_emptyK3K4 hσ hU hXc hMX hT hS hK3 hK4

/-- **Public endpoint (mathematically named): a taut filling of a combinatorial 2-sphere is a flag
complex** — every clique of its 1-skeleton spans a simplex.  Paper-independent name for `theorem4_flag`. -/
theorem taut_filling_is_flagComplex {σ : Finset (Finset V)} {X M : Chain V} (hσ : IsSphere2 σ)
    (hU : UnitOn X σ) (hXc : bdry X = 0) (hMX : bdry M = X) (hT : IsTaut M)
    (hS : SimplicialChain M) : IsFlagComplex M.support :=
  theorem4_flag hσ hU hXc hMX hT hS

end Taut
