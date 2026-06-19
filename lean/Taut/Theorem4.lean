import Taut.Theorem3Clean

/-!
# Theorem 4 (the flag-complex theorem) — first bounded target

This file opens the formalization of Theorem 4 of "Taut fillings": a taut filling
of a triangulated `S²` is a *flag complex* — every clique in its 1-skeleton spans a
simplex.  In the combinatorial setting (no topology) the relevant notion of "flag"
is captured by `IsFlagComplex`: every set `s` whose every edge is a simplex of `τ`
is itself a simplex of `τ`.

Two pieces are proved here.

* `NoTaboo.to_flag` — **purely combinatorial.** A complex with no "taboo"
  configuration (no empty triangle `K₃`, no empty tetrahedron `K₄`, no `5`-clique
  `K₅` of edges) is a flag complex.  The proof is a case split on `s.card`; cliques of
  card `0,1,2` span simplices outright, and cards `3,4,≥5` each hit one of the three
  forbidden configurations.

* `no_k5Clique_of_no_emptyK4_taut` — **the geometric crux.** For a taut, simplicial,
  pure filling `M` of a sphere `σ`, the absence of an empty `K₄` already forbids any
  `K₅` of edges.  This replaces the paper's `S³ ⊄ B³` step: a `K₅` of edges in
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
  -- Reduce to: card ≤ 4 (else extract a 5-clique and contradict hK5).
  by_cases hge5 : 5 ≤ s.card
  · exfalso
    obtain ⟨s', hs'sub, hs'card⟩ := Finset.exists_subset_card_eq hge5
    exact hK5 ⟨s', hs'card, fun e he hec => hedges e (he.trans hs'sub) hec⟩
  have hge5 : s.card ≤ 4 := by omega
  -- Now s.card ≤ 4; split on the exact card.
  interval_cases hc : s.card
  · -- card 0
    exact Or.inl (Finset.card_eq_zero.mp hc)
  · -- card 1: s = {v}, v a vertex of τ
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    have hvmem : v ∈ vertsOf τ := hsub (hv ▸ Finset.mem_singleton_self v)
    obtain ⟨t, htτ, hvt⟩ := mem_vertsOf.mp hvmem
    exact Or.inr ⟨t, htτ, by rw [hv]; exact Finset.singleton_subset_iff.mpr hvt⟩
  · -- card 2: s itself is one of its edges
    exact hedges s (Finset.Subset.refl s) hc
  · -- card 3: an empty K₃ unless s is a simplex
    by_contra hns
    exact hK3 ⟨s, hc, hedges, hns⟩
  · -- card 4: an empty K₄ unless s is a simplex
    by_contra hns
    exact hK4 ⟨s, hc, hedges, hns⟩

/-! ## (2) The K₅ obstruction (geometric crux) -/

/-- A `card`-`4` subset of a `5`-clique whose edges are all simplices, in a pure
support, is itself a tet. -/
private lemma fourSubset_mem_support {V : Type*} [LinearOrder V]
    {M : Chain V} {s q : Finset V}
    (hPure : ∀ t ∈ M.support, t.card = 4)
    (hK4 : ¬ HasEmptyK4 M.support)
    (hedges : ∀ e, e ⊆ s → e.card = 2 → SimplexOf M.support e)
    (hqs : q ⊆ s) (hq4 : q.card = 4) : q ∈ M.support := by
  -- every edge of q is an edge of s, hence a simplex; ¬K₄ ⟹ q is a simplex
  have hqedges : ∀ e, e ⊆ q → e.card = 2 → SimplexOf M.support e :=
    fun e he hec => hedges e (he.trans hqs) hec
  have hsimp : SimplexOf M.support q := by
    by_contra hns
    exact hK4 ⟨q, hq4, hqedges, hns⟩
  rcases hsimp with hempty | ⟨t, htM, hqt⟩
  · rw [hempty] at hq4; simp at hq4
  · -- q ⊆ t, both card 4 ⟹ q = t ∈ support
    have : q = t := Finset.eq_of_subset_of_card_le hqt (by rw [hPure t htM, hq4])
    rwa [this]

/-- For a triangle `f` inside the `5`-clique `s`, the two `4`-subsets of `s` that
contain `f` (`insert a f`, `insert b f`, where `{a,b} = s \ f`) are *distinct tets of
`M.support` containing `f`*. -/
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
  -- the two 4-subsets
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

/-- **Containment of bounding tets.** For a triangle `f ⊆ s` (card 3) of the
`5`-clique `s`, every tet of `M.support` that contains `f` is `⊆ s`.  Indeed
`f` already lies in two tets `insert a f, insert b f` both `⊆ s`, and
pseudomanifoldness caps the count at two, so the two-element filter is exactly
those two tets. -/
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
  -- the two tets sit in the filter, which has card ≤ 2; so it *equals* the pair
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
  -- faceCount = 2 from the two distinct bounding tets and pseudomanifoldness
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
  -- ±1 is impossible at f; UnitOn then pins the coefficient to 0
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
  -- coefficient of U: M t when t ⊆ s, else 0
  have hUapp : ∀ t, U t = if t ⊆ s then M t else 0 := by
    intro t; rw [hUdef, Finsupp.filter_apply]
  have hUsupp : U.support ⊆ M.support := by
    rw [hUdef, Finsupp.support_filter]; exact Finset.filter_subset _ _
  ext f
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_cases hcase : f ⊆ s ∧ f.card = 3
  · obtain ⟨hfs, hf3⟩ := hcase
    -- every tet of M containing f is ⊆ s
    have hcont : ∀ t ∈ M.support, f ⊆ t → t ⊆ s :=
      tet_containing_subset hPure hPM hK4 hedges hs5 hfs hf3
    -- bdry U f and bdry M f are sums over the same facet filter, with equal coeffs
    have hsumU : bdry U f = ∑ t ∈ U.support.filter (fun t => f ⊆ t), U t * bdryGen t f :=
      bdry_eq_sum_facets
    have hsumM : bdry M f = ∑ t ∈ M.support.filter (fun t => f ⊆ t), M t * bdryGen t f :=
      bdry_eq_sum_facets
    -- the two filters coincide
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
    -- on this filter, U = M
    have hterms : ∀ t ∈ M.support.filter (fun t => f ⊆ t),
        U t * bdryGen t f = M t * bdryGen t f := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have htsub : t ⊆ s := hcont t ht.1 ht.2
      rw [hUapp, if_pos htsub]
    rw [Finset.sum_congr rfl hterms, ← hsumM]
    exact bdry_eq_zero_of_triangle hU hMX hS hPure hPM hK4 hedges hs5 hfs hf3
  · -- f not a triangle of s: the local sum is term-by-term zero
    rw [show bdry U f = ∑ t ∈ U.support.filter (fun t => f ⊆ t), U t * bdryGen t f from
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
    -- f ⊆ s but ¬(f⊆s ∧ card=3) ⟹ f.card ≠ 3 ⟹ bdryGen t f = 0
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
  -- the closed sub-chain on s
  set U := M.filter (fun t => t ⊆ s) with hUdef
  have hbU : bdry U = 0 :=
    bdry_filter_subset_eq_zero hU hMX hS hPure hPM hK4 hedges hs5
  have hsub : SubChain U M := subChain_filter _ M
  have hTU : IsTaut U := hT.subChain hsub
  -- nrm U = Zvol (bdry U) = Zvol 0 = 0
  have hZ0 : Zvol (0 : Chain V) = 0 := Nat.le_zero.mp (by
    simpa using Zvol_le (show bdry (0 : Chain V) = 0 by simp))
  have hnrmU : nrm U = 0 := by rw [IsTaut] at hTU; rw [hTU, hbU, hZ0]
  have hU0 : U = 0 := nrm_eq_zero_iff.mp hnrmU
  -- but U carries a tet of s: any 4-subset q ⊆ s is a tet, and U q = M q ≠ 0
  obtain ⟨q, hqs, hq4⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
  have hqM : q ∈ M.support := fourSubset_mem_support hPure hK4 hedges hqs hq4
  have hUq : U q = M q := by rw [hUdef, Finsupp.filter_apply, if_pos hqs]
  have hMq : M q ≠ 0 := Finsupp.mem_support_iff.mp hqM
  rw [hU0] at hUq
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hUq
  exact hMq hUq.symm

end Taut
