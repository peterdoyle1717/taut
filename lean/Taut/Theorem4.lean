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

/-- **Theorem 4, public assembly (interface lock).** Once the two taboo configurations
`HasEmptyK3` / `HasEmptyK4` are ruled out for a taut filling `M` of a 2-sphere `σ`, the support
is a flag complex.  This composes the combinatorial bridge `NoTaboo.to_flag` with the config-3
obstruction `no_k5Clique_of_no_emptyK4_taut` (which supplies `¬ HasK5Clique` from `¬ HasEmptyK4`),
deriving purity from `aleph_base_taut_support_card4_subset_verts`.  The remaining work for the full
`theorem4_flag` endpoint is exactly `no_emptyK3K4_of_taut` (the minimal-counterexample / edge-flip
induction). -/
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

In the minimal-counterexample induction (`no_emptyK3K4_of_taut`, to come) we remove a tet — a
degree-3 star or an eligible flip — and need the taboo configuration to SURVIVE in the smaller
complex.  Removing a tet only *removes* simplices, so `¬ SimplexOf` of the witness is automatic
(monotonicity); the content is that each witness EDGE keeps a witness tet other than the one removed.
This is pure `SimplexOf` bookkeeping over `M.support.erase e` (= `(removeTet M e).support`). -/

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

/-- `removeTet` form of empty-K3 persistence. -/
lemma hasEmptyK3_removeTet_of_witness {M : Chain V} {e s : Finset V} (he : e ∈ M.support)
    (hs3 : s.card = 3)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → ∃ t ∈ M.support, t ≠ e ∧ x ⊆ t)
    (hno : ¬ SimplexOf M.support s) : HasEmptyK3 (removeTet M e).support := by
  rw [support_removeTet_of_mem he]
  exact hasEmptyK3_erase_of_witness hs3 hedges hno

/-- `removeTet` form of empty-K4 persistence. -/
lemma hasEmptyK4_removeTet_of_witness {M : Chain V} {e s : Finset V} (he : e ∈ M.support)
    (hs4 : s.card = 4)
    (hedges : ∀ x, x ⊆ s → x.card = 2 → ∃ t ∈ M.support, t ≠ e ∧ x ⊆ t)
    (hno : ¬ SimplexOf M.support s) : HasEmptyK4 (removeTet M e).support := by
  rw [support_removeTet_of_mem he]
  exact hasEmptyK4_erase_of_witness hs4 hedges hno

/-! ### No-flip persistence (sub-target 3)

In the eligible-flip step of the induction we remove an eligible tet `e` whose two
*shared* (boundary) faces `g₃, g₄` get their common edge `g₃ ∩ g₄ = "ab"` deleted from the
boundary.  A witness edge `x` of a taboo configuration survives the removal provided `x` is
not exactly that deleted edge: every other edge of `e` lies in an *exposed* (interior) face,
and an exposed face is carried by a neighbouring tet `≠ e`.  These three lemmas package that
into `removeTet`-persistence of the taboo configurations, with the side condition stated as
`x ≠ g₃ ∩ g₄` (`havoid`). -/

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
  -- no exposed face contains `x`, so the (card-2) filter of tetFaces lands inside sharedFaces
  have hsubsh : (tetFaces e).filter (fun F => x ⊆ F) ⊆ sharedFaces M e := by
    intro F hF
    rw [Finset.mem_filter] at hF
    by_contra hns
    exact hcon F (Finset.mem_sdiff.mpr ⟨hF.1, hns⟩) hF.2
  have hfiltcard : ((tetFaces e).filter (fun F => x ⊆ F)).card = 2 :=
    tetFaces_edge_filter_card_eq_two he.1 hxe hx2
  have hsheq : (tetFaces e).filter (fun F => x ⊆ F) = sharedFaces M e :=
    Finset.eq_of_subset_of_card_le hsubsh (by rw [he.2.2.1, hfiltcard])
  -- so both g₃, g₄ contain `x`
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
  -- `x` is nonempty (card 2), so it has an honest witness tet `t₀`
  have hxne0 : x ≠ ∅ := by
    intro h; rw [h, Finset.card_empty] at hx2; exact absurd hx2 (by decide)
  obtain ⟨t₀, ht₀, hxt₀⟩ := hx.resolve_left hxne0
  by_cases hxe : x ⊆ e
  · -- `x ⊆ e`: route through an exposed face
    obtain ⟨f, hf, hxf⟩ := edge_in_exposed_of_ne_sharedInter he hsh hg hx2 hxe hxne
    -- `f` is a tet-face of `e` off the boundary: `bdry M f = 0`
    have hftet : f ∈ tetFaces e := exposedFaces_subset_tetFaces M e hf
    have hf3 : f.card = 3 := (Finset.mem_powersetCard.mp hftet).2
    have hfnsh : f ∉ sharedFaces M e := (Finset.mem_sdiff.mp hf).2
    have hfnb : f ∉ (bdry M).support := fun hb =>
      hfnsh (by rw [sharedFaces]; exact Finset.mem_inter.mpr ⟨hftet, hb⟩)
    have hbf0 : bdry M f = 0 := Finsupp.notMem_support_iff.mp hfnb
    -- the `e`-term of `bdry M f = ∑_{t ⊇ f} M t · bdryGen t f` is nonzero
    have hfsube : f ⊆ e := (Finset.mem_powersetCard.mp hftet).1
    have heF : e ∈ M.support.filter (fun t => f ⊆ t) :=
      Finset.mem_filter.mpr ⟨he.2.1, hfsube⟩
    have hMe : M e ≠ 0 := Finsupp.mem_support_iff.mp he.2.1
    have hgene : bdryGen e f ≠ 0 := bdryGen_ne_zero_of_subset he.1 hf3 hfsube
    have htermE : M e * bdryGen e f ≠ 0 := mul_ne_zero hMe hgene
    -- the sum is zero, so some other facet-tet contributes a nonzero term
    have hsum0 : (∑ t ∈ M.support.filter (fun t => f ⊆ t), M t * bdryGen t f) = 0 := by
      rw [← bdry_eq_sum_facets]; exact hbf0
    have hexists : ∃ t ∈ M.support.filter (fun t => f ⊆ t),
        t ≠ e ∧ M t * bdryGen t f ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      -- every facet-tet other than `e` contributes zero, so the sum equals the `e`-term ≠ 0
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
  · -- `¬ x ⊆ e`: the honest witness `t₀` cannot be `e`
    refine ⟨t₀, ht₀, ?_, hxt₀⟩
    intro hte
    exact hxe (hte ▸ hxt₀)

/-- Empty-K3 persists past an eligible flip whose deleted diagonal `g₃ ∩ g₄` is avoided by all
edges of the witness triangle. -/
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

/-- Empty-K4 persists past an eligible flip whose deleted diagonal `g₃ ∩ g₄` is avoided by all
edges of the witness `K4`. -/
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

/-! ### Side localization of empty configurations (sub-target 4)

In the eligible-flip / edge-split step of the minimal-counterexample induction the support `τ`
of a taboo configuration sits across a separating edge `A ∩ B` (card 2): every tet lies in `A`
or in `B`, the two sides are "bridged" by tets that cap the seam edge, and we must localize a
whole empty `K₃`/`K₄` witness to a single side's filter.  The geometric content is:

* a card-`≥ 2` witness whose every edge is a simplex lies entirely in one side (`witness_subset_side`);
* once on side `P`, each of its edges transfers to the side filter `τ ↾ {t | t ⊆ P}`, seam edges
  via the bridging tet (`edge_simplexOf_filter_of_subset`); and
* `¬ SimplexOf` of the witness is monotone, so it survives the (smaller) side filter. -/

/-- **A clique witness localizes to one side of a separating edge.** If every tet of `τ` lies in
`A` or `B`, and every `2`-subset of `s` (card `≥ 2`) is a simplex of `τ`, then `s ⊆ A` or `s ⊆ B`.
Each vertex of `s` lands in `A ∪ B` (an incident edge, being a simplex, sits in a side tet); a
vertex outside `A` and one outside `B` would force the edge between them into a side tet, putting
that vertex on the wrong side. -/
private lemma witness_subset_side {τ : Finset (Finset V)} {A B s : Finset V}
    (hcover : ∀ t ∈ τ, t ⊆ A ∨ t ⊆ B) (hs2 : 2 ≤ s.card)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf τ x) : s ⊆ A ∨ s ⊆ B := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnA, hnB⟩ := hcon
  obtain ⟨a, has, hanA⟩ := Finset.not_subset.mp hnA
  obtain ⟨b, hbs, hbnB⟩ := Finset.not_subset.mp hnB
  -- every vertex of `s` lands in `A ∪ B`
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
  -- so `a ∈ B`, `b ∈ A`, and `a ≠ b`
  have haB : a ∈ B := (hvAB a has).resolve_left hanA
  have hbA : b ∈ A := (hvAB b hbs).resolve_right hbnB
  have hab : a ≠ b := by intro h; exact hanA (h ▸ hbA)
  -- the edge `{a, b}` lands in a side tet, putting `a` in `A` or `b` in `B`
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
A witness tet `t ⊇ x` either already lies in `P` (done), or lies in the other side `Q`; then `x`
sits in `P ∩ Q`, has the same card `2`, hence equals `P ∩ Q`, so the bridging tet of `P`
(containing `P ∩ Q`) carries it. -/
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
  · -- `x ⊆ P ∩ Q`, card-matched, so `x = P ∩ Q`; the bridge tet carries it
    have hxPQ : x ⊆ P ∩ Q := Finset.subset_inter (hxs.trans hsP) (hxt.trans htQ)
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
Since the families' shared-face sets are pairwise disjoint, each face `p` (resp. `q`) lies in the
`sharedFaces` of at most one member; so at most two members hit `{p,q}`.  (This is the config-2
counting input: `≤ 2` eligible tets can carry a forbidden interior face `ABC`/`BCD`.) -/
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
of faces containing a vertex `v` equals the number of vertices of its link.  (For a closed
surface each link is a cycle, so faces-at-`v` = link-vertices = link-edges; this is the
counting form.)  Proved by double-counting the incidence between faces at `v` and link
vertices: each face at `v` meets the link in exactly `2` vertices (its two non-`v`
corners), and each link vertex `x` lies on exactly `2` faces at `v` (the edge `{v,x}` is
in exactly two faces, by closedness). -/
lemma incident_faces_card_eq_linkVerts_card {σ : Finset (Finset V)} (hσ : IsSphere2 σ)
    {v : V} (_hv : v ∈ vertsOf σ) :
    (σ.filter (fun f => v ∈ f)).card = (linkVerts σ v).card := by
  classical
  set A := σ.filter (fun f => v ∈ f) with hA
  set B := linkVerts σ v with hB
  -- Claim1: each face at `v` meets the link in exactly two vertices.
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
  -- Claim2: each link vertex lies on exactly two faces at `v`.
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
  -- Double count: swap the order of summation.
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

/-- **Vertex–face incidence double count: `∑_v (#faces at v) = 3f`.**  Summing the number
of faces containing each vertex equals `3` times the face count, since every face is a
triangle (`hσ.pure`) and so is counted once for each of its three vertices. -/
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
  -- every link size is exactly 4
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
most one of them can have its flip-edge `g₃ ∩ g₄` equal to a fixed edge `ab`.  Each such
tet contributes the *two* distinct faces `g₃, g₄ ⊇ ab` to `σ`, and the disjointness of
shared-face sets makes all those faces distinct across tets; if two tets shared the same
`ab`, the edge `ab` would lie in ≥ 4 faces of `σ`, contradicting `edgeDeg σ ab = 2`. -/
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
  -- Unpack the two filter memberships.
  rw [Finset.mem_filter] at he₁ he₂
  obtain ⟨he₁E, g₃, g₄, hsh₁, hne₁, hab₁⟩ := he₁
  obtain ⟨he₂E, h₃, h₄, hsh₂, hne₂, hab₂⟩ := he₂
  -- Each face is a shared face of its tet.
  have hg₃sh : g₃ ∈ sharedFaces M e₁ := by rw [hsh₁]; exact Finset.mem_insert_self _ _
  have hg₄sh : g₄ ∈ sharedFaces M e₁ := by
    rw [hsh₁]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hh₃sh : h₃ ∈ sharedFaces M e₂ := by rw [hsh₂]; exact Finset.mem_insert_self _ _
  have hh₄sh : h₄ ∈ sharedFaces M e₂ := by
    rw [hsh₂]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  -- Each shared face is a tet face of its tet.
  have hg₃tet : g₃ ∈ tetFaces e₁ := sharedFaces_subset_tetFaces M e₁ hg₃sh
  have hg₄tet : g₄ ∈ tetFaces e₁ := sharedFaces_subset_tetFaces M e₁ hg₄sh
  -- `ab.card = 2` from the tet-pair intersection formula.
  have he₁card : e₁.card = 4 := (helig e₁ he₁E).1
  have habcard : ab.card = 2 := by
    rw [hab₁]; exact tetFaces_pair_inter_card_eq_two he₁card hg₃tet hg₄tet hne₁
  -- `ab` sits inside all four faces.
  have hab_g₃ : ab ⊆ g₃ := hab₁ ▸ Finset.inter_subset_left
  have hab_g₄ : ab ⊆ g₄ := hab₁ ▸ Finset.inter_subset_right
  have hab_h₃ : ab ⊆ h₃ := hab₂ ▸ Finset.inter_subset_left
  have hab_h₄ : ab ⊆ h₄ := hab₂ ▸ Finset.inter_subset_right
  -- Each shared face is in σ (via `bdry M`'s support = σ).
  have hmemσ : ∀ {g : Finset V}, g ∈ sharedFaces M e₁ ∨ g ∈ sharedFaces M e₂ → g ∈ σ := by
    intro g hg
    rcases hg with hg | hg
    · have := (Finset.mem_inter.mp hg).2; rwa [hU.1] at this
    · have := (Finset.mem_inter.mp hg).2; rwa [hU.1] at this
  have hg₃σ : g₃ ∈ σ := hmemσ (Or.inl hg₃sh)
  have hg₄σ : g₄ ∈ σ := hmemσ (Or.inl hg₄sh)
  have hh₃σ : h₃ ∈ σ := hmemσ (Or.inr hh₃sh)
  have hh₄σ : h₄ ∈ σ := hmemσ (Or.inr hh₄sh)
  -- The shared-face sets of `e₁, e₂` are disjoint.
  have hdisj : Disjoint (sharedFaces M e₁) (sharedFaces M e₂) :=
    hpair (Finset.mem_coe.mpr he₁E) (Finset.mem_coe.mpr he₂E) hne
  rw [Finset.disjoint_left] at hdisj
  -- Cross-distinctness between the two pairs.
  have hg₃h₃ : g₃ ≠ h₃ := fun h => hdisj hg₃sh (h ▸ hh₃sh)
  have hg₃h₄ : g₃ ≠ h₄ := fun h => hdisj hg₃sh (h ▸ hh₄sh)
  have hg₄h₃ : g₄ ≠ h₃ := fun h => hdisj hg₄sh (h ▸ hh₃sh)
  have hg₄h₄ : g₄ ≠ h₄ := fun h => hdisj hg₄sh (h ▸ hh₄sh)
  -- `ab ∈ edgesOf σ`, hence `edgeDeg σ ab = 2`.
  have habedge : ab ∈ edgesOf σ := mem_edgesOf.mpr ⟨g₃, hg₃σ, hab_g₃, habcard⟩
  have habdeg : (σ.filter (fun f => ab ⊆ f)).card = 2 := hσ.closed ab habedge
  -- The four faces form a 4-element subset of the filter; contradiction with card 2.
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
  -- The bad tets: those whose flip edge is a 2-subset of `s`.
  set badE := E.filter (fun e =>
    ∃ g₃ g₄, sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧ g₃ ∩ g₄ ∈ s.powersetCard 2)
    with hbadE
  -- `badE ⊆ ⋃_{ab ∈ powersetCard 2 s} (E.filter "flip edge = ab")`.
  have hbadsub : badE ⊆ (s.powersetCard 2).biUnion (fun ab =>
      E.filter (fun e => ∃ g₃ g₄, sharedFaces M e = {g₃, g₄} ∧ g₃ ≠ g₄ ∧ ab = g₃ ∩ g₄)) := by
    intro e he
    rw [hbadE, Finset.mem_filter] at he
    obtain ⟨heE, g₃, g₄, hsh, hne, hmem⟩ := he
    rw [Finset.mem_biUnion]
    exact ⟨g₃ ∩ g₄, hmem, Finset.mem_filter.mpr ⟨heE, g₃, g₄, hsh, hne, rfl⟩⟩
  -- Hence `badE.card ≤ 3`.
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
  -- Some eligible tet escapes `badE`.
  have hbadsubE : badE ⊆ E := by rw [hbadE]; exact Finset.filter_subset _ _
  have hne : (E \ badE).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hbadsubE, hEcard]
    omega
  obtain ⟨e, he⟩ := hne
  rw [Finset.mem_sdiff] at he
  obtain ⟨heE, hebad⟩ := he
  -- `e` is eligible with exactly two shared faces.
  have helig : EligibleTet M e := hElig e heE
  have hshcard : (sharedFaces M e).card = 2 := helig.2.2.1
  obtain ⟨g₃, g₄, hg, hsh⟩ := Finset.card_eq_two.mp hshcard
  -- The flip edge avoids every edge of `s`.
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

/-! ### Theorem 4 config-2 (K₄) corrected persistence route

Under `¬ HasEmptyK3`, removing ANY eligible tet `e` preserves an empty `K₄`.  The insight: a
`K₄` edge `x ⊆ e` that is the deleted diagonal still survives, because some `K₄` FACE through it
is a simplex (`emptyK4_face_simplex_of_no_emptyK3`) living in a tet `≠ e` (the face is `¬ ⊆ e`,
since `s ⊄ e`).  No counting / octahedron / 5-family is needed — only the diagonal edge needs the
face argument; every other edge already has a witness `≠ e` from
`edge_witness_ne_removed_of_not_sharedEdge`. -/

/-- **A `K₄` face through an edge `x ⊆ e` that escapes `e`.**  Since `s ⊄ e` (else `s` is a
simplex), some `v ∈ s \ e`; then `f := insert v x` is a card-`3` subset of `s` containing `x`
with `f ⊄ e` (as `v ∈ f`, `v ∉ e`). -/
lemma exists_k4_face_through_edge_not_subset_tet {τ : Finset (Finset V)} {e s x : Finset V}
    (hs4 : s.card = 4) (hno : ¬ SimplexOf τ s) (he : e ∈ τ)
    (hx : x ⊆ s) (hx2 : x.card = 2) (hxe : x ⊆ e) :
    ∃ f, f ⊆ s ∧ f.card = 3 ∧ x ⊆ f ∧ ¬ f ⊆ e := by
  -- `s ⊄ e`, else `s` is a simplex via `e`
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

/-- **A `K₄` edge `x ⊆ e` keeps a witness `≠ e` (no empty `K₃` case).**  Take a `K₄` face `f`
through `x` escaping `e`; under `¬ HasEmptyK3` it is a simplex of `M.support`, so `f ⊆ t` for some
tet `t`.  Then `t ≠ e` (else `f ⊆ e`) and `x ⊆ f ⊆ t`. -/
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
  · -- `x` is the flip edge: it lies `⊆ e`, so use the `K₄`-face route
    have hg₃sh : g₃ ∈ sharedFaces M e := by rw [hsh]; exact Finset.mem_insert_self _ _
    have hg₃e : g₃ ⊆ e :=
      (Finset.mem_powersetCard.mp (sharedFaces_subset_tetFaces M e hg₃sh)).1
    have hxe : x ⊆ e := hxflip ▸ Finset.inter_subset_left.trans hg₃e
    exact k4_edge_has_witness_ne_removed_of_no_emptyK3 hNoK3 hs4 hsedges hno he.2.1 hxs hx2 hxe
  · exact edge_witness_ne_removed_of_not_sharedEdge he hsh hg hxsimp hx2 hxflip

/-- **Empty-`K₄` persists past removing ANY eligible tet, under `¬ HasEmptyK3`.**  Assembles the
edge-witness lemma into `removeTet`-persistence; the witness card-`4` `s` survives because each of
its edges keeps a witness tet `≠ e`. -/
lemma hasEmptyK4_removeTet_of_eligible {M : Chain V} {e s : Finset V}
    (hNoK3 : ¬ HasEmptyK3 M.support) (hs4 : s.card = 4)
    (hsedges : ∀ x, x ⊆ s → x.card = 2 → SimplexOf M.support x)
    (hno : ¬ SimplexOf M.support s) (he : EligibleTet M e) :
    HasEmptyK4 (removeTet M e).support :=
  hasEmptyK4_removeTet_of_witness he.2.1 hs4
    (emptyK4_edge_witness_ne_removed_of_eligible hNoK3 hs4 hsedges hno he) hno

end Taut
