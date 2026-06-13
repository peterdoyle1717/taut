import Taut.Complex2

/-!
# 𝔽₂ homology of a combinatorial 2-complex, and the separation theorem

The watershed of Theorem 2. A non-face triangle (a 3-cycle in the 1-skeleton
that is not a face of σ) partitions a combinatorial 2-sphere into two sides,
each capping to a sphere. The route (settled with the PI):

* the Euler–Poincaré identity χ = b₀ − b₁ + b₂ is pure linear algebra;
* `IsSphere2` already asserts χ = 2, and gives b₀ = 1 (connected) and
  b₂ = 1 (the fundamental class is unique up to scale — a 2-cycle assigns equal
  weight across every edge, hence is constant on the dual-connected complex);
* so the given χ = 2 forces **b₁ = 0**, i.e. every 1-cycle bounds.

We avoid Betti numbers and work with ranks over 𝔽₂ = `ZMod 2`:
`bd1 ∘ bd2 = 0`, `r₂ := finrank (range bd2) = F − 1` (dual connectivity),
`r₁ := finrank (range bd1) = V − 1` (skeleton connectivity), then
`finrank (ker bd1) = E − (V−1) = F − 1 = finrank (range bd2)` using χ = 2;
with `range bd2 ⊆ ker bd1`, equal finrank forces `range bd2 = ker bd1` — H₁ = 0.

Chain groups are function spaces on Finset-coerced subtypes (`finrank = card`).
Orientation is *not* present here; it is re-attached afterward via the integral
fundamental cycle when packaging the split for `IsTaut.splits`.
-/

namespace Taut

open Module Finset

variable {V : Type*} [LinearOrder V]

/-! ## Chain groups and boundary maps over 𝔽₂ -/

/-- 0-chains: 𝔽₂-functions on the vertices. -/
abbrev C0 (σ : Finset (Finset V)) := (vertsOf σ) → ZMod 2
/-- 1-chains: 𝔽₂-functions on the edges. -/
abbrev C1 (σ : Finset (Finset V)) := (edgesOf σ) → ZMod 2
/-- 2-chains: 𝔽₂-functions on the faces. -/
abbrev C2 (σ : Finset (Finset V)) := σ → ZMod 2

/-- The 2-boundary `∂₂ : C₂ → C₁`. Over 𝔽₂ (no signs): a face contributes 1 to
each of its edges. -/
noncomputable def bd2 (σ : Finset (Finset V)) : C2 σ →ₗ[ZMod 2] C1 σ :=
  LinearMap.pi fun e => ∑ f : σ,
    (if (e : Finset V) ⊆ (f : Finset V) then (1 : ZMod 2) else 0) • LinearMap.proj f

/-- The 1-boundary `∂₁ : C₁ → C₀`. An edge contributes 1 to each of its
vertices. -/
noncomputable def bd1 (σ : Finset (Finset V)) : C1 σ →ₗ[ZMod 2] C0 σ :=
  LinearMap.pi fun x => ∑ e : (edgesOf σ),
    (if (x : V) ∈ (e : Finset V) then (1 : ZMod 2) else 0) • LinearMap.proj e

lemma bd2_apply (σ : Finset (Finset V)) (w : C2 σ) (e : edgesOf σ) :
    bd2 σ w e = ∑ f : σ, (if (e : Finset V) ⊆ (f : Finset V) then 1 else 0) * w f := by
  simp only [bd2, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

lemma bd1_apply (σ : Finset (Finset V)) (u : C1 σ) (x : vertsOf σ) :
    bd1 σ u x = ∑ e : (edgesOf σ), (if (x : V) ∈ (e : Finset V) then 1 else 0) * u e := by
  simp only [bd1, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

/-- The edges of a triangle through a fixed vertex: exactly the two pairs
`{x, y}` with `y` in the other two vertices. Used for `∂∂ = 0`. -/
lemma card_edges_through_vertex {σ : Finset (Finset V)} {f : Finset V} (hf : f ∈ σ)
    (hf3 : f.card = 3) (x : V) :
    ((edgesOf σ).filter (fun e => x ∈ e ∧ e ⊆ f)).card = if x ∈ f then 2 else 0 := by
  classical
  -- the filter over edgesOf is the filter of card-2 subsets of `f` through `x`
  have hrw : (edgesOf σ).filter (fun e => x ∈ e ∧ e ⊆ f)
      = (f.powersetCard 2).filter (fun e => x ∈ e) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨he, hxe, hef⟩
      exact ⟨⟨hef, card_of_mem_edgesOf he⟩, hxe⟩
    · rintro ⟨⟨hef, hc⟩, hxe⟩
      exact ⟨mem_edgesOf.mpr ⟨f, hf, hef, hc⟩, hxe, hef⟩
  rw [hrw]
  by_cases hx : x ∈ f
  · simp only [hx, if_true]
    -- card-2 subsets of `f` through `x`  ↔  `f.erase x`  via  `y ↦ {x, y}`
    have himg : (f.powersetCard 2).filter (fun e => x ∈ e)
        = (f.erase x).image (fun y => {x, y}) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image,
        Finset.mem_erase]
      constructor
      · rintro ⟨⟨hef, hc⟩, hxe⟩
        have h1 : (e.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxe, hc]
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
        have hymem : y ∈ e.erase x := hy ▸ Finset.mem_singleton_self y
        have hye : y ∈ e := Finset.mem_of_mem_erase hymem
        have hyx : y ≠ x := Finset.ne_of_mem_erase hymem
        refine ⟨y, ⟨hyx, hef hye⟩, ?_⟩
        rw [← Finset.insert_erase hxe, hy]
      · rintro ⟨y, ⟨hyx, hyf⟩, rfl⟩
        refine ⟨⟨?_, Finset.card_pair (Ne.symm hyx)⟩, Finset.mem_insert_self x _⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · rw [Finset.mem_singleton] at hz; rw [hz]; exact hyf
    rw [himg]
    have hinj : Set.InjOn (fun y => ({x, y} : Finset V)) (f.erase x) := by
      intro y1 h1 y2 h2 heq
      have heq' : ({x, y1} : Finset V) = {x, y2} := heq
      have hy1 : y1 ∈ ({x, y2} : Finset V) := heq' ▸ (show y1 ∈ ({x, y1} : Finset V) by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy1
      rcases hy1 with rfl | h
      · exact absurd rfl (Finset.mem_erase.mp h1).1
      · exact h
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hx, hf3]
  · simp only [hx, if_false]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hxe
    exact hx ((Finset.mem_powersetCard.mp he).1 hxe)

/-- `∂₁ ∘ ∂₂ = 0`: over 𝔽₂ this holds because every vertex of a triangle lies
in exactly two of its edges (and a vertex outside lies in none). -/
theorem bd1_comp_bd2 (σ : Finset (Finset V)) (hpure : ∀ f ∈ σ, f.card = 3) :
    bd1 σ ∘ₗ bd2 σ = 0 := by
  classical
  refine LinearMap.ext fun w => ?_
  funext x
  show bd1 σ (bd2 σ w) x = 0
  rw [bd1_apply]
  -- expand `∂₂ w` at each edge and swap the order of summation
  have hstep : ∀ e : edgesOf σ,
      (if (x : V) ∈ (e : Finset V) then (1 : ZMod 2) else 0) * bd2 σ w e
        = ∑ f : σ, (if (x : V) ∈ (e : Finset V) ∧ (e : Finset V) ⊆ (f : Finset V)
            then (1 : ZMod 2) else 0) * w f := by
    intro e
    rw [bd2_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [← mul_assoc]
    congr 1
    by_cases h1 : (x : V) ∈ (e : Finset V) <;> by_cases h2 : (e : Finset V) ⊆ (f : Finset V) <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl (fun e _ => hstep e), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun f _ => ?_)
  rw [← Finset.sum_mul]
  have hsum0 : (∑ e : edgesOf σ, (if (x : V) ∈ (e : Finset V) ∧ (e : Finset V) ⊆ (f : Finset V)
      then (1 : ZMod 2) else 0)) = 0 := by
    rw [Finset.sum_coe_sort (edgesOf σ)
        (fun e => if (x : V) ∈ e ∧ e ⊆ (f : Finset V) then (1 : ZMod 2) else 0),
      Finset.sum_boole, card_edges_through_vertex f.2 (hpure f f.2) x]
    split <;> decide
  rw [hsum0, zero_mul]

/-- The all-faces 2-chain `𝟙` is a cycle: every edge lies in exactly two faces,
so over 𝔽₂ its boundary vanishes. This is the combinatorial fundamental class,
witnessing `b₂ ≥ 1`. -/
theorem bd2_one (σ : Finset (Finset V)) (hclosed : ∀ e ∈ edgesOf σ, edgeDeg σ e = 2) :
    bd2 σ (fun _ => 1) = 0 := by
  classical
  funext e
  show bd2 σ (fun _ => 1) e = 0
  rw [bd2_apply]
  simp only [mul_one]
  rw [Finset.sum_coe_sort σ (fun f => if (e : Finset V) ⊆ f then (1 : ZMod 2) else 0),
    Finset.sum_boole]
  have : (σ.filter (fun f => (e : Finset V) ⊆ f)).card = 2 := hclosed e e.2
  rw [this]
  decide

/-! ## `ker ∂₂` is the constants (b₂ = 1) -/

/-- In a sphere, `∂₂ w` at an edge equals the sum of `w` over the edge's two
faces. This turns the cocycle condition into "equal weight across every edge". -/
lemma bd2_at_edge {σ : Finset (Finset V)} (w : C2 σ) {e : Finset V} (he : e ∈ edgesOf σ)
    {f₁ f₂ : Finset V} (h1 : f₁ ∈ σ) (h2 : f₂ ∈ σ) (hne : f₁ ≠ f₂)
    (he1 : e ⊆ f₁) (he2 : e ⊆ f₂) (huniq : ∀ f ∈ σ, e ⊆ f → f = f₁ ∨ f = f₂) :
    bd2 σ w ⟨e, he⟩ = w ⟨f₁, h1⟩ + w ⟨f₂, h2⟩ := by
  classical
  rw [bd2_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter (fun f : σ => (e : Finset V) ⊆ (f : Finset V)))
      = {⟨f₁, h1⟩, ⟨f₂, h2⟩} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hef
      rcases huniq f f.2 hef with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact he1
      · exact he2
  rw [hfilter, Finset.sum_pair (by simp only [ne_eq, Subtype.mk.injEq]; exact hne)]

/-- The dual graph: two distinct faces are adjacent iff they share an edge. -/
def dualGraph (σ : Finset (Finset V)) : SimpleGraph σ where
  Adj f g := f ≠ g ∧ ∃ e ∈ edgesOf σ, e ⊆ (f : Finset V) ∧ e ⊆ (g : Finset V)
  symm := by
    rintro f g ⟨hne, e, he, hf, hg⟩
    exact ⟨hne.symm, e, he, hg, hf⟩
  loopless := ⟨fun f h => h.1 rfl⟩

@[simp] lemma dualGraph_adj {σ : Finset (Finset V)} {f g : σ} :
    (dualGraph σ).Adj f g ↔
      f ≠ g ∧ ∃ e ∈ edgesOf σ, e ⊆ (f : Finset V) ∧ e ⊆ (g : Finset V) := Iff.rfl

/-- A 2-cycle (element of `ker ∂₂`) assigns equal weight to dual-adjacent faces:
across their shared edge, `∂₂ w = w f + w g = 0`. -/
lemma dualGraph_ker_const {σ : Finset (Finset V)} (h : IsSphere2 σ) {w : C2 σ}
    (hw : bd2 σ w = 0) {f g : σ} (hadj : (dualGraph σ).Adj f g) : w f = w g := by
  rw [dualGraph_adj] at hadj
  obtain ⟨hne, e, he, hef, heg⟩ := hadj
  obtain ⟨f₁, h1, f₂, h2, hne12, he1, he2, huniq⟩ := exists_two_faces h he
  have hfg_ne : (f : Finset V) ≠ (g : Finset V) := fun heq => hne (Subtype.ext heq)
  -- `f` and `g` are exactly the two faces of `e`
  have huniq_fg : ∀ f' ∈ σ, e ⊆ f' → f' = (f : Finset V) ∨ f' = (g : Finset V) := by
    have hfm := huniq (f : Finset V) f.2 hef
    have hgm := huniq (g : Finset V) g.2 heg
    intro f' hf' hef'
    rcases huniq f' hf' hef' with rfl | rfl
    · rcases hfm with hh | hh
      · exact Or.inl hh.symm
      · rcases hgm with hh2 | hh2
        · exact Or.inr hh2.symm
        · exact absurd (hh.trans hh2.symm) hfg_ne
    · rcases hgm with hh | hh
      · rcases hfm with hh2 | hh2
        · exact absurd (hh2.trans hh.symm) hfg_ne
        · exact Or.inl hh2.symm
      · exact Or.inr hh.symm
  have hbd : bd2 σ w ⟨e, he⟩ = w f + w g :=
    bd2_at_edge w he f.2 g.2 hfg_ne hef heg huniq_fg
  rw [hw] at hbd
  -- 0 = w f + w g  in ZMod 2  ⟹  w f = w g
  have : w f + w g = 0 := hbd.symm
  have hwg : w g = - w f := by linear_combination this
  rw [hwg]
  exact (CharTwo.neg_eq (w f)).symm

/-! ### Dual-graph connectivity (from `conn` + `linkConn` + `closed`) -/

/-- Two faces that share an edge are dual-reachable. -/
lemma dualReach_of_common_edge {σ : Finset (Finset V)} {f g : σ} {e : Finset V}
    (he : e ∈ edgesOf σ) (hef : e ⊆ (f : Finset V)) (heg : e ⊆ (g : Finset V)) :
    (dualGraph σ).Reachable f g := by
  by_cases hfg : f = g
  · exact hfg ▸ SimpleGraph.Reachable.refl f
  · exact SimpleGraph.Adj.reachable (by rw [dualGraph_adj]; exact ⟨hfg, e, he, hef, heg⟩)

/-- Two faces meeting in the edge `{v, a}` (`a ≠ v`) are dual-reachable. -/
lemma dualReach_of_pair {σ : Finset (Finset V)} {f g : σ} {v a : V} (hav : a ≠ v)
    (hvf : v ∈ (f : Finset V)) (haf : a ∈ (f : Finset V))
    (hvg : v ∈ (g : Finset V)) (hag : a ∈ (g : Finset V)) :
    (dualGraph σ).Reachable f g := by
  have hsub : ∀ {h : σ}, v ∈ (h : Finset V) → a ∈ (h : Finset V) →
      ({v, a} : Finset V) ⊆ (h : Finset V) := by
    intro h hvh hah z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hvh
    · rw [Finset.mem_singleton] at hz; exact hz ▸ hah
  have he : ({v, a} : Finset V) ∈ edgesOf σ :=
    mem_edgesOf.mpr ⟨f, f.2, hsub hvf haf, Finset.card_pair (Ne.symm hav)⟩
  exact dualReach_of_common_edge he (hsub hvf haf) (hsub hvg hag)

/-- Faces along a link-walk at `v` are dual-reachable: induction transporting a
walk in `linkGraph σ v` to a dual path. -/
lemma linkwalk_dual {σ : Finset (Finset V)} (h : IsSphere2 σ) {v : V} :
    ∀ {a a' : V} (_ : (linkGraph σ v).Walk a a') {f f' : σ},
      v ∈ (f : Finset V) → a ∈ (f : Finset V) → a ≠ v →
      v ∈ (f' : Finset V) → a' ∈ (f' : Finset V) → a' ≠ v →
      (dualGraph σ).Reachable f f' := by
  intro a a' p
  induction p with
  | nil =>
      intro f f' hvf haf hav hvf' haf' _
      exact dualReach_of_pair hav hvf haf hvf' haf'
  | @cons a x a' hadj q ih =>
      intro f f' hvf haf hav hvf' haf' ha'v
      -- the head edge `a — x` of the link walk is the face `{v, a, x}`
      rw [linkGraph] at hadj
      obtain ⟨hax, hface⟩ := hadj
      have hmem : ({v, a, x} : Finset V) ∈ σ := hface
      have hxv : x ≠ v := by
        intro hxv
        have h3 := h.pure _ hmem
        have hle : ({v, a, x} : Finset V).card ≤ 2 := by
          have hsub : ({v, a, x} : Finset V) ⊆ {v, a} := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact Or.inl hxv
          exact le_trans (Finset.card_le_card hsub)
            (le_trans (Finset.card_insert_le _ _) (by simp))
        omega
      set hf : σ := ⟨{v, a, x}, hmem⟩ with hhf
      have hvh : v ∈ (hf : Finset V) := by rw [hhf]; exact Finset.mem_insert_self v _
      have hah : a ∈ (hf : Finset V) := by
        rw [hhf]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self a _)
      have hxh : x ∈ (hf : Finset V) := by
        rw [hhf]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self x))
      exact (dualReach_of_pair hav hvf haf hvh hah).trans
        (ih hvh hxh hxv hvf' haf' ha'v)

/-- Two faces sharing a vertex are dual-reachable (uses `linkConn`). -/
lemma dual_reach_shared_vertex {σ : Finset (Finset V)} (h : IsSphere2 σ) {f g : σ} {v : V}
    (hvf : v ∈ (f : Finset V)) (hvg : v ∈ (g : Finset V)) :
    (dualGraph σ).Reachable f g := by
  obtain ⟨a, ha⟩ : (((f : Finset V).erase v)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hvf, h.pure _ f.2]; omega
  obtain ⟨c, hc⟩ : (((g : Finset V).erase v)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hvg, h.pure _ g.2]; omega
  have hav : a ≠ v := Finset.ne_of_mem_erase ha
  have hcv : c ≠ v := Finset.ne_of_mem_erase hc
  have haf : a ∈ (f : Finset V) := Finset.mem_of_mem_erase ha
  have hcg : c ∈ (g : Finset V) := Finset.mem_of_mem_erase hc
  have hvV : v ∈ vertsOf σ := mem_vertsOf.mpr ⟨f, f.2, hvf⟩
  have haL : a ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hav, f, f.2, hvf, haf⟩
  have hcL : c ∈ linkVerts σ v := mem_linkVerts.mpr ⟨hcv, g, g.2, hvg, hcg⟩
  obtain ⟨p⟩ := h.linkConn v hvV a haL c hcL
  exact linkwalk_dual h p hvf haf hav hvg hcg hcv

/-- Faces along a skeleton walk are dual-reachable: induction transporting a
walk in `skel σ` to a dual path, jumping between vertex-stars. -/
lemma skelwalk_dual {σ : Finset (Finset V)} (h : IsSphere2 σ) :
    ∀ {u w : V} (_ : (skel σ).Walk u w) {f f' : σ},
      u ∈ (f : Finset V) → w ∈ (f' : Finset V) → (dualGraph σ).Reachable f f' := by
  intro u w p
  induction p with
  | nil =>
      intro f f' huf huf'
      exact dual_reach_shared_vertex h huf huf'
  | @cons u x w hadj q ih =>
      intro f f' huf hwf'
      rw [skel] at hadj
      obtain ⟨hux, hedge⟩ := hadj
      -- a face containing the edge `{u, x}`
      obtain ⟨hf, hhf, hsub, _⟩ := mem_edgesOf.mp hedge
      have huh : u ∈ hf := hsub (Finset.mem_insert_self u _)
      have hxh : x ∈ hf := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self x))
      exact (dual_reach_shared_vertex h huf huh).trans
        (ih (f := ⟨hf, hhf⟩) hxh hwf')

/-- **Dual connectivity.** The dual graph of a sphere is connected. -/
theorem dualGraph_preconnected {σ : Finset (Finset V)} (h : IsSphere2 σ) :
    (dualGraph σ).Preconnected := by
  intro f g
  obtain ⟨u, hu⟩ : (f : Finset V).Nonempty := by
    rw [← Finset.card_pos, h.pure _ f.2]; omega
  obtain ⟨w, hw⟩ : (g : Finset V).Nonempty := by
    rw [← Finset.card_pos, h.pure _ g.2]; omega
  have huV : u ∈ vertsOf σ := mem_vertsOf.mpr ⟨f, f.2, hu⟩
  have hwV : w ∈ vertsOf σ := mem_vertsOf.mpr ⟨g, g.2, hw⟩
  obtain ⟨p⟩ := h.conn u huV w hwV
  exact skelwalk_dual h p hu hw

/-! ### `ker ∂₂` is one-dimensional -/

/-- A function constant across every adjacency is constant on reachable vertices. -/
lemma const_of_adj_of_reachable {W α : Type*} {G : SimpleGraph W} {φ : W → α}
    (hφ : ∀ a b, G.Adj a b → φ a = φ b) {a b : W} (hab : G.Reachable a b) : φ a = φ b := by
  obtain ⟨p⟩ := hab
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hφ _ _ hadj).trans ih

/-- A sphere is nonempty (its Euler relation fails on the empty complex). -/
lemma IsSphere2.nonempty {σ : Finset (Finset V)} (h : IsSphere2 σ) : σ.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  have := h.euler
  simp [vertsOf, edgesOf] at this

/-- Every 2-cycle is constant: dual connectivity propagates the edge-local
equality. -/
lemma bd2_ker_constant {σ : Finset (Finset V)} (h : IsSphere2 σ) {w : C2 σ}
    (hw : bd2 σ w = 0) (f g : σ) : w f = w g :=
  const_of_adj_of_reachable (fun _ _ hab => dualGraph_ker_const h hw hab)
    (dualGraph_preconnected h f g)

/-- `ker ∂₂` is exactly the constants, i.e. the span of the fundamental class. -/
lemma ker_bd2_eq_span {σ : Finset (Finset V)} (h : IsSphere2 σ) :
    LinearMap.ker (bd2 σ) = Submodule.span (ZMod 2) {(fun _ => 1 : C2 σ)} := by
  obtain ⟨f₀, hf₀⟩ := h.nonempty
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    rw [Submodule.mem_span_singleton]
    refine ⟨w ⟨f₀, hf₀⟩, ?_⟩
    funext g
    show w ⟨f₀, hf₀⟩ • (1 : ZMod 2) = w g
    rw [smul_eq_mul, mul_one]
    exact bd2_ker_constant h hw ⟨f₀, hf₀⟩ g
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact bd2_one σ h.closed

/-- **b₂ = 1.** The space of 2-cycles is one-dimensional. -/
theorem finrank_ker_bd2 {σ : Finset (Finset V)} (h : IsSphere2 σ) :
    finrank (ZMod 2) (LinearMap.ker (bd2 σ)) = 1 := by
  rw [ker_bd2_eq_span h]
  apply finrank_span_singleton
  obtain ⟨f₀, hf₀⟩ := h.nonempty
  intro hcontra
  have := congrFun hcontra ⟨f₀, hf₀⟩
  simp only [Pi.zero_apply] at this
  exact one_ne_zero this

end Taut
