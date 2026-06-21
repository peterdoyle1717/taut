import Taut.Projection

/-!
# Theorem 1 of "Taut fillings": additivity of Zvol

Setting: `A B : Finset V`, `p q ∈ A ∩ B` distinct, `(A ∩ B).card ≤ n+1`;
`X` a closed chain of pure dimension `n` (card `n+1`) supported in `A`,
`Y` likewise in `B`, with `n ≥ 1`.

This file proves `Zvol (X + Y) = Zvol X + Zvol Y`
(`Zvol_add_of_almost_disjoint`).  The splitting statement for `n ≥ 2`
is `Taut/Splitting.lean`.

The hypothesis `p ≠ q ∈ A ∩ B` corresponds to the paper's situation
`|A ∩ B| ≥ 2` (all geometric applications: connected sums share `n+1`
vertices, edge-unions share 2).  The disjoint-union case `|A ∩ B| ≤ 1`
of the paper's Theorem 1 is not yet formalized; it is a separate, easier
argument.

Key pieces:
* `Kkills_or_Kkills` — every `(n+2)`-simplex in `A ∪ B` is killed by
  `K_{A,p}` or by `K_{B,q}` (the paper's types analysis, in general
  dimension);
* `Kmap_eq_self` / `Kmap_eq_zero_of_closed` — `K_{A,p}` is the identity
  on `A`-chains and annihilates closed pure `B`-chains (the recovery
  argument, via small-support triviality);
* `IsTaut.dim_pure` — a taut chain with pure-dimensional boundary is
  pure-dimensional (so optimal fillings are honest `(n+1)`-chains);
* `IsTaut.vert_subset` — a taut filling has no vertices beyond its
  boundary's.
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

/-! ## Vertex bookkeeping -/

lemma vert_add_subset (M N : Chain V) : vert (M + N) ⊆ vert M ∪ vert N := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_vert.mp hx
  have := Finsupp.support_add hs
  rw [Finset.mem_union] at this ⊢
  rcases this with h | h
  · exact Or.inl (mem_vert.mpr ⟨s, h, hxs⟩)
  · exact Or.inr (mem_vert.mpr ⟨s, h, hxs⟩)

lemma vert_subset_of_supp {M : Chain V} {W : Finset V}
    (h : ∀ s ∈ M.support, s ⊆ W) : vert M ⊆ W := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_vert.mp hx
  exact h s hs hxs

lemma supp_subset_vert {M : Chain V} {t : Finset V} (ht : t ∈ M.support) :
    t ⊆ vert M := fun x hx => mem_vert.mpr ⟨t, ht, hx⟩

/-! ## Dimension parts and purity of taut chains -/

/-- The part of a chain in simplices of size `k`. -/
noncomputable def dimPart (k : ℕ) (M : Chain V) : Chain V :=
  M.filter (fun s => s.card = k)

lemma dimPart_apply (k : ℕ) (M : Chain V) (s : Finset V) :
    dimPart k M s = if s.card = k then M s else 0 := by
  simp [dimPart, Finsupp.filter_apply]

lemma dimPart_add (k : ℕ) (M N : Chain V) :
    dimPart k (M + N) = dimPart k M + dimPart k N := by
  ext s
  simp only [dimPart_apply, Finsupp.add_apply]
  split <;> simp

@[simp] lemma dimPart_zero (k : ℕ) : dimPart k (0 : Chain V) = 0 := by
  rw [dimPart, Finsupp.filter_zero]

lemma dimPart_single_of_eq {k : ℕ} {s : Finset V} (h : s.card = k) (c : ℤ) :
    dimPart k (Finsupp.single s c) = Finsupp.single s c :=
  Finsupp.filter_single_of_pos (p := fun u : Finset V => u.card = k) h

lemma dimPart_single_of_ne {k : ℕ} {s : Finset V} (h : ¬ s.card = k) (c : ℤ) :
    dimPart k (Finsupp.single s c) = 0 :=
  Finsupp.filter_single_of_neg (p := fun u : Finset V => u.card = k) h

lemma dimPart_eq_self {k : ℕ} {M : Chain V}
    (h : ∀ s ∈ M.support, s.card = k) : dimPart k M = M := by
  ext s
  rw [dimPart_apply]
  split
  · rfl
  · rename_i hs
    by_contra hMs
    exact hs (h s (Finsupp.mem_support_iff.mpr (fun h0 => hMs h0.symm)))

/-- The boundary respects the grading by dimension. -/
theorem dimPart_bdry (k : ℕ) (M : Chain V) :
    dimPart k (bdry M) = bdry (dimPart (k + 1) M) := by
  induction M using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, dimPart_add, hf, hg, dimPart_add, map_add]
  | single s c =>
    by_cases hs : s.card = k + 1
    · rw [dimPart_single_of_eq hs, bdry_single]
      -- all facets have size k, so the filter keeps everything
      ext u
      rw [dimPart_apply]
      split
      · rfl
      · rename_i hu
        rw [Finsupp.smul_apply]
        have hgen : bdryGen s u = 0 := by
          rw [bdryGen, Finset.sum_apply']
          refine Finset.sum_eq_zero fun z hz => ?_
          rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
          intro h
          apply hu
          rw [← h, Finset.card_erase_of_mem hz, hs]
          omega
        rw [hgen, smul_zero]
    · rw [dimPart_single_of_ne hs, map_zero, bdry_single]
      -- no facet has size k
      ext u
      rw [dimPart_apply, Finsupp.coe_zero, Pi.zero_apply]
      split
      · rename_i hu
        rw [Finsupp.smul_apply]
        have hgen : bdryGen s u = 0 := by
          rw [bdryGen, Finset.sum_apply']
          refine Finset.sum_eq_zero fun z hz => ?_
          rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
          intro h
          apply hs
          have hcard := Finset.card_erase_of_mem hz
          rw [h, hu] at hcard
          have hpos : 0 < s.card := Finset.card_pos.mpr ⟨z, hz⟩
          omega
        rw [hgen, smul_zero]
      · rfl

/-- A taut chain whose boundary is pure of dimension `k` is itself pure of
dimension `k+1`: optimal fillings carry no junk. -/
theorem IsTaut.dim_pure {M : Chain V} (hM : IsTaut M) {k : ℕ}
    (hbd : ∀ s ∈ (bdry M).support, s.card = k) :
    ∀ s ∈ M.support, s.card = k + 1 := by
  set P := dimPart (k + 1) M with hP
  have hPM : SubChain P M := subChain_filter _ M
  have hbdP : bdry P = bdry M := by
    rw [hP, ← dimPart_bdry, dimPart_eq_self hbd]
  have h1 : Zvol (bdry M) ≤ nrm P := Zvol_le hbdP
  have h2 := hPM.nrm_add_nrm_sub
  rw [IsTaut] at hM
  have h0 : nrm (M - P) = 0 := by omega
  have hMP : M = P := sub_eq_zero.mp (nrm_eq_zero_iff.mp h0)
  intro s hs
  rw [hMP, hP] at hs
  rw [dimPart, Finsupp.support_filter, Finset.mem_filter] at hs
  exact hs.2

/-- A taut chain in dimensions ≥ 1 has all its vertices on its boundary. -/
theorem IsTaut.vert_subset {M : Chain V} (hM : IsTaut M)
    (hdim : ∀ s ∈ M.support, 2 ≤ s.card) :
    vert M ⊆ vert (bdry M) := by
  intro x hx
  by_contra hxB
  exact hM.no_internal_vertex hdim hx hxB

/-! ## K on supported chains, and recovery -/

/-- `K_{A,p}` is the identity on chains supported in `A`. -/
lemma Kmap_eq_self {A : Finset V} {p : V} {M : Chain V}
    (h : ∀ s ∈ M.support, s ⊆ A) : Kmap A p M = M := by
  rw [Kmap_eq_sum]
  conv_rhs => rw [← Finsupp.sum_single M, Finsupp.sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [KGen_of_subset (h s hs), Finsupp.smul_single, smul_eq_mul, mul_one]

lemma inter_eq_erase_of_sdiff_singleton {A s : Finset V} {z : V}
    (hz : s \ A = {z}) : s ∩ A = s.erase z := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨hys, hyA⟩
    refine ⟨fun h => ?_, hys⟩
    have : y ∈ s \ A := hz ▸ (h ▸ Finset.mem_singleton_self z)
    exact (Finset.mem_sdiff.mp this).2 hyA
  · rintro ⟨hyz, hys⟩
    refine ⟨hys, ?_⟩
    by_contra hyA
    have : y ∈ s \ A := Finset.mem_sdiff.mpr ⟨hys, hyA⟩
    rw [hz, Finset.mem_singleton] at this
    exact hyz this

/-- Where the projection of a generator lives: inside `(s ∩ A) ∪ {p}`,
in the same dimension. -/
lemma KGen_support {A : Finset V} {p : V} {s t : Finset V}
    (ht : t ∈ (KGen A p s).support) :
    t ⊆ (s ∩ A) ∪ {p} ∧ t.card = s.card := by
  rw [KGen] at ht
  split at ht
  · rename_i hsub
    rw [Finsupp.support_single_ne_zero _ one_ne_zero,
      Finset.mem_singleton] at ht
    subst ht
    exact ⟨fun x hx => Finset.mem_union_left _
      (Finset.mem_inter.mpr ⟨hx, hsub hx⟩), rfl⟩
  · split at ht
    · rename_i hcond
      obtain ⟨hcard, hps⟩ := hcond
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
      rw [hz, Finset.sum_singleton] at ht
      obtain ⟨hzs, hzA⟩ := mem_of_sdiff_singleton hz
      have hpz : p ∉ s.erase z := fun h => hps (Finset.mem_of_mem_erase h)
      rw [coneGen, if_neg hpz, smul_smul,
        Finsupp.support_smul_eq
          (mul_ne_zero (sgn_ne_zero _ _) (sgn_ne_zero _ _)),
        Finsupp.support_single_ne_zero _ one_ne_zero,
        Finset.mem_singleton] at ht
      subst ht
      constructor
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · exact Finset.mem_union_left _
            (inter_eq_erase_of_sdiff_singleton hz ▸ hx)
      · rw [Finset.card_insert_of_notMem hpz,
          Finset.card_erase_of_mem hzs]
        have : 0 < s.card := Finset.card_pos.mpr ⟨z, hzs⟩
        omega
    · simp at ht

/-- The recovery argument: `K_{A,p}` annihilates a closed pure chain on
`B`, because its image lives on `A ∩ B` (plus `p ∈ A ∩ B`), where chains
of that dimension are trivial. -/
theorem Kmap_eq_zero_of_closed {A B : Finset V} {p : V} {n : ℕ} (hn : 1 ≤ n)
    (hp : p ∈ A ∩ B) (hC : (A ∩ B).card ≤ n + 1) {Y : Chain V}
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1) (hYc : bdry Y = 0) :
    Kmap A p Y = 0 := by
  have hsupp : ∀ t ∈ (Kmap A p Y).support, t ⊆ A ∩ B ∧ t.card = n + 1 := by
    intro t ht
    rw [Kmap_eq_sum] at ht
    obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum ht)
    have hts' : t ∈ (KGen A p s).support :=
      Finsupp.support_smul hts
    obtain ⟨hsub, hcard⟩ := KGen_support hts'
    obtain ⟨hsB, hsn⟩ := hY s hs
    constructor
    · intro x hx
      rcases Finset.mem_union.mp (hsub hx) with h | h
      · obtain ⟨hxs, hxA⟩ := Finset.mem_inter.mp h
        exact Finset.mem_inter.mpr ⟨hxA, hsB hxs⟩
      · rw [Finset.mem_singleton] at h
        exact h ▸ hp
    · rw [hcard, hsn]
  rcases Nat.lt_or_ge (A ∩ B).card (n + 1) with hlt | hge
  · exact eq_zero_of_supp_card_lt hsupp hlt
  · have hcard : (A ∩ B).card = n + 1 := le_antisymm hC hge
    have hNc : bdry (Kmap A p Y) = 0 := by
      rw [bdry_Kmap A (Finset.mem_inter.mp hp).1, hYc, map_zero]
    exact eq_zero_of_closed_supp_card_eq (by omega) hsupp hcard hNc

/-! ## The kill lemma (the types analysis, in general dimension) -/

/-- Every `(n+2)`-simplex with vertices in `A ∪ B` is killed by `K_{A,p}`
or by `K_{B,q}`, provided `p ≠ q` lie in `A ∩ B` and
`(A ∩ B).card ≤ n+1`. -/
theorem Kkills_or_Kkills {A B : Finset V} {p q : V} {n : ℕ}
    (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q)
    (hC : (A ∩ B).card ≤ n + 1) {t : Finset V}
    (htAB : t ⊆ A ∪ B) (htcard : t.card = n + 2) :
    Kkills A p t ∨ Kkills B q t := by
  by_contra h
  obtain ⟨hA, hB⟩ := not_or.mp h
  rw [Kkills, not_and_or, not_not, not_not] at hA hB
  -- the three-part count: t = (t ∩ (A∩B)) ⊎ (t \ A) ⊎ (t \ B)
  have hdisj : Disjoint (t \ A) (t \ B) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rcases Finset.mem_union.mp (htAB (Finset.mem_sdiff.mp hxA).1) with h | h
    · exact (Finset.mem_sdiff.mp hxA).2 h
    · exact (Finset.mem_sdiff.mp hxB).2 h
  have hsplit : t \ (A ∩ B) = (t \ A) ∪ (t \ B) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    tauto
  have hpart : (t ∩ (A ∩ B)).card + ((t \ A).card + (t \ B).card) = n + 2 := by
    have h1 := Finset.card_inter_add_card_sdiff t (A ∩ B)
    rw [hsplit, Finset.card_union_of_disjoint hdisj] at h1
    omega
  -- the inner part sits inside A ∩ B
  have hinter : t ∩ (A ∩ B) ⊆ A ∩ B := Finset.inter_subset_right
  have hintercard := Finset.card_le_card hinter
  rcases hA with hA | ⟨hxa, hpt⟩ <;> rcases hB with hB | ⟨hxb, hqt⟩
  · -- t ⊆ A and t ⊆ B
    have : t ⊆ A ∩ B := Finset.subset_inter hA hB
    have := Finset.card_le_card this
    omega
  · -- t ⊆ A, one vertex outside B, q ∉ t
    have hxa0 : (t \ A).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.sdiff_eq_empty_iff_subset.mpr hA)
    have hc : (t ∩ (A ∩ B)).card = n + 1 := by omega
    have heq : t ∩ (A ∩ B) = A ∩ B :=
      Finset.eq_of_subset_of_card_le hinter (by omega)
    exact hqt (Finset.mem_inter.mp (heq ▸ hq)).1
  · -- symmetric: t ⊆ B, one vertex outside A, p ∉ t
    have hxb0 : (t \ B).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.sdiff_eq_empty_iff_subset.mpr hB)
    have hc : (t ∩ (A ∩ B)).card = n + 1 := by omega
    have heq : t ∩ (A ∩ B) = A ∩ B :=
      Finset.eq_of_subset_of_card_le hinter (by omega)
    exact hpt (Finset.mem_inter.mp (heq ▸ hp)).1
  · -- one vertex outside each, p, q ∉ t: A ∩ B is too big
    have hc : (t ∩ (A ∩ B)).card = n := by omega
    have hqn : q ∉ t ∩ (A ∩ B) := fun h => hqt (Finset.mem_inter.mp h).1
    have hpn : p ∉ insert q (t ∩ (A ∩ B)) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hpq h
      · exact hpt (Finset.mem_inter.mp h).1
    have hsub : insert p (insert q (t ∩ (A ∩ B))) ⊆ A ∩ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hq
        · exact hinter hx
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hpn,
      Finset.card_insert_of_notMem hqn] at this
    omega

/-! ## Theorem 1, part 1: additivity of Zvol -/

lemma exists_fill_eq_Zvol {X : Chain V} (W : Chain V) (hW : bdry W = X) :
    ∃ M : Chain V, bdry M = X ∧ nrm M = Zvol X := by
  obtain ⟨M, h1, h2⟩ :=
    Nat.sInf_mem (⟨nrm W, W, hW, rfl⟩ :
      {m | ∃ M : Chain V, bdry M = X ∧ nrm M = m}.Nonempty)
  exact ⟨M, h1, h2⟩

/-- The mass of `M` is at most the mass killed by `K_{A,p}` plus the mass
killed by `K_{B,q}`, when every generator is killed on at least one side. -/
lemma nrm_le_killed_add_killed {A B : Finset V} {p q : V} {M : Chain V}
    (hkill : ∀ t ∈ M.support, Kkills A p t ∨ Kkills B q t) :
    nrm M ≤ nrm (M.filter (Kkills A p)) + nrm (M.filter (Kkills B q)) := by
  classical
  have hsubA : (M.filter (Kkills A p)).support ⊆ M.support := by
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
  have hsubB : (M.filter (Kkills B q)).support ⊆ M.support := by
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
  rw [nrm_eq_sum_subset hsubA, nrm_eq_sum_subset hsubB,
    ← Finset.sum_add_distrib, nrm]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  rcases hkill s hs with h | h
  · rw [if_pos h]
    omega
  · rw [if_pos h]
    split <;> omega

/-- **Theorem 1, additivity** (Ellison): for an almost disjoint union
`X + Y` — `X` a closed pure `n`-chain on `A`, `Y` on `B`, with
`(A ∩ B).card ≤ n + 1` witnessed by two distinct shared vertices
`p ≠ q ∈ A ∩ B` — the filling volume adds:
`Zvol (X + Y) = Zvol X + Zvol Y`. -/
theorem Zvol_add_of_almost_disjoint {A B : Finset V} {p q : V} {n : ℕ}
    (hn : 1 ≤ n) (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q)
    (hC : (A ∩ B).card ≤ n + 1)
    {X Y : Chain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : bdry X = 0) (hYc : bdry Y = 0) :
    Zvol (X + Y) = Zvol X + Zvol Y := by
  have hpA : p ∈ A := (Finset.mem_inter.mp hp).1
  have hqB : q ∈ B := (Finset.mem_inter.mp hq).2
  have hXYc : bdry (X + Y) = 0 := by rw [map_add, hXc, hYc, add_zero]
  obtain ⟨Mx, hMx, hMxn⟩ := exists_fill_eq_Zvol (cone p X) (bdry_cone_of_closed hXc)
  obtain ⟨My, hMy, hMyn⟩ := exists_fill_eq_Zvol (cone p Y) (bdry_cone_of_closed hYc)
  obtain ⟨M, hM1, hM2⟩ :=
    exists_fill_eq_Zvol (cone p (X + Y)) (bdry_cone_of_closed hXYc)
  refine le_antisymm ?_ ?_
  · -- ≤ : concatenate optimal fillings
    have hbd : bdry (Mx + My) = X + Y := by rw [map_add, hMx, hMy]
    calc Zvol (X + Y) ≤ nrm (Mx + My) := Zvol_le hbd
      _ ≤ nrm Mx + nrm My := nrm_add_le _ _
      _ = Zvol X + Zvol Y := by rw [hMxn, hMyn]
  · -- ≥ : project an optimal filling to both sides
    have hMt : IsTaut M := by rw [IsTaut, hM1]; exact hM2
    have hbdsupp : ∀ s ∈ (bdry M).support, s.card = n + 1 := by
      intro s hs
      rw [hM1] at hs
      rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
      · exact (hX s h).2
      · exact (hY s h).2
    have hpure : ∀ s ∈ M.support, s.card = n + 2 :=
      fun s hs => hMt.dim_pure hbdsupp s hs
    have hdim2 : ∀ s ∈ M.support, 2 ≤ s.card := by
      intro s hs
      rw [hpure s hs]
      omega
    have hvert : vert M ⊆ A ∪ B := by
      refine (hMt.vert_subset hdim2).trans ?_
      rw [hM1]
      refine (vert_add_subset X Y).trans ?_
      exact Finset.union_subset_union
        (vert_subset_of_supp fun s hs => (hX s hs).1)
        (vert_subset_of_supp fun s hs => (hY s hs).1)
    have hsuppAB : ∀ t ∈ M.support, t ⊆ A ∪ B :=
      fun t ht => (supp_subset_vert ht).trans hvert
    -- the two projections fill X and Y
    have hbx : bdry (Kmap A p M) = X := by
      rw [bdry_Kmap A hpA, hM1, map_add,
        Kmap_eq_self (fun s hs => (hX s hs).1),
        Kmap_eq_zero_of_closed hn hp hC hY hYc, add_zero]
    have hby : bdry (Kmap B q M) = Y := by
      rw [bdry_Kmap B hqB, hM1, map_add,
        Kmap_eq_self (fun s hs => (hY s hs).1),
        Kmap_eq_zero_of_closed hn (Finset.inter_comm A B ▸ hq)
          (Finset.inter_comm A B ▸ hC) hX hXc, zero_add]
    -- norm bookkeeping
    have h1 := nrm_Kmap_add_killed_le A p M
    have h2 := nrm_Kmap_add_killed_le B q M
    have h3 : nrm M ≤ nrm (M.filter (Kkills A p)) + nrm (M.filter (Kkills B q)) :=
      nrm_le_killed_add_killed fun t ht =>
        Kkills_or_Kkills hp hq hpq hC (hsuppAB t ht) (hpure t ht)
    have h4 : Zvol X ≤ nrm (Kmap A p M) := Zvol_le hbx
    have h5 : Zvol Y ≤ nrm (Kmap B q M) := Zvol_le hby
    omega

/-- **Theorem 1, additivity (full paper statement)**: the hypothesis
`(A ∩ B).card ≤ n + 1` alone (with `n ≥ 1`) suffices — no witnessing pair
`p ≠ q` is needed.  When `|A ∩ B| ≥ 2` we extract a pair and invoke
`Zvol_add_of_almost_disjoint`; when `|A ∩ B| ≤ 1` we enlarge both `A` and
`B` by the same fresh vertices to reach exactly `|A' ∩ B'| = 2` (still
`≤ n + 1`), which never changes `X`, `Y`, or the conclusion.

`[Infinite V]` is pure ambient bookkeeping, not a finiteness restriction: chains are
finitely supported (`Chain V := Finset V →₀ ℤ`), so the active vertex set is always finite.
The hypothesis only guarantees that *fresh cut vertices are available* for the `|A ∩ B| ≤ 1`
enlargement above (the paper's "add a brand-new point to `C` if necessary"); a taut filling
never uses vertices beyond its boundary (`IsTaut.vert_subset`), so the unused ambient vertices
play no mathematical role. -/
theorem Zvol_add_of_almost_disjoint_full {V : Type*} [LinearOrder V] [Infinite V]
    {A B : Finset V} {n : ℕ} (hn : 1 ≤ n) (hC : (A ∩ B).card ≤ n + 1)
    {X Y : Chain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : bdry X = 0) (hYc : bdry Y = 0) :
    Zvol (X + Y) = Zvol X + Zvol Y := by
  classical
  by_cases h2 : 2 ≤ (A ∩ B).card
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
    exact Zvol_add_of_almost_disjoint hn hp hq hpq hC hX hY hXc hYc
  · push_neg at h2
    -- `|A ∩ B| ≤ 1`: enlarge both sides by `F`, a fresh set capping the
    -- intersection to exactly two shared vertices.
    have hle : (A ∪ B).card ≤ (A ∪ B).card + (2 - (A ∩ B).card) := Nat.le_add_right _ _
    obtain ⟨W, hWsub, hWcard⟩ :=
      Infinite.exists_superset_card_eq (A ∪ B) _ hle
    set F := W \ (A ∪ B) with hF
    have hFdisj : Disjoint F (A ∪ B) := Finset.sdiff_disjoint
    have hFcard : F.card = 2 - (A ∩ B).card := by
      have hkey : F.card + (A ∪ B).card = (A ∪ B).card + (2 - (A ∩ B).card) := by
        rw [hF, Finset.card_sdiff_add_card_eq_card hWsub, hWcard]
      omega
    set A' := A ∪ F with hA'
    set B' := B ∪ F with hB'
    have hFA : Disjoint F A := hFdisj.mono_right Finset.subset_union_left
    have hFB : Disjoint F B := hFdisj.mono_right Finset.subset_union_right
    -- the new intersection is exactly `(A ∩ B) ∪ F`
    have hinter : A' ∩ B' = (A ∩ B) ∪ F := by
      ext x
      simp only [hA', hB', Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxF, hxB | hxF⟩
        · exact Or.inl ⟨hxA, hxB⟩
        · exact Or.inr hxF
        · exact Or.inr hxF
        · exact Or.inr hxF
      · rintro (⟨hxA, hxB⟩ | hxF)
        · exact ⟨Or.inl hxA, Or.inl hxB⟩
        · exact ⟨Or.inr hxF, Or.inr hxF⟩
    have hABFdisj : Disjoint (A ∩ B) F :=
      (hFdisj.mono_right (Finset.inter_subset_left.trans Finset.subset_union_left)).symm
    have hcard' : (A' ∩ B').card = 2 := by
      rw [hinter, Finset.card_union_of_disjoint hABFdisj, hFcard]
      omega
    have h1lt : 1 < (A' ∩ B').card := by rw [hcard']; omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1lt
    have hC' : (A' ∩ B').card ≤ n + 1 := by rw [hcard']; omega
    have hAA' : A ⊆ A' := Finset.subset_union_left
    have hBB' : B ⊆ B' := Finset.subset_union_left
    have hX' : ∀ s ∈ X.support, s ⊆ A' ∧ s.card = n + 1 :=
      fun s hs => ⟨(hX s hs).1.trans hAA', (hX s hs).2⟩
    have hY' : ∀ s ∈ Y.support, s ⊆ B' ∧ s.card = n + 1 :=
      fun s hs => ⟨(hY s hs).1.trans hBB', (hY s hs).2⟩
    exact Zvol_add_of_almost_disjoint hn hp hq hpq hC' hX' hY' hXc hYc

end Taut
