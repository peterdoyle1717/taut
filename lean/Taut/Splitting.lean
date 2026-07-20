import Taut.Theorem1

/-!
# Theorem 1 of "Taut fillings", part 2: taut fillings split

Same setting as `Taut/Theorem1.lean` (`p ≠ q ∈ A ∩ B`,
`(A ∩ B).card ≤ n+1`, `X`/`Y` closed pure `n`-chains on `A`/`B`), now with
`n ≥ 2`: ANY taut filling `M` of `X + Y` splits as `M = M_X + M_Y` with
`M_X` a taut filling of `X` and `M_Y` of `Y` (`IsTaut.splits`).

Proof skeleton (the paper's, in general dimension):
1. no generator of `M` is killed by both projections, for ANY admissible
   pair `(p', q')` — else `M` would beat `Zvol X + Zvol Y`
   (`no_double_kill`);
2. hence every generator is pure (`⊆ A` or `⊆ B`) or extreme-hybrid
   (`n+1` vertices on one pure side, one vertex on the other, none
   shared) (`hybrid_structure`);
3. extreme hybrids form a complete cone over their lone vertex, which a
   taut chain cannot contain (`no_extreme_hybrid`);
4. so generators are pure and the filter along `· ⊆ A` splits `M`.
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

lemma card_three_part {A B t : Finset V} (htAB : t ⊆ A ∪ B) :
    (t ∩ (A ∩ B)).card + ((t \ A).card + (t \ B).card) = t.card := by
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
  have h1 := Finset.card_inter_add_card_sdiff t (A ∩ B)
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at h1
  omega

lemma bdry_eq_sum (M : Chain V) :
    bdry M = ∑ t ∈ M.support, M t • bdryGen t := by
  rw [bdry, Finsupp.lsum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun s _ => LinearMap.toSpanSingleton_apply ..

lemma exists_facet_of_bdryGen_ne_zero {t s : Finset V}
    (h : bdryGen t s ≠ 0) : ∃ w ∈ t, s = t.erase w := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [bdryGen, Finset.sum_apply']
  refine Finset.sum_eq_zero fun w hw => ?_
  rw [Finsupp.smul_apply, Finsupp.single_apply,
    if_neg (fun he => hcon w hw he.symm), smul_zero]

lemma bdry_apply_eq_sum (M : Chain V) (s : Finset V) :
    bdry M s = ∑ t ∈ M.support, M t * bdryGen t s := by
  rw [bdry_eq_sum, Finset.sum_apply']
  exact Finset.sum_congr rfl fun t _ => by
    rw [Finsupp.smul_apply, smul_eq_mul]

lemma bdry_supp_of_supp {B : Finset V} {k : ℕ} {M : Chain V}
    (h : ∀ t ∈ M.support, t ⊆ B ∧ t.card = k + 1) :
    ∀ s ∈ (bdry M).support, s ⊆ B ∧ s.card = k := by
  intro s hs
  rw [Finsupp.mem_support_iff, bdry_apply_eq_sum] at hs
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hgen : bdryGen t s ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  obtain ⟨w, hw, rfl⟩ := exists_facet_of_bdryGen_ne_zero hgen
  obtain ⟨h1, h2⟩ := h t ht
  exact ⟨(Finset.erase_subset w t).trans h1,
    by rw [Finset.card_erase_of_mem hw, h2]; omega⟩

/-- The closedness of the link: if `U` is supported on simplices
containing `x` and its boundary has no `x`-part, then `lk x U` is
closed. -/
lemma bdry_lk_eq_zero {x : V} {U : Chain V} (hU : nbhd x U = U)
    (hbU : nbhd x (bdry U) = 0) : bdry (lk x U) = 0 := by
  have hWfree : nbhd x (lk x U) = 0 := nbhd_lk x U
  have hWb : nbhd x (bdry (lk x U)) = 0 := nbhd_bdry_eq_zero hWfree
  have hconeU : cone x (lk x U) = U := by rw [cone_lk, hU]
  have hhom := bdry_cone_add_cone_bdry x (lk x U)
  rw [hconeU] at hhom
  have happ := congrArg (nbhd x) hhom
  rw [nbhd_add, hbU, zero_add, nbhd_cone, hWfree] at happ
  have h := eq_nbhd_of_cone_eq_zero happ
  rw [hWb] at h
  exact h

lemma exists_pair_of_one_lt_card {s : Finset V} (h : 2 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < s.card by omega)
  exact ⟨a, ha, b, hb, hab⟩

lemma kills_of_two_sdiff {A : Finset V} (p : V) {t : Finset V}
    (h : 2 ≤ (t \ A).card) : Kkills A p t := by
  constructor
  · intro hsub
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at h
    simp at h
  · intro hc
    omega

lemma kills_of_mem {A : Finset V} {p : V} {t : Finset V}
    (h1 : (t \ A).card = 1) (h2 : p ∈ t) : Kkills A p t := by
  constructor
  · intro hsub
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at h1
    simp at h1
  · exact fun hc => hc.2 h2

/-! ## Step 1: no generator is killed on both sides -/

/-- The strengthened mass bound: a doubly-killed generator contributes
twice. -/
lemma nrm_add_le_killed_add_killed {A B : Finset V} {p q : V} {M : Chain V}
    (hkill : ∀ t ∈ M.support, Kkills A p t ∨ Kkills B q t)
    {t₀ : Finset V} (ht₀ : t₀ ∈ M.support)
    (hkA : Kkills A p t₀) (hkB : Kkills B q t₀) :
    nrm M + (M t₀).natAbs ≤
      nrm (M.filter (Kkills A p)) + nrm (M.filter (Kkills B q)) := by
  classical
  have hsubA : (M.filter (Kkills A p)).support ⊆ M.support := by
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
  have hsubB : (M.filter (Kkills B q)).support ⊆ M.support := by
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
  rw [nrm_eq_sum_subset hsubA, nrm_eq_sum_subset hsubB,
    ← Finset.sum_add_distrib, nrm]
  have hsplit : (M t₀).natAbs
      = ∑ s ∈ M.support, if s = t₀ then (M t₀).natAbs else 0 := by
    rw [Finset.sum_ite_eq' M.support t₀ fun _ => (M t₀).natAbs, if_pos ht₀]
  rw [hsplit, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hst : s = t₀
  · subst hst
    rw [if_pos hkA, if_pos hkB, if_pos rfl]
  · rw [if_neg hst, add_zero]
    rcases hkill s hs with h | h
    · rw [if_pos h]
      omega
    · rw [if_pos h]
      split <;> omega

/-- No generator of a taut filling of `X + Y` is killed by both
projections, for ANY admissible pair of base points. -/
lemma no_double_kill {A B : Finset V} {n : ℕ}
    (hn : 1 ≤ n) {p q : V} (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q)
    (hC : (A ∩ B).card ≤ n + 1)
    {X Y : Chain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : bdry X = 0) (hYc : bdry Y = 0)
    {M : Chain V} (hM1 : bdry M = X + Y) (hMt : IsTaut M)
    {p' q' : V} (hp' : p' ∈ A ∩ B) (hq' : q' ∈ A ∩ B) (hpq' : p' ≠ q')
    {t₀ : Finset V} (ht₀ : t₀ ∈ M.support)
    (hkA : Kkills A p' t₀) (hkB : Kkills B q' t₀) : False := by
  have hbdsupp : ∀ s ∈ (bdry M).support, s.card = n + 1 := by
    intro s hs
    rw [hM1] at hs
    rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
    · exact (hX s h).2
    · exact (hY s h).2
  have hpure : ∀ s ∈ M.support, s.card = n + 2 :=
    fun s hs => hMt.dim_pure hbdsupp s hs
  have hdim2 : ∀ s ∈ M.support, 2 ≤ s.card := by
    intro s hs; rw [hpure s hs]; omega
  have hsuppAB : ∀ t ∈ M.support, t ⊆ A ∪ B := by
    intro t ht
    refine (supp_subset_vert ht).trans ((hMt.vert_subset hdim2).trans ?_)
    rw [hM1]
    exact (vert_add_subset X Y).trans (Finset.union_subset_union
      (vert_subset_of_supp fun s hs => (hX s hs).1)
      (vert_subset_of_supp fun s hs => (hY s hs).1))
  have hbx : bdry (Kmap A p' M) = X := by
    rw [bdry_Kmap A (Finset.mem_inter.mp hp').1, hM1, map_add,
      Kmap_eq_self (fun s hs => (hX s hs).1),
      Kmap_eq_zero_of_closed hn hp' hC hY hYc, add_zero]
  have hby : bdry (Kmap B q' M) = Y := by
    rw [bdry_Kmap B (Finset.mem_inter.mp hq').2, hM1, map_add,
      Kmap_eq_self (fun s hs => (hY s hs).1),
      Kmap_eq_zero_of_closed hn (Finset.inter_comm A B ▸ hq')
        (Finset.inter_comm A B ▸ hC) hX hXc, zero_add]
  have h1 := nrm_Kmap_add_killed_le A p' M
  have h2 := nrm_Kmap_add_killed_le B q' M
  have h3 := nrm_add_le_killed_add_killed
    (fun t ht => Kkills_or_Kkills hp' hq' hpq' hC (hsuppAB t ht) (hpure t ht))
    ht₀ hkA hkB
  have h4 : Zvol X ≤ nrm (Kmap A p' M) := Zvol_le hbx
  have h5 : Zvol Y ≤ nrm (Kmap B q' M) := Zvol_le hby
  have hadd := Zvol_add_of_almost_disjoint hn hp hq hpq hC hX hY hXc hYc
  have hM2 : nrm M = Zvol (X + Y) := by rw [IsTaut, hM1] at hMt; exact hMt
  have ht0ne : (M t₀).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Finsupp.mem_support_iff.mp ht₀)
  omega

/-! ## Step 2: generators are pure or extreme hybrids -/

/-- With `n ≥ 2`, every generator of a taut filling of `X + Y` is pure
(`⊆ A` or `⊆ B`) or an extreme hybrid: exactly one vertex on the
opposite pure side and no shared vertices. -/
lemma hybrid_structure {A B : Finset V} {n : ℕ}
    (hn : 2 ≤ n) {p q : V} (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q)
    (hC : (A ∩ B).card ≤ n + 1)
    {X Y : Chain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : bdry X = 0) (hYc : bdry Y = 0)
    {M : Chain V} (hM1 : bdry M = X + Y) (hMt : IsTaut M)
    (hpure : ∀ s ∈ M.support, s.card = n + 2)
    (hsuppAB : ∀ t ∈ M.support, t ⊆ A ∪ B)
    {t : Finset V} (ht : t ∈ M.support) :
    t ⊆ A ∨ t ⊆ B ∨
    ((t \ A).card = 1 ∧ t ∩ (A ∩ B) = ∅) ∨
    ((t \ B).card = 1 ∧ t ∩ (A ∩ B) = ∅) := by
  have hn1 : 1 ≤ n := by omega
  have hpart := card_three_part (hsuppAB t ht)
  rw [hpure t ht] at hpart
  by_cases hxa : (t \ A).card = 0
  · exact Or.inl (Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.card_eq_zero.mp hxa))
  by_cases hxb : (t \ B).card = 0
  · exact Or.inr (Or.inl (Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.card_eq_zero.mp hxb)))
  by_cases hc0 : (t ∩ (A ∩ B)).card = 0
  · by_cases hxa1 : (t \ A).card = 1
    · exact Or.inr (Or.inr (Or.inl ⟨hxa1, Finset.card_eq_zero.mp hc0⟩))
    by_cases hxb1 : (t \ B).card = 1
    · exact Or.inr (Or.inr (Or.inr ⟨hxb1, Finset.card_eq_zero.mp hc0⟩))
    exact (no_double_kill hn1 hp hq hpq hC hX hY hXc hYc hM1 hMt hp hq hpq ht
      (kills_of_two_sdiff p (by omega))
      (kills_of_two_sdiff q (by omega))).elim
  · have hcap : (t ∩ (A ∩ B)).Nonempty :=
      Finset.card_pos.mp (by omega)
    by_cases hxa1 : (t \ A).card = 1
    · by_cases hxb1 : (t \ B).card = 1
      · have hc2 : 2 ≤ (t ∩ (A ∩ B)).card := by omega
        obtain ⟨p', hp', q', hq', hpq'⟩ := exists_pair_of_one_lt_card hc2
        have hp'AB : p' ∈ A ∩ B := (Finset.mem_inter.mp hp').2
        have hq'AB : q' ∈ A ∩ B := (Finset.mem_inter.mp hq').2
        exact (no_double_kill hn1 hp hq hpq hC hX hY hXc hYc hM1 hMt
          hp'AB hq'AB hpq' ht
          (kills_of_mem hxa1 (Finset.mem_inter.mp hp').1)
          (kills_of_mem hxb1 (Finset.mem_inter.mp hq').1)).elim
      · obtain ⟨p', hp'⟩ := hcap
        have hp'AB : p' ∈ A ∩ B := (Finset.mem_inter.mp hp').2
        set q' := if p' = p then q else p with hq'def
        have hq'AB : q' ∈ A ∩ B := by
          rw [hq'def]; split <;> assumption
        have hpq' : p' ≠ q' := by
          rw [hq'def]
          split
          · rename_i h; rw [h]; exact hpq
          · assumption
        exact (no_double_kill hn1 hp hq hpq hC hX hY hXc hYc hM1 hMt
          hp'AB hq'AB hpq' ht
          (kills_of_mem hxa1 (Finset.mem_inter.mp hp').1)
          (kills_of_two_sdiff q' (by omega))).elim
    · by_cases hxb1 : (t \ B).card = 1
      · obtain ⟨q', hq'⟩ := hcap
        have hq'AB : q' ∈ A ∩ B := (Finset.mem_inter.mp hq').2
        set p' := if q' = p then q else p with hp'def
        have hp'AB : p' ∈ A ∩ B := by
          rw [hp'def]; split <;> assumption
        have hpq' : p' ≠ q' := by
          rw [hp'def]
          split
          · rename_i h; rw [h]; exact fun he => hpq he.symm
          · rename_i h; exact fun he => h he.symm
        exact (no_double_kill hn1 hp hq hpq hC hX hY hXc hYc hM1 hMt
          hp'AB hq'AB hpq' ht
          (kills_of_two_sdiff p' (by omega))
          (kills_of_mem hxb1 (Finset.mem_inter.mp hq').1)).elim
      · exact (no_double_kill hn1 hp hq hpq hC hX hY hXc hYc hM1 hMt hp hq hpq ht
          (kills_of_two_sdiff p (by omega))
          (kills_of_two_sdiff q (by omega))).elim

/-! ## Step 3: extreme hybrids form a forbidden complete cone -/

/-- No generator of a taut filling is an extreme hybrid on the `Y` side:
the simplices `X^{n+1}y₀` would form a complete cone over `y₀`.  This is
the coefficient-level vanishing argument: hybrid faces `X^n y₀` are
absent from `X + Y`, and all their cofaces in `M` lie in the cone. -/
lemma no_extreme_hybrid {A B : Finset V} {n : ℕ}
    (hn : 2 ≤ n) {p q : V} (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q)
    (hC : (A ∩ B).card ≤ n + 1)
    {X Y : Chain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : bdry X = 0) (hYc : bdry Y = 0)
    {M : Chain V} (hM1 : bdry M = X + Y) (hMt : IsTaut M)
    (hpure : ∀ s ∈ M.support, s.card = n + 2)
    (hsuppAB : ∀ t ∈ M.support, t ⊆ A ∪ B)
    {t₀ : Finset V} (ht₀ : t₀ ∈ M.support) {y₀ : V}
    (hy : t₀ \ A = {y₀}) (hcap : t₀ ∩ (A ∩ B) = ∅) : False := by
  classical
  obtain ⟨hy₀t, hy₀A⟩ := mem_of_sdiff_singleton hy
  -- the cone candidate: simplices with y₀ and at least two X-vertices
  set U := M.filter (fun t => y₀ ∈ t ∧ 2 ≤ (t \ B).card) with hU
  have hUsub : SubChain U M := subChain_filter _ M
  have hUnbhd : nbhd y₀ U = U := by
    ext t
    rw [nbhd_apply]
    split
    · rfl
    · rename_i hyt
      rw [hU, Finsupp.filter_apply, if_neg (fun h => hyt h.1)]
  have hUstruct : ∀ t ∈ U.support,
      t \ A = {y₀} ∧ t ∩ (A ∩ B) = ∅ ∧ (t \ B).card = n + 1 := by
    intro t ht
    rw [hU, Finsupp.support_filter, Finset.mem_filter] at ht
    obtain ⟨htM, hyt, h2t⟩ := ht
    rcases hybrid_structure hn hp hq hpq hC hX hY hXc hYc hM1 hMt hpure
      hsuppAB htM with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h hyt) hy₀A
    · rw [Finset.sdiff_eq_empty_iff_subset.mpr h] at h2t
      simp at h2t
    · obtain ⟨y', hy'⟩ := Finset.card_eq_one.mp h1
      have hyy' : y₀ ∈ t \ A := Finset.mem_sdiff.mpr ⟨hyt, hy₀A⟩
      rw [hy', Finset.mem_singleton] at hyy'
      subst hyy'
      have hpart := card_three_part (hsuppAB t htM)
      rw [hpure t htM, h2, hy'] at hpart
      simp only [Finset.card_empty, Finset.card_singleton] at hpart
      exact ⟨hy', h2, by omega⟩
    · omega
  have hxb₀ : (t₀ \ B).card = n + 1 := by
    have hpart := card_three_part (hsuppAB t₀ ht₀)
    rw [hpure t₀ ht₀, hcap, hy] at hpart
    simp only [Finset.card_empty, Finset.card_singleton] at hpart
    omega
  have hUt₀ : U t₀ = M t₀ := by
    rw [hU, Finsupp.filter_apply, if_pos ⟨hy₀t, by omega⟩]
  have ht₀U : t₀ ∈ U.support := by
    rw [Finsupp.mem_support_iff, hUt₀]
    exact Finsupp.mem_support_iff.mp ht₀
  have hbU : nbhd y₀ (bdry U) = 0 := by
    ext s
    rw [nbhd_apply, Finsupp.coe_zero, Pi.zero_apply]
    split
    · rename_i hys
      by_cases hs2 : 2 ≤ (s \ B).card
      · -- here ∂U agrees with ∂M, which carries no such face
        have hMU : bdry (M - U) s = 0 := by
          rw [bdry_apply_eq_sum]
          refine Finset.sum_eq_zero fun t ht => ?_
          by_cases hgen : bdryGen t s = 0
          · rw [hgen, mul_zero]
          · obtain ⟨w, hw, hsw⟩ := exists_facet_of_bdryGen_ne_zero hgen
            have hst : s ⊆ t := hsw ▸ Finset.erase_subset w t
            have hzero : (M - U) t = 0 := by
              rw [Finsupp.sub_apply, hU, Finsupp.filter_apply,
                if_pos ⟨hst hys, le_trans hs2 (Finset.card_le_card
                  (Finset.sdiff_subset_sdiff hst (Finset.Subset.refl B)))⟩,
                sub_self]
            rw [hzero, zero_mul]
        have hXY0 : (X + Y) s = 0 := by
          rw [Finsupp.add_apply]
          have hXs : X s = 0 := by
            by_contra h
            exact hy₀A ((hX s (Finsupp.mem_support_iff.mpr h)).1 hys)
          have hYs : Y s = 0 := by
            by_contra h
            have hsB := (hY s (Finsupp.mem_support_iff.mpr h)).1
            rw [Finset.sdiff_eq_empty_iff_subset.mpr hsB] at hs2
            simp at hs2
          rw [hXs, hYs, add_zero]
        have hkey : bdry U s = bdry M s - bdry (M - U) s := by
          rw [map_sub, Finsupp.sub_apply]
          ring
        rw [hkey, hMU, sub_zero, hM1, hXY0]
      · -- faces of U-generators with y₀ have ≥ n ≥ 2 X-vertices
        rw [bdry_apply_eq_sum]
        refine Finset.sum_eq_zero fun t ht => ?_
        by_cases hgen : bdryGen t s = 0
        · rw [hgen, mul_zero]
        · obtain ⟨w, hw, hsw⟩ := exists_facet_of_bdryGen_ne_zero hgen
          obtain ⟨htA, htcap, htxb⟩ := hUstruct t ht
          have hcard : n ≤ (s \ B).card := by
            rw [hsw, erase_sdiff]
            have hle := Finset.pred_card_le_card_erase (a := w) (s := t \ B)
            omega
          exact absurd hcard (by omega)
    · rfl
  -- assemble the complete cone and contradict tautness
  have hWclosed := bdry_lk_eq_zero hUnbhd hbU
  have hdegy : deg y₀ (lk y₀ U) = 0 := by rw [deg, nbhd_lk, nrm_zero]
  have hconeU : cone y₀ (lk y₀ U) = U := by rw [cone_lk, hUnbhd]
  have hWne : lk y₀ U (t₀.erase y₀) ≠ 0 := by
    intro h0
    have happ : cone y₀ (lk y₀ U) t₀ = U t₀ := by rw [hconeU]
    rw [cone_apply, if_pos hy₀t, h0, mul_zero] at happ
    exact Finsupp.mem_support_iff.mp ht₀U happ.symm
  have hne : (t₀.erase y₀).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hy₀t, hpure t₀ ht₀]
    omega
  obtain ⟨x', hx'⟩ := hne
  have hdegx' : deg x' (lk y₀ U) ≠ 0 := by
    intro h
    exact (deg_eq_zero_iff.mp h)
      (mem_vert.mpr ⟨t₀.erase y₀, Finsupp.mem_support_iff.mpr hWne, hx'⟩)
  exact not_taut_complete_cone hMt (by rw [hconeU]; exact hUsub)
    hWclosed hdegy hdegx'

/-! ## Theorem 1, part 2: taut fillings split -/

/-- **Theorem 1, splitting** (Doyle–Ellison–Wang): for `n ≥ 2`, ANY taut
filling `M` of an almost disjoint union `X + Y` splits: filtering `M`
along `· ⊆ A` yields taut fillings of `X` and of `Y` summing to `M`. -/
theorem IsTaut.splits {A B : Finset V} {n : ℕ}
    (hn : 2 ≤ n) {p q : V} (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ B) (hpq : p ≠ q)
    (hC : (A ∩ B).card ≤ n + 1)
    {X Y : Chain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : bdry X = 0) (hYc : bdry Y = 0)
    {M : Chain V} (hMt : IsTaut M) (hM1 : bdry M = X + Y) :
    bdry (M.filter (fun t => t ⊆ A)) = X ∧
    bdry (M.filter (fun t => ¬ t ⊆ A)) = Y ∧
    IsTaut (M.filter (fun t => t ⊆ A)) ∧
    IsTaut (M.filter (fun t => ¬ t ⊆ A)) ∧
    M.filter (fun t => t ⊆ A) + M.filter (fun t => ¬ t ⊆ A) = M := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hbdsupp : ∀ s ∈ (bdry M).support, s.card = n + 1 := by
    intro s hs
    rw [hM1] at hs
    rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
    · exact (hX s h).2
    · exact (hY s h).2
  have hpure : ∀ s ∈ M.support, s.card = n + 2 :=
    fun s hs => hMt.dim_pure hbdsupp s hs
  have hdim2 : ∀ s ∈ M.support, 2 ≤ s.card := by
    intro s hs; rw [hpure s hs]; omega
  have hsuppAB : ∀ t ∈ M.support, t ⊆ A ∪ B := by
    intro t ht
    refine (supp_subset_vert ht).trans ((hMt.vert_subset hdim2).trans ?_)
    rw [hM1]
    exact (vert_add_subset X Y).trans (Finset.union_subset_union
      (vert_subset_of_supp fun s hs => (hX s hs).1)
      (vert_subset_of_supp fun s hs => (hY s hs).1))
  have hdich : ∀ t ∈ M.support, t ⊆ A ∨ t ⊆ B := by
    intro t ht
    rcases hybrid_structure hn hp hq hpq hC hX hY hXc hYc hM1 hMt hpure
      hsuppAB ht with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨y₀, hy⟩ := Finset.card_eq_one.mp h1
      exact (no_extreme_hybrid hn hp hq hpq hC hX hY hXc hYc hM1 hMt hpure
        hsuppAB ht hy h2).elim
    · -- symmetric configuration, roles of A and B exchanged
      obtain ⟨x₀, hx⟩ := Finset.card_eq_one.mp h1
      have hM1' : bdry M = Y + X := by rw [hM1, add_comm]
      have hsuppBA : ∀ t' ∈ M.support, t' ⊆ B ∪ A := by
        intro t' ht'
        rw [Finset.union_comm]
        exact hsuppAB t' ht'
      exact (no_extreme_hybrid hn (Finset.inter_comm A B ▸ hq)
        (Finset.inter_comm A B ▸ hp) hpq.symm (Finset.inter_comm A B ▸ hC)
        hY hX hYc hXc hM1' hMt hpure hsuppBA ht hx
        (Finset.inter_comm A B ▸ h2)).elim
  set Mx := M.filter (fun t => t ⊆ A) with hMx
  set My := M.filter (fun t => ¬ t ⊆ A) with hMy
  have hsum : Mx + My = M := Finsupp.filter_pos_add_filter_neg M _
  have hMxsupp : ∀ t ∈ Mx.support, t ⊆ A ∧ t.card = n + 2 := by
    intro t ht
    rw [hMx, Finsupp.support_filter, Finset.mem_filter] at ht
    exact ⟨ht.2, hpure t ht.1⟩
  have hMysupp : ∀ t ∈ My.support, t ⊆ B ∧ t.card = n + 2 := by
    intro t ht
    rw [hMy, Finsupp.support_filter, Finset.mem_filter] at ht
    exact ⟨(hdich t ht.1).resolve_left ht.2, hpure t ht.1⟩
  have hbsum : bdry Mx + bdry My = X + Y := by rw [← map_add, hsum, hM1]
  have hbx : bdry Mx = X := by
    have happly := congrArg (Kmap A p) hbsum
    rw [map_add, map_add,
      Kmap_eq_self (fun s hs => (bdry_supp_of_supp hMxsupp s hs).1),
      Kmap_eq_zero_of_closed hn1 hp hC (bdry_supp_of_supp hMysupp)
        (bdry_bdry My),
      Kmap_eq_self (fun s hs => (hX s hs).1),
      Kmap_eq_zero_of_closed hn1 hp hC hY hYc, add_zero, add_zero] at happly
    exact happly
  have hby : bdry My = Y := by
    have h := hbsum
    rw [hbx] at h
    exact add_left_cancel h
  have hnrm : nrm Mx + nrm My = nrm M := nrm_filter_add_nrm_filter_neg _ M
  have hadd := Zvol_add_of_almost_disjoint hn1 hp hq hpq hC hX hY hXc hYc
  have hM2 : nrm M = Zvol (X + Y) := by rw [IsTaut, hM1] at hMt; exact hMt
  have h4 : Zvol X ≤ nrm Mx := Zvol_le hbx
  have h5 : Zvol Y ≤ nrm My := Zvol_le hby
  have hMxt : IsTaut Mx := by rw [IsTaut, hbx]; omega
  have hMyt : IsTaut My := by rw [IsTaut, hby]; omega
  exact ⟨hbx, hby, hMxt, hMyt, hsum⟩

/-- **Theorem 1, splitting (full paper statement)**: for `n ≥ 2`, the
hypothesis `(A ∩ B).card ≤ n + 1` alone suffices — no witnessing pair
`p ≠ q` is needed.  When `|A ∩ B| ≥ 2` we extract a pair and invoke
`IsTaut.splits`; when `|A ∩ B| ≤ 1` we enlarge both sides by the same
fresh vertices `F` to reach `|A' ∩ B'| = 2 ≤ n + 1`, run the split along
`· ⊆ A'`, then transfer it back to `· ⊆ A`.  The transfer is valid because
every generator of the filling `M` lies in `A ∪ B`, hence is disjoint from
the fresh set `F`, so `t ⊆ A' ↔ t ⊆ A` on `M.support`.

`[Infinite V]` only guarantees that fresh cut vertices are available for the
`|A ∩ B| ≤ 1` enlargement; a taut filling never uses vertices beyond its boundary
(`IsTaut.vert_subset`). -/
theorem IsTaut.splits_full {V : Type*} [LinearOrder V] [Infinite V]
    {A B : Finset V} {n : ℕ} (hn : 2 ≤ n) (hC : (A ∩ B).card ≤ n + 1)
    {X Y : Chain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : bdry X = 0) (hYc : bdry Y = 0)
    {M : Chain V} (hMt : IsTaut M) (hM1 : bdry M = X + Y) :
    bdry (M.filter (fun t => t ⊆ A)) = X ∧
    bdry (M.filter (fun t => ¬ t ⊆ A)) = Y ∧
    IsTaut (M.filter (fun t => t ⊆ A)) ∧
    IsTaut (M.filter (fun t => ¬ t ⊆ A)) ∧
    M.filter (fun t => t ⊆ A) + M.filter (fun t => ¬ t ⊆ A) = M := by
  classical
  by_cases h2 : 2 ≤ (A ∩ B).card
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
    exact IsTaut.splits hn hp hq hpq hC hX hY hXc hYc hMt hM1
  · push_neg at h2
    have hn1 : 1 ≤ n := by omega
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
    obtain ⟨hbx', hby', hMxt', hMyt', hsum'⟩ :=
      IsTaut.splits hn hp hq hpq hC' hX' hY' hXc hYc hMt hM1
    have hbdsupp : ∀ s ∈ (bdry M).support, s.card = n + 1 := by
      intro s hs
      rw [hM1] at hs
      rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
      · exact (hX s h).2
      · exact (hY s h).2
    have hpure : ∀ s ∈ M.support, s.card = n + 2 :=
      fun s hs => hMt.dim_pure hbdsupp s hs
    have hdim2 : ∀ s ∈ M.support, 2 ≤ s.card := by
      intro s hs; rw [hpure s hs]; omega
    have hsuppAB : ∀ t ∈ M.support, t ⊆ A ∪ B := by
      intro t ht
      refine (supp_subset_vert ht).trans ((hMt.vert_subset hdim2).trans ?_)
      rw [hM1]
      exact (vert_add_subset X Y).trans (Finset.union_subset_union
        (vert_subset_of_supp fun s hs => (hX s hs).1)
        (vert_subset_of_supp fun s hs => (hY s hs).1))
    have hiff : ∀ t ∈ M.support, (t ⊆ A' ↔ t ⊆ A) := by
      intro t ht
      have hdisj : Disjoint t F := (hFdisj.mono_right (hsuppAB t ht)).symm
      constructor
      · intro htA' x hx
        rcases Finset.mem_union.mp (htA' hx) with h | h
        · exact h
        · exact absurd h (Finset.disjoint_left.mp hdisj hx)
      · intro htA
        exact htA.trans hAA'
    have hfilt_pos : M.filter (fun t => t ⊆ A') = M.filter (fun t => t ⊆ A) := by
      ext s
      rw [Finsupp.filter_apply, Finsupp.filter_apply]
      by_cases hs : s ∈ M.support
      · simp only [hiff s hs]
      · rw [Finsupp.notMem_support_iff.mp hs]; simp
    have hfilt_neg : M.filter (fun t => ¬ t ⊆ A') = M.filter (fun t => ¬ t ⊆ A) := by
      ext s
      rw [Finsupp.filter_apply, Finsupp.filter_apply]
      by_cases hs : s ∈ M.support
      · simp only [hiff s hs]
      · rw [Finsupp.notMem_support_iff.mp hs]; simp
    rw [hfilt_pos] at hbx' hMxt' hsum'
    rw [hfilt_neg] at hby' hMyt' hsum'
    exact ⟨hbx', hby', hMxt', hMyt', hsum'⟩

end Taut
