import Taut.Zvol

/-!
# The projection chain map K_{A,p}

For `A : Finset V` and `p ∈ A`, the vertex map `π(v) = if v ∈ A then v
else p` induces a chain map `Kmap A p : Chain V →ₗ[ℤ] Chain V` (landing in
chains on `A`).  On a generator `s`:

* if `s ⊆ A`, it is the identity;
* if exactly one vertex `z` of `s` lies outside `A` and `p ∉ s`, it
  replaces `z` by `p`, with the sign `sgn z s • coneGen p (s.erase z)`
  (the composite sign `(-1)^(cnt z s + cnt p (s.erase z))`);
* otherwise two vertices collide and the simplex dies.

Main results:
* `bdry_Kmap` : ∂ ∘ K = K ∘ ∂ (the chain-map property);
* `nrm_Kmap_add_killed_le` : norm accounting — `K` loses at least the mass
  of the generators it kills;
* small-support triviality: `eq_zero_of_supp_card_lt`,
  `eq_zero_of_closed_supp_card_eq` (the paper's `C_c(C) = 0`,
  `Z_{c-1}(C) = 0`).
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

def Kkills (A : Finset V) (p : V) (s : Finset V) : Prop :=
  ¬ s ⊆ A ∧ ¬ ((s \ A).card = 1 ∧ p ∉ s)

instance (A : Finset V) (p : V) : DecidablePred (Kkills A p) := fun s => by
  unfold Kkills; infer_instance

noncomputable def KGen (A : Finset V) (p : V) (s : Finset V) : Chain V :=
  if s ⊆ A then Finsupp.single s 1
  else if (s \ A).card = 1 ∧ p ∉ s then
    ∑ z ∈ s \ A, sgn z s • coneGen p (s.erase z)
  else 0

/-- The projection chain map induced by `π(v) = if v ∈ A then v else p`. -/
noncomputable def Kmap (A : Finset V) (p : V) : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.lsum ℤ fun s => LinearMap.toSpanSingleton ℤ (Chain V) (KGen A p s)

@[simp] lemma Kmap_single (A : Finset V) (p : V) (s : Finset V) (c : ℤ) :
    Kmap A p (Finsupp.single s c) = c • KGen A p s := by
  simp [Kmap, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-! ## Unfolding lemmas -/

lemma KGen_of_subset {A : Finset V} {p : V} {s : Finset V} (h : s ⊆ A) :
    KGen A p s = Finsupp.single s 1 := by
  rw [KGen, if_pos h]

lemma not_subset_of_sdiff_singleton {A s : Finset V} {z : V}
    (h : s \ A = {z}) : ¬ s ⊆ A := by
  intro hsub
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at h
  exact absurd h.symm (Finset.singleton_ne_empty z)

lemma mem_of_sdiff_singleton {A s : Finset V} {z : V}
    (h : s \ A = {z}) : z ∈ s ∧ z ∉ A := by
  have : z ∈ s \ A := h ▸ Finset.mem_singleton_self z
  exact Finset.mem_sdiff.mp this

lemma KGen_of_one {A : Finset V} {p : V} {s : Finset V} {z : V}
    (hz : s \ A = {z}) (hps : p ∉ s) :
    KGen A p s = sgn z s • coneGen p (s.erase z) := by
  rw [KGen, if_neg (not_subset_of_sdiff_singleton hz),
    if_pos ⟨by rw [hz, Finset.card_singleton], hps⟩, hz,
    Finset.sum_singleton]

lemma KGen_of_mem {A : Finset V} {p : V} {s : Finset V}
    (h1 : ¬ s ⊆ A) (hps : p ∈ s) : KGen A p s = 0 := by
  rw [KGen, if_neg h1, if_neg (fun h => h.2 hps)]

lemma KGen_of_two {A : Finset V} {p : V} {s : Finset V}
    (h : 2 ≤ (s \ A).card) : KGen A p s = 0 := by
  have h1 : ¬ s ⊆ A := by
    intro hsub
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub] at h
    simp at h
  rw [KGen, if_neg h1, if_neg (fun hh => by omega)]

lemma KGen_of_kills {A : Finset V} {p : V} {s : Finset V}
    (h : Kkills A p s) : KGen A p s = 0 := by
  rw [KGen, if_neg h.1, if_neg h.2]

lemma erase_sdiff (s A : Finset V) (w : V) :
    (s.erase w) \ A = (s \ A).erase w := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  tauto

/-! ## The chain-map property, case by case -/

/-- Case `s ⊆ A`: both sides are the identity. -/
lemma bdry_KGen_subset {A : Finset V} {p : V} {s : Finset V} (hsub : s ⊆ A) :
    bdry (KGen A p s) = Kmap A p (bdryGen s) := by
  rw [KGen_of_subset hsub, bdry_single, one_smul]
  conv_rhs => rw [bdryGen, map_sum]
  rw [bdryGen]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [map_smul, Kmap_single, one_smul,
    KGen_of_subset ((Finset.erase_subset w s).trans hsub)]

/-- Case `(s \ A).card ≥ 2`: both sides vanish (for the right-hand side,
the two leftover outside vertices cancel in pairs). -/
lemma bdry_KGen_two {A : Finset V} {p : V} (hp : p ∈ A) {s : Finset V}
    (h2 : 2 ≤ (s \ A).card) :
    bdry (KGen A p s) = Kmap A p (bdryGen s) := by
  rw [KGen_of_two h2, map_zero, bdryGen, map_sum]
  have hterm : ∀ w ∈ s, Kmap A p (sgn w s • Finsupp.single (s.erase w) 1)
      = sgn w s • KGen A p (s.erase w) := fun w _ => by
    rw [map_smul, Kmap_single, one_smul]
  rw [Finset.sum_congr rfl hterm]
  rcases Nat.lt_or_ge (s \ A).card 3 with h3 | h3
  · have hcard : (s \ A).card = 2 := by omega
    obtain ⟨z₁, z₂, hne, hz12⟩ := Finset.card_eq_two.mp hcard
    have hz₁s : z₁ ∈ s ∧ z₁ ∉ A := by
      have : z₁ ∈ s \ A := by rw [hz12]; exact Finset.mem_insert_self _ _
      exact Finset.mem_sdiff.mp this
    have hz₂s : z₂ ∈ s ∧ z₂ ∉ A := by
      have : z₂ ∈ s \ A := by
        rw [hz12]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact Finset.mem_sdiff.mp this
    have herase₁ : (s.erase z₁) \ A = {z₂} := by
      rw [erase_sdiff, hz12, Finset.erase_insert (by simp [hne])]
    have herase₂ : (s.erase z₂) \ A = {z₁} := by
      rw [erase_sdiff, hz12]
      ext y
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hy' | hy'⟩
        · exact hy'
        · exact absurd hy' hy
      · rintro rfl
        exact ⟨hne, Or.inl rfl⟩
    by_cases hps : p ∈ s
    · refine (Finset.sum_eq_zero fun w hw => ?_).symm
      by_cases hw₁ : w = z₁
      · subst hw₁
        rw [KGen_of_mem (not_subset_of_sdiff_singleton herase₁)
          (Finset.mem_erase_of_ne_of_mem
            (fun h => hz₁s.2 (h ▸ hp)) hps), smul_zero]
      · by_cases hw₂ : w = z₂
        · subst hw₂
          rw [KGen_of_mem (not_subset_of_sdiff_singleton herase₂)
            (Finset.mem_erase_of_ne_of_mem
              (fun h => hz₂s.2 (h ▸ hp)) hps), smul_zero]
        · have h2' : 2 ≤ ((s.erase w) \ A).card := by
            rw [erase_sdiff, hz12,
              Finset.erase_eq_of_notMem (by simp [hw₁, hw₂]),
              Finset.card_pair hne]
          rw [KGen_of_two h2', smul_zero]
    · have hzero : ∀ w ∈ s, w ∉ ({z₁, z₂} : Finset V) →
          sgn w s • KGen A p (s.erase w) = 0 := by
        intro w hw hwn
        have h2' : 2 ≤ ((s.erase w) \ A).card := by
          rw [erase_sdiff, hz12, Finset.erase_eq_of_notMem (by simpa using hwn),
            Finset.card_pair hne]
        rw [KGen_of_two h2', smul_zero]
      rw [← Finset.sum_subset
          (Finset.insert_subset hz₁s.1 (Finset.singleton_subset_iff.mpr hz₂s.1))
          hzero, Finset.sum_pair hne,
        KGen_of_one herase₁ (fun h => hps (Finset.mem_of_mem_erase h)),
        KGen_of_one herase₂ (fun h => hps (Finset.mem_of_mem_erase h)),
        Finset.erase_right_comm (a := z₂) (b := z₁), smul_smul, smul_smul,
        ← add_smul, sgn_erase_cancel hz₁s.1 hz₂s.1 hne, neg_add_cancel,
        zero_smul]
  · refine (Finset.sum_eq_zero fun w hw => ?_).symm
    have h2' : 2 ≤ ((s.erase w) \ A).card := by
      rw [erase_sdiff]
      have h := Finset.pred_card_le_card_erase (a := w) (s := s \ A)
      omega
    rw [KGen_of_two h2', smul_zero]

/-- Case `s \ A = {z₀}`, `p ∈ s`: the `z₀`-facet and the `p`-facet of the
right-hand side cancel. -/
lemma bdry_KGen_one_mem {A : Finset V} {p : V} (hp : p ∈ A) {s : Finset V}
    {z₀ : V} (hz : s \ A = {z₀}) (hps : p ∈ s) :
    bdry (KGen A p s) = Kmap A p (bdryGen s) := by
  obtain ⟨hz₀s, hz₀A⟩ := mem_of_sdiff_singleton hz
  have hpz : p ≠ z₀ := fun h => hz₀A (h ▸ hp)
  rw [KGen_of_mem (not_subset_of_sdiff_singleton hz) hps, map_zero, bdryGen,
    map_sum]
  have hterm : ∀ w ∈ s, Kmap A p (sgn w s • Finsupp.single (s.erase w) 1)
      = sgn w s • KGen A p (s.erase w) := fun w _ => by
    rw [map_smul, Kmap_single, one_smul]
  have hzero : ∀ w ∈ s, w ∉ ({z₀, p} : Finset V) →
      sgn w s • KGen A p (s.erase w) = 0 := by
    intro w hw hwn
    have hwz : w ≠ z₀ := fun h => hwn (h ▸ Finset.mem_insert_self _ _)
    have hwp : w ≠ p := fun h =>
      hwn (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have herase : (s.erase w) \ A = {z₀} := by
      rw [erase_sdiff, hz, Finset.erase_eq_of_notMem (by simp [hwz])]
    rw [KGen_of_mem (not_subset_of_sdiff_singleton herase)
      (Finset.mem_erase_of_ne_of_mem (Ne.symm hwp) hps), smul_zero]
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_subset
      (Finset.insert_subset hz₀s (Finset.singleton_subset_iff.mpr hps))
      hzero,
    Finset.sum_pair (fun h => hpz h.symm)]
  have hsub₀ : s.erase z₀ ⊆ A := by
    rw [← Finset.sdiff_eq_empty_iff_subset, erase_sdiff, hz,
      Finset.erase_singleton]
  have heraseP : (s.erase p) \ A = {z₀} := by
    rw [erase_sdiff, hz, Finset.erase_eq_of_notMem (by simp [hpz])]
  rw [KGen_of_subset hsub₀,
    KGen_of_one heraseP (Finset.notMem_erase p s), coneGen,
    if_neg (fun h => (Finset.notMem_erase p s) (Finset.mem_of_mem_erase h)),
    Finset.erase_right_comm (a := p) (b := z₀),
    Finset.insert_erase
      (Finset.mem_erase_of_ne_of_mem hpz hps),
    smul_smul, smul_smul, ← add_smul]
  have hc := sgn_erase_cancel hps hz₀s hpz
  have h2 := sgn_erase_self p (s.erase z₀)
  have h3 := sgn_mul_self p (s.erase z₀)
  have hcoef : sgn z₀ s + sgn p s * sgn z₀ (s.erase p) *
      sgn p ((s.erase z₀).erase p) = 0 := by
    rw [h2]
    linear_combination sgn p (s.erase z₀) * hc - sgn z₀ s * h3
  rw [hcoef, zero_smul]

/-- Case `s \ A = {z₀}`, `p ∉ s`: the replacement case, via the
contracting homotopy. -/
lemma bdry_KGen_one_notMem {A : Finset V} {p : V} (hp : p ∈ A) {s : Finset V}
    {z₀ : V} (hz : s \ A = {z₀}) (hps : p ∉ s) :
    bdry (KGen A p s) = Kmap A p (bdryGen s) := by
  obtain ⟨hz₀s, hz₀A⟩ := mem_of_sdiff_singleton hz
  set u := s.erase z₀ with hu
  have hpu : p ∉ u := fun h => hps (Finset.mem_of_mem_erase h)
  have hsub₀ : u ⊆ A := by
    rw [hu, ← Finset.sdiff_eq_empty_iff_subset, erase_sdiff, hz,
      Finset.erase_singleton]
  have hcone : coneGen p u = cone p (Finsupp.single u 1) := by
    rw [cone_single, one_smul]
  have hstep : bdry (cone p (Finsupp.single u (1 : ℤ)))
      = Finsupp.single u 1 - cone p (bdryGen u) := by
    have hhom := bdry_cone_add_cone_bdry p (Finsupp.single u (1 : ℤ))
    rw [bdry_single, one_smul] at hhom
    rw [eq_sub_iff_add_eq]
    exact hhom
  have hlhs : bdry (KGen A p s)
      = sgn z₀ s • Finsupp.single u 1
        - sgn z₀ s • cone p (bdryGen u) := by
    rw [KGen_of_one hz hps, map_smul, hcone, hstep, smul_sub]
  rw [hlhs]
  conv_rhs => rw [bdryGen, map_sum]
  have hterm : ∀ w ∈ s, Kmap A p (sgn w s • Finsupp.single (s.erase w) 1)
      = sgn w s • KGen A p (s.erase w) := fun w _ => by
    rw [map_smul, Kmap_single, one_smul]
  rw [Finset.sum_congr rfl hterm, ← Finset.add_sum_erase _ _ hz₀s, ← hu,
    KGen_of_subset hsub₀]
  have hrest : ∀ w ∈ u, sgn w s • KGen A p (s.erase w)
      = (sgn w s * sgn z₀ (s.erase w)) • coneGen p (u.erase w) := by
    intro w hw
    have hwz : w ≠ z₀ := Finset.ne_of_mem_erase hw
    have herase : (s.erase w) \ A = {z₀} := by
      rw [erase_sdiff, hz, Finset.erase_eq_of_notMem (by simp [hwz])]
    rw [KGen_of_one herase (fun h => hps (Finset.mem_of_mem_erase h)),
      smul_smul, hu, Finset.erase_right_comm (a := z₀) (b := w)]
  have hconebdry : cone p (bdryGen u)
      = ∑ w ∈ u, (sgn w u) • coneGen p (u.erase w) := by
    rw [bdryGen, map_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [map_smul, cone_single, one_smul]
  rw [Finset.sum_congr rfl hrest, hconebdry, Finset.smul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w hw => ?_
  have hws : w ∈ s := Finset.mem_of_mem_erase (hu ▸ hw)
  have hwz : w ≠ z₀ := Finset.ne_of_mem_erase (hu ▸ hw)
  rw [smul_smul, ← neg_smul]
  congr 1
  have hc := sgn_erase_cancel hz₀s hws (Ne.symm hwz)
  rw [← hu] at hc
  linarith [hc]

theorem bdry_KGen (A : Finset V) {p : V} (hp : p ∈ A) (s : Finset V) :
    bdry (KGen A p s) = Kmap A p (bdryGen s) := by
  rcases Nat.lt_or_ge (s \ A).card 2 with h2 | h2
  · rcases hc : (s \ A).card with _ | n
    · exact bdry_KGen_subset
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hc))
    · have h1 : (s \ A).card = 1 := by omega
      obtain ⟨z₀, hz⟩ := Finset.card_eq_one.mp h1
      by_cases hps : p ∈ s
      · exact bdry_KGen_one_mem hp hz hps
      · exact bdry_KGen_one_notMem hp hz hps
  · exact bdry_KGen_two hp h2

/-- ∂ ∘ K = K ∘ ∂: `Kmap A p` is a chain map. -/
theorem bdry_Kmap (A : Finset V) {p : V} (hp : p ∈ A) (M : Chain V) :
    bdry (Kmap A p M) = Kmap A p (bdry M) := by
  induction M using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, ← map_add]
  | single s c =>
    rw [Kmap_single, map_smul, bdry_single, map_smul, bdry_KGen A hp s]

/-! ## Norm accounting for K -/

lemma nrm_sum_le {α : Type*} (t : Finset α) (f : α → Chain V) :
    nrm (∑ i ∈ t, f i) ≤ ∑ i ∈ t, nrm (f i) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact le_trans (nrm_add_le _ _) (by omega)

lemma nrm_smul (c : ℤ) (M : Chain V) : nrm (c • M) = c.natAbs * nrm M := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [nrm, nrm, Finsupp.support_smul_eq hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Finsupp.smul_apply, smul_eq_mul, Int.natAbs_mul]

lemma nrm_coneGen_le_one (p : V) (u : Finset V) : nrm (coneGen p u) ≤ 1 := by
  rw [coneGen]
  split
  · simp
  · rw [nrm_smul, nrm_single, natAbs_sgn, Int.natAbs_one, mul_one]

lemma nrm_KGen_le_one (A : Finset V) (p : V) (s : Finset V) :
    nrm (KGen A p s) ≤ 1 := by
  rw [KGen]
  split
  · rw [nrm_single, Int.natAbs_one]
  · split
    · rename_i h
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h.1
      rw [hz, Finset.sum_singleton, nrm_smul, natAbs_sgn, one_mul]
      exact nrm_coneGen_le_one p _
    · simp

lemma Kmap_eq_sum (A : Finset V) (p : V) (M : Chain V) :
    Kmap A p M = ∑ s ∈ M.support, M s • KGen A p s := by
  rw [Kmap, Finsupp.lsum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun s _ => LinearMap.toSpanSingleton_apply ..

/-- Norm accounting: `K` loses at least the mass of the killed
generators. -/
theorem nrm_Kmap_add_killed_le (A : Finset V) (p : V) (M : Chain V) :
    nrm (Kmap A p M) + nrm (M.filter (Kkills A p)) ≤ nrm M := by
  classical
  have h1 : nrm (Kmap A p M) ≤
      ∑ s ∈ M.support.filter (fun s => ¬ Kkills A p s), (M s).natAbs := by
    calc nrm (Kmap A p M) ≤ ∑ s ∈ M.support, nrm (M s • KGen A p s) := by
          rw [Kmap_eq_sum]; exact nrm_sum_le _ _
      _ = ∑ s ∈ M.support, (M s).natAbs * nrm (KGen A p s) := by
          exact Finset.sum_congr rfl fun s _ => nrm_smul _ _
      _ = (∑ s ∈ M.support.filter (fun s => Kkills A p s),
            (M s).natAbs * nrm (KGen A p s))
          + ∑ s ∈ M.support.filter (fun s => ¬ Kkills A p s),
            (M s).natAbs * nrm (KGen A p s) := by
          rw [Finset.sum_filter_add_sum_filter_not]
      _ = ∑ s ∈ M.support.filter (fun s => ¬ Kkills A p s),
            (M s).natAbs * nrm (KGen A p s) := by
          rw [Finset.sum_eq_zero (fun s hs => ?_), zero_add]
          rw [KGen_of_kills (Finset.mem_filter.mp hs).2, nrm_zero, mul_zero]
      _ ≤ ∑ s ∈ M.support.filter (fun s => ¬ Kkills A p s), (M s).natAbs := by
          refine Finset.sum_le_sum fun s _ => ?_
          calc (M s).natAbs * nrm (KGen A p s)
              ≤ (M s).natAbs * 1 :=
                Nat.mul_le_mul_left _ (nrm_KGen_le_one A p s)
            _ = (M s).natAbs := Nat.mul_one _
  have h2 : nrm (M.filter (Kkills A p)) =
      ∑ s ∈ M.support.filter (fun s => Kkills A p s), (M s).natAbs := by
    rw [nrm, Finsupp.support_filter]
    exact Finset.sum_congr rfl fun s hs => by
      rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hs).2]
  have h3 : nrm M = (∑ s ∈ M.support.filter (fun s => Kkills A p s),
      (M s).natAbs)
      + ∑ s ∈ M.support.filter (fun s => ¬ Kkills A p s), (M s).natAbs := by
    rw [nrm, Finset.sum_filter_add_sum_filter_not]
  omega

/-! ## Small-support triviality -/

/-- `C_k(W)` is trivial when `|W| < k+1`. -/
lemma eq_zero_of_supp_card_lt {W : Finset V} {k : ℕ} {M : Chain V}
    (hsupp : ∀ s ∈ M.support, s ⊆ W ∧ s.card = k) (hk : W.card < k) :
    M = 0 := by
  rw [← Finsupp.support_eq_empty]
  by_contra h
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr h
  obtain ⟨h1, h2⟩ := hsupp s hs
  have := Finset.card_le_card h1
  omega

/-- `Z_{k-1}(W)` is trivial when `|W| = k ≥ 1`. -/
lemma eq_zero_of_closed_supp_card_eq {W : Finset V} {k : ℕ} (hk : 1 ≤ k)
    {M : Chain V} (hsupp : ∀ s ∈ M.support, s ⊆ W ∧ s.card = k)
    (hW : W.card = k) (hM : bdry M = 0) : M = 0 := by
  have hsub : M.support ⊆ {W} := by
    intro s hs
    obtain ⟨h1, h2⟩ := hsupp s hs
    rw [Finset.mem_singleton]
    exact Finset.eq_of_subset_of_card_le h1 (by omega)
  have hMeq : M = Finsupp.single W (M W) :=
    Finsupp.support_subset_singleton.mp hsub
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
  have hbW : bdryGen W (W.erase x) = sgn x W := by
    rw [bdryGen, Finset.sum_apply']
    rw [Finset.sum_eq_single_of_mem x hx]
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, smul_eq_mul,
        mul_one]
    · intro y hy hyx
      rw [Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (fun h => hyx ((Finset.erase_inj W hy).mp h)), smul_zero]
  have h0 : (M W) * sgn x W = 0 := by
    have := DFunLike.congr_fun hM (W.erase x)
    rw [Finsupp.coe_zero, Pi.zero_apply] at this
    rw [← hbW]
    calc M W * bdryGen W (W.erase x)
        = (M W • bdryGen W) (W.erase x) := by
          rw [Finsupp.smul_apply, smul_eq_mul]
      _ = bdry M (W.erase x) := by rw [← bdry_single, ← hMeq]
      _ = 0 := this
  have hMW : M W = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h (sgn_ne_zero x W)
  rw [hMeq, hMW, Finsupp.single_zero]

end Taut
