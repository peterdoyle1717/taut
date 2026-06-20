import Taut.Splitting

/-!
# Corollary 1: rational filling foundations

Rational analogue of the integral chain machinery in `Taut/Chains.lean`.

A *rational chain* is a finitely supported `ℚ`-combination of simplices,
`QChain V := Finset V →₀ ℚ`.  We mirror the integral boundary and cone
operators (`Qbdry`, `Qcone`), introduce the real-valued L¹ norm `Qnrm`
(real-valued so the filling-volume infimum lives in a conditionally complete
order), the achievable-norm set `QvolSet`, the rational filling volume `Qvol`,
order-optimal (taut) rational fillings `IsQTaut`, and the predicate
`QChain.IsIntegral` (every coefficient is an integer).

The first bounded target is `exists_nat_smul_integral`: every rational chain
becomes integral after scaling by a positive natural number (the lcm of its
coefficients' denominators).
-/

namespace Taut

open Finset

variable {V : Type*} [LinearOrder V]

/-! ## Rational chains and operators -/

/-- A rational chain: a finitely supported ℚ-combination of simplices. -/
abbrev QChain (V : Type*) := Finset V →₀ ℚ

/-- Boundary of one generator over ℚ (mirrors `bdryGen`). -/
noncomputable def QbdryGen (s : Finset V) : QChain V :=
  ∑ x ∈ s, (sgn x s : ℚ) • Finsupp.single (s.erase x) (1 : ℚ)

/-- The rational boundary operator. -/
noncomputable def Qbdry : QChain V →ₗ[ℚ] QChain V :=
  Finsupp.lsum ℚ fun s => LinearMap.toSpanSingleton ℚ (QChain V) (QbdryGen s)

@[simp] lemma Qbdry_single (s : Finset V) (c : ℚ) :
    Qbdry (Finsupp.single s c) = c • QbdryGen s := by
  simp [Qbdry, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- Cone of one generator over ℚ (mirrors `coneGen`). -/
noncomputable def QconeGen (x : V) (s : Finset V) : QChain V :=
  if x ∈ s then 0 else (sgn x s : ℚ) • Finsupp.single (insert x s) (1 : ℚ)

/-- The rational cone operator. -/
noncomputable def Qcone (x : V) : QChain V →ₗ[ℚ] QChain V :=
  Finsupp.lsum ℚ fun s => LinearMap.toSpanSingleton ℚ (QChain V) (QconeGen x s)

@[simp] lemma Qcone_single (x : V) (s : Finset V) (c : ℚ) :
    Qcone x (Finsupp.single s c) = c • QconeGen x s := by
  simp [Qcone, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-! ## Norm, volume, tautness, integrality -/

/-- The rational L¹ norm (ℝ-valued, so `sInf` lives in a conditionally complete
order). -/
noncomputable def Qnrm (M : QChain V) : ℝ := ∑ s ∈ M.support, |(M s : ℝ)|

/-- The set of achievable filling norms of `X`. -/
noncomputable def QvolSet (X : QChain V) : Set ℝ :=
  {r | ∃ M : QChain V, Qbdry M = X ∧ Qnrm M = r}

/-- The rational filling volume. -/
noncomputable def Qvol (X : QChain V) : ℝ := sInf (QvolSet X)

/-- `M` is a *taut* (order-optimal) rational filling: it minimises `Qnrm` among
all fillings of its boundary.  (Order-optimal, NOT `Qnrm = Qvol` — this avoids
needing rational minimisers to exist.) -/
def IsQTaut (M : QChain V) : Prop := ∀ N : QChain V, Qbdry N = Qbdry M → Qnrm M ≤ Qnrm N

/-- A rational chain is *integral* if every coefficient is an integer. -/
def QChain.IsIntegral (M : QChain V) : Prop := ∀ s, ∃ z : ℤ, M s = (z : ℚ)

/-! ## Clearing denominators -/

/-- **Clearing denominators.** Every rational chain becomes integral after
scaling by a positive natural number (the lcm of its coefficients'
denominators). -/
lemma exists_nat_smul_integral (M : QChain V) :
    ∃ q : ℕ, 0 < q ∧ QChain.IsIntegral ((q : ℚ) • M) := by
  classical
  refine ⟨M.support.lcm (fun s => (M s).den), ?_, ?_⟩
  · -- positivity: the lcm of nonzero denominators is nonzero.
    refine Nat.pos_of_ne_zero ?_
    rw [Finset.lcm_ne_zero_iff]
    intro s _
    exact (M s).den_ne_zero
  · -- integrality, coefficient by coefficient.
    intro s
    rw [Finsupp.smul_apply, smul_eq_mul]
    by_cases hs : s ∈ M.support
    · -- denominator of `M s` divides the lcm; clear it.
      set q : ℕ := M.support.lcm (fun s => (M s).den) with hq
      have hdvd : (M s).den ∣ q := Finset.dvd_lcm hs
      refine ⟨((q / (M s).den : ℕ) : ℤ) * (M s).num, ?_⟩
      have hden : ((M s).den : ℚ) ≠ 0 := by exact_mod_cast (M s).den_ne_zero
      have hcancel : (q / (M s).den) * (M s).den = q := Nat.div_mul_cancel hdvd
      have hqcast : (q : ℚ) = ((q / (M s).den : ℕ) : ℚ) * ((M s).den : ℚ) := by
        rw [← Nat.cast_mul, hcancel]
      have hmul : ((M s).den : ℚ) * M s = ((M s).num : ℚ) := by
        have h := Rat.num_div_den (M s)
        rw [div_eq_iff hden] at h
        rw [h, mul_comm]
      rw [hqcast, mul_assoc, hmul, Int.cast_mul, Int.cast_natCast]
    · -- outside the support the coefficient is already `0`.
      rw [Finsupp.notMem_support_iff.mp hs, mul_zero]
      exact ⟨0, by push_cast; ring⟩

/-! ## The ℤ ↔ ℚ bridge -/

/-- Cast an integer chain to a rational chain (coefficientwise `Int.cast`). -/
noncomputable def intToQChain (M : Chain V) : QChain V :=
  Finsupp.mapRange (fun z : ℤ => (z : ℚ)) (by simp) M

omit [LinearOrder V] in
@[simp] lemma intToQChain_apply (M : Chain V) (s : Finset V) :
    intToQChain M s = (M s : ℚ) := by
  simp only [intToQChain, Finsupp.mapRange_apply]

omit [LinearOrder V] in
lemma intToQChain_add (M N : Chain V) :
    intToQChain (M + N) = intToQChain M + intToQChain N := by
  ext s; simp

omit [LinearOrder V] in
lemma intToQChain_smul (z : ℤ) (M : Chain V) :
    intToQChain (z • M) = (z : ℚ) • intToQChain M := by
  ext s
  simp only [intToQChain_apply, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul]

@[simp] lemma intToQChain_single (s : Finset V) (c : ℤ) :
    intToQChain (Finsupp.single s c) = Finsupp.single s (c : ℚ) := by
  ext t
  by_cases h : t = s
  · subst h; simp
  · simp [h]

/-- The rational boundary of a cast generator equals the cast of the integer
boundary generator. -/
lemma QbdryGen_eq_intToQChain_bdryGen (s : Finset V) :
    QbdryGen s = intToQChain (bdryGen s) := by
  ext t
  rw [QbdryGen, bdryGen, intToQChain_apply, Finsupp.finset_sum_apply,
    Finsupp.finset_sum_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
    Int.cast_mul]
  congr 1
  by_cases h : t = s.erase x
  · subst h; simp
  · simp [h]

/-- The boundary operator commutes with the integer→rational cast. -/
lemma Qbdry_intToQChain (M : Chain V) :
    Qbdry (intToQChain M) = intToQChain (bdry M) := by
  induction M using Finsupp.induction with
  | zero => simp [intToQChain]
  | single_add s c M hs hc ih =>
      rw [map_add, intToQChain_add, map_add, ih, intToQChain_add,
        intToQChain_single, Qbdry_single, bdry_single, intToQChain_smul,
        QbdryGen_eq_intToQChain_bdryGen]

omit [LinearOrder V] in
/-- The rational L¹ norm of a cast chain equals the integer L¹ norm. -/
lemma Qnrm_intToQChain (M : Chain V) : Qnrm (intToQChain M) = (nrm M : ℝ) := by
  have hsupp : (intToQChain M).support = M.support := by
    rw [intToQChain]
    exact Finsupp.support_mapRange_of_injective (by simp) M Int.cast_injective
  rw [Qnrm, hsupp, nrm, Nat.cast_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [intToQChain_apply, Rat.cast_intCast, Nat.cast_natAbs, Int.cast_abs]

omit [LinearOrder V] in
/-- The support of a positive natural scaling of a rational chain is unchanged. -/
lemma support_nat_smul_of_pos {q : ℕ} (hq : 0 < q) (M : QChain V) :
    ((q : ℚ) • M).support = M.support := by
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  ext s
  simp only [Finsupp.mem_support_iff, Finsupp.smul_apply, smul_eq_mul, ne_eq,
    mul_eq_zero, hqne, false_or]

/-- Recover the integer chain underlying an integral rational chain (the
coefficient `M s` is an integer, so `⌊M s⌋` recovers it). -/
noncomputable def QChain.toInt (M : QChain V) (_hM : QChain.IsIntegral M) :
    Chain V :=
  Finsupp.mapRange (fun r : ℚ => ⌊r⌋) Int.floor_zero M

omit [LinearOrder V] in
@[simp] lemma intToQChain_toInt (M : QChain V) (hM : QChain.IsIntegral M) :
    intToQChain (QChain.toInt M hM) = M := by
  ext s
  rw [intToQChain_apply, QChain.toInt, Finsupp.mapRange_apply]
  obtain ⟨z, hz⟩ := hM s
  rw [hz, Int.floor_intCast]

/-- **The integer bridge.** If `M` minimises `nrm` among all fillings of its
own boundary (order-optimal), then `M` is taut (`nrm M = Zvol (bdry M)`). -/
lemma IsTaut.of_forall_nrm_le {M : Chain V}
    (h : ∀ N : Chain V, bdry N = bdry M → nrm M ≤ nrm N) : IsTaut M := by
  obtain ⟨W, hW, hWn⟩ := exists_optimal_fill M
  have hle : nrm M ≤ Zvol (bdry M) := hWn ▸ h W hW
  exact le_antisymm hle (Zvol_le rfl)

end Taut
