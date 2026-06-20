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

end Taut
