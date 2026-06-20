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

/-! ## Scaling the rational norm and forward tautness transfer -/

omit [LinearOrder V] in
/-- Scaling a rational chain by `c` scales its L¹ norm by `|c|`. -/
lemma Qnrm_smul (c : ℚ) (M : QChain V) : Qnrm (c • M) = |(c : ℝ)| * Qnrm M := by
  classical
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [zero_smul, Rat.cast_zero, abs_zero, zero_mul, Qnrm,
      Finsupp.support_zero, Finset.sum_empty]
  · -- `c ≠ 0`: the support is preserved.
    have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hsupp : (c • M).support = M.support := by
      ext s
      simp only [Finsupp.mem_support_iff, Finsupp.smul_apply, smul_eq_mul, ne_eq,
        mul_eq_zero, hc, false_or]
    rw [Qnrm, Qnrm, hsupp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
    push_cast
    rw [abs_mul]

omit [LinearOrder V] in
/-- Scaling a rational chain by a natural number `q` scales its L¹ norm by `q`. -/
lemma Qnrm_nat_smul (q : ℕ) (M : QChain V) : Qnrm ((q : ℚ) • M) = (q : ℝ) * Qnrm M := by
  rw [Qnrm_smul]
  congr 1
  rw [Rat.cast_natCast, abs_of_nonneg (by positivity)]

/-- **Forward tautness transfer (Cor 1, step 5).** If a rational chain `M` is
taut and `(q : ℚ) • M` is integral (for `0 < q`), then the underlying integer
chain `QChain.toInt ((q : ℚ) • M)` is taut. -/
lemma IsQTaut.toInt_nat_smul {M : QChain V} (hMt : IsQTaut M) {q : ℕ} (hq : 0 < q)
    (hM : QChain.IsIntegral ((q : ℚ) • M)) :
    IsTaut (QChain.toInt ((q : ℚ) • M) hM) := by
  classical
  set K : Chain V := QChain.toInt ((q : ℚ) • M) hM with hK
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- `intToQChain K = (q : ℚ) • M`.
  have hKQ : intToQChain K = (q : ℚ) • M := intToQChain_toInt _ hM
  apply IsTaut.of_forall_nrm_le
  intro N hN
  -- Reduce to the real inequality.
  rw [← Nat.cast_le (α := ℝ)]
  -- `(nrm K : ℝ) = (q : ℝ) * Qnrm M`.
  have hKn : (nrm K : ℝ) = (q : ℝ) * Qnrm M := by
    rw [← Qnrm_intToQChain, hKQ, Qnrm_nat_smul]
  -- The ℚ-competitor for `M`.
  set Nq : QChain V := ((q : ℚ)⁻¹) • intToQChain N with hNq
  -- `Qbdry Nq = Qbdry M`.
  have hbdry : Qbdry Nq = Qbdry M := by
    have h1 : Qbdry (intToQChain N) = (q : ℚ) • Qbdry M := by
      rw [Qbdry_intToQChain, hN, ← Qbdry_intToQChain, hKQ, map_smul]
    rw [hNq, map_smul, h1, smul_smul, inv_mul_cancel₀ hqQ, one_smul]
  -- Tautness of `M` gives `Qnrm M ≤ Qnrm Nq`.
  have hcomp : Qnrm M ≤ Qnrm Nq := hMt Nq hbdry
  -- `Qnrm Nq = (q : ℝ)⁻¹ * (nrm N : ℝ)`.
  have hNqn : Qnrm Nq = (q : ℝ)⁻¹ * (nrm N : ℝ) := by
    rw [hNq, Qnrm_smul, Qnrm_intToQChain, Rat.cast_inv, Rat.cast_natCast,
      abs_of_nonneg (by positivity)]
  -- Assemble.
  rw [hNqn] at hcomp
  have key : (q : ℝ) * Qnrm M ≤ (nrm N : ℝ) := by
    have := mul_le_mul_of_nonneg_left hcomp hqRpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hqR, one_mul] at this
  rw [hKn]
  exact key

/-! ## Cast / filter / support / injectivity and `Qnrm` algebra for splitting

The first bounded sub-target of Corollary 1, step 6: the elementary cast,
filter, support, and injectivity facts for `intToQChain`, together with the
L¹-norm triangle inequality and the filter-partition additivity of `Qnrm`. -/

omit [LinearOrder V] in
@[simp] lemma intToQChain_zero : intToQChain (0 : Chain V) = 0 := by
  ext s; simp [intToQChain_apply]

omit [LinearOrder V] in
@[simp] lemma support_intToQChain (K : Chain V) :
    (intToQChain K).support = K.support := by
  rw [intToQChain]
  exact Finsupp.support_mapRange_of_injective (by simp) K Int.cast_injective

omit [LinearOrder V] in
lemma intToQChain_injective :
    Function.Injective (intToQChain : Chain V → QChain V) := by
  intro M N h
  ext s
  have hs : intToQChain M s = intToQChain N s := by rw [h]
  rw [intToQChain_apply, intToQChain_apply] at hs
  exact_mod_cast hs

omit [LinearOrder V] in
@[simp] lemma intToQChain_filter (K : Chain V) (p : Finset V → Prop)
    [DecidablePred p] :
    intToQChain (K.filter p) = (intToQChain K).filter p := by
  ext s
  rw [intToQChain_apply, Finsupp.filter_apply, Finsupp.filter_apply,
    intToQChain_apply]
  by_cases hp : p s
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, Int.cast_zero]

omit [LinearOrder V] in
@[simp] lemma QChain.filter_smul (c : ℚ) (M : QChain V) (p : Finset V → Prop)
    [DecidablePred p] :
    (c • M).filter p = c • (M.filter p) := by
  ext s
  rw [Finsupp.filter_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.filter_apply, smul_eq_mul, smul_eq_mul]
  by_cases hp : p s
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, mul_zero]

omit [LinearOrder V] in
/-- L¹ triangle inequality for `Qnrm`. -/
lemma Qnrm_add_le (M N : QChain V) : Qnrm (M + N) ≤ Qnrm M + Qnrm N := by
  classical
  -- The common index set `M.support ∪ N.support` contains `(M + N).support`.
  set s : Finset (Finset V) := M.support ∪ N.support with hs
  have hsubMN : (M + N).support ⊆ s := Finsupp.support_add
  have hsubM : M.support ⊆ s := Finset.subset_union_left
  have hsubN : N.support ⊆ s := Finset.subset_union_right
  -- Step 1: enlarge the index set of `Qnrm (M + N)` to `s`.
  have h1 : Qnrm (M + N) ≤ ∑ t ∈ s, |((M + N) t : ℝ)| := by
    rw [Qnrm]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubMN
      (fun t _ _ => abs_nonneg _)
  -- Step 2: termwise triangle inequality and distribute the sum.
  have h2 : ∑ t ∈ s, |((M + N) t : ℝ)| ≤
      (∑ t ∈ s, |(M t : ℝ)|) + ∑ t ∈ s, |(N t : ℝ)| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [Finsupp.add_apply]
    push_cast
    exact abs_add_le _ _
  -- Step 3: the enlarged single-chain sums recover `Qnrm M` and `Qnrm N`.
  have hM : ∑ t ∈ s, |(M t : ℝ)| = Qnrm M := by
    rw [Qnrm]
    refine (Finset.sum_subset hsubM fun t _ ht => ?_).symm
    rw [Finsupp.notMem_support_iff.mp ht, Rat.cast_zero, abs_zero]
  have hN : ∑ t ∈ s, |(N t : ℝ)| = Qnrm N := by
    rw [Qnrm]
    refine (Finset.sum_subset hsubN fun t _ ht => ?_).symm
    rw [Finsupp.notMem_support_iff.mp ht, Rat.cast_zero, abs_zero]
  calc Qnrm (M + N) ≤ ∑ t ∈ s, |((M + N) t : ℝ)| := h1
    _ ≤ (∑ t ∈ s, |(M t : ℝ)|) + ∑ t ∈ s, |(N t : ℝ)| := h2
    _ = Qnrm M + Qnrm N := by rw [hM, hN]

omit [LinearOrder V] in
/-- Splitting a chain by a predicate splits its `Qnrm` additively. -/
lemma Qnrm_filter_add_Qnrm_filter_neg (p : Finset V → Prop) [DecidablePred p]
    (M : QChain V) :
    Qnrm (M.filter p) + Qnrm (M.filter fun s => ¬ p s) = Qnrm M := by
  classical
  -- On the `p`-part, the coefficient is `M s` exactly where `p s` holds.
  have hp : Qnrm (M.filter p) = ∑ s ∈ M.support.filter p, |(M s : ℝ)| := by
    rw [Qnrm, Finsupp.support_filter]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hs).2]
  -- Likewise on the `¬p`-part.
  have hnp : Qnrm (M.filter fun s => ¬ p s)
      = ∑ s ∈ M.support.filter (fun s => ¬ p s), |(M s : ℝ)| := by
    rw [Qnrm, Finsupp.support_filter]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hs).2]
  rw [hp, hnp, Qnrm,
    Finset.sum_filter_add_sum_filter_not M.support p (fun s => |(M s : ℝ)|)]

/-! ## Common clearing of denominators across several chains -/

omit [LinearOrder V] in
/-- If `(q : ℚ) • M` is integral, then so is `((r * q : ℕ) : ℚ) • M` for any `r`. -/
lemma QChain.IsIntegral.nat_mul_smul {M : QChain V} {q : ℕ} (r : ℕ)
    (h : QChain.IsIntegral ((q : ℚ) • M)) :
    QChain.IsIntegral (((r * q : ℕ) : ℚ) • M) := by
  intro s
  obtain ⟨z, hz⟩ := h s
  refine ⟨r * z, ?_⟩
  have hrw : (((r * q : ℕ) : ℚ) • M) s = (r : ℚ) * (((q : ℚ) • M) s) := by
    simp only [Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hrw, hz]
  push_cast
  ring

/-- **Common clearing of denominators.** Three rational chains become
simultaneously integral after scaling by a single positive natural number. -/
lemma exists_nat_smul_integral_three (M X Y : QChain V) :
    ∃ q : ℕ, 0 < q ∧ QChain.IsIntegral ((q : ℚ) • M) ∧
      QChain.IsIntegral ((q : ℚ) • X) ∧ QChain.IsIntegral ((q : ℚ) • Y) := by
  obtain ⟨qM, hqM, hM⟩ := exists_nat_smul_integral M
  obtain ⟨qX, hqX, hX⟩ := exists_nat_smul_integral X
  obtain ⟨qY, hqY, hY⟩ := exists_nat_smul_integral Y
  refine ⟨qM * qX * qY, by positivity, ?_, ?_, ?_⟩
  · have := hM.nat_mul_smul (qX * qY)
    rwa [show qX * qY * qM = qM * qX * qY by ring] at this
  · have := hX.nat_mul_smul (qM * qY)
    rwa [show qM * qY * qX = qM * qX * qY by ring] at this
  · have := hY.nat_mul_smul (qM * qX)
    rwa [show qM * qX * qY = qM * qX * qY from rfl] at this

/-! ## The rational splitting endpoint -/

/-- **Rational splitting (Corollary 1, step 6 endpoint).** A taut rational
filling `M` of a sum `X + Y` (with `X` supported on `A`, `Y` on `B`, both cycles,
and a small intersection) splits along the predicate `· ⊆ A` into a taut filling
of `X` and a taut filling of `Y`.  Proved by clearing denominators to the
committed integer endpoint `IsTaut.splits_full` and dividing back. -/
theorem IsQTaut.splits_full {V : Type*} [LinearOrder V] [Infinite V]
    {A B : Finset V} {n : ℕ} (hn : 2 ≤ n) (hC : (A ∩ B).card ≤ n + 1)
    {X Y : QChain V}
    (hX : ∀ s ∈ X.support, s ⊆ A ∧ s.card = n + 1)
    (hY : ∀ s ∈ Y.support, s ⊆ B ∧ s.card = n + 1)
    (hXc : Qbdry X = 0) (hYc : Qbdry Y = 0)
    {M : QChain V} (hMt : IsQTaut M) (hM1 : Qbdry M = X + Y) :
    Qbdry (M.filter fun t => t ⊆ A) = X ∧ Qbdry (M.filter fun t => ¬ t ⊆ A) = Y ∧
    IsQTaut (M.filter fun t => t ⊆ A) ∧ IsQTaut (M.filter fun t => ¬ t ⊆ A) ∧
    M.filter (fun t => t ⊆ A) + M.filter (fun t => ¬ t ⊆ A) = M := by
  classical
  -- Step 1: clear denominators of M, X, Y simultaneously.
  obtain ⟨q, hq, hMint, hXint, hYint⟩ := exists_nat_smul_integral_three M X Y
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  -- Step 2: the underlying integer chains.
  set K : Chain V := QChain.toInt ((q : ℚ) • M) hMint with hKdef
  set KX : Chain V := QChain.toInt ((q : ℚ) • X) hXint with hKXdef
  set KY : Chain V := QChain.toInt ((q : ℚ) • Y) hYint with hKYdef
  have hKM : intToQChain K = (q : ℚ) • M := intToQChain_toInt _ hMint
  have hKX : intToQChain KX = (q : ℚ) • X := intToQChain_toInt _ hXint
  have hKY : intToQChain KY = (q : ℚ) • Y := intToQChain_toInt _ hYint
  -- Step 4: KX, KY are integer cycles.
  have hKXc : bdry KX = 0 := by
    apply intToQChain_injective
    rw [intToQChain_zero, ← Qbdry_intToQChain, hKX, map_smul, hXc, smul_zero]
  have hKYc : bdry KY = 0 := by
    apply intToQChain_injective
    rw [intToQChain_zero, ← Qbdry_intToQChain, hKY, map_smul, hYc, smul_zero]
  -- Step 5: bdry K = KX + KY.
  have hKbdry : bdry K = KX + KY := by
    apply intToQChain_injective
    rw [← Qbdry_intToQChain, hKM, map_smul, hM1, smul_add, intToQChain_add, hKX,
      hKY]
  -- Step 6: support transfer for the side hypotheses.
  have hKXsupp : KX.support = X.support := by
    rw [← support_intToQChain KX, hKX, support_nat_smul_of_pos hq]
  have hKYsupp : KY.support = Y.support := by
    rw [← support_intToQChain KY, hKY, support_nat_smul_of_pos hq]
  have hX' : ∀ s ∈ KX.support, s ⊆ A ∧ s.card = n + 1 := by
    rw [hKXsupp]; exact hX
  have hY' : ∀ s ∈ KY.support, s ⊆ B ∧ s.card = n + 1 := by
    rw [hKYsupp]; exact hY
  -- Step 7: K is a taut integer filling.
  have hKtaut : IsTaut K := IsQTaut.toInt_nat_smul hMt hq hMint
  -- Step 8: invoke the integer endpoint.
  obtain ⟨hbA, hbB, _, _, _⟩ :=
    IsTaut.splits_full hn hC hX' hY' hKXc hKYc hKtaut hKbdry
  -- Step 9: boundary equalities, divided back.
  have hQbA : Qbdry (M.filter fun t => t ⊆ A) = X := by
    apply smul_right_injective (QChain V) hqQ
    show (q : ℚ) • Qbdry (M.filter fun t => t ⊆ A) = (q : ℚ) • X
    rw [← map_smul, ← QChain.filter_smul, ← hKM, ← intToQChain_filter,
      Qbdry_intToQChain, hbA, hKX]
  have hQbB : Qbdry (M.filter fun t => ¬ t ⊆ A) = Y := by
    apply smul_right_injective (QChain V) hqQ
    show (q : ℚ) • Qbdry (M.filter fun t => ¬ t ⊆ A) = (q : ℚ) • Y
    rw [← map_smul, ← QChain.filter_smul, ← hKM, ← intToQChain_filter,
      Qbdry_intToQChain, hbB, hKY]
  -- Step 10: the filter partition recovers M.
  have hMsum : M.filter (fun t => t ⊆ A) + M.filter (fun t => ¬ t ⊆ A) = M :=
    Finsupp.filter_pos_add_filter_neg M _
  -- Step 11: tautness of each piece, from global tautness of M (no reverse
  -- transfer).
  set MA : QChain V := M.filter (fun t => t ⊆ A) with hMAdef
  set MB : QChain V := M.filter (fun t => ¬ t ⊆ A) with hMBdef
  have hnorm : Qnrm MA + Qnrm MB = Qnrm M :=
    Qnrm_filter_add_Qnrm_filter_neg _ M
  have hMtaut_A : IsQTaut MA := by
    intro N hN
    have hbdryN : Qbdry (N + MB) = Qbdry M := by
      rw [map_add, hN, hMAdef, hMBdef, hQbA, hQbB, hM1]
    have hle : Qnrm M ≤ Qnrm (N + MB) := hMt (N + MB) hbdryN
    have htri : Qnrm (N + MB) ≤ Qnrm N + Qnrm MB := Qnrm_add_le N MB
    have : Qnrm M ≤ Qnrm N + Qnrm MB := le_trans hle htri
    rw [← hnorm] at this
    exact le_of_add_le_add_right this
  have hMtaut_B : IsQTaut MB := by
    intro N hN
    have hbdryN : Qbdry (MA + N) = Qbdry M := by
      rw [map_add, hN, hMAdef, hMBdef, hQbA, hQbB, hM1]
    have hle : Qnrm M ≤ Qnrm (MA + N) := hMt (MA + N) hbdryN
    have htri : Qnrm (MA + N) ≤ Qnrm MA + Qnrm N := Qnrm_add_le MA N
    have : Qnrm M ≤ Qnrm MA + Qnrm N := le_trans hle htri
    rw [← hnorm] at this
    exact le_of_add_le_add_left this
  exact ⟨hQbA, hQbB, hMtaut_A, hMtaut_B, hMsum⟩

end Taut
