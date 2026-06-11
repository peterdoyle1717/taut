import Mathlib

/-!
# Simplicial chains on a full simplex

Foundation for formalizing Doyle–Ellison–Wang, "Taut fillings".

We work with the AUGMENTED, dimension-mixed simplicial chain group of the
full simplex on a linearly ordered vertex type `V`: a chain is a finitely
supported function `Finset V →₀ ℤ`, a generator being an unoriented simplex
`s : Finset V` carrying its canonical orientation (vertices in increasing
order).  `∅` is the (−1)-simplex; its presence makes the contracting
homotopy `∂ ∘ cone + cone ∘ ∂ = id` exact and global, which is what gives
filling-existence for closed chains.

Sign bookkeeping is via `cnt x s = #{y ∈ s | y < x}` and
`sgn x s = (-1) ^ cnt x s`: the `i`-th vertex of a sorted simplex has
exactly `i` smaller members, so `sgn` is the classical `(-1)^i`.

Main definitions: `bdry` (boundary), `cone`, `lk` (link/strip), `nbhd`
(restriction to simplices containing a vertex), `vert`, `nrm` (L¹ norm),
`deg`, `SubChain`.

Main results (the validation invariants of the G1 spec):
* `bdry_bdry` : ∂∂ = 0;
* `bdry_cone_add_cone_bdry` : ∂(cone x M) + cone x (∂M) = M;
* `cone_lk` : cone x (lk x M) = nbhd x M;
* `nrm_cone_add_deg` : nrm (cone x M) + deg x M = nrm M.
-/

namespace Taut

variable {V : Type*} [LinearOrder V]

/-- Augmented, dimension-mixed simplicial chains on the full simplex with
vertex type `V`. -/
abbrev Chain (V : Type*) := Finset V →₀ ℤ

/-! ## Counting below, and signs -/

/-- The number of vertices of `s` strictly below `x`: the position `x` takes
(or would take) in the sorted listing of `insert x s`. -/
def cnt (x : V) (s : Finset V) : ℕ := (s.filter (· < x)).card

/-- The sign `(-1) ^ cnt x s`: the sign of the permutation sorting `x`
into `s`. -/
def sgn (x : V) (s : Finset V) : ℤ := (-1) ^ cnt x s

lemma sgn_mul_self (x : V) (s : Finset V) : sgn x s * sgn x s = 1 := by
  simp only [sgn, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

lemma natAbs_sgn (x : V) (s : Finset V) : (sgn x s).natAbs = 1 := by
  simp [sgn, Int.natAbs_pow]

lemma sgn_smul_sgn_smul (x : V) (s : Finset V) (M : Chain V) :
    sgn x s • sgn x s • M = M := by
  rw [smul_smul, sgn_mul_self, one_smul]

lemma cnt_insert (x z : V) (t : Finset V) (hz : z ∉ t) :
    cnt x (insert z t) = cnt x t + if z < x then 1 else 0 := by
  unfold cnt
  rw [Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (fun h => hz (Finset.mem_of_mem_filter z h))]
  · rw [add_zero]

lemma cnt_self_insert (x : V) (t : Finset V) (hx : x ∉ t) :
    cnt x (insert x t) = cnt x t := by
  rw [cnt_insert x x t hx, if_neg (lt_irrefl x), add_zero]

lemma sgn_insert (x z : V) (t : Finset V) (hz : z ∉ t) :
    sgn x (insert z t) = (if z < x then -1 else 1) * sgn x t := by
  rw [sgn, sgn, cnt_insert x z t hz]
  split <;> simp [pow_add]

lemma sgn_self_insert (x : V) (t : Finset V) (hx : x ∉ t) :
    sgn x (insert x t) = sgn x t := by
  rw [sgn, sgn, cnt_self_insert x t hx]

/-- Express the sign on `s` via the sign on `s.erase z`. -/
lemma sgn_eq_erase (x z : V) (s : Finset V) (hz : z ∈ s) :
    sgn x s = (if z < x then -1 else 1) * sgn x (s.erase z) := by
  conv_lhs => rw [← Finset.insert_erase hz]
  exact sgn_insert x z _ (Finset.notMem_erase z s)

lemma sgn_erase_self (x : V) (s : Finset V) : sgn x (s.erase x) = sgn x s := by
  by_cases hx : x ∈ s
  · rw [sgn_eq_erase x x s hx, if_neg (lt_irrefl x), one_mul]
  · rw [Finset.erase_eq_of_notMem hx]

/-- The fundamental parity fact: for `x ≠ z` exactly one of the two
order-comparisons fires. -/
lemma if_lt_mul_if_lt {x z : V} (h : x ≠ z) :
    (if z < x then (-1 : ℤ) else 1) * (if x < z then -1 else 1) = -1 := by
  rcases h.lt_or_gt with h' | h'
  · rw [if_neg (asymm h'), if_pos h', one_mul]
  · rw [if_pos h', if_neg (asymm h'), mul_one]

/-- Sign cancellation for `∂∂ = 0`: removing `x` then `z` versus removing
`z` then `x`. -/
lemma sgn_erase_cancel {x z : V} {s : Finset V} (hx : x ∈ s) (hz : z ∈ s)
    (hne : x ≠ z) :
    sgn x s * sgn z (s.erase x) = -(sgn z s * sgn x (s.erase z)) := by
  rw [sgn_eq_erase x z s hz, sgn_eq_erase z x s hx]
  rcases hne.lt_or_gt with h' | h'
  · rw [if_neg (asymm h'), if_pos h']; ring
  · rw [if_pos h', if_neg (asymm h')]; ring

/-- Sign cancellation for the homotopy identity: adjoining `x` versus
removing `z`, for `x ∉ s`, `z ∈ s`. -/
lemma sgn_insert_cancel {x z : V} {s : Finset V} (hx : x ∉ s) (hz : z ∈ s) :
    sgn x s * sgn z (insert x s) = -(sgn z s * sgn x (s.erase z)) := by
  have hne : x ≠ z := fun h => hx (h ▸ hz)
  rw [sgn_insert z x s hx, sgn_eq_erase x z s hz]
  rcases hne.lt_or_gt with h' | h'
  · rw [if_pos h', if_neg (asymm h')]; ring
  · rw [if_neg (asymm h'), if_pos h']; ring

/-! ## The operators -/

/-- Boundary of one generator: the alternating sum of its facets. -/
noncomputable def bdryGen (s : Finset V) : Chain V :=
  ∑ x ∈ s, sgn x s • Finsupp.single (s.erase x) 1

/-- The boundary operator. -/
noncomputable def bdry : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.lsum ℤ fun s => LinearMap.toSpanSingleton ℤ (Chain V) (bdryGen s)

@[simp] lemma bdry_single (s : Finset V) (c : ℤ) :
    bdry (Finsupp.single s c) = c • bdryGen s := by
  simp [bdry, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- Cone of one generator: adjoin `x`, with the sign that sorts `x` into
place; kill simplices already containing `x`. -/
noncomputable def coneGen (x : V) (s : Finset V) : Chain V :=
  if x ∈ s then 0 else sgn x s • Finsupp.single (insert x s) 1

/-- The cone operator `M ↦ x ∗ M`. -/
noncomputable def cone (x : V) : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.lsum ℤ fun s => LinearMap.toSpanSingleton ℤ (Chain V) (coneGen x s)

@[simp] lemma cone_single (x : V) (s : Finset V) (c : ℤ) :
    cone x (Finsupp.single s c) = c • coneGen x s := by
  simp [cone, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- Link (strip) of one generator: remove `x`, with the matching sign;
kill simplices not containing `x`. -/
noncomputable def lkGen (x : V) (s : Finset V) : Chain V :=
  if x ∈ s then sgn x s • Finsupp.single (s.erase x) 1 else 0

/-- The link/strip operator: inverse to `cone x` on simplices containing
`x`. -/
noncomputable def lk (x : V) : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.lsum ℤ fun s => LinearMap.toSpanSingleton ℤ (Chain V) (lkGen x s)

@[simp] lemma lk_single (x : V) (s : Finset V) (c : ℤ) :
    lk x (Finsupp.single s c) = c • lkGen x s := by
  simp [lk, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- Restriction of a chain to the simplices containing `x`
(the paper's `nbhd`). -/
noncomputable def nbhd (x : V) (M : Chain V) : Chain V :=
  M.filter (fun s => x ∈ s)

@[simp] lemma nbhd_apply (x : V) (M : Chain V) (s : Finset V) :
    nbhd x M s = if x ∈ s then M s else 0 := by
  simp [nbhd, Finsupp.filter_apply]

lemma nbhd_add (x : V) (M N : Chain V) :
    nbhd x (M + N) = nbhd x M + nbhd x N := by
  ext s; simp only [nbhd_apply, Finsupp.add_apply]; split <;> simp

lemma nbhd_single_of_mem {x : V} {s : Finset V} (h : x ∈ s) (c : ℤ) :
    nbhd x (Finsupp.single s c) = Finsupp.single s c :=
  Finsupp.filter_single_of_pos (p := fun u => x ∈ u) h

lemma nbhd_single_of_notMem {x : V} {s : Finset V} (h : x ∉ s) (c : ℤ) :
    nbhd x (Finsupp.single s c) = 0 :=
  Finsupp.filter_single_of_neg (p := fun u => x ∈ u) h

@[simp] lemma nbhd_zero (x : V) : nbhd x (0 : Chain V) = 0 := by
  rw [nbhd, Finsupp.filter_zero]

/-- The vertex set of a chain. -/
noncomputable def vert (M : Chain V) : Finset V := M.support.biUnion id

lemma mem_vert {x : V} {M : Chain V} :
    x ∈ vert M ↔ ∃ s ∈ M.support, x ∈ s := by
  simp [vert]

lemma nbhd_eq_zero_iff {x : V} {M : Chain V} :
    nbhd x M = 0 ↔ x ∉ vert M := by
  constructor
  · intro h hx
    obtain ⟨s, hs, hxs⟩ := mem_vert.mp hx
    have := DFunLike.congr_fun h s
    rw [nbhd_apply, if_pos hxs] at this
    exact Finsupp.mem_support_iff.mp hs (by simpa using this)
  · intro h
    ext s
    rw [nbhd_apply]
    split
    · by_contra hMs
      exact h (mem_vert.mpr ⟨s, Finsupp.mem_support_iff.mpr (by simpa using hMs), by assumption⟩)
    · rfl

/-- Pointwise formula for the cone. -/
lemma cone_apply (x : V) (M : Chain V) (u : Finset V) :
    cone x M u = if x ∈ u then sgn x (u.erase x) * M (u.erase x) else 0 := by
  induction M using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]
    split <;> ring
  | single s c =>
    rw [cone_single, coneGen]
    split
    · -- x ∈ s : cone kills it, and `u.erase x ≠ s` since `x ∉ u.erase x`
      rename_i hxs
      simp only [smul_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply]
      have hs : s ≠ u.erase x := fun h => (Finset.notMem_erase x u) (h ▸ hxs)
      rw [if_neg hs]
      split <;> simp
    · rename_i hxs
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hxu : x ∈ u
      · by_cases he : insert x s = u
        · have hs : s = u.erase x := by rw [← he, Finset.erase_insert hxs]
          rw [if_pos hxu, if_pos he, if_pos hs, ← hs]
          ring
        · have hs : s ≠ u.erase x := fun h => he (by rw [h, Finset.insert_erase hxu])
          rw [if_pos hxu, if_neg he, if_neg hs]
          ring
      · have he : insert x s ≠ u := fun h => hxu (h ▸ Finset.mem_insert_self x s)
        rw [if_neg hxu, if_neg he]
        ring

/-! ## The two fundamental identities -/

lemma bdry_bdryGen (s : Finset V) : bdry (bdryGen s) = (0 : Chain V) := by
  have step : ∀ x ∈ s, bdry (sgn x s • Finsupp.single (s.erase x) 1)
      = ∑ z ∈ s, (if z = x then 0 else
          (sgn x s * sgn z (s.erase x)) •
            Finsupp.single ((s.erase x).erase z) (1 : ℤ)) := by
    intro x hx
    rw [map_smul, bdry_single, one_smul, bdryGen, Finset.smul_sum]
    rw [← Finset.sum_erase (f := fun z => if z = x then 0 else
        (sgn x s * sgn z (s.erase x)) •
          Finsupp.single ((s.erase x).erase z) (1 : ℤ)) s (if_pos rfl)]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [if_neg (Finset.ne_of_mem_erase hz), smul_smul]
  rw [bdryGen, map_sum, Finset.sum_congr rfl step, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    simp only [Prod.fst_swap, Prod.snd_swap]
    by_cases he : p.2 = p.1
    · simp [he]
    · have hne : ¬(p.1 = p.2) := fun h => he h.symm
      rw [if_neg he, if_neg hne, Finset.erase_right_comm,
        sgn_erase_cancel h1 h2 hne, neg_smul, neg_add_cancel]
  · intro p _ hF hswap
    apply hF
    have h : p.2 = p.1 := by
      have h1 := congrArg Prod.fst hswap
      simpa using h1
    rw [if_pos h]
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨h2, h1⟩
  · intro p _
    exact Prod.swap_swap p

/-- ∂∂ = 0. -/
theorem bdry_bdry (M : Chain V) : bdry (bdry M) = 0 := by
  induction M using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single s c => rw [bdry_single, map_smul, bdry_bdryGen, smul_zero]

/-- The contracting homotopy of the (augmented) full simplex:
`∂(x ∗ M) + x ∗ (∂M) = M`, exactly and globally. -/
theorem bdry_cone_add_cone_bdry (x : V) (M : Chain V) :
    bdry (cone x M) + cone x (bdry M) = M := by
  induction M using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, map_add, map_add, map_add, add_add_add_comm, hf, hg]
  | single s c =>
    by_cases hx : x ∈ s
    · -- cone kills the generator; the cone of the boundary restores it.
      have key : cone x (bdryGen s) = Finsupp.single s 1 := by
        rw [bdryGen, map_sum]
        rw [Finset.sum_eq_single_of_mem x hx]
        · rw [map_smul, cone_single, one_smul, coneGen,
            if_neg (Finset.notMem_erase x s), sgn_erase_self,
            Finset.insert_erase hx, sgn_smul_sgn_smul]
        · intro z hz hzx
          rw [map_smul, cone_single, one_smul, coneGen,
            if_pos (Finset.mem_erase_of_ne_of_mem (Ne.symm hzx) hx), smul_zero]
      rw [cone_single, coneGen, if_pos hx, smul_zero, map_zero, zero_add,
        bdry_single, map_smul, key, Finsupp.smul_single, smul_eq_mul, mul_one]
    · -- the generic case: the two sums cancel termwise.
      have h1 : bdry (sgn x s • Finsupp.single (insert x s) (1 : ℤ))
          = Finsupp.single s 1 + ∑ z ∈ s,
              (sgn x s * sgn z (insert x s)) •
                Finsupp.single (insert x (s.erase z)) (1 : ℤ) := by
        rw [map_smul, bdry_single, one_smul, bdryGen, Finset.sum_insert hx,
          smul_add, Finset.smul_sum]
        congr 1
        · rw [Finset.erase_insert hx, sgn_self_insert x s hx, sgn_smul_sgn_smul]
        · refine Finset.sum_congr rfl fun z hz => ?_
          rw [smul_smul,
            Finset.erase_insert_of_ne (fun h => hx (by rw [h]; exact hz))]
      have h2 : cone x (bdryGen s) = ∑ z ∈ s,
          (sgn z s * sgn x (s.erase z)) •
            Finsupp.single (insert x (s.erase z)) (1 : ℤ) := by
        rw [bdryGen, map_sum]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [map_smul, cone_single, one_smul, coneGen,
          if_neg (fun h => hx (Finset.mem_of_mem_erase h)), smul_smul]
      rw [cone_single, coneGen, if_neg hx, map_smul, h1, bdry_single, map_smul,
        h2, ← smul_add, add_assoc, ← Finset.sum_add_distrib]
      have hzero : ∀ z ∈ s,
          (sgn x s * sgn z (insert x s)) •
              Finsupp.single (insert x (s.erase z)) (1 : ℤ)
            + (sgn z s * sgn x (s.erase z)) •
              Finsupp.single (insert x (s.erase z)) (1 : ℤ) = 0 := by
        intro z hz
        rw [← add_smul, sgn_insert_cancel hx hz, neg_add_cancel, zero_smul]
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, add_zero,
        Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## Cone, link, neighborhood -/

lemma sgn_ne_zero (x : V) (s : Finset V) : sgn x s ≠ 0 := by
  simp [sgn]

/-- Coning the link recovers the neighborhood. -/
theorem cone_lk (x : V) (M : Chain V) : cone x (lk x M) = nbhd x M := by
  induction M using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, nbhd, Finsupp.filter_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, nbhd_add]
  | single s c =>
    rw [lk_single, lkGen]
    by_cases hxs : x ∈ s
    · rw [if_pos hxs, map_smul, map_smul, cone_single, one_smul, coneGen,
        if_neg (Finset.notMem_erase x s), sgn_erase_self,
        Finset.insert_erase hxs, sgn_smul_sgn_smul,
        nbhd_single_of_mem hxs, Finsupp.smul_single, smul_eq_mul, mul_one]
    · rw [if_neg hxs, smul_zero, map_zero, nbhd_single_of_notMem hxs]

/-- The neighborhood of `x` in `∂M` only depends on the neighborhood of `x`
in `M`: tets without `x` contribute no faces with `x`. -/
theorem nbhd_bdry_nbhd (x : V) (M : Chain V) :
    nbhd x (bdry (nbhd x M)) = nbhd x (bdry M) := by
  induction M using Finsupp.induction_linear with
  | zero => rw [nbhd_zero, map_zero, nbhd_zero]
  | add f g hf hg => rw [nbhd_add, map_add, nbhd_add, map_add, nbhd_add, hf, hg]
  | single s c =>
    by_cases hxs : x ∈ s
    · rw [nbhd_single_of_mem hxs]
    · have hz : nbhd x (bdry (Finsupp.single s c)) = 0 := by
        ext u
        rw [nbhd_apply, Finsupp.coe_zero, Pi.zero_apply]
        split
        · rename_i hxu
          rw [bdry_single, Finsupp.smul_apply]
          have hgen : bdryGen s u = 0 := by
            rw [bdryGen, Finset.sum_apply']
            refine Finset.sum_eq_zero fun z hz => ?_
            rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
            intro h
            exact hxs (Finset.mem_of_mem_erase (h ▸ hxu))
          rw [hgen, smul_zero]
        · rfl
      rw [nbhd_single_of_notMem hxs, map_zero, nbhd_zero, hz]

/-- A chain supported away from `x` has boundary supported away from `x`. -/
theorem nbhd_bdry_eq_zero {x : V} {N : Chain V} (h : nbhd x N = 0) :
    nbhd x (bdry N) = 0 := by
  rw [← nbhd_bdry_nbhd, h, map_zero, nbhd_zero]

/-- The cone from `x` lands in simplices containing `x`. -/
theorem nbhd_cone (x : V) (N : Chain V) : nbhd x (cone x N) = cone x N := by
  ext u
  rw [nbhd_apply]
  split
  · rfl
  · rename_i hxu
    rw [cone_apply, if_neg hxu]

/-- The link of `x` lives away from `x`. -/
theorem nbhd_lk (x : V) (M : Chain V) : nbhd x (lk x M) = 0 := by
  induction M using Finsupp.induction_linear with
  | zero => rw [map_zero, nbhd_zero]
  | add f g hf hg => rw [map_add, nbhd_add, hf, hg, add_zero]
  | single s c =>
    rw [lk_single, lkGen]
    split
    · ext u
      rw [nbhd_apply, Finsupp.coe_zero, Pi.zero_apply]
      split
      · rename_i hxu
        rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_apply,
          if_neg, smul_zero, smul_zero]
        intro h
        exact (Finset.notMem_erase x s) (h ▸ hxu)
      · rfl
    · rw [smul_zero, nbhd_zero]

/-- Cone injectivity: if the cone of `N` vanishes, `N` was supported on
simplices containing `x`. -/
theorem eq_nbhd_of_cone_eq_zero {x : V} {N : Chain V} (h : cone x N = 0) :
    N = nbhd x N := by
  ext t
  rw [nbhd_apply]
  split
  · rfl
  · rename_i hxt
    have hc := DFunLike.congr_fun h (insert x t)
    rw [cone_apply, if_pos (Finset.mem_insert_self x t),
      Finset.erase_insert hxt, Finsupp.coe_zero, Pi.zero_apply] at hc
    exact (mul_eq_zero.mp hc).resolve_left (sgn_ne_zero x t)

/-! ## The L¹ norm -/

/-- The L¹ norm of a chain: its size as a multiset of oriented simplices. -/
noncomputable def nrm (M : Chain V) : ℕ := ∑ s ∈ M.support, (M s).natAbs

lemma nrm_eq_sum_subset {M : Chain V} {t : Finset (Finset V)}
    (h : M.support ⊆ t) : nrm M = ∑ s ∈ t, (M s).natAbs := by
  refine Finset.sum_subset h fun s _ hs => ?_
  rw [Finsupp.notMem_support_iff.mp hs, Int.natAbs_zero]

@[simp] lemma nrm_zero : nrm (0 : Chain V) = 0 := by simp [nrm]

lemma nrm_eq_zero_iff {M : Chain V} : nrm M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext s
    by_cases hs : s ∈ M.support
    · have := Finset.sum_eq_zero_iff.mp h s hs
      simpa using this
    · simpa using Finsupp.notMem_support_iff.mp hs
  · intro h; rw [h, nrm_zero]

@[simp] lemma nrm_single (s : Finset V) (c : ℤ) :
    nrm (Finsupp.single s c) = c.natAbs := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [nrm, Finsupp.support_single_ne_zero s hc, Finset.sum_singleton,
      Finsupp.single_eq_same]

@[simp] lemma nrm_neg (M : Chain V) : nrm (-M) = nrm M := by
  rw [nrm, nrm, Finsupp.support_neg]
  exact Finset.sum_congr rfl fun s _ => by simp

lemma nrm_add_le (M N : Chain V) : nrm (M + N) ≤ nrm M + nrm N := by
  rw [nrm_eq_sum_subset (Finsupp.support_add),
    nrm_eq_sum_subset (M := M) (t := M.support ∪ N.support)
      Finset.subset_union_left,
    nrm_eq_sum_subset (M := N) (t := M.support ∪ N.support)
      Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [Finsupp.add_apply]
  exact Int.natAbs_add_le _ _

lemma nrm_filter_add_nrm_filter_neg (p : Finset V → Prop) [DecidablePred p]
    (M : Chain V) :
    nrm (M.filter p) + nrm (M.filter fun s => ¬ p s) = nrm M := by
  have h1 : (M.filter p).support ⊆ M.support := by
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
  have h2 : (M.filter fun s => ¬ p s).support ⊆ M.support := by
    rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
  rw [nrm_eq_sum_subset h1, nrm_eq_sum_subset h2, ← Finset.sum_add_distrib, nrm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hp : p s
  · rw [if_pos hp, if_neg (not_not_intro hp), Int.natAbs_zero, add_zero]
  · rw [if_neg hp, if_pos hp, Int.natAbs_zero, zero_add]

/-- The degree of a vertex in a chain: the mass of its neighborhood. -/
noncomputable def deg (x : V) (M : Chain V) : ℕ := nrm (nbhd x M)

lemma deg_eq_zero_iff {x : V} {M : Chain V} : deg x M = 0 ↔ x ∉ vert M := by
  rw [deg, nrm_eq_zero_iff, nbhd_eq_zero_iff]

/-- Norm accounting for the cone: no cancellation happens, so coning loses
exactly the mass at `x`. -/
theorem nrm_cone_add_deg (x : V) (M : Chain V) :
    nrm (cone x M) + deg x M = nrm M := by
  classical
  set F := M.filter (fun s => ¬ x ∈ s) with hF
  have hkill : cone x (nbhd x M) = 0 := by
    ext u
    rw [cone_apply, Finsupp.coe_zero, Pi.zero_apply]
    split
    · rw [nbhd_apply, if_neg (Finset.notMem_erase x u), mul_zero]
    · rfl
  -- the cone only sees the part away from `x`
  have hcone : cone x M = cone x F := by
    conv_lhs => rw [← Finsupp.filter_pos_add_filter_neg M (fun s => x ∈ s)]
    rw [map_add, ← nbhd, hkill, zero_add, hF]
  have hfree : ∀ t ∈ F.support, x ∉ t := by
    intro t ht
    rw [hF, Finsupp.support_filter, Finset.mem_filter] at ht
    exact ht.2
  have himg : (cone x F).support ⊆ F.support.image (insert x) := by
    intro u hu
    rw [Finsupp.mem_support_iff, cone_apply] at hu
    by_cases hxu : x ∈ u
    · rw [if_pos hxu] at hu
      have hFu : F (u.erase x) ≠ 0 := fun h => hu (by rw [h, mul_zero])
      exact Finset.mem_image.mpr ⟨u.erase x, Finsupp.mem_support_iff.mpr hFu,
        Finset.insert_erase hxu⟩
    · exact absurd (if_neg hxu) (fun h => hu h)
  have hinj : ∀ t₁ ∈ F.support, ∀ t₂ ∈ F.support,
      insert x t₁ = insert x t₂ → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ h
    rw [← Finset.erase_insert (hfree t₁ h₁), h, Finset.erase_insert (hfree t₂ h₂)]
  have hnrmF : nrm (cone x F) = nrm F := by
    rw [nrm_eq_sum_subset himg, Finset.sum_image hinj, nrm]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [cone_apply, if_pos (Finset.mem_insert_self x t),
      Finset.erase_insert (hfree t ht), Int.natAbs_mul, natAbs_sgn, one_mul]
  have hsplit := nrm_filter_add_nrm_filter_neg (fun s => x ∈ s) M
  rw [hcone, hnrmF, deg, nbhd, hF, add_comm]
  exact hsplit

end Taut
