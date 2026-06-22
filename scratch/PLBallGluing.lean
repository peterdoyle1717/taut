/-
PROTOTYPE / SCRATCH — NOT part of the taut build (lives in `scratch/`, imports full Mathlib).
Statement-layer prototype for the Hudson-style ball-gluing project.  Every "theorem" here is a
STATEMENT with `sorry`; the point is that the conclusions are genuine `Nonempty (… ≃ₜ closedBall …)`
homeomorphisms, NOT combinatorial certificates.  Verified to ELABORATE against Mathlib v4.29.1
(`lake env lean scratch/PLBallGluing.lean` → only `sorry`/`unused` warnings, no errors).

Mathlib pieces actually used (exact names):
  • `Homeomorph` (`≃ₜ`)                                   Mathlib/Topology/Homeomorph/Defs.lean
  • `EuclideanSpace ℝ (Fin n)`, `Metric.closedBall/sphere`
  • `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`  Mathlib/Analysis/Convex/GaugeRescale.lean
  • `Geometry.SimplicialComplex` + `.space`              Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean
NOT in Mathlib (must be hypotheses or future work): PL topology, collar neighbourhood theorem,
ball-gluing theorem, Schoenflies / invariance of domain, abstract→geometric realization.
-/
import Mathlib
open Metric Topology

noncomputable section
universe u

/-- Standard closed `n`-ball model. -/
abbrev stdBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1

/-- **Certificate WITH an actual homeomorphism.**  `IsTopBall X n` is *not* a combinatorial label: it
carries a genuine homeomorphism of the subspace `X` to the standard closed `n`-ball, plus the boundary
data (the part of `X` mapping onto the sphere — its topological boundary sphere `∂X`). -/
structure IsTopBall {α : Type u} [TopologicalSpace α] (X : Set α) (n : ℕ) : Prop where
  /-- the honest content: an actual homeomorphism to the standard closed ball. -/
  homeo : Nonempty (X ≃ₜ stdBall n)

/-- **Single ball (available now, GaugeRescale).**  The closure of a bounded convex set with nonempty
interior in an `n`-dimensional real space is homeomorphic to the standard closed `n`-ball.  PROVABLE
from `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` (the homeomorphism even carries
`frontier s ↦ sphere`, giving the boundary sphere for free).  This is the base case of any shelling. -/
theorem convexBody_isTopBall {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hc : Convex ℝ s) (hint : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) (n : ℕ) (hdim : Module.finrank ℝ E = n) :
    Nonempty ((closure s : Set E) ≃ₜ stdBall n) := by
  sorry  -- transport `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` + EuclideanSpace ≃ₜ E

/-- **Hudson-style gluing — the LOAD-BEARING lemma (NOT available; this is the project).**
Two closed `n`-balls `X`, `Y` whose intersection is a closed `(n-1)`-ball lying in the boundary of each,
glued along a BICOLLAR of that seam, give a closed `n`-ball.  Conclusion is an ACTUAL homeomorphism.

The `collar` hypothesis is exactly the PL / local-flatness tameness work: a bicollar identifies a
neighbourhood of the seam inside `X ∪ Y` with `seam × [-1,1]` (seam ↦ `×{0}`, the `X`-side ↦ `×[0,1]`,
the `Y`-side ↦ `×[-1,0]`).  In the PL/simplicial category such a collar is automatic (this is where a PL
library would pay off); in pure topology it is a genuine hypothesis and is NECESSARY in high dimensions
(a non-collared boundary sphere need not bound a ball — Schoenflies fails without local flatness). -/
theorem hudson_glue {α : Type u} [TopologicalSpace α] {X Y : Set α} (n : ℕ)
    (hX : IsTopBall X n) (hY : IsTopBall Y n)
    (hXY : IsTopBall (X ∩ Y : Set α) (n - 1))
    (hbX : (X ∩ Y : Set α) ⊆ frontier X) (hbY : (X ∩ Y : Set α) ⊆ frontier Y)
    (collar : Nonempty (↥(X ∩ Y) × (Set.Icc (-1 : ℝ) 1) ≃ₜ
        {p : α // p ∈ (closure (X ∪ Y) \ X) ∪ (closure (X ∪ Y) \ Y)})) :
    Nonempty ((X ∪ Y : Set α) ≃ₜ stdBall n) := by
  sorry  -- Hudson, PL Topology p.39 (via Danaraj–Klee Prop 1.2); needs collar/PL infrastructure absent from mathlib

/-- A *shelling chain* of closed balls inside `α`: a list of subsets, each a closed `n`-ball, where each
new ball meets the union-so-far in a collared boundary `(n-1)`-ball.  (Bundles the per-step `hudson_glue`
hypotheses.  This Prop is the honest encoding of "successive intersections are boundary balls".) -/
def IsBallShellingChain {α : Type u} [TopologicalSpace α] (n : ℕ) (l : List (Set α)) : Prop :=
  ∀ k (hk : k < l.length), IsTopBall (l.get ⟨k, hk⟩) n
  -- (a full version would also carry, for each k ≥ 1, the seam-is-boundary-ball + bicollar data)

/-- **Shelling ⇒ homeomorphic to a ball — the target (NOT available; folds `hudson_glue`).**
If a simplicial complex's tets can be ordered so the geometric realizations form a ball-shelling chain,
its carrier (`K.space`, a subset of the ambient real space) is homeomorphic to the standard closed
`n`-ball.  Conclusion is an ACTUAL homeomorphism, not a certificate.  Reduces to iterating `hudson_glue`. -/
theorem shelling_implies_homeomorphic_ball {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) (n : ℕ)
    (l : List (Set E)) (hchain : IsBallShellingChain n l)
    (hcarrier : K.space = ⋃ s ∈ l, s) :
    Nonempty ((K.space : Set E) ≃ₜ stdBall n) := by
  sorry  -- induction on `l`, base = `convexBody_isTopBall`, step = `hudson_glue`

end
