# Survey: Hudson-style ball-gluing in mathlib (PL / topological ball)

Investigation branch `pl-ball-gluing-survey`. Separate from the taut cleanup; `lean/Taut` untouched.
mathlib **v4.29.1** (`~/.cache/taut-lean/packages/mathlib`, toolchain `leanprover/lean4:v4.29.1`).
Reference `danarajklee.pdf` is **not** in the repo filesystem; this survey uses the facts stated in the
task (Danaraj–Klee Prop 1.2; Hudson's PL gluing, *Piecewise Linear Topology* p.39).

Every "exists" below was confirmed by `#check`/`grep` against the mathlib source; every "absent" by an
empty `grep` over `Mathlib/`. The prototype `scratch/PLBallGluing.lean` ELABORATES (only `sorry`/unused
warnings) — its statements use only the names below and conclude in `Nonempty (… ≃ₜ closedBall …)`.

## 1. What mathlib has (exact names)

| concept | status | exact name / file |
|---|---|---|
| `Homeomorph` (`≃ₜ`) | **EXISTS** | `Homeomorph`, `Mathlib/Topology/Homeomorph/Defs.lean` |
| standard closed ball in ℝⁿ | **EXISTS** | `Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1` |
| sphere / boundary of ball | **EXISTS** | `Metric.sphere`; `frontier (closedBall …) = sphere …` is a lemma |
| **convex body ≃ₜ closed ball (pair!)** | **EXISTS** | `exists_homeomorph_image_interior_closure_frontier_eq_unitBall`, `Mathlib/Analysis/Convex/GaugeRescale.lean` — an ambient `h : E ≃ₜ E` with `h '' closure s = closedBall`, `h '' frontier s = sphere`, `h '' interior s = ball` |
| normed space ≃ₜ unit ball | EXISTS | `Mathlib/Analysis/Normed/Module/Ball/Homeomorph.lean` |
| gluing / pushout of top. spaces | **EXISTS (generic)** | `TopCat.GlueData`, `Mathlib/Topology/Gluing.lean`; category-theory pushouts in `TopCat`. No ball-specific results. |
| finite abstract simplicial complex | EXISTS | `AbstractSimplicialComplex`, `Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean` |
| geometric simplicial complex + carrier | EXISTS | `Geometry.SimplicialComplex 𝕜 E` with `.space : Set E` (= ⋃ faces' convex hulls), `Mathlib/Analysis/Convex/SimplicialComplex/Basic.lean` |
| CW complexes (cells = balls) | EXISTS | `Mathlib/Topology/CWComplex/{Abstract,Classical}/…` |
| manifolds with boundary/corners | PARTIAL | `ModelWithCorners`, `ChartedSpace`, `Mathlib/Geometry/Manifold/…`; sphere is a manifold (`Instances/Sphere.lean`, `stereographic`) |

## 2. What mathlib LACKS (confirmed empty greps — the load-bearing gaps)

| missing | grep over `Mathlib/` |
|---|---|
| **PL topology** (piecewise-linear, `PLManifold`, `PLHomeomorph`, `PLMap`, PL ball) | EMPTY |
| **collar neighbourhood theorem** | only a *comment* in `Geometry/Manifold/Bordism.lean:22`; no `Collar` def/theorem |
| **ball-gluing theorem** (two balls along a boundary ball = ball — Hudson) | EMPTY |
| **Schoenflies / Jordan–Brouwer / invariance of domain** | EMPTY (the `Brouwer`/`prime` hits are order theory) |
| **geometric realization of an *abstract* simplicial complex as a TopSpace** | none — `Geometry.SimplicialComplex.space` lives in a vector space already; there is no `AbstractSimplicialComplex → TopCat` realization |
| combinatorial/PL `n`-ball; shellable ⇒ ball | EMPTY |

## 3. Answers to the five questions

**Q1 (objects):** see the two tables above.

**Q2 (can we STATE the gluing theorem with existing defs, no PL library?):** **YES.** Verified: the
prototype's `hudson_glue` and `shelling_implies_homeomorphic_ball` elaborate using only `Homeomorph`,
`EuclideanSpace`/`Metric.closedBall`, `frontier`, `Set.Icc`, and `Geometry.SimplicialComplex.space`. The
catch: with no PL, the **collar/local-flatness must be an explicit hypothesis** (it cannot be derived).

**Q3 (minimal local API to state a useful Homeomorph theorem):** small and statable now —
`stdBall n := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1`; a certificate `IsTopBall X n`
**carrying a real `Nonempty (X ≃ₜ stdBall n)`** (not a label); a *bicollar* hypothesis
(`Nonempty (seam × Icc(-1,1) ≃ₜ nbhd)`); a *ball-shelling-chain* predicate. All in the prototype.

**Q4 (best proof route):**
- **Single ball:** Route A is real and **available now** — `convexBody_isTopBall` follows from
  `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` (+ identifying `E ≃ₜ EuclideanSpace ℝ
  (Fin n)` in dimension `n`). A simplex's geometric realization is a bounded convex body with nonempty
  interior in its affine span — base case done.
- **Gluing (the crux):** Route C (extensional "ball := carrier ≃ₜ closedBall", which `IsTopBall` is) is
  best for **stating**; but the **proof** of `hudson_glue` is the same hard topology in every route. It
  needs one of: (B) a **PL library** (absent) where the collar is automatic; or (A′) the **topological
  collar/bicollar gluing theorem** (absent), itself essentially the collar neighbourhood theorem +
  a Mayer–Vietoris-style homeomorphism construction. There is no shortcut in current mathlib.
- **Shelling ⇒ ball:** folds `hudson_glue` by induction over the shelling (prototype
  `shelling_implies_homeomorphic_ball`); blocked entirely on the gluing lemma.

**Q5 (existing mathlib / nearby Lean results for any of these):** **none found.** No ball-gluing, no
shellable⇒ball, no abstract realization, no PL. The CWComplex library is the nearest neighbour (its cells
are attached via maps from closed balls) but proves nothing of this shape; no Lean project surfaced that
proves Hudson-style gluing.

## 4. Verdict

- **Single ball ≃ₜ closed ball:** **FEASIBLE NOW** (GaugeRescale), modulo the affine-span identification.
- **Hudson gluing + shelling ⇒ ball:** **REQUIRES SUBSTANTIAL NEW INFRASTRUCTURE.** The *statement layer*
  (with explicit collar hypotheses and genuine `Homeomorph` conclusions) is buildable today and is
  prototyped. The *proof* is a real topology project: mathlib has no PL, no collar theorem, no
  Schoenflies/invariance-of-domain, and no ball-gluing result. This is "feasible only after a sizeable
  PL **or** collar-neighbourhood foundation," not "feasible after a small API."

**Collar/local-flatness explicitly:** in the PL/simplicial category the seam disk is automatically
(bi)collared, so a PL library would discharge the hypothesis. In **pure topology it is NOT automatic and
IS necessary** in high dimensions: a non-locally-flat boundary sphere need not bound a ball (Schoenflies
fails without local flatness for `n ≥ 4`; even for `n = 3` bicollaring is the substantive content). So
any honest pure-topology `hudson_glue` MUST carry the collar hypothesis — the prototype does.

## 5. Recommendation (AlephProver suitability): **MAYBE**

- **Statement/API layer + the single-ball base case:** plausibly **YES** for Aleph — assembling
  `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` + the `EuclideanSpace`/affine-span
  identification into `convexBody_isTopBall` is a bounded, mathlib-backed target.
- **The Hudson gluing lemma and `shelling ⇒ ball`:** **NO** — not within Aleph's reach, because the
  missing piece is *infrastructure* (a collar neighbourhood theorem or a PL library), not a proof-search
  gap over existing lemmas. Aleph cannot conjure the collar theorem from an empty namespace.
- **Net:** MAYBE — viable as "Aleph builds the statement layer and the single-ball case; a human-led (or
  much larger) effort builds the collar/PL foundation that the gluing proof rests on." A certificate-only
  result is explicitly **not** the goal, and `IsTopBall` is defined to carry an actual homeomorphism, so
  there is no temptation to stop at a label.

## Files
- `scratch/PLBallGluing.lean` — prototype (3 `sorry` statements, all with `Nonempty Homeomorph`
  conclusions; elaborates against Mathlib v4.29.1; outside `lean/Taut`, not in the taut build).
- `notes/future-projects.md` — records the Danaraj–Klee/Björner route at a high level (this survey is the
  detailed feasibility pass).
