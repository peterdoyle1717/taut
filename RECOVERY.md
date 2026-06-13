# RECOVERY — canonical checkpoint

> **To get back to exactly where the project was when Fable was removed from
> the workflow, run:**
>
> ```sh
> git checkout fable-axed        # annotated tag → commit a8a8954 on main
> # (equivalently)  git checkout a8a895400888cf1139cecb2e114d12de59aaa4dd
> ```
>
> If you want `main` itself reset to that point (discarding anything after):
>
> ```sh
> git reset --hard fable-axed    # DESTRUCTIVE — only if you mean it
> ```

## What is at the checkpoint (`fable-axed` = `a8a8954`, branch `main`)

Milestones **M9–M16** of the taut-fillings Lean 4 / Mathlib formalization
(Doyle–Ellison–Wang, "Taut fillings"), all committed:

| commit | milestone |
|---|---|
| `0453722` | M9 — `Ball.lean`: shelling-certified balls |
| `0eb207f` | M10 — `Homology2.lean`: 𝔽₂ chain complex, ∂∂=0, fundamental cycle, dual connectivity, **b₂=1** |
| `7eff1c5` | M11 — `Homology2.lean`: r₁=V−1 and **H₁=0 (the watershed)** |
| `6e5da1d` | M12 — `Separation.lean`: the cut (`exists_cut`), `edge_cut_parity`, `closed_cut` |
| `36f9aa7` | M13 — `Separation.lean`: `gammaCycle_dichotomy` |
| `53f16e6` | M14 — `Separation.lean`: `cutSet_dualConn` (σ₁ dual-connected) |
| `ef9d062` | M15 — `Separation.lean`: `conn_cut` (`conn` for the cut pieces) |
| `a8a8954` | M16 — `Separation.lean`: `linkConn` infrastructure + the v∉γ half |

(Also `cf807d1`: records the codex **G1 APPROVED** verdict for the
homology/separation design, session `019ec1fd`, and the codex stdin fix.)

Earlier foundation (pre-M9): M2–M8 — chains, Zvol, Theorem 1, K-maps,
`IsSphere2`, sphere local structure.

### Verification at the checkpoint
- `cd lean && lake build` → "Build completed successfully (8258 jobs)".
- `grep -rnwE "sorry|admit|native_decide" lean/Taut/` → none.
- `#print axioms` on the exported theorems → `[propext, Classical.choice, Quot.sound]` only.

## Protocol going forward (Fable removed)

Back to the full teamwork protocol with **codex doing the architecture**:
- **G1 (codex design audit) before new load-bearing code.** Run it correctly:
  `codex exec "$PROMPT" < /dev/null` — codex blocks forever if stdin is not
  redirected to EOF (this was the cause of the earlier "hangs"; not an infra
  fault). Log each consult under `notes/codex-consults/`.
- **G2 (codex commit gate) on every commit** — the runner pipes the staged
  diff + evidence as a bundle (`codex exec "$PROMPT" < bundle`).

## What remains toward Theorem 2 (the next packets)
1. **v∈γ case of `linkConn`** — the remaining crux: the vertex link is a cycle
   (`link_two_regular` + `linkConn`); the cut flips side exactly at the two
   γ-link-vertices, so the cut-faces form an arc closed by γ. Needs cycle/arc
   structure (Mathlib `SimpleGraph.IsCycles`). **G1-audit this before coding.**
2. assemble full `linkConn`, then `euler` (χ-additivity + χ≤2 from b₂);
3. assemble `IsSphere2 (insert γ σᵢ)` for both sides (σ₂ = `cutSet` of W+𝟙);
4. the `X = X₁+X₂` chain wrapper feeding `IsTaut.splits` (needs the
   "orientation coherence" lemma codex flagged);
5. the merged Theorem 2 + Theorem 3 induction (eligible tets, the flip, base
   case ∂Δ³, shelling reassembly) — its own G1 design packet.

Live state of record: `TEAMWORK.md`.
