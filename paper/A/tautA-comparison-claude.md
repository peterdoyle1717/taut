# Claude's comparison of tautA-{claude,codex,gpt}-01

All three start from the Feb-20 base, build to 14 pages, use no Lean terminology, fix the carrier typo
(homeomorphic to the manifold, not $S^2$), keep the Triangulations section live, define $K(M)$ and the
clean-filling convention, state Theorem 2 with cleanness + $K(M)$ triangulating $B^3$, use a
support-tet/correct-sign eligible count, handle both post-flip cases (one sphere / two conjoined spheres
with $M-t$ splitting into clean pieces) and the multiplicity-2 obstruction via a disjoint eligible tet,
give a shucking shelling, and a fuller flag proof with the $K_4$ correct (no $K_5$ typo). So they agree on
the substance the task demanded. Differences:

## Dimension-by-dimension

1. **Theorem 2 cleanness verification (the most important difference).**
   - **claude, codex:** KEEP the explicit three-condition verification (pseudomanifold, connected
     edge-links, connected vertex-links), each forced by minimality. More complete.
   - **gpt:** COLLAPSES this into one compressed "gluing preserves cleanness" paragraph; gpt's own report
     admits it "may want a separate lemma for clean gluing." This is exactly the "don't collapse `M is
     clean`" risk the task warned about. **gpt weakest here.**

2. **Eligible-tet count.**
   - **codex:** most rigorous — defines $A(u)$ (correctly-oriented boundary faces), $|A(u)|\le2$, a
     reveal/first-seen argument giving $r\ge\maxdeg$ disjointly eligible. Cleanest.
   - **gpt:** same $A(u)$ reveal idea, slightly terser. Solid.
   - **claude:** a $2$-to-$1$ pigeonhole — correct, a touch less explicit than the $A(u)$ version.

3. **Proof framing.** codex & gpt use the "good/bad filling pair" framing (crisp). claude uses
   "minimal counterexample pair" (the base's framing; equivalent). All fine.

4. **Jokey prose.** claude, codex removed all. **gpt LEFT two** ("This is clear, but let's drag it out";
   "a long-winded way of saying"). gpt weakest here.

5. **Shelling.** all three: shucking recursion, "freely shellable", three-face move excluded. codex names
   it "dismantle"; claude/gpt "shuck". claude keeps a one-line "monotone" remark; codex/gpt drop the word
   but keep its content. All fine.

6. **Flag.** all three: fuller Config-2 (octahedral exception, $\maxdeg\ge5$, interior edge $AD$, $K_4$),
   $K_5\Rightarrow\partial\Delta^4\not\subseteq B^3$. claude & codex keep "(clique complex)" parenthetical;
   **gpt drops it**. Flag theorem: gpt/codex label it; claude's is unlabeled. Octahedral case is named-not-
   worked in all three (codex gestures "checked directly").

7. **Bibliography.** claude, codex keep `\bibliography{taut}` (the real `taut.bib`). **gpt inlines a
   `thebibliography`** — standalone build, but the entries look partly reconstructed (e.g. titles/years for
   `mt`, `pw:flip`); risk of inaccurate citation details. (stt:jams matches the real cite.)

8. **Tidiness.** **gpt removed the commented-out Overview induction sketch**; claude & codex left it
   (commented, harmless, but stale, still in `Y`). gpt tidier here.

9. **Length.** gpt 948 < codex 1055 < claude 1084. gpt's brevity partly comes from #1 (collapsed
   cleanness), which is a loss, not just economy.

## Claude's overall ranking and v02 recommendation

- **codex and claude are the two strongest and are very close** (both keep the full cleanness
  verification; codex has the more rigorous eligible count + crisp filling-pair framing).
- **gpt** has real virtues (standalone build, removed the stale commented sketch, concise, the $A(u)$
  count) but is **weakest on the load-bearing cleanness verification** (collapsed/sketched), **left two
  jokes**, dropped the clique parenthetical, and risks inaccurate inline bib.

**Proposed joint v02:** take **codex's draft as the spine** (rigorous $A(u)$ eligible count + good/bad
filling-pair framing + kept cleanness verification), and graft:
- **gpt's removal of the commented Overview sketch** (tidy);
- **claude's "(clique complex)" parenthetical** and the one-line monotone remark;
- keep `\bibliography{taut}` (real bib), OR adopt gpt's inline bibliography only after verifying every
  entry against `taut.bib`.
Fix the residual sketchy spots in all three: actually dispose of the octahedral $\maxdeg=4$ case (or cite),
and decide the $S^3\not\subseteq B^3$ step's level of rigor.
- **Open wording choice for humans:** "taut filling of $\sigma$" (claude) vs "of $X(\sigma)$" (codex/gpt).
