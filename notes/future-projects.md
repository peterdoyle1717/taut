# Future projects (not part of the current cleanup)

## PL-ball certificate: the Danaraj–Klee / Björner route

The Lean development proves a **combinatorial certificate**: a taut filling of a simplicial 2-sphere is a
*stickerball* — a shellable clean (normal) 3-pseudomanifold with nonempty boundary — and indeed an
*anyrooted* stickerball.

It does **not** formalize the external PL theorem that such a certificate is homeomorphic to `B³`. That
bridge is a possible future AlephProver/mathlib project:

- **Danaraj–Klee:** a shellable normal pseudomanifold is a PL sphere (closed case) / PL ball (with
  nonempty boundary).
- **Björner:** thin shellable posets are CW posets; shellability of the face poset yields the PL
  structure.

Formalizing this would let one upgrade `IsStickerball` (the combinatorial certificate) to an actual
"triangulation of `B³`" statement. It is out of scope here; the current project deliberately stops at the
combinatorial certificate and records that boundary explicitly in the `IsStickerball` docstring.
