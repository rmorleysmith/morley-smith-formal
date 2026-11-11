# morley-smith-formal

Lean-verified results by Richard Morley-Smith. Each result is stated in a short `Challenge.lean`
that uses only Mathlib definitions, proved in `Solution.lean`, and checked by Lean's
[Comparator](https://github.com/leanprover/comparator), the same way the
[Palomar registry](https://palomar-registry.org/) checks submissions. Each result has its own
`formalization.yaml`, recording its sources, its scope and how AI was used.

Lean `v4.35.0`, Mathlib `v4.35.0`, every file in the module system. No `sorry`; only Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Results

| Result | Statement | Read first |
|---|---|---|
| [Congruences are decided at the primes](MorleySmithFormal/HeckePropagation) | Two multiplicative sequences in a commutative ring, each obeying a Hecke recursion `c(p^{r+2}) = c(p) c(p^{r+1}) − w(p) c(p^r)` with weights congruent mod an ideal `I`, that agree mod `I` at every prime agree mod `I` at every `n`. The divisor sums `σ_k` obey the recursion with `w(p) = p^k`. | [`Challenge.lean`](MorleySmithFormal/HeckePropagation/Challenge.lean) |
| [Ramanujan's congruences](MorleySmithFormal/RamanujanCongruences) | If `M_{k−12}` has rank one and `2k / B_k = D / ℓ` in lowest terms, the coefficients of `Δ · E₄^a · E₆^b` are integers congruent to `σ_{k−1}(n)` modulo `ℓ`. So for `k = 12, 16, 18, 20, 22, 26`, the coefficients of the level-one cusp form `Δ · E₄^a · E₆^b` of weight `k` are integers congruent to `σ_{k−1}(n)` modulo 691, 3617, 43867, 283·617, 131·593 and 657931, the numerators of `B_k / 2k`. | [`Challenge.lean`](MorleySmithFormal/RamanujanCongruences/Challenge.lean) |

Both are known mathematics: the first is a standard step in the theory of congruences between
modular forms, and the second goes back to Ramanujan (1916, the case `k = 12`) and
Swinnerton-Dyer (1973). What is new here is a complete, checked Lean proof. The case `k = 12`
was first proved in [fugue-formal](https://github.com/rmorleysmith/fugue-formal) (Lean v4.34.1);
the proof here generalises it to all six weights.

## Check it

```bash
lake exe cache get
scripts/check.sh      # build, Comparator on every result (needs bubblewrap), metadata check
```

The same check runs on GitHub on every push. A result passes when its `Solution.lean` proves
exactly the statements in its `Challenge.lean` using only the three standard axioms, and its
`formalization.yaml` matches the v0.4 schema and Palomar's rules for sources.

## Layout

```
MorleySmithFormal/<Result>/Challenge.lean      the statement only (with sorry)
MorleySmithFormal/<Result>/Solution.lean       the statement again, proved
MorleySmithFormal/<Result>/Basic.lean          definitions and proofs
MorleySmithFormal/<Result>/comparator.json     which theorems the Comparator checks
MorleySmithFormal/<Result>/formalization.yaml  sources, scope, AI use
scripts/check.sh                               build + Comparator + metadata check
```

## How AI was used

The ideas in this work are Richard Morley-Smith's: the questions, the links between areas of
mathematics, and the choices of what to pursue. Claude, through Claude Code, helps the author
formalise them in Lean 4: it wrote the statements and proofs in this repository under the
author's direction. Each result's `formalization.yaml` records how AI was used for that result.

Checking the results does not rely on trusting the AI. Every proof is verified by the Lean
kernel against Mathlib, and the Comparator checks that each proof establishes exactly the
statement in its `Challenge.lean` using only Lean's three standard axioms.

## Licence

Apache-2.0. See [`LICENSE`](LICENSE).
