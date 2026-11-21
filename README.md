# morley-smith-formal

Lean-verified results by Richard Morley-Smith. Each result is stated in a short `Challenge.lean`
that imports only Mathlib (any auxiliary definition is written out in the file), proved in
`Solution.lean`, and checked by Lean's [Comparator](https://github.com/leanprover/comparator), the
same way the [Palomar registry](https://palomar-registry.org/) checks submissions. Each result has its own
`formalization.yaml`, recording its sources, its scope and how AI was used.

Lean `v4.35.0`, Mathlib `v4.35.0`, every file in the module system. No `sorry` outside the
`Challenge.lean` statements, which are stated with `sorry` by design and proved in `Solution.lean`;
only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Results

| Result | Statement | Read first |
|---|---|---|
| [Congruences are decided at the primes](MorleySmithFormal/HeckePropagation) | Two multiplicative sequences in a commutative ring, each obeying a Hecke recursion `c(p^{r+2}) = c(p) c(p^{r+1}) − w(p) c(p^r)` with weights congruent mod an ideal `I`, that agree mod `I` at every prime agree mod `I` at every `n`. The divisor sums `σ_k` obey the recursion with `w(p) = p^k`. | [`Challenge.lean`](MorleySmithFormal/HeckePropagation/Challenge.lean) |
| [Ramanujan's congruences](MorleySmithFormal/RamanujanCongruences) | For `k = 12 + 4a + 6b`: if `M_{k−12}` has rank one and `2k / B_k = D / ℓ` in lowest terms, the coefficients of `Δ · E₄^a · E₆^b` are integers congruent to `σ_{k−1}(n)` modulo `ℓ`. So for `k = 12, 16, 18, 20, 22, 26`, the coefficients of the level-one cusp form `Δ · E₄^a · E₆^b` of weight `k` are integers congruent to `σ_{k−1}(n)` modulo 691, 3617, 43867, 283·617, 131·593 and 657931, the numerators of `B_k / 2k`. | [`Challenge.lean`](MorleySmithFormal/RamanujanCongruences/Challenge.lean) |
| [The least displacement of a hyperbolic element of `SL(2, ℤ)`](MorleySmithFormal/ModularSystole) | For `γ = (a b; c d)` in `SL(2, ℤ)` with trace `t`, and `z = x + iy` in the upper half-plane: `cosh d(z, γz) = t²/2 − 1 + (c(x² + y²) + (d − a)x − b)²/(2y²)`. Every element with `\|t\| > 2` moves every point at least `4 log φ`, with `φ` the golden ratio; `(2 1; 1 1)` moves `i` exactly that far; each such element has translation length `arcosh(t²/2 − 1)`. (This is the length `4 log φ` of the shortest closed geodesic of the modular surface; the surface and its geodesics are not formalised.) The elliptic points `i` and `ρ` are at distance `(log 3)/2`, so `tanh d(i, ρ) = 1/2`. | [`Challenge.lean`](MorleySmithFormal/ModularSystole/Challenge.lean) |
| [The hypercharges of a generation of the Standard Model](MorleySmithFormal/Hypercharge) | For rational hypercharges `q, u, d, l, e` of `Q, uᶜ, dᶜ, L, eᶜ`, the gauge anomaly conditions `2q + u + d = 0`, `3q + l = 0`, `6q³ + 3u³ + 3d³ + 2l³ + e³ = 0` hold exactly when `q = l = e = 0, d = −u`, or `(u, d, l, e) = (2q, −4q, −3q, 6q)`, or `(−4q, 2q, −3q, 6q)`: the Standard Model's hypercharges up to scale and `u ↔ d`. They imply the gravitational condition. The cubic condition is Fermat's `e³ + (u − 2q)³ = (u + 4q)³`, and the proof is Mathlib's Fermat's last theorem for exponent 3. The same is proved for `N ≥ 1` colours: the cubic is `e³ + (u + (1 − N)q)³ = (u + (N + 1)q)³` and the solutions with `q ≠ 0` are `{u, d} = {(N − 1)q, −(N + 1)q}`, `l = −Nq`, `e = 2Nq`. Rational hypercharges (quantised hypercharge), one generation, no right-handed neutrino. | [`Challenge.lean`](MorleySmithFormal/Hypercharge/Challenge.lean) |
| [The silent shells of the cubic lattice](MorleySmithFormal/SilentShells) | No integer `4^a (8b + 7)` is a sum of three squares of integers: the sphere of that squared radius about the origin contains no point of `ℤ³`. This is the elementary direction of the three-square theorem of Legendre and Gauss, by descent modulo 8 and 4. | [`Challenge.lean`](MorleySmithFormal/SilentShells/Challenge.lean) |
| [The Fermat cubic modulo a prime `p ≡ 2 (mod 3)`](MorleySmithFormal/FermatCubicModP) | For a prime `p ≡ 2 (mod 3)`, cubing is a bijection of `ℤ/p`, and `x³ + y³ ≡ z³ (mod p)` has exactly `p²` solutions. So the projective cubic has `p + 1` points and its `L`-function has `a(p) = 0` at these primes. The cubic is the one to which the hypercharge conditions above reduce. | [`Challenge.lean`](MorleySmithFormal/FermatCubicModP/Challenge.lean) |
| [The log-determinant divergence of two lattice metrics](MorleySmithFormal/LatticeMetricDivergence) | For `z` in the upper half-plane let `M(z) = (1/y)[[x² + y², x], [x, 1]]`, the Gram matrix of the basis `(z, 1)` of `ℤ + ℤz` divided by the covolume. For `G = M(z)M(w)⁻¹`: `det G = 1`, `tr G = 2 cosh d(z, w)` with `d` the hyperbolic distance, so the divergence `tr G − 2 − log det G` is `2 cosh d − 2`. For `γ = (a b; c d) ∈ SL(2, ℤ)` of trace `t` it is `t² − 4 + (c(x² + y²) + (d − a)x − b)²/y²`: at least `t² − 4`, with equality exactly when the square vanishes; for `|t| > 2` at least `5`, and `(2 1; 1 1)` attains `5` at `i`. The expression `tr(G − 1 − log G)` has the form of the emergent cosmological term of Bianconi's gravity from entropy. | [`Challenge.lean`](MorleySmithFormal/LatticeMetricDivergence/Challenge.lean) |

All seven are known mathematics. The first is a standard step in the theory of congruences between
modular forms, and the second goes back to Ramanujan (1916, the case `k = 12`) and
Swinnerton-Dyer (1973); the author's earlier Lean proof of the case `k = 12` is in
[fugue-formal](https://github.com/rmorleysmith/fugue-formal) (Lean v4.34.1), and the proof here
covers all six weights (the general statement has exactly these six instances). The third is the classical computation of translation lengths
in the modular group. The fourth is a theorem of Lohitsiri and Tong (2020);
[Physlib](https://github.com/leanprover-community/physlib) proves its gravitational consequence
within its own definitions of the anomaly conditions, and the statement here is the explicit list
of solutions. The fifth is the elementary half of the three-square theorem of Legendre and Gauss. The sixth is a standard exercise. The seventh is the classical point-pair invariant of the upper half-plane, read as the log-determinant divergence of binary forms.
What is new in each case is a complete, checked Lean proof of the statement as given.

## Results that use TauCeti

The folder [`tau-track/`](tau-track) is a separate Lake package: Lean `v4.36.0-rc2`, with
[TauCeti](https://github.com/TauCetiProject/TauCeti) pinned at commit `83769e4` and the Mathlib
commit that TauCeti uses. TauCeti is a library written with AI. The statements still import only
Mathlib; the proofs use
TauCeti's Hecke operators, Sturm bound, lattices, one-variable theta series, period polynomials,
Eichler–Shimura isomorphism, and Fricke operator with its functional equation. Each
`Challenge.lean` imports only the Mathlib modules its statement needs.

| Result | Statement | Read first |
|---|---|---|
| [The newform of weight 2 and level 11](tau-track/TauTrack/LevelEleven) | `η(z)²η(11z)²` is a cusp form of weight 2 for `Γ₀(11)` with integer coefficients `a(n)`, `a(1) = 1`, `a(2) = −2`. It spans `S₂(Γ₀(11))`; a modular form of that weight and level agreeing with it up to `q²` equals it; and `a(m)a(n) = ∑ d·a(mn/d²)` over `d ∣ (m, n)`, `11 ∤ d`. | [`Challenge.lean`](tau-track/TauTrack/LevelEleven/Challenge.lean) |
| [The Eisenstein congruence modulo 5 at level 11](tau-track/TauTrack/ElevenFive) | For `η(z)²η(11z)² = ∑ a(n) qⁿ`: `a(n) ≡ ∑_{d ∣ n, 11 ∤ d} d` mod 5 for every `n ≥ 1`, so `a(p) ≡ 1 + p` mod 5 for every prime `p ≠ 11`, the level-11 analogue of `τ(n) ≡ σ₁₁(n)` mod 691. The proof writes the theta series of two copies of `x² + xy + 3y²` as `Ẽ + c·f`, with `Ẽ = 1 + (12/5)∑ σ*(n) qⁿ` the Eisenstein series of level 11. | [`Challenge.lean`](tau-track/TauTrack/ElevenFive/Challenge.lean) |
| [The functional equation at level 11](tau-track/TauTrack/ElevenFunctionalEquation) | For `f = η(z)²η(11z)²` and `Λ(s) = (2π)^{−s}Γ(s)L(f, s)`: the Fricke relation `f(−1/(11z)) = −11z²f(z)`; the functional equation `Λ(2 − s) = 11^{s−1}Λ(s)`, so `11^{s/2}Λ(s)` is invariant under `s ↦ 2 − s` (root number `+1`); `L(f, 1)` is a positive real number; and `11^{s/2}Λ(s)` is real on the critical line `s = 1 + it`. The functional equation of a Fricke eigenvector is TauCeti's; the eigenvalue `−1` comes from `η(−1/τ)² = −iτη(τ)²`. | [`Challenge.lean`](tau-track/TauTrack/ElevenFunctionalEquation/Challenge.lean) |
| [Ramanujan's tau function](tau-track/TauTrack/RamanujanTau) | The coefficients of `Δ` are the values of one multiplicative `τ : ℕ → ℤ` with `τ(p^(r+2)) = τ(p)τ(p^(r+1)) − p¹¹τ(p^r)`, the product formula, and `τ(n) ≡ σ₁₁(n)` mod 691. Multiplicativity and the recursion are TauCeti's. | [`Challenge.lean`](tau-track/TauTrack/RamanujanTau/Challenge.lean) |
| [Theta series are Siegel modular forms](tau-track/TauTrack/SiegelTheta) | For an even unimodular lattice `L` of rank `2k` and every degree `n`, `Θ_L(Z) = ∑_{x ∈ Lⁿ} exp(πi·tr(G(x)Z))` converges absolutely, is holomorphic, is bounded on `Im Z ≥ c·1`, and satisfies `Θ_L((AZ + B)(CZ + D)⁻¹) = det(CZ + D)^k Θ_L(Z)` for every `(A B; C D)` in `Sp(2n, ℤ)`: the four defining properties of a Siegel modular form of weight `k`. The proofs (in [`Siegel/`](tau-track/TauTrack/Siegel)) define Siegel modular forms, show they are Mathlib's modular forms in degree one, and exhibit the theta series of `E₈`. | [`Challenge.lean`](tau-track/TauTrack/SiegelTheta/Challenge.lean) |
| [Generators of `Sp(2n, ℤ)`](tau-track/TauTrack/SymplecticGeneration) | `Sp(2n, ℤ)` is generated by `J = (0 −1; 1 0)`, the translations `(1 S; 0 1)` with `S` symmetric, and the matrices `(U 0; 0 U⁻ᵀ)` with `U` in `GL(n, ℤ)`. The proof imports only Mathlib. | [`Challenge.lean`](tau-track/TauTrack/SymplecticGeneration/Challenge.lean) |
| [Relations between critical values of Ramanujan's `L`-function](tau-track/TauTrack/RamanujanLValues) | For `L(Δ, s)`, Mathlib's `L`-function of `Δ` (equal to `∑ τ(n) n^{−s}` for `Re s > 7`, and entire): `L(Δ, 4) = (25π²/72)·L(Δ, 2)`, `L(Δ, 6) = (π⁴/18)·L(Δ, 2)` and `L(Δ, 5) = (3π²/14)·L(Δ, 3)`. That `L(Δ, 2)` and `L(Δ, 3)` are non-zero is not proved here. The proofs (in [`Cohomology/`](tau-track/TauTrack/Cohomology)) go through the period polynomial of `Δ`: modulo `X¹⁰ − Y¹⁰` it is a combination of `X²Y²(X² − Y²)³` and `4X⁹Y − 25X⁷Y³ + 42X⁵Y⁵ − 25X³Y⁷ + 4XY⁹`. | [`Challenge.lean`](tau-track/TauTrack/RamanujanLValues/Challenge.lean) |
| [The symplectic group acts on the Siegel upper half-space](tau-track/TauTrack/Siegel) | For `M = (A B; C D)` real symplectic and `Z` symmetric with `Im Z` positive definite: `CZ + D` is invertible, `(AZ + B)(CZ + D)⁻¹` is again such a matrix, and this is a group action. A foundation for the theta-series result. | [`Challenge.lean`](tau-track/TauTrack/Siegel/Challenge.lean) |
| [The twelve characters of the modular group](tau-track/TauTrack/Tones) | Every homomorphism `χ` from `SL(2, ℤ)` to a commutative group has `χ(S) = χ(T)⁻³` and `χ(T)¹² = 1`. There is an additive map `p : SL(2, ℤ) → ℤ/12` with `p(T) = 1`, `p(S) = 9`, `p(−1) = 6`, given by an explicit formula in the entries modulo 12, such that `χ(γ) = χ(T)^{p(γ)}` for every such `χ` (so `p` is the abelianisation), `η(γτ)² = e^{2πi p(γ)/12}(cτ + d)η(τ)²`, and every character `SL(2, ℤ) → ℂˣ` is `γ ↦ e^{2πi k p(γ)/12}` for exactly one `k` in `ℤ/12`. | [`Challenge.lean`](tau-track/TauTrack/Tones/Challenge.lean) |

All nine are known mathematics. The source each proof follows, and whether it was consulted or
cited from memory, is recorded in its `formalization.yaml`.

Check them with `cd tau-track && lake exe cache get && ./check.sh`.
`check.sh` skips the comparator for a result that carries a `CI-SKIP` file, because its kernel
replay needs more memory than a CI runner has; the file says why. The Ramanujan `L`-values result
is such a result: check it locally with `lake comparator --config=TauTrack/RamanujanLValues/comparator.json`.

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
tau-track/                                     a second Lake package, same layout, with TauCeti
```

## How AI was used

The questions in this work are Richard Morley-Smith's: the links between areas of mathematics to
look for, and the choices of what to pursue. Claude (Anthropic), through Claude Code, found the
relevant theorems in the literature, chose the precise formal statements, and wrote the statements
and proofs in this repository under the author's direction. Each result's `formalization.yaml`
records what the AI did for that result, and which sources were read and which were cited without
being consulted.

Checking the results does not rely on trusting the AI. Every proof is verified by the Lean
kernel against Mathlib, and the Comparator checks that each proof establishes exactly the
statement in its `Challenge.lean` using only Lean's three standard axioms. One result,
the relations between values of Ramanujan's `L`-function, needs more memory for this check than a CI
runner has and is checked locally (see above). A check of statement fidelity (does each formal
statement say what its description says) was made in November 2026; its findings are in the commit
history.

## Licence

Apache-2.0. See [`LICENSE`](LICENSE).
