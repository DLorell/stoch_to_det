# stoch_to_det

For every joint distribution of finite observables $X,Y$, there is one deterministic
$\Gamma=g(X,Y)$ such that

$$
I(X;Y\mid\Gamma)+H(\Gamma\mid X)+H(\Gamma\mid Y)
\le \frac{47}{5}\bigl(I(X;Y\mid V)+I(V;X\mid Y)+I(V;Y\mid X)\bigr)
$$

for every stochastic latent $V$ with that observable marginal. The constant is
$47/5=9.4$, and all information quantities are in bits. The same $\Gamma$ works for
all such $V$, with at most $|X\times Y|$ labels. Zero-probability entries are allowed.

## Main results

- [`stoch_to_det.T_le_94`](stoch_to_det/Bound94.lean) proves the finite optimization
  bound $T(p)\le (47/5)\tau(p)$.
- [`stoch_to_det.generalized_stoch_to_det_94_joint`](stoch_to_det/Bound94.lean)
  gives the displayed inequality for arbitrary measurable latent alphabets.
- [`NaturalLatentsFinite.natural_latents_linear_bound`](stoch_to_det/ReadableStatement.lean)
  states the finite-latent case directly using probability tables, with explicit
  definitions of entropy, conditional entropy, and mutual information.

The proof combines fifth- and sixth-power reference bounds for the same shared-race
entropy, then applies a coordinate entropy bound and a refined mismatch estimate.
See [the derivation of the constant](docs/constant-9-4.md).

The earlier 1771 results remain available in
[`stoch_to_det/MainTheorems.lean`](stoch_to_det/MainTheorems.lean).

## Verification

Install `elan`, then run from this directory:

```sh
./verify.sh
```

The first run may download the pinned Lean toolchain and Mathlib dependencies.
The pins are Lean `v4.33.0-rc2` and Mathlib `v4.33.0-rc2`; `lake-manifest.json`
records the exact dependency commits.
The verifier:

1. rejects unfinished or disallowed source constructs;
2. builds the complete library;
3. checks transitively that the three 9.4 endpoints and the retained 1771 endpoints
   contain no `sorryAx`; and
4. validates their complete axiom dependencies against the expected set.

The expected axiom set for each public declaration is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The two checker commands may also be run directly:

```sh
lake build --log-level=error stoch_to_det
lake env lean Verify.lean
```

## Reproducibility files

- `lean-toolchain` pins Lean.
- `lakefile.toml` declares the library and its Mathlib release.
- `lake-manifest.json` pins the complete transitive dependency graph.
- `stoch_to_det.lean` is the root module.
- `stoch_to_det/` contains the proof sources.
