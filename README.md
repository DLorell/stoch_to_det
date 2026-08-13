# stoch_to_det

The headline declarations are collected in
`stoch_to_det/MainTheorems.lean`:

- `stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint` <- This is the existence theorem of the finite bound.
- `stoch_to_det.Cdagger1771_lt_1771` <- This is the theorem which says C <= 1771

The current best certified two-variable endpoint is
`stoch_to_det.T_le_517`, declared in `stoch_to_det/Final517.lean`.


## Verification

Install `elan`, then run from this directory:

```sh
./verify.sh
```

The first run may download the pinned Lean toolchain and Mathlib dependencies.
The verifier:

1. rejects unfinished or disallowed source constructs;
2. builds the complete library;
3. checks transitively that the public declarations contain no `sorryAx`; and
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
