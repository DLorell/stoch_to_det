# stoch_to_det

The original finite and joint-law endpoints are collected in
`stoch_to_det/MainTheorems.lean`:

- `stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint`: the finite-latent
  existence theorem.
- `stoch_to_det.Cdagger1771_lt_1771`: the strict numerical bound
  `Cdagger1771 < 1771`.

The current best certified two-variable endpoint is
`stoch_to_det.T_le_96 : IsPMF p → T p ≤ 96 * tau p`, assembled in
`stoch_to_det/SharedRace.lean`.

Its shared-race input applies to every finite source and finite nonempty label
alphabet. Posterior rows on `support μ` must be PMFs that are strictly positive
on every label; rows outside `support μ` are unrestricted. In the library's bit
units the inequality is `W ≤ 2I + d`. Equivalently, after converting the entropy
terms to natural-log units, it is `W_nats ≤ 2I_nats + (log 2)d`.

The finite interface, standalone clock laws, and entropy/KL assembly live in
the `stoch_to_det/SharedRace/` modules. The exact clock-cell analysis and
concrete grouped-Gumbel bridge require substantial additional work in
`stoch_to_det/Race.lean`. Together with the calibrated near/far mismatch charge
and exact hybrid ledger, they yield the unconditional 96 endpoint.


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
4. validates the audited endpoints' complete axiom dependencies against the
   expected set.

The expected axiom set for each public declaration is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The checker commands may also be run directly:

```sh
lake build --log-level=error stoch_to_det
lake env lean Verify.lean
lake env lean Verify96.lean
lake env lean VerifySharedRace.lean
```

## Reproducibility files

- `lean-toolchain` pins Lean.
- `lakefile.toml` declares the library and its Mathlib release.
- `lake-manifest.json` pins the complete transitive dependency graph.
- `stoch_to_det.lean` is the root module.
- `stoch_to_det/` contains the proof sources.
