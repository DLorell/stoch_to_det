# An unconditional constant of 9.4

`Bound94.lean` proves

$$
T(p)\le \frac{47}{5}\,\tau(p)=9.4\,\tau(p).
$$

The only hypothesis on `p` is that it is a PMF on an arbitrary finite product
alphabet. The joint-law endpoint chooses one deterministic function before
quantifying over every measurable stochastic latent and its joint law.
The latent alphabet need not be finite. Zero probabilities and disconnected
support are covered by the existing reductions.

## Combine estimates of the same entropy

Let `W` denote shared-race entropy, `I` the mutual information between the
source and its sampled posterior label, and `d` categorical mismatch. The
fifth-power reference gives

$$
W\le(5+J_5)I+\frac{J_5}{\ln2}d,
\qquad J_5=\frac14-\frac1{18}+\frac1{42}-\frac1{76}+\frac1{120}
          =\frac{10219}{47880}.
$$

The sixth-power reference gives the same form with `5` replaced by `6` and

$$
J_6=\frac15-\frac1{22}+\frac1{51}-\frac1{92}+\frac1{145}-\frac1{420}
    =\frac{1465061}{8731030}.
$$

The correction `−1/420` follows from the elementary inequality, for `0≤x≤1`,

$$
\ln(1+x)\le x-\frac{x^2}{2}+\frac{x^3}{3}-\frac{x^4}{4}
                 +\frac{x^5}{5}-\frac{x^6}{12}.
$$

The difference between the right and left sides vanishes at zero and has
derivative `x⁵(1−x)/(2(1+x))≥0`. The sixth-power integral substitution turns
the correction into `−∫₀¹ x³⁴/12 dx = −1/420`.

Both bounds apply to the **same shared-race winner**. Only the reference
distribution used to bound its entropy changes. We may therefore take a
convex combination, with weights `3/28` on fifth power and `25/28` on sixth:

$$
W\le(a+J)I+\frac J{\ln2}d,\qquad
a=\frac{165}{28},\qquad
J=\frac{3J_5+25J_6}{28}=\frac{9625453351}{55738895520}.
$$

## Apply the existing coordinate ledger

For the optimal contact latent, let

$$
M=I(X;Y\mid L),\quad B=I(L;X\mid Y)+I(L;Y\mid X),\quad \tau=M+B.
$$

Write `hX` and `hY` for the seed-averaged entropies of the rounded label
conditional on each observed coordinate. The existing calibration ledger,
fiber transfer, and clustered contact mismatch estimate give

$$
\begin{aligned}
T&\le M-\tfrac12 B+\tfrac32(hX+hY),\\
hX+hY&\le(a+J)B+\frac{2J}{\ln2}d,\\
\frac d{\ln2}&\le\frac{733}{50}M+\frac{77}{50}b,
\qquad b\le M+B.
\end{aligned}
$$

Consequently,

$$
\begin{aligned}
T&\le\left(1+\frac{243}{5}J\right)M
   +\left(\frac32a-\frac12+\frac{153}{25}J\right)B\\
 &=\frac{872559880631}{92898159200}M
   +\frac{256730563553}{27322988000}B\\
 &\le\frac{47}{5}(M+B).
\end{aligned}
$$

The two coefficients are approximately `9.39264984522` and `9.39613791702`.
The last inequality uses `M,B≥0` and exact rational comparisons in Lean.

## Formalization

- `stoch_to_det/PoweredRaceFifth.lean`: fifth-power normalization and entropy estimate.
- `stoch_to_det/PoweredRaceSixthRefined.lean`: corrected sixth-power normalization and entropy estimate.
- `stoch_to_det/Bound94.lean`: interpolation, `T_le_94`, and the joint-law theorem.
- `stoch_to_det/ReadableStatement.lean`: finite probability-table statement with explicit entropy sums.
- `Verify.lean`: transitive proof checks and exact axiom guards for the new and existing endpoints.

Run `./verify.sh` for the source audit, complete library build, and endpoint checks.
The permitted axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
