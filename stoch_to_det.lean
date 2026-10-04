import stoch_to_det.Prelude
import stoch_to_det.Entropy
import stoch_to_det.Toolkit
import stoch_to_det.Functionals
import stoch_to_det.Envelope
import stoch_to_det.Duality
import stoch_to_det.Connected
import stoch_to_det.Constants
import stoch_to_det.Floor
import stoch_to_det.Seed
import stoch_to_det.Quotient
import stoch_to_det.Mismatch
import stoch_to_det.Scalar
import stoch_to_det.Cone
import stoch_to_det.SeedConstant
import stoch_to_det.Race
import stoch_to_det.Main
import stoch_to_det.Constants1771
import stoch_to_det.SeedConstant1771
import stoch_to_det.Main1771
import stoch_to_det.ConstantBound1771
import stoch_to_det.GeneralLatent
import stoch_to_det.JointLatent
import stoch_to_det.MainTheorems
import stoch_to_det.Bound94
import stoch_to_det.ReadableStatement

/-!
# stoch_to_det — root module

The deterministic-partition functional `T` is at most a universal constant
times the auxiliary-variable functional `τ`.

The bound `T_le_94` gives constant `47/5 = 9.4`, with the joint-law endpoint
`generalized_stoch_to_det_94_joint`. The finite probability-table formulation is
`NaturalLatentsFinite.natural_latents_linear_bound` in `stoch_to_det.ReadableStatement`.

The historical Main Theorem is `stoch_to_det.T_le_Cstar`. The improved finite theorem,
ordinary joint-law theorem, and LessWrong joint-law corollary are respectively
`stoch_to_det.T_le_1771`, `stoch_to_det.generalized_stoch_to_det_Cdagger1771_joint`, and
`stoch_to_det.LW_sum_1771_joint`. The corresponding posterior-mixture interface remains
available as `stoch_to_det.generalized_stoch_to_det_Cdagger1771` and `stoch_to_det.LW_sum_1771`.
The three 1771 public endpoints are declared together in
`stoch_to_det.MainTheorems` with their information sums displayed explicitly. Its
rounded deterministic intermediate is `stoch_to_det.LW_sum_1771_joint_deterministic`,
while `stoch_to_det.LW_sum_1771_joint` has the deliberately weaker conclusion
`G : Latent p` with no determinism assumption.
-/
