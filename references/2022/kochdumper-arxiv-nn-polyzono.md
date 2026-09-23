# Open- and Closed-Loop Neural Network Verification using Polynomial Zonotopes

N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification using Polynomial
Zonotopes". arXiv:2207.02715, 2022.

**Source:** https://arxiv.org/html/2207.02715v2  
**Inventory:** confirmed

Where propagating a set through a network as a polynomial zonotope comes
from, which is what `NN.enclose` does.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (§2) feed-forward neural network: weight matrices W_i and bias vectors b_i, i in {1,...,κ+1} | n/a — a preliminary restated from the literature, not a result of this paper |
| `Def. 2` | (§2) polynomial zonotope PZ = ⟨c, G, G_I, E⟩ with center c, dependent generators G, independent generators G_I, exponent matrix E | n/a — restated; tracked as `Def. 1` on [Sparse Polynomial Zonotopes](../2021/kochdumper-tac-sparse-polyzonotopes.md) |
| `Def. 3` | (§4) reachable set: solution ξ(t, x0, u_c(·), w(·)) of the system over initial states, control law, and disturbance trajectory | [`ReachSet.lean`](../../src/CORALean/ContDynamics/NeurNetContrSys/Definitions/ReachSet.lean) — at a *linear* plant with no disturbance set `w`, so `R(t)` has none to quantify over |
| `Prop. 1` | (§5) interval enclosure of a polynomial zonotope, I = [c+g1-g2-g3-g4, c+g1+g2+g3+g4] ⊇ PZ, splitting generators by exponent parity | [`PolyZonotope_to_Interval.lean`](../../src/CORALean/ContSet/Conversion/Real/PolyZonotope_to_Interval.lean) |
| `Prop. 2` | (§5) image of a quadratic function g(x)=a1 x^2+a2 x+a3 applied to a 1-D polynomial zonotope | n/a — done differently on purpose: `evalPoly` composed with `dependent` (see [`ActivationPoly.lean`](../../src/CORALean/NN/Layers/ActivationPoly.lean)) gives an exact image of a polynomial zonotope under any real polynomial, the quadratic case included, by making every independent generator dependent first rather than spending a new independent factor on the cross terms this proposition's own formula bounds |
| `Alg. 1` | (§3) enclosure of the image of a neural network layer by layer, using quadratic approximation of the activation and an added approximation-error term | [`Enclose.lean`](../../src/CORALean/NN/Operations/Enclose.lean), [`EncloseOuter.lean`](../../src/CORALean/NN/Theorems/EncloseOuter.lean), [`ActivationPoly.lean`](../../src/CORALean/NN/Layers/ActivationPoly.lean), [`PolyFit.lean`](../../src/CORALean/NN/Layers/PolyFit.lean) |
| `Alg. 2` | (§4) reachable set computation for a neural-network-controlled system, looping over control cycles: image through the controller (Alg. 1), Cartesian product with the plant reachable set, then nonlinear reachability analysis | [`Reach.lean`](../../src/CORALean/ContDynamics/NeurNetContrSys/Operations/Reach.lean), [`ReachSetSubsetReach.lean`](../../src/CORALean/ContDynamics/NeurNetContrSys/Theorems/ReachSetSubsetReach.lean) — at a *linear* plant with no disturbance set, and at the control-period boundaries only; the union over `R(τ_i)` of line 9 is not stated |
