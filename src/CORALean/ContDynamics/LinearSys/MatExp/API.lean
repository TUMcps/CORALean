module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.API
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.API
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.API
public import CORALean.ContDynamics.LinearSys.MatExp.Counterexamples.API

/-!
# Enclosing a matrix exponential, collected

What a discretization needs and nothing else uses: `e^{AΔt}` is transcendental, so a step is
taken against an interval matrix around it rather than against it. `Operations` widens the
point exponential's enclosure to a whole interval matrix and to a matrix zonotope, at the usual
dependency-loss and correlation-preserving trade-offs of each, and pays that cost more
narrowly still where the second order is exactly computable. It also runs the choice the other
way: `ExpRemainderOrder`/`ExpRemainderStep` take an admissible error and name a parameter
meeting it, one step of adaptive parameter tuning and not the algorithm — the error bounded is
the exponential's, not the reachable set's.

`Definitions` collects what these enclosures are held to without itself being computed: the
error measures Wetzlinger et al. and CDC 2020 name (`Δε^h_k`, `Δε^{U,τ}_k`, `ε_H`, `ε_P`), the
exact tube an affine step's outer approximation encloses, and the two tuning knobs' specs.
-/
