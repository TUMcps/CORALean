module

public import CORALean.ContSet.ProbZonotope.Float.API
public import CORALean.ContSet.ProbZonotope.Real.API

/-!
# Probabilistic zonotopes

CORA's `probZonotope`: a zonotope of possible means and a covariance, standing for the Gaussian
laws `N(μ, Σ)` with `μ` in the zonotope. The float layer stores the mean zonotope in floats and
the covariance as an interval matrix, and states each operation's guarantee on the family of laws.
-/
