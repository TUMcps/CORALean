module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalMulVecSet
public import CORALean.Global.Err

@[expose] public section

/-!
# `ε_P([t_i,t_i+Δt_i])`, eq. (22)

[1]'s eq. (22): `ε_P([t_i,t_{i+1}]) = err(e^{At_i} E(Δt_i,η_i) Δt_i U)`, the error of the
inhomogeneous solution over the `i`-th step — `err` of `PR^+([0,Δt]) = E(Δt,η)ΔtU` (eq. (20))
carried to `t_i` by `e^{At_i}` as eq. (2) requires. `err` is `Global/Err.lean`'s `r(box(·))`,
[1, Prop. 1]'s radius of the smallest hypersphere at the origin enclosing the box, so this is the
Euclidean quantity [1] states and not a supremum-norm stand-in.

`E(Δt,η)` is the interval matrix `[−E_abs(Δt,η), E_abs(Δt,η)]` of eq. (15)-(16), `E_abs` being
`MatExp.expRemainderMat`, and `intervalMulVecSet` is that interval matrix acting on a set of
vectors. It reads the radius as `|E_abs|`, which is `E_abs` itself at every step `Δt ≥ 0`.

`LinearSys.timePointStepRemainderError` is a different number: a scalar upper bound at the base
step `t_i = 0`, built from a zonotope's `absBound`s and the operator-norm remainder, rather than
`err` of the set.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `e^{At_i} E(Δt,η) Δt U`, the set eq. (22) takes `err` of: eq. (20)'s `PR^+([0,Δt])` carried
to the `i`-th step. -/
noncomputable def MatExp.particularRemainderSet (A : Mat ℝ n n) (ti : ℝ) (U : Set (Vec ℝ n))
    (Δt : ℝ) (η : ℕ) : Set (Vec ℝ n) :=
  (fun x => (exp (ti • A)).mulVec x) '' MatExp.intervalMulVecSet (MatExp.expRemainderMat A Δt η)
    (Δt • U)

/-- [1]'s eq. (22): `ε_P([t_i,t_i+Δt]) := err(e^{At_i} E(Δt,η) Δt U)`. -/
noncomputable def MatExp.particularRemainderError (A : Mat ℝ n n) (ti : ℝ) (U : Set (Vec ℝ n))
    (Δt : ℝ) (η : ℕ) : ℝ :=
  err (MatExp.particularRemainderSet A ti U Δt η)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
