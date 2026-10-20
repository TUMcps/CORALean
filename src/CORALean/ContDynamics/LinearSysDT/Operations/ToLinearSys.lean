module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The continuous-time system of a discrete-time one

CORA's `linearSys(linsysDT)` [1], its matrix-logarithm branch: `A = logm(A_d)/dt` and, for
each of `B`, `c`, `E` that is not zero, `linsolve(A_d - I, A X)`, `dt` the system's sampling
time. The matrix logarithm is an argument `L` (one with `e^L = A_d`, as `logm` returns where it
is real: Mathlib has none). Where `logm` is not real or `linsolve` fails, CORA
runs `fmincon` on a cost of the discretization, not formalized (solver-dependent).

## Inputs
* `sys` – discrete-time system
* `L` – matrix logarithm of the state matrix

## Output
* the continuous-time system with the same output equation

## References

* [1] `contDynamics/@linearSysDT/linearSys.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `linearSys(A, B, c, C, D, k, E, F)`, the output equation carried over as it stands. -/
noncomputable def LinearSysDT.toLinearSys (sys : LinearSysDT ℝ n) (L : Mat ℝ n n) :
    LinearSys ℝ n :=
  let A := sys.dt⁻¹ • L                                              -- logm(sys.A)/sys.dt
  let M := sys.A - 1                                                 -- sys.A - eye(n)
  let B := M⁻¹ * (A * sys.B)                                         -- linsolve(M, A*sys.B)
  let c := M⁻¹ *ᵥ (A *ᵥ sys.c)                                       -- linsolve(M, A*sys.c)
  let E := M⁻¹ * (A * sys.E)                                         -- linsolve(M, A*sys.E)
  ⟨sys.m, sys.q, sys.r, sys.s, A, B, c, sys.C, sys.D, sys.k, E, sys.F⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
