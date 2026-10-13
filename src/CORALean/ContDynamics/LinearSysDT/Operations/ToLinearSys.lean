module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The continuous-time system of a discrete-time one

CORA's `linearSys(linsysDT)` [1], its matrix-logarithm branch: `A = logm(A_d)/Δt` and, for
each of `B`, `c`, `E` that is not zero, `linsolve(A_d - I, A X)`. The matrix logarithm is an
argument `L` (one with `e^L = A_d`, as `logm` returns where it is real: Mathlib has none), and
`Δt` is as well, `LinearSysDT` counting steps. Where `logm` is not real or `linsolve` fails, CORA
runs `fmincon` on a cost of the discretization, not formalized (solver-dependent).

## References

* [1] `contDynamics/@linearSysDT/linearSys.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `A` of the returned system with `B`, `c`, `E`; the record keeps `A` only. -/
noncomputable def LinearSysDT.toLinearSys (sys : LinearSysDT ℝ n) (L : Mat ℝ n n) (Δt : ℝ)
    (B : Mat ℝ n m) (c : Vec ℝ n) (E : Mat ℝ n q) :
    LinearSys ℝ n × Mat ℝ n m × Vec ℝ n × Mat ℝ n q :=
  let A := Δt⁻¹ • L                                                  -- logm(sys.A)/sys.dt
  let M := sys.A - 1                                                 -- sys.A - eye(n)
  (⟨A⟩, M⁻¹ * (A * B), M⁻¹ *ᵥ (A *ᵥ c), M⁻¹ * (A * E))               -- linsolve(M, A*B), ...

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
