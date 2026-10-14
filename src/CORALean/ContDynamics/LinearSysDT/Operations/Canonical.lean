module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# The canonical-form system at a given `A`

`x(k+1) = A x(k) + u(k)`, `y(k) = x(k)`: the system `(A, I, 0, I, 0, 0, 0, I)`, as
`LinearSys.canonical` is in continuous time. Its `Trajectory` is its `CanonicalTrajectory`, so
it is the system an operation handed only a state matrix builds: a discretization, a
linearization, an observer's error dynamics.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝕋 : Type} [Zero 𝕋] [One 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, I, 0, I, 0, 0, 0, I)`, every dimension `n`. -/
abbrev LinearSysDT.canonical (A : Mat 𝕋 n n) : LinearSysDT 𝕋 n :=
  ⟨n, n, n, n, A, 1, 0, 1, 0, 0, 0, 1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
