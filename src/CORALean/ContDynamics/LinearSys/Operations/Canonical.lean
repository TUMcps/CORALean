module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# The canonical-form system at a given `A`

`ẋ = A x + u`, `y = x`: the system `(A, I, 0, I, 0, 0, 0, I)`, which is what CORA's
`canonicalForm` returns at `C = I`. Its `IsTrajectory` is its `IsCanonicalTrajectory`, `B = I` and
`c = E = 0` adding nothing to the input in state coordinates, so it is the system an operation
handed only a state matrix builds: a linearization, a time inversion, the point matrix of a
parametric system.

## Inputs
* `A` – system matrix

## Output
* linear system in canonical form with the given matrix
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝕋 : Type} [Zero 𝕋] [One 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, I, 0, I, 0, 0, 0, I)`, every dimension `n`. -/
abbrev LinearSys.canonical (A : Mat 𝕋 n n) : LinearSys 𝕋 n :=
  ⟨n, n, n, n, A, 1, 0, 1, 0, 0, 0, 1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
