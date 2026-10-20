module

public import CORALean.ContDynamics.LinearSysDT.Operations.CanonicalFloat

@[expose] public section

/-!
# The linear system a linearization leaves behind

`linearize`: fresh rather than `NonlinearSys.linearize`, whose target
`LinearSys` carries a flow this system has none of. The canonical form at `A`,
`LinearSysDT.canonicalFloat`, its input the linearization's in state coordinates.

## Inputs
* `A` – state matrix

## Output
* the linear system with that matrix
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝕋 : Type} [CORALean.Float.FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linear system a linearization at any matrix `A` leaves behind. Fresh
rather than `NonlinearSys.linearize`, whose target `LinearSys` carries a flow
this system has none of. -/
def NonlinearSysDT.linearize (A : Mat 𝕋 n n) : LinearSysDT 𝕋 n :=
  LinearSysDT.canonicalFloat A

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
