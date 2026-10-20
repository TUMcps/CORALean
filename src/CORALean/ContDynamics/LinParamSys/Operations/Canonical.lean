module

public import CORALean.ContDynamics.LinParamSys.LinParamSys

@[expose] public section

/-!
# The canonical-form system at a given set of matrices

`ẋ = A x + u` with `A` in the set: `B` the point set `{I}` and `c = 0`, so its `IsTrajectory` is its
`IsCanonicalTrajectory`. It is the system an operation handed only the matrix set builds: an
enclosure of a parametric matrix, the linearization of a parametric nonlinear system, a
`LinearSys`'s point matrix.

## Inputs
* `A` – matrix set

## Output
* the canonical-form system with that matrix set
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [OfIdentity 𝕄]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(A, {I}, 0)`, `n` inputs. -/
abbrev LinParamSys.canonical (A : 𝕄 n n) : LinParamSys 𝕄 n :=
  ⟨A, n, OfIdentity.identity n, 0⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
