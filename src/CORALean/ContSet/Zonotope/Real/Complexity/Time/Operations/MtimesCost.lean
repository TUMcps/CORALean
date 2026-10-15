module

public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the centre and each of the
`h` generators through `M *ᵥ ·`, so it pays `h + 1` matrix-vector products at
`m × n` and nothing else.

`mtimesCost_mono` is what lets a caller use a *bound* on `h` rather than `h`
itself, which is how the reachability bound in `ContDynamics/` is assembled.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.mtimes` costs at `M : Mat ℝ m n` and `h` generators: one
matrix-vector product for the centre and one per generator. -/
def Zonotope.mtimesCost (m n h : ℕ) : Cost := (h + 1) • Cost.matVec m n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
