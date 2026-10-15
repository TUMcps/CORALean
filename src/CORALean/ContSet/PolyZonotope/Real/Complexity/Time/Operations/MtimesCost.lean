module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `PolyZonotope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` is `map` at `M *ᵥ ·`, so it pays
one matrix-vector product for the centre and one for each generator of either
block, and nothing for the exponent matrix.

Written as `mapCost` at `Cost.matVec m n` rather than spelt out again, which is
what `map` being the general form is worth: a second linear layer priced
differently changes the argument and not the shape.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.mtimes` costs at `M : Mat ℝ m n` on `h` dependent and
`q` independent generators: `h + q + 1` matrix-vector products at `m × n`. -/
def PolyZonotope.mtimesCost (m n h q : ℕ) : Cost :=
  PolyZonotope.mapCost (Cost.matVec m n) h q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
