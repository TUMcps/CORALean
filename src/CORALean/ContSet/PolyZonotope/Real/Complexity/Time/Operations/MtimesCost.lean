module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `PolyZonotope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` is `map` at `M *ᵥ ·`, so it pays
one matrix-vector product for the center and one for each generator of either
block, each writing its result, and the `p * h` writes of the exponent matrix, which the result
carries.

Written as `mapCost` at `Cost.matVec m n` rather than spelt out again, which is
what `map` being the general form is worth: a second linear layer priced
differently changes the argument and not the shape.

## Inputs
* `m` – output dimension
* `n` – input dimension
* `p` – number of factors
* `h` – dependent generator count
* `q` – independent generator count

## Output
* operation count of the matrix product
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.mtimes` costs at `M : Mat ℝ m n` on `p` factors, `h` dependent and `q`
independent generators: `h + q + 1` matrix-vector products at `m × n`, and `p * h` writes for the
exponent matrix. -/
def PolyZonotope.mtimesCost (m n p h q : ℕ) : Cost :=
  PolyZonotope.mapCost (Cost.matVec m n) p h q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
