module

public import CORALean.ContSet.Zonotope.Real.Operations.Rotate
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost

@[expose] public section

/-!
# `Zonotope.rotateCost`

Asserted, not proved: `Operations/Rotate.lean` is `Zonotope.mtimes` at the plane
rotation `rotMat`, whose two nonzero entries cost a `cos` and a `sin`, priced
at one operation each, on top of `Zonotope.mtimesCost n n h`: the matrix is
applied dense, the zeros of the rotation not being exploited.

The rotation matrix is a result of its own, `n * n` writes, zeros included; the product writes
its result inside `mtimesCost`.

## Inputs
* `n` – dimension
* `h` – generator count

## Output
* cost of sine, cosine, rotation matrix and product
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.rotate` costs at `Vec ℝ n` and `h` generators: the sine and the cosine, the
`n * n` writes of the rotation matrix, and the product. -/
def Zonotope.rotateCost (n h : ℕ) : Cost := ⟨2 + n * n⟩ + Zonotope.mtimesCost n n h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
