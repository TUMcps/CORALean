import CORALean.ContSet.ConZonotope.Real.Cost.Map
import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes

/-!
# `ConZonotope.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the centre and each of the
`h` generators through `M *ᵥ ·` and carries the constraint polytope over
unchanged, so it pays `h + 1` matrix-vector products and nothing else.

The same count as `Zonotope.mtimesCost`, which is the useful thing to be able
to say: a linear map is exactly as cheap on a constrained zonotope as on an
unconstrained one, because the constraints live over the coefficients and a
linear map does not move those.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.mtimes` costs at `M : Mat ℝ m n` and `h` generators: one
matrix-vector product for the centre and one per generator. -/
def ConZonotope.mtimesCost (m n h : ℕ) : Cost := ConZonotope.mapCost (Cost.matVec m n) h

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mtimesCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    ConZonotope.mtimesCost m n h ≤ ConZonotope.mtimesCost m n h' :=
  ConZonotope.mapCost_mono _ hh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
