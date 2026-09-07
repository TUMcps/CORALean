import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.AbsMax
import CORALean.ContSet.Zonotope.Real.Operations.MatPow
import CORALean.ContSet.Zonotope.Real.Operations.Map
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# Matrix zonotopes: enclosing the exponential of a matrix zonotope

CORA's `expmInd`, which is what `expm` defers to: the finite Taylor sum kept as
a matrix zonotope, so that the correlations between a system matrix's entries
survive the powers, and the tail bounded through the interval matrix the
zonotope encloses, where no matrix-zonotope machinery is needed at all.

`expMatZonoTaylor` is `expIntervalTaylor`'s recursion at a zonotope: orders
`0 … η`, matching `expTaylor`'s `Finset.range (η + 1)` exactly. The remainder is
a box of one uniform width — `expRemainderBound` bounds a norm, not an entry —
and becomes a matrix zonotope with one generator per entry.

The order `η` is a choice, sound at any value: `expRemainderBound` widens to
cover whatever the sum left out.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- Order `i` of the series as a matrix zonotope: the zonotope's `i`-th power
scaled by `1/i!`. -/
noncomputable def MatExp.expMatZonoTerm (M : Zonotope (Mat ℝ n n)) (i : ℕ) :
    Zonotope (Mat ℝ n n) :=
  Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) ((Nat.factorial i : ℝ)⁻¹)) (M.matPow i)

/-- The Taylor truncation as a matrix zonotope, `i = 0 … η` matching
`MatExp.expTaylor`'s `Finset.range (η + 1)` exactly. -/
noncomputable def MatExp.expMatZonoTaylor (M : Zonotope (Mat ℝ n n)) :
    ℕ → Zonotope (Mat ℝ n n)
  | 0 => MatExp.expMatZonoTerm M 0
  | k + 1 => Zonotope.plus (MatExp.expMatZonoTerm M (k + 1)) (MatExp.expMatZonoTaylor M k)

/-- A box of uniform width `b` as a matrix zonotope: centre zero, and one
generator per entry carrying `b` there and nothing anywhere else. -/
noncomputable def MatExp.expMatZonoRemainder (m : ℕ) (b : ℝ) : Zonotope (Mat ℝ m m) where
  h := m * m
  c := 0
  G := fun k i j => if finProdFinEquiv (i, j) = k then b else 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor sum kept as a matrix zonotope, widened by the tail bound taken at
the dominating matrix of the interval matrix the zonotope encloses. -/
noncomputable def MatExp.expMatZonoEnclosure (M : Zonotope (Mat ℝ n n)) (η : ℕ) :
    Zonotope (Mat ℝ n n) :=
  Zonotope.plus (MatExp.expMatZonoTaylor M η)
    (MatExp.expMatZonoRemainder n (MatExp.expRemainderBound M.interval.absMax η))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
