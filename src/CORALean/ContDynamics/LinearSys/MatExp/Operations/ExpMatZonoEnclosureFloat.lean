module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTaylorFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Float.Operations.MatPlusInterval

@[expose] public section

/-!
# `MatExp.expMatZonoEnclosure`, over a floating-point scalar

`Real.MatExp.expMatZonoEnclosure` rounded, CORA's `expmInd` at [1, Sec. 3.3.2]: the
Taylor sum kept as a float matrix zonotope, and the tail bounded through the interval
matrix the zonotope encloses — `expRemainderBound` at `normUpperBound` of its `interval`,
as `expIntervalEnclosure` bounds it — added as an interval matrix into the box.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor sum as a matrix zonotope, widened by the tail bound taken at the
interval matrix the zonotope encloses. -/
def MatExp.expMatZonoEnclosure (M : Zonotope (Mat 𝕋 n n)) (η : ℕ) : Zonotope (Mat 𝕋 n n) :=
  let T := MatExp.expMatZonoTaylor M η                                     -- the Taylor sum
  let b := MatExp.expRemainderBound (MatExp.normUpperBound M.matInterval) η   -- its tail, entrywise
  Zonotope.matPlusInterval T (MatExp.expMatZonoRemainder n b)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
