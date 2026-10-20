module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `MatExp.expMatZonoRemainder`, over a floating-point scalar

`Real.MatExp.expMatZonoRemainder`'s box of uniform width `b`, kept as the interval matrix
`[-b, b]` it denotes rather than one generator per entry: a float matrix zonotope already
carries an interval-matrix box, and the remainder joins it there (`plusInterval`),
adding no generators to what later products multiply.

## Inputs
* `m` – matrix dimension
* `b` – float entry bound

## Output
* float interval matrix with every entry within the bound

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

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.3.2]'s tail: every entry within `b`, as an interval matrix. -/
def MatExp.expMatZonoRemainder (m : ℕ) (b : 𝕋) : Interval (Mat 𝕋 m m) :=
  ⟨fun _ _ => neg b, fun _ _ => b⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
