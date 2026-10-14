module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# `ConPolyZono.unionUpperB`

What the two selector rows are held to: `α₁α₂ = 1` and the selector polynomial
`= 0`, both crisp, so both are `Interval.point`s. [1, Thm. 1] writes them as the
scalars `b̂ = 1` and `b̄ = 0`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand sides of the two selector rows. -/
def ConPolyZono.unionUpperB : Interval (Vec ℝ (1 + 1)) :=
  ConPolyZono.plusB (Interval.point (fun _ => (1 : ℝ))) (Interval.point (0 : Vec ℝ 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
