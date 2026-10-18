module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# `ConPolyZono.unionUpperB`

What the two selector rows are held to: `α₁α₂ = 1` and the selector polynomial
`= 0`, which [1, Thm. 1] writes as the scalars `b̂ = 1` and `b̄ = 0`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The right-hand sides of the two selector rows. -/
def ConPolyZono.unionUpperB : Vec ℝ (1 + 1) :=
  ConPolyZono.plusB (fun _ => (1 : ℝ)) (0 : Vec ℝ 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
