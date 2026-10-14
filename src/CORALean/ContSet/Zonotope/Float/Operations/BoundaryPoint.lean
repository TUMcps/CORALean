module

public import CORALean.ContSet.Zonotope.Float.Operations.BoundaryRatio

@[expose] public section

/-!
# `Zonotope.boundaryPoint`, over a floating-point scalar

CORA's `boundaryPoint(Z, dir, startPoint)`: `startPoint + t * dir` with `t` the largest step that
stays in the zonotope. The exit step is bounded above by `boundaryRatio` (a minimum over facet
rows, in place of CORA's linear program), and the result is the box swept by the step in
`[0, t_max]`: `startPoint` plus the corner products of `[0, t_max]` and `dir`, rounded outward.
The step is at least `0` (the lower end is clamped, `maximum zero`). `none` when no facet row has a
certified positive denominator.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box around the segment from `start` to `start + t_max * dir`. -/
def Zonotope.boundaryPoint (Z : Zonotope (Vec 𝕋 (n + 1))) (dir start : Vec 𝕋 (n + 1)) :
    Option (Interval (Vec 𝕋 (n + 1))) :=
  (Z.boundaryRatio dir start).map fun U =>
    let t := maximum zero U                                                 -- t_max, at least 0
    ⟨fun i => addDown (start i) (minimum zero (mulDown t (dir i))),
      fun i => addUp (start i) (maximum zero (mulUp t (dir i)))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
