module

public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyLevelSet.lhs` over a floating-point scalar

The rows' polynomial part as a polynomial zonotope over `Vec 𝕋 m`, as over ℝ: the columns of `A`
as dependent generators at the exponents `R`, no center, no independent generators, an error box
that is the origin. Whatever a `PolyZonotope` operation does to its generators is then done to
the rows' coefficients.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows' polynomial part, as a polynomial zonotope over `Vec 𝕋 m`. -/
def PolyLevelSet.lhs (P : PolyLevelSet 𝕋 n) : PolyZonotope (Vec 𝕋 P.m) where
  p := n
  h := P.q
  q := 0
  c := fun _ => zero
  G := fun l i => P.A i l
  E := P.R
  GI := Fin.elim0
  I_error := Interval.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
