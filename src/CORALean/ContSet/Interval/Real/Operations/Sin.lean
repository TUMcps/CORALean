import CORALean.ContSet.Interval.Real.Operations.Cos

/-!
# `Interval.sin`

CORA's `@interval/sin`: `cos (I - π/2)`, the box shifted by `π/2` in every coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.sin (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) :=
  let J : Interval (Vec ℝ n) :=                                     -- I - pi/2
    { inf := fun i => I.inf i - Real.pi / 2, sup := fun i => I.sup i - Real.pi / 2 }
  Interval.cos J

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
