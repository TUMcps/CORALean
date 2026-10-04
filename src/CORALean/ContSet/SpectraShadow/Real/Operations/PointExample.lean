import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.pointExample`

The point `{0}` of `ℝ¹` as `1 ⪰ 0` with `A₁ = 0` and `G = 0`, the counterexample set of
`SpectraShadow.supportFuncCoraAllZero_ne_supportFunc`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.pointExample : SpectraShadow (Vec ℝ 1) :=
  ⟨1, 1, 1, fun _ => 0, 0, fun _ => 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
