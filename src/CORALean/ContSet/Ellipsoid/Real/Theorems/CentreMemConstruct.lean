import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstruct

/-!
# An ellipsoid contains its centre

CORA's `center` is the field `q`; it is the image of the zero coefficient vector,
whatever the generators.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.centre_mem_construct (E : Ellipsoid n) : E.q ∈ E.construct := by
  have hu : ‖(0 : Vec ℝ E.k)‖₂ ≤ 1 := mem_unitBall₂.mp zero_mem_unitBall₂
  simpa using Ellipsoid.mem_construct (E := E) hu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
