module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstruct

@[expose] public section

/-!
# An ellipsoid contains its centre

CORA's `center` is the field `q`; it is the image of the zero coefficient vector,
whatever the generators.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.centre_mem_construct (E : Ellipsoid n) : E.q ∈ E.construct := by
  have hu : ‖(0 : Vec ℝ E.k)‖₂ ≤ 1 := mem_unitBall₂.mp zero_mem_unitBall₂
  simpa using Ellipsoid.mem_construct (E := E) hu

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
