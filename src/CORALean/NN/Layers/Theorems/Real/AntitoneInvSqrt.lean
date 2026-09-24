import CORALean.NN.Layers.Definitions.InvSqrt

/-!
# The clamped inverse square root falls

A reciprocal of a monotone square root of a monotone clamp.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem antitone_invSqrt : Antitone invSqrt := by
  intro a b hab
  unfold invSqrt
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
