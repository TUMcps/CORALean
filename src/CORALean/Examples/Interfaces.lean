/-!
# Reading a scalar as a native `Float`

`ToF` is what `RunCheck` prints and tests for NaN through: any scalar the run checker executes at
is read back as a hardware `Float`. Its instances sit beside the executable.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.RunCheck


-- ========================================  MAIN TYPE  ========================================= --

/-- Reads a scalar as a native `Float`, for printing and the NaN test. -/
class ToF (𝕋 : Type) where
  toF : 𝕋 → Float

end CORALean.RunCheck


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
