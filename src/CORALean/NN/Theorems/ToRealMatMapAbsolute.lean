import CORALean.Global.Float.SoundFloatArithmetic

/-!
# The absolute value of a float matrix reads as the absolute value
`absolute` is exact, so reading `W.map absolute` as reals is the entrywise absolute value of the
real reading of `W`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem toRealMat_map_absolute {m n : ℕ} (W : Mat 𝕋 m n) :
    (toRealMat W).map abs = toRealMat (W.map absolute) :=
  funext fun _ => funext fun _ => (toReal_absolute _).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
