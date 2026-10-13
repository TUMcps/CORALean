import CORALean.Global.Float.FloatOps

/-!
# A bound on the argument from the box alone

`max(|l|, |u|)`, with `l` and `u` not assumed of one sign: what an affine conjugate charges
the gap between its two slope roundings against, the argument being bounded by nothing
smaller than the box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A bound on `t` from the box alone. -/
def Relaxation.conjTBound (l u : 𝕋) : 𝕋 := maximum (absolute l) (absolute u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
