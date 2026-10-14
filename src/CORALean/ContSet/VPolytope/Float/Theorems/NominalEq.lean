module

public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.nominal_eq`

-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The nominal vertex list, so proofs can see through the instance. Through it
every count is `P.k`, where going via the instance gives the equal-but-distinct
`(nominal P).k`. -/
theorem VPolytope.nominal_eq [SoundFloatArithmetic 𝕋] (P : VPolytope (Vec 𝕋 n)) :
    InflatedContSet.nominal P
      = CORALean.Real.VPolytope.mk P.k (fun l i => toReal (P.V l i)) := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
