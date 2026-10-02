import CORALean.ContSet.Interval.Float.Theorems.NormLe
import CORALean.ContSet.Zonotope.Float.Operations.NormSq

/-!
# `Zonotope.normSq` bounds every member

The box contains the zonotope (`Zonotope.interval_contains`) and a certificate `σ` with
`normSq ≤ σ·σ` makes `|σ|` an upper bound of `Interval.norm`. An upper bound only, and not
tight in general: a box is larger than its zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.normSq_le (Z : Zonotope 𝕋 n) {σ : 𝕋}
    (hσ : toReal Z.normSq ≤ toReal (mulDown σ σ)) {x : Vec ℝ n} (hx : x ∈ Z.construct) :
    ‖x‖₂ ≤ toReal (absolute σ) :=
  Interval.norm_le Z.interval hσ (Zonotope.interval_contains Z hx)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
