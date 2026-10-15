module

public import CORALean.ContSet.Taylm.Float.Operations.ReexpandAt

@[expose] public section

/-!
# `Taylm.reexpand`, over a floating-point scalar

CORA's `reexpand(obj, int)`: the model re-expanded at the center `m` of a sub-box of the normalized
box and rescaled by its radius `r`, so that the new variables again range over `[-1, 1]`; the
remainder is kept, and widened by what storing each new coefficient costs. The center and radius are
the floats the caller supplies (a sub-box's `(lo + hi)/2` and `(hi - lo)/2` are not exact in the
scalar); the expansion substitutes one variable after another, in order.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.reexpand (m r : Vec 𝕋 n) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  (List.finRange n).foldl (fun T k => T.reexpandAt k (m k) (r k)) T

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
