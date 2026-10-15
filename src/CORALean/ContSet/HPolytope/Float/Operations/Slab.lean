module

public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows

@[expose] public section

/-!
# `HPolytope.slab`, over a floating-point scalar

`lo ≤ A x ≤ hi`, as the two inequalities `A x ≤ hi` and `-A x ≤ -lo`: what an equality with a
rounded right-hand side becomes when no certificate keeps it (`ConZonotope.anchorSlab`). Negation is
exact, so the rows copy `A` and `lo` and compute nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.slab (A : Mat 𝕋 q n) (lo hi : Vec 𝕋 q) : HPolytope 𝕋 (Vec 𝕋 n) :=
  (HPolytope.ineqs A hi).stackRows
    (HPolytope.ineqs (fun i j => neg (A i j)) fun i => neg (lo i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
