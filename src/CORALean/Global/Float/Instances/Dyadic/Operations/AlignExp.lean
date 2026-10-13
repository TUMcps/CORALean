import CORALean.Global.Float.Instances.Dyadic.Operations.AlignGuard

/-!
# The exponent a sum is coarsened to

Both operands of `addUp`/`addDown` are coarsened to `alignGuard p` binades below the larger
exponent, so the alignment inside the exact sum spans at most `alignGuard p` bits whatever the
operands' exponents.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Dyadic

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def alignExp (a b : Dyadic p) : ℤ := max a.exponent b.exponent - alignGuard p

end Dyadic

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
