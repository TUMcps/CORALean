import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.ZeroMemDependentErr

/-!
# `dependent` loses no point

Read back through `ContSet`, for a caller that only wants the inclusion:
`dependent_nominal` places every point in the nominal set, and the box denotes
the origin alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.dependent_outer (PZ : PolyZonotope 𝕋 n) :
    PZ.construct ⊆ PZ.dependent.construct := fun x hx =>
  ⟨x, PolyZonotope.dependent_nominal PZ hx, 0,
    PolyZonotope.zero_mem_dependent_err PZ, add_zero x⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
