import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.Global.Partition

/-!
# `ξ_E`, the width `relaxExp` pays into an independent generator

Split out of `RelaxExp.lean` (issue #62): read again by the float layer's own
`relaxExp`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E`: how far the two monomials can drift apart, read at the one index
where their exponent columns may differ. -/
def PolyZonotope.relaxWidth (PZ : PolyZonotope α)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : ℕ :=
  PolyZonotope.eDiff (PZ.E k₀ (part.right 0)) (PZ.E k₀ (part.right 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
