module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
public import CORALean.Global.Partition

@[expose] public section

/-!
# `ξ_E`, the width `relaxExp` pays into an independent generator

Split out of `RelaxExp.lean` (issue #62): read again by the float layer's own
`relaxExp`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E`: how far the two monomials can drift apart, read at the one index
where their exponent columns may differ. -/
def PolyZonotope.relaxWidth (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : ℕ :=
  PolyZonotope.eDiff (pZ.E k₀ (part.right 0)) (pZ.E k₀ (part.right 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
