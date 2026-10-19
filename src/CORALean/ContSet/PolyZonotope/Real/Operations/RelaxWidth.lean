module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiffTight
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `ξ_E`, the width `relaxExp` pays into an independent generator

Split out of `RelaxExp.lean` (issue #62). It is `eDiffTight` of the two exponents at the one index
where the columns may differ: the maximum of `|x^a - x^b|` itself, which CORA computes by
`minMaxDiffPoly` for each edge of its merge graph, and which is below the parity bound `eDiff` the
float layer's own `relaxExp` still reads.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E`: how far the two monomials can drift apart, read at the one index
where their exponent columns may differ. -/
noncomputable def PolyZonotope.relaxWidth (pZ : PolyZonotope α)
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : ℝ :=
  PolyZonotope.eDiffTight (pZ.E k₀ (part.right 0)) (pZ.E k₀ (part.right 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
