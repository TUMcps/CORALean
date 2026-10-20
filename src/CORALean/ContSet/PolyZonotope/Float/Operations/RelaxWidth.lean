module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `ξ_E`, over a floating-point scalar

Split out of `RelaxExp.lean` (issue #62): read again by `relaxExpEven` in this
directory and by `Theorems/RelaxExpOuter.lean` and
`Theorems/RelaxExpEvenOuter.lean`, all outside this file.

## Inputs
* `pZ` – polynomial zonotope
* `part` – split with two selected generators
* `k₀` – factor index

## Output
* exponent difference of the two generators in that factor
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E`, read off the exponent matrix and so the exact layer's own width. -/
def PolyZonotope.relaxWidth (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : ℕ :=
  Real.PolyZonotope.eDiff (pZ.E k₀ (part.right 0)) (pZ.E k₀ (part.right 1))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
