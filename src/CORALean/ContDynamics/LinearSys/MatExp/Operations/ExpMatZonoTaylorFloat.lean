module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTermFloat
public import CORALean.ContSet.Zonotope.Float.Operations.MatPlus

@[expose] public section

/-!
# `MatExp.expMatZonoTaylor`, over a floating-point scalar

`Real.MatExp.expMatZonoTaylor` rounded, the same recursion `i = 0 … η`, each partial sum
materialised before the next order joins it.

## Inputs
* `M` – float matrix zonotope

## Output
* float matrix zonotope of the Taylor truncation up to the given order

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.1]'s Taylor truncation as a float matrix zonotope, orders `0 … η`. -/
def MatExp.expMatZonoTaylor (M : Zonotope (Mat 𝕋 n n)) : ℕ → Zonotope (Mat 𝕋 n n)
  | 0 => MatExp.expMatZonoTerm M 0
  | k + 1 => (Zonotope.matPlus (MatExp.expMatZonoTerm M (k + 1))
      (MatExp.expMatZonoTaylor M k)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
