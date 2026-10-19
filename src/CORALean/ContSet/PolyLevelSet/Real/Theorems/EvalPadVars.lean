module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.PadVars
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The rows of `PolyLevelSet.padVars`

A monomial reads each fresh variable at exponent zero, so the padded system's values at a point
are the original's at its first `n` variables.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The padded rows' values ignore the fresh variables. -/
theorem PolyLevelSet.eval_padVars (P : PolyLevelSet n) (r : ℕ) (x : Vec ℝ (n + r)) :
    (P.padVars r).eval x = P.eval fun k => x (Fin.castAdd r k) := by -- --- PROOF ---
  have hμ : PolyZonotope.monomial (PolyZonotope.padE P.R r) x
      = PolyZonotope.monomial P.R (fun k => x (Fin.castAdd r k)) := by
    funext l
    simp [PolyZonotope.monomial, PolyZonotope.padE, Fin.prod_univ_add]
  show P.A *ᵥ PolyZonotope.monomial (PolyZonotope.padE P.R r) x - P.b = _
  rw [hμ]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
