import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexMonomial
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraVertex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Corner images of `isPolytopeCex`

The corner images of `PolyZonotope.isPolytopeCex` are `(2a + b, a c)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

set_option simprocs false in
/-- The corner images of the example: `(2a + b, a c)`. -/
theorem PolyZonotope.isPolytopeCex_coraVertex (I : Fin 3 → ℝ) :
    PolyZonotope.isPolytopeCex.coraVertex I = ![2 * I 0 + I 1, I 0 * I 2] := by -- --- PROOF ---
  -- sum over the three generators, then entry by entry
  unfold PolyZonotope.coraVertex
  erw [Fin.sum_univ_three]
  funext i
  fin_cases i
  all_goals
    simp only [PolyZonotope.isPolytopeCex, Fin.zero_eta, Fin.mk_one,
      PolyZonotope.isPolytopeCex_monomial]
  all_goals
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  all_goals ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
