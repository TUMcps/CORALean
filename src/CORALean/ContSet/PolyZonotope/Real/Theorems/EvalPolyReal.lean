import CORALean.Global.Mathlib

/-!
# The reference evaluator: Horner's rule over `ℝ`

Split out of `EvalPolyExact.lean` (issue #62): read again by the float layer's
own `Theorems/EvalPolyOuter.lean`, by `Theorems/EvalPolyRealOfFn.lean`, and by
`NN.Layers.Theorems.ActivationPolySound`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reference evaluator: Horner's rule over `ℝ`, coefficients lowest degree
first, exactly `evalPoly`'s own recursion carried to a single coordinate. -/
def PolyZonotope.evalPolyReal (coeffs : List ℝ) (x : ℝ) : ℝ :=
  match coeffs with
  | [] => 0
  | a :: rest => a + x * PolyZonotope.evalPolyReal rest x

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
