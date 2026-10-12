import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPolytopeCora
import Mathlib.Data.Fin.VecNotation

/-!
# CORA's `representsa_(Z,'polytope')` returns a set other than `Z`

For `Z = zonotope([0;0], eye(2))` the set CORA's `@zonotope/representsa_.m` returns as second
output for `'polytope'` (`S = polytope(S)` with `S = []`, line 113) is empty, while `Z` contains its
centre. Wrong output, not a soundness issue: no caller in `~/CORA` reads it.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.representsaPolytopeCora_ne_construct :
    let Z : Zonotope (Vec ℝ 2) := ⟨2, 0, ![![1, 0], ![0, 1]]⟩
    Z.representsaPolytopeCora ≠ Z.construct := by -- --- PROOF ---
  intro Z h
  -- the centre is a point of `Z` (all coefficients `0`)
  have hc : Z.c ∈ Z.construct := ⟨0, fun j => by simp, by simp⟩
  rw [← h] at hc
  exact hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
