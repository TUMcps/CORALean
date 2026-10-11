import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet

/-!
# `SetBasedNet.depth`

`κ`, the number of layers of a `SetBasedNet`, linear and nonlinear alike, against which
[1, Prop. 16] and [1, Prop. 17] count running time.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def SetBasedNet.depth : {n k : ℕ} → SetBasedNet n k → ℕ
  | _, _, .output => 0
  | _, _, .linear _ _ tail => tail.depth + 1
  | _, _, .nonlinear _ _ _ tail => tail.depth + 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
