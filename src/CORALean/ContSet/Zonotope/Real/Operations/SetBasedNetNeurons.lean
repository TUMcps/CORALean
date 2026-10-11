import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet

/-!
# `SetBasedNet.neurons`

`Σ_{k ∈ [κ]} n_k`, the widths of the layers' outputs added up, the bound [1, Prop. 16] puts on
the generators a forward propagation adds: a nonlinear layer adds `n_k` of them and a linear
one none.

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

def SetBasedNet.neurons : {n k : ℕ} → SetBasedNet n k → ℕ
  | _, _, .output => 0
  | _, _, @SetBasedNet.linear _ m _ _ _ tail => m + tail.neurons
  | n, _, .nonlinear _ _ _ tail => n + tail.neurons

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
