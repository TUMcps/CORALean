module

public import CORALean.NN.Definitions.SmoothNetwork

@[expose] public section

/-!
# The dimension of the input CORA's conversion adds

CORA's `dim_u`: one block per linear layer, the size of its bias.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `dim_u`: the sizes of the linear layers' biases, added up. -/
def SmoothNetwork.nu : ∀ {n k : ℕ}, SmoothNetwork n k → ℕ
  | _, _, .output => 0
  | _, _, .linear (m := m) _ _ rest => m + rest.nu
  | _, _, .elementwiseAffine _ _ rest => rest.nu
  | _, _, .tanh rest => rest.nu
  | _, _, .relu rest => rest.nu
  | _, _, .sigmoid rest => rest.nu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
