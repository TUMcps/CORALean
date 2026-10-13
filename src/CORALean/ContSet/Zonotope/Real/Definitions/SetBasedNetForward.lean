import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNet
import CORALean.ContSet.Zonotope.Real.Operations.Affine
import CORALean.ContSet.Zonotope.Real.Operations.ImageEnclosure

/-!
# `SetBasedNet.forward`

The set-based forward propagation of [1, Prop. 6] through a `SetBasedNet`: `H_k = W_k H_{k-1} + b_k`
(`Zonotope.affine`) at a linear layer and the image enclosure of [1, Alg. 1]
(`Zonotope.imageEnclosure`) at a nonlinear one, from the input set `H_0` to the output set
`Y = H_κ`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SetBasedNet.forward : {n k : ℕ} → SetBasedNet n k → Zonotope (Vec ℝ n) →
    Zonotope (Vec ℝ k)
  | _, _, .output, H => H
  | _, _, .linear W b tail, H => tail.forward (H.affine W b)
  | _, _, .nonlinear m eLo eUp tail, H => tail.forward (H.imageEnclosure m eLo eUp)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
