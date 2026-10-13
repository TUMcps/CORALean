module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.affine`

[1, Prop. 4]: the image of `Z = ⟨c, G⟩` under the affine map `x ↦ W x + b` is the zonotope
`W Z ⊕ b = ⟨W c + b, W G⟩`, the generator count unchanged: the set-based forward propagation of a
linear layer [1, Prop. 6]. Its generators are those of `Zonotope.mtimes W Z`, its centre that
shifted by `b`.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.affine (W : Mat ℝ m n) (b : Vec ℝ m) (Z : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ m) where
  h := Z.h
  c := W *ᵥ Z.c + b
  G := fun j => W *ᵥ Z.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
