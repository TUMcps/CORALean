module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The tensor of `cubMap` as one quadratic form per pair

`T{i,k}` read at the pair `(i, k)`, one index `Fin (m * n)` through `finProdFinEquiv`: the
matrices `quadBilin` is applied to in `cubMapDepOn`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tensor read as one quadratic form per pair: `T{i,k}` at `(i, k)`. -/
def PolyZonotope.cubQuad (T : Fin m → Fin n → Mat ℝ n n) : Fin (m * n) → Mat ℝ n n :=
  fun l => T (finProdFinEquiv.symm l).1 (finProdFinEquiv.symm l).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
