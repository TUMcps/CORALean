module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# `Zonotope.embed`

The zero-padding map: coordinate `proj k` of the image is coordinate `k`, all others are `0`.
It is the transpose of the selection matrix, and linear.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.embed (proj : Fin n → Fin N) : Vec ℝ n →ₗ[ℝ] Vec ℝ N :=
  Matrix.mulVecLin (Matrix.of fun (i : Fin N) (k : Fin n) => if proj k = i then (1 : ℝ) else 0)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
