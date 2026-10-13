import CORALean.ContSet.Zonotope.Real.Operations.TensorMultiplication
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# `Zonotope.tensorMultiplication_zono`

CORA's `@zonotope/tensorMultiplication_zono.m`: the tensor is a matrix zonotope
`M = {M.center + Σᵢ γᵢ M.generator{i} | γᵢ ∈ [-1, 1]}`, here a `Zonotope` over the tensor space
`Zonotope.Tensor3 n` (a zonotope over any real module, as for the matrix zonotope). The result is
`tensorMultiplication(Z, M.center)` plus, in a loop over the generators, `tensorMultiplication(Z,
M.generator{i})` with Minkowski sums.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `tensorMultiplication_zono(Z, M, options)` for a third-order tensor zonotope `M`. -/
noncomputable def Zonotope.tensorMultiplication_zono (Z : Zonotope (Vec ℝ n))
    (M : Zonotope (Zonotope.Tensor3 n)) (L : Zonotope.TensorLists Z.h) :
    Zonotope (Vec ℝ n) :=
  let Zres := Z.tensorMultiplication M.c L
  -- `for i = 1:M.numgens, Zres = Zres + tensorMultiplication(Z, M.generator{i})`
  (List.finRange M.h).foldl (fun Zres i => Zres.plus (Z.tensorMultiplication (M.G i) L)) Zres

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
