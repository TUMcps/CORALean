module

public import CORALean.ContSet.Zonotope.Float.Operations.TensorMultiplication
public import CORALean.ContSet.Zonotope.Float.Operations.Plus

@[expose] public section

/-!
# `Zonotope.tensorMultiplication_zono`, over a floating-point scalar

CORA's `@zonotope/tensorMultiplication_zono.m`: the tensor is a matrix zonotope
`M = {M.center + Σᵢ γᵢ M.generator{i} | γᵢ ∈ [-1, 1]}`, here a `Zonotope` over the float tensor
space `Zonotope.Tensor3 𝕋 n`, of which the center and the generators are read (its box is not: a
caller passes the stored tensors). The result is `tensorMultiplication(Z, M.center)` plus, in a
loop over the generators, `tensorMultiplication(Z, M.generator{i})` with Minkowski sums.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.tensorMultiplication_zono (Z : Zonotope (Vec 𝕋 n))
    (M : Zonotope (Zonotope.Tensor3 𝕋 n))
    (L : Real.Zonotope.TensorLists Z.absorbRounding.h) : Zonotope (Vec 𝕋 n) :=
  let Zres := Z.tensorMultiplication M.c L
  -- `for i = 1:M.numgens, Zres = Zres + tensorMultiplication(Z, M.generator{i})`
  (List.finRange M.h).foldl (fun Zres i => Zres.plus (Z.tensorMultiplication (M.G i) L)) Zres

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
