module

public import CORALean.ContSet.Zonotope.Float.Operations.TensorHDiff
public import CORALean.ContSet.Zonotope.Float.Operations.Dependent
public import CORALean.ContSet.Zonotope.Float.Operations.GeneratorError

@[expose] public section

/-!
# `Zonotope.tensorMultiplication`, over a floating-point scalar

CORA's `@zonotope/tensorMultiplication.m` for a third-order tensor `M = {M₁, ..., Mₙ}`: an
enclosure of `{ Mᵢⱼₖₗ xⱼ xₖ xₗ | x ∈ Z }` by a zonotope `(0, H)`, when the centre of `Z` is the
origin (otherwise CORA leaves `H` undefined and errors). The error box of `Z` is made into
generators first (`dependent`), so the lists `options.list` are those of the `Z.h + n` generators
of `Z.dependent`; the generators of `H` are stored rounded down and the gap to rounding up is
charged to the box. CORA's `options.list.perm`, `.comb` and `.map` are arguments, as in the exact
layer (`Real.Zonotope.TensorLists`), and the second-order branch, which errors for every input, is
not modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.tensorMultiplication (Z : Zonotope (Vec 𝕋 n)) (M : Zonotope.Tensor3 𝕋 n)
    (L : Real.Zonotope.TensorLists Z.dependent.h) : Zonotope (Vec 𝕋 n) where
  h := L.C
  c := fun _ => zero
  G := fun cInd iDim => Zonotope.tensorHDown M Z.dependent L iDim cInd
  E := Zonotope.generatorError (Zonotope.tensorHDiff M Z.dependent L)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
