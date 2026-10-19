module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.TensorHDown
public import CORALean.ContSet.Zonotope.Float.Operations.TensorHUp

@[expose] public section

/-!
# `Zonotope.tensorMultiplication`, over a floating-point scalar

CORA's `@zonotope/tensorMultiplication.m` for a third-order tensor `M = {M₁, ..., Mₙ}`: an enclosure
of `{ Mᵢⱼₖₗ xⱼ xₖ xₗ | x ∈ Z }` by a zonotope `(0, H)`, when the center of `Z` is the origin
(otherwise CORA leaves `H` undefined and errors). The error box of `Z` is made into generators first
(`absorbRounding`), so the lists `options.list` are those of the `Z.h + n` generators of
`Z.absorbRounding`; the generators of `H` are stored rounded down and the gap to rounding up is
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def Zonotope.aux_tensorHDiff (M : Zonotope.Tensor3 𝕋 n) (Z : Zonotope (Vec 𝕋 n))
    (L : Real.Zonotope.TensorLists Z.h) : Fin n → Fin L.C → 𝕋 :=
  fun iDim cInd => subUp (Zonotope.tensorHUp M Z L iDim cInd) (Zonotope.tensorHDown M Z L iDim cInd)


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.tensorMultiplication (Z : Zonotope (Vec 𝕋 n)) (M : Zonotope.Tensor3 𝕋 n)
    (L : Real.Zonotope.TensorLists Z.absorbRounding.h) : Zonotope (Vec 𝕋 n) where
  h := L.C
  c := fun _ => zero
  G := fun cInd iDim => Zonotope.tensorHDown M Z.absorbRounding L iDim cInd
  I_error := Zonotope.generatorError (Zonotope.aux_tensorHDiff M Z.absorbRounding L)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
