import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.ContSet.Zonotope.Real.Operations.Tensor3

/-!
# `Zonotope.Tensor3`, over a floating-point scalar

The third-order tensors of CORA's `@zonotope/tensorMultiplication.m`, `M = {M₁, ..., Mₙ}` with `Mᵢ`
an `n × n × n` array, `M iDim ind1 ind2 ind3`, with entries in `𝕋`. A function type, as the exact
layer's, so that a matrix zonotope of tensors is a `Zonotope` over it and each `M iDim ind1` is a
matrix of `Mat 𝕋 n n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

abbrev Zonotope.Tensor3 (𝕋 : Type) (n : ℕ) : Type := Fin n → Fin n → Fin n → Fin n → 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
