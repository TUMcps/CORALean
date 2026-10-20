module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# Stored block-diagonal matrices read as reals

A block-diagonal matrix of stored floats reads as the block-diagonal matrix of
what its blocks read as, the zero between them being the stored `zero`, which
`SoundFloatArithmetic` says reads as `0`. What lets the exact layer's statements
about the inequality of a sum apply to the stored one.

## Inputs
* `a` – natural number
* `b` – natural number
* `M` – `a × a` matrix
* `N` – `b × b` matrix

## Hypotheses
* none

## Conclusion
* reading a block diagonal matrix as reals gives the block diagonal of the readings
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.toRealMat_blockDiag {a b : ℕ} (M : Mat 𝕋 a a) (N : Mat 𝕋 b b) :
    toRealMat (blockDiag zero M N) = blockDiag 0 (toRealMat M) (toRealMat N) := by
  refine blockDiag_ext ?_ ?_ ?_ ?_ <;> intros <;> simp [toRealMat, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
