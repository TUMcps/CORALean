module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `GridPartition`: a grid partition with dividers held in a floating-point scalar

CORA's `partition` with the dividers stored in `𝕋`: the same `nrOfSegments` and the same numbering
of the cells, the dividers read as reals by `nominal` to give the grid partition the stored floats
describe. The cell numbering and the segment counts are natural numbers, so only the dividers
carry a scalar.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A box cut into cells by `nrOfSegments j` segments along dimension `j`, the dividers
stored in `𝕋`. -/
structure GridPartition (𝕋 : Type) (n : ℕ) where
  /-- CORA's `nrOfSegments`. -/
  nrOfSegments : Fin n → ℕ
  /-- CORA's `dividers{j}(k + 1)`, counted from `k = 0`. -/
  dividers : Fin n → ℕ → 𝕋

/-- The exact grid partition the stored dividers describe, read as reals. -/
protected abbrev GridPartition.nominal [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    (P : GridPartition 𝕋 n) : CORALean.GridPartition n :=
  ⟨P.nrOfSegments, fun j k => toReal (P.dividers j k)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
