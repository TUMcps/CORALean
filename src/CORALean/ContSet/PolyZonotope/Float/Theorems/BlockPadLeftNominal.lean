module

public import CORALean.ContSet.PolyZonotope.Float.Operations.BlockPadLeft
public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.Global.Block

@[expose] public section

/-!
# The left-padded set denotes the padded nominal set

The nominal set of `blockPadLeft` is the exact layer's `map` at the block embedding, entry by entry:
the padded rows are zero on both sides.

## Inputs
* `n₂` – number of appended zero coordinates
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* nominal set of the padded set is the padded nominal set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.nominal_blockPadLeft (n₂ : ℕ) (pZ : PolyZonotope (Vec 𝕋 n)) :
    nominal (pZ.blockPadLeft n₂) =
      Real.PolyZonotope.map (CORALean.blockPadLeft n n₂) (nominal pZ) := by -- --- PROOF ---
  -- the same fields, entry by entry
  show (⟨_, _, _, _, _, _, _⟩ : Real.PolyZonotope (Vec ℝ (n + n₂))) = ⟨_, _, _, _, _, _, _⟩
  congr 1
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [PolyZonotope.blockPadLeft, CORALean.blockPadLeft, RealImage.realImage, toRealVec]
      rfl
    · simp [PolyZonotope.blockPadLeft, CORALean.blockPadLeft, RealImage.realImage, toRealVec,
        toReal_zero]
  -- each generator of either block, padded as the center is
  · funext l j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [PolyZonotope.blockPadLeft, CORALean.blockPadLeft, RealImage.realImage, toRealVec]
      rfl
    · simp [PolyZonotope.blockPadLeft, CORALean.blockPadLeft, RealImage.realImage, toRealVec,
        toReal_zero]
  · funext l j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [PolyZonotope.blockPadLeft, CORALean.blockPadLeft, RealImage.realImage, toRealVec]
      rfl
    · simp [PolyZonotope.blockPadLeft, CORALean.blockPadLeft, RealImage.realImage, toRealVec,
        toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
