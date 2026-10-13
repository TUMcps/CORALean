import CORALean.ContSet.PolyZonotope.Float.Operations.BlockPadRight
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.Global.Block

/-!
# The right-padded set denotes the padded nominal set

The nominal set of `blockPadRight` is the exact layer's `map` at the block embedding, entry by
entry: the padded rows are zero on both sides.
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

theorem PolyZonotope.nominal_blockPadRight (n₁ : ℕ) (pZ : PolyZonotope (Vec 𝕋 n)) :
    nominal (pZ.blockPadRight n₁) =
      Real.PolyZonotope.map (CORALean.blockPadRight n₁ n) (nominal pZ) := by -- --- PROOF ---
  -- the same fields, entry by entry
  show (⟨_, _, _, _, _, _, _⟩ : Real.PolyZonotope (Vec ℝ (n₁ + n))) = ⟨_, _, _, _, _, _, _⟩
  congr 1
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [PolyZonotope.blockPadRight, CORALean.blockPadRight, RealImage.realImage, toRealVec,
        toReal_zero]
    · simp [PolyZonotope.blockPadRight, CORALean.blockPadRight, RealImage.realImage, toRealVec]
      rfl
  -- each generator of either block, padded as the centre is
  · funext l j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [PolyZonotope.blockPadRight, CORALean.blockPadRight, RealImage.realImage, toRealVec,
        toReal_zero]
    · simp [PolyZonotope.blockPadRight, CORALean.blockPadRight, RealImage.realImage, toRealVec]
      rfl
  · funext l j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [PolyZonotope.blockPadRight, CORALean.blockPadRight, RealImage.realImage, toRealVec,
        toReal_zero]
    · simp [PolyZonotope.blockPadRight, CORALean.blockPadRight, RealImage.realImage, toRealVec]
      rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
