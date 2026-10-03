import CORALean.ContSet.PolyZonotope.Float.Operations.BlockPadLeft
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.Global.Block

/-!
# The left-padded set denotes the padded nominal set

The nominal set of `blockPadLeft` is the exact layer's `map` at the block embedding, entry by entry:
the padded rows are zero on both sides.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.nominal_blockPadLeft (n₂ : ℕ) (pZ : PolyZonotope 𝕋 n) :
    nominal (pZ.blockPadLeft n₂) =
      Real.PolyZonotope.map (CORALean.blockPadLeft n n₂) (nominal pZ) := by -- --- PROOF ---
  -- the same fields, entry by entry
  show (⟨_, _, _, _, _, _, _⟩ : Real.PolyZonotope (Vec ℝ (n + n₂))) = ⟨_, _, _, _, _, _, _⟩
  congr 1
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [PolyZonotope.blockPadLeft,
      CORALean.blockPadLeft, toRealVec, toReal_zero] <;> rfl
  · funext l j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [PolyZonotope.blockPadLeft,
      CORALean.blockPadLeft, toRealVec, toReal_zero] <;> rfl
  · funext l j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [PolyZonotope.blockPadLeft,
      CORALean.blockPadLeft, toRealVec, toReal_zero] <;> rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
