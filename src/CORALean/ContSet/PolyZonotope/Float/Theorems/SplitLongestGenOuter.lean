import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGen
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitDepFactorOuter

/-!
# `PolyZonotope.splitLongestGen` covers the set

`splitDepFactor_outer` at whichever factor the float ranking chose, the set being its own cover
where there is none. Outer, not exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.splitLongestGen_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.splitLongestGen.1.construct ∪ pZ.splitLongestGen.2.construct := by
  unfold PolyZonotope.splitLongestGen
  cases pZ.longestFactor with
  | some k => exact PolyZonotope.splitDepFactor_outer pZ k
  | none => exact fun y hy => Or.inl hy

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
