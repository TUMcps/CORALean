module

public import CORALean.ContSet.ConPolyZono.Float.Operations.SplitLongestGen
public import CORALean.ContSet.ConPolyZono.Float.Theorems.SplitDepFactorOuter

@[expose] public section

/-!
# `ConPolyZono.splitLongestGen` covers the set

`splitDepFactor_outer` at whichever factor the float ranking chose, the set being its own cover
where there is none. Outer, not exact.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is covered by the two halves
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

theorem ConPolyZono.splitLongestGen_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.splitLongestGen.1.construct ∪ cPZ.splitLongestGen.2.construct := by
  unfold ConPolyZono.splitLongestGen
  cases cPZ.longestFactor with
  | some k => exact ConPolyZono.splitDepFactor_outer cPZ k
  | none => exact fun y hy => Or.inl hy

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
