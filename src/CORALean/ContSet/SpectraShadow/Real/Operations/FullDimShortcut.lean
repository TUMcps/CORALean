import CORALean.ContSet.SpectraShadow.Real.Operations.GFro

/-!
# `SpectraShadow.fullDimShortcut`

The early exit of CORA's `isFullDim(SpS)` (`@spectraShadow/isFullDim.m`, l.63): when `norm(SpS.G,
'fro') < 1e-8` it answers `false` and writes the cache of the object, `fullDim.val = false`,
`bounded.val = true` and `emptySet.val = true`. The property CORA means is `ContSet.IsFullDim`, a
nonempty interior (`Theorems.IsFullDimIffAffineSpan`); the tolerance is not part of it.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.fullDimShortcut (S : SpectraShadow (Vec ℝ n)) : Prop :=
  S.gFro < 1 / 10 ^ 8

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
