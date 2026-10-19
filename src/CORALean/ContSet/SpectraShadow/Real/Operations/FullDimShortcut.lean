module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.fullDimShortcut`

The early exit of CORA's `isFullDim(SpS)` (`@spectraShadow/isFullDim.m`, l.63): when `norm(SpS.G,
'fro') < 1e-8` it answers `false` and writes the cache of the object, `fullDim.val = false`,
`bounded.val = true` and `emptySet.val = true`. The property CORA means is `ContSet.IsFullDim`, a
nonempty interior (`Theorems.IsFullDimIffAffineSpan`); the tolerance is not part of it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

noncomputable def SpectraShadow.aux_gFro (S : SpectraShadow (Vec ℝ n)) : ℝ :=
  Real.sqrt (∑ j, ∑ i, S.G j i ^ 2)


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.fullDimShortcut (S : SpectraShadow (Vec ℝ n)) : Prop :=
  S.aux_gFro < 1 / 10 ^ 8

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
