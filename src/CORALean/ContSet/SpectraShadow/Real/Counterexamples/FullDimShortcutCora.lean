module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.fullDimShortcutCora`

CORA's code as printed, kept to be refuted: the early exit of CORA's `isFullDim(SpS)`
(`@spectraShadow/isFullDim.m`, l.63): when `norm(SpS.G, 'fro') < 1e-8` it answers `false` and
writes the cache of the object, `fullDim.val = false`, `bounded.val = true` and
`emptySet.val = true`. The property CORA means is `ContSet.IsFullDim`, a
nonempty interior (`Theorems.IsFullDimIffAffineSpan`); the tolerance is not part of it, and the
shortcut contradicts it, see `fullDimShortcut_pointExample_counterexample` and
`fullDimShortcut_thinLine_counterexample`.

## Inputs
* `S` – spectrahedral shadow

## Output
* `norm(SpS.G, 'fro') < 1e-8`, the test on the generator matrix alone
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `norm(SpS.G, 'fro') < 1e-8`, the test on the generator matrix alone. -/
noncomputable def SpectraShadow.fullDimShortcutCora (S : SpectraShadow (Vec ℝ n)) : Prop :=
  Real.sqrt (∑ j, ∑ i, S.G j i ^ 2) < 1 / 10 ^ 8

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
