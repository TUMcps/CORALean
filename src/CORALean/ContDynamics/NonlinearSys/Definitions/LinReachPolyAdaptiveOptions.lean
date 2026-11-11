module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptiveOptions

@[expose] public section

/-!
# The options of CORA's adaptive `'poly'` algorithm

`LinReachPolyAdaptiveOptions`: the options of `'lin'` (`LinReachAdaptiveOptions`: the tuning
constants `postProcessing` sets, here with `redFactor = 0.0001`, `zetaphi = [0.80; 0.75; 0.63]`)
and what `'poly'` adds. `dHused` is `aux_optimaldeltat`'s `0.3` for `'poly'` in place of `0.5`.
`thirdOrderEmpty` is `options.thirdOrderTensorempty`, true when the field has no third derivative,
which `aux_getPowers` reads (`sigma + 1`, `polyGain`), and `maxDepGenOrder` is
`options.polyZono.maxDepGenOrder`, the order `aux_reduceOnlyDep` keeps.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The `params` and `options` of CORA's `poly-adaptive`, its tuning constants and literals. -/
structure NonlinearSys.LinReachPolyAdaptiveOptions (τ : Type) extends
    NonlinearSys.LinReachAdaptiveOptions τ where
  /-- `dHused`, `0.3`. -/
  dHused : τ
  /-- `options.thirdOrderTensorempty`. -/
  thirdOrderEmpty : Bool
  /-- `options.polyZono.maxDepGenOrder`. -/
  maxDepGenOrder : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
