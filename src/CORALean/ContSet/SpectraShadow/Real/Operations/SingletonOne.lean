module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.singletonOne`

`spectraShadow([1 0 -1 0; 0 -1 0 1])`: the inequality `diag(1 - β, β - 1) ⪰ 0` holds only at `β =
1`, so this is the point `{1}` of `ℝ¹`, which `convHull_` appends to put a shadow at height `1`.
`Theorems.SingletonOneConstruct` says so.

## Inputs
* none

## Output
* the point `{1}` of `ℝ¹`, the inequality `diag(1 - β, β - 1) ⪰ 0`
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

abbrev SpectraShadow.singletonOne : SpectraShadow (Vec ℝ 1) :=
  ⟨2, 1, !![1, 0; 0, -1], fun _ => !![-1, 0; 0, 1], 0, fun _ => fun _ => 1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
