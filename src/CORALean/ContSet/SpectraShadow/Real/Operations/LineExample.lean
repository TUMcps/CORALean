module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.lineExample`

The diagonal `{(t, t)}` of `ℝ²`: `A₀ = I`, `A₁ = 0`, `A₂ = diag(1, 0)`, `G₁ = (1, 1)`, `G₂ = 0`,
the counterexample set of `SpectraShadow.representsa_fullspaceCora_line` and
`SpectraShadow.containsPointCora_line`. `A₂` is nonzero, so CORA's solver branch runs.

## Inputs
* none

## Output
* the diagonal `{(t, t)}` of `ℝ²`, with `A₀ = I`, `A₂ = diag(1, 0)` and `G₁ = (1, 1)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.lineExample : SpectraShadow (Vec ℝ 2) :=
  ⟨2, 2, 1,
    fun i : Fin 2 =>
      if i = 0 then 0 else Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 0),
    0, fun i : Fin 2 => if i = 0 then (fun _ => 1) else 0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
