module

public import CORALean.ContSet.SpectraShadow.Real.Operations.LineExample

@[expose] public section

/-!
# `SpectraShadow.lineExample_sum`

The combination of the line example's generators is the diagonal point `(β₁, β₁)`.

## Inputs
* `β` – real numbers indexed by `Fin 2`

## Hypotheses
* none

## Conclusion
* the combination of the generators is the diagonal point `(β₀, β₀)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.lineExample_sum (β : Fin 2 → ℝ) :
    SpectraShadow.lineExample.c + ∑ i : Fin 2, β i • SpectraShadow.lineExample.G i
      = (fun _ => β 0 : Vec ℝ 2) := by
  funext j
  simp [SpectraShadow.lineExample]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
