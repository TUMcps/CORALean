import CORALean.ContSet.SpectraShadow.Real.Operations.LineExample

/-!
# `SpectraShadow.lineExample_sum`

The combination of the line example's generators is the diagonal point `(β₁, β₁)`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
