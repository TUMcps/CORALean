import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.Global.Cost

/-!
# `ConPolyZono.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the two centres — `n`
additions at `Vec ℝ n` — and lays every other field block-diagonally, by
`Fin.append`, `plusA` or `PolyZonotope.plusE`, all of them index and
allocation work and free under `Global/Cost.lean`'s model.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.plus` costs at `Vec ℝ n`: `n` additions for the centre,
and nothing for the six block-diagonal concatenations. -/
def ConPolyZono.plusCost (n : ℕ) : Cost := ⟨n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
