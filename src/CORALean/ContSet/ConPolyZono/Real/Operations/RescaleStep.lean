import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset

/-!
# `ConPolyZono.rescaleStep`

One factor of `rescale`: factor `r`, if it is a factor of `acc`, re-parametrized onto
`cen r ± rad r` by `getSubset`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.rescaleStep (cen rad : ℕ → ℝ) (acc : ConPolyZono α) (r : ℕ) :
    ConPolyZono α :=
  if h : r < acc.p then acc.getSubset ⟨r, h⟩ (cen r) (rad r) else acc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
