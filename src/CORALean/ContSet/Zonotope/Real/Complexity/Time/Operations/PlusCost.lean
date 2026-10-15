module

public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.plusCost`

Asserted, not proved: `Operations/Plus.lean` adds the two centres — `n`
additions at `Vec ℝ n` — and concatenates the generator blocks, which is index
work and free under `Global/Cost.lean`'s model. So the count of the operands'
generators does not enter, though the memory traffic does grow with it.

`Complexity/Space/Plus.lean` is the other half and the other kind of claim: how large
the *result* is, which is `rfl` against the definition.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.plus` costs at `Vec ℝ n`: `n` additions for the centre, and
nothing for the concatenation. -/
def Zonotope.plusCost (n : ℕ) : Cost := ⟨n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
