import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# `ZonoBundle.and`

CORA's `zonoBundle`/`and`, the whole point of the representation: appending the
two families of zonotopes. `Theorems.AndExact` is why appending denotes the
intersection of what each bundle denoted.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.and (B₁ B₂ : ZonoBundle α) : ZonoBundle α where
  k := B₁.k + B₂.k
  Z := Fin.append B₁.Z B₂.Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
