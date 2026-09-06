import CORALean.ContSet.HPolytope.Float.Operations.API

/-!
# What the float `HPolytope` instantiates

`ContSet` and no more, as over ℝ: a halfspace description computes none of
`plus`, `linComb` or `reduce` without enumerating vertices first, so it
instantiates none of them and owes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : ContSet (HPolytope 𝕋 n) (Vec ℝ n) := ⟨HPolytope.construct⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
