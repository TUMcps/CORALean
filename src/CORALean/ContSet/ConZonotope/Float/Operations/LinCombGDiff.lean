import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# What `ConZonotope.linComb`'s stored generators fall short by

Split out of `LinComb.lean` (issue #62): read again by
`Theorems/LinCombOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the stored generators fall short by: nothing on the copied blocks, and
on the centre generator the gap between its two directed roundings. -/
def ConZonotope.linCombGDiff (cZ₁ cZ₂ : ConZonotope 𝕋 n) : Mat 𝕋 n (cZ₁.h + cZ₂.h + 1) :=
  fun i => Fin.append (fun _ : Fin (cZ₁.h + cZ₂.h) => zero)
    fun _ : Fin 1 => subUp (half (subUp (cZ₁.c i) (cZ₂.c i))) (half (subDown (cZ₁.c i) (cZ₂.c i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
