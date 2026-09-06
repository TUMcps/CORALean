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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- What the stored generators fall short by: nothing on the copied blocks, and
on the centre generator the gap between its two directed roundings. -/
def ConZonotope.linCombGDiff (C₁ C₂ : ConZonotope 𝕋 n) : Mat 𝕋 n (C₁.h + C₂.h + 1) :=
  fun i => Fin.append (fun _ : Fin (C₁.h + C₂.h) => zero)
    fun _ : Fin 1 => subUp (half (subUp (C₁.c i) (C₂.c i))) (half (subDown (C₁.c i) (C₂.c i)))

end CORALean.Float
