import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# `HPolytope.emptySet`, over a floating-point scalar

The single constraint `0 ≤ -1`, which no point satisfies, as over ℝ. `neg one` is
exact, so reading it back gives `-1` and nothing is rounded.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.emptySet (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : HPolytope 𝕋 n where
  m := 1
  A := fun _ _ => zero
  b := fun _ => neg one
  me := 0
  Ae := fun i => i.elim0
  be := ⟨fun i => i.elim0, fun i => i.elim0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
