module

public import CORALean.ContSet.HPolytope.Real.HPolytope

@[expose] public section

/-!
# `HPolytope.tightAt`

The rows tight at a point, as the choice that names it. Noncomputable, and
unavoidably so at this layer — whether two reals are equal is not decidable.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows tight at `x`, as the choice that names `x`. -/
noncomputable def HPolytope.tightAt (P : HPolytope (Vec ℝ n)) (x : Vec ℝ n) : Fin P.m → Bool :=
  fun i => if P.A i x = P.b i then true else false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
