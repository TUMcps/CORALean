import CORALean.ContSet.Interval.Real.Operations.Empty
import CORALean.ContSet.Interval.Real.Operations.RepresentsaEmptySet

/-!
# `Interval.projectHighDim_`

CORA's `@interval/projectHighDim_`: the box placed into the coordinates `proj` of `ℝᴺ`, every
other coordinate `0`; an empty box stays empty. The test is `representsa_emptySet`, as in CORA.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
noncomputable def Interval.projectHighDim_ (I : Interval (Vec ℝ m)) (N : ℕ) (proj : Fin m → Fin N) :
    Interval (Vec ℝ N) :=
  if I.representsa_emptySet then Interval.empty N
  else ⟨Function.extend proj I.inf 0, Function.extend proj I.sup 0⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
