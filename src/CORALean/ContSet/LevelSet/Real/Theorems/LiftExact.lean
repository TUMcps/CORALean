import CORALean.ContSet.LevelSet.Real.Operations.Lift

/-!
# `LevelSet.lift_` is a preimage

The lifted level set is exactly the points whose selected coordinates lie in the original.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.lift_exact {N : ℕ} (L : LevelSet n) (dims : Fin n → Fin N) :
    (L.lift_ dims).construct = (fun x : Vec ℝ N => fun i => x (dims i)) ⁻¹' L.construct :=
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
