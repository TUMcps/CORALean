module

public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# The star set of a point

No factors, no rows: `c + G α` over the empty family is `c`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def StarSet.ofPoint {n : ℕ} (v : Vec ℝ n) : StarSet n where
  m := 0
  c := v
  G := fun _ => Fin.elim0
  cons := []
  l := Fin.elim0
  u := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
