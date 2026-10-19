module

public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# The star set of a point

No factors, no rows, the empty box: `c + G α` over the empty family is `c`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The point `v` as CORA's star set: no factors, no rows, an empty box. -/
def StarSet.ofPoint {n : ℕ} (v : Vec ℝ n) : StarSet ℋ𝒫 n where
  m := 0
  c := v
  G := fun _ => Fin.elim0
  dom := ⟨Fin.elim0, Fin.elim0⟩
  pred := HPolytope.fullspace (Vec ℝ 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
