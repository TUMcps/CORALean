import CORALean.ContSet.HPolytope.Real.Operations.OfPoint

/-!
# A point's own coordinates satisfy its equality rows

`ofPoint v` has no inequalities and reads coordinate `i` back through
`LinearMap.proj i`, so each equality row holds by `LinearMap.proj_apply`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_ofPoint (v : Vec ℝ n) : v ∈ (HPolytope.ofPoint v).construct :=
  ⟨fun i => i.elim0, fun i => LinearMap.proj_apply i v⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
