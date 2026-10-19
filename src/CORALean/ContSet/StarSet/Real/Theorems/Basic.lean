module

public import CORALean.ContSet.StarSet.Real.Operations.OfPoint

@[expose] public section

/-!
# `ContSet/StarSet/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n : ℕ}


-- ==================================  `StarSet.mem_ofPoint`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---

/-- A point is in its star set: no factors, no rows, and `c + G α` is `c`. -/
theorem StarSet.mem_ofPoint (v : Vec ℝ n) : v ∈ (StarSet.ofPoint v).construct :=
  ⟨Fin.elim0, ⟨fun k => k.elim0, fun i => i.elim0, fun i => i.elim0⟩, fun i => by
    simp [StarSet.ofPoint]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
