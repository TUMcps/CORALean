import CORALean.ContDynamics.LinearSysDT.Operations.ReachError
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRep

/-!
# The inner approximation, at a representation

`reachInner` is a `Set`, a guarantee about a set, not an object a later step
could consume. `reachInnerRep` is the same difference at a representation:
`minkDiffRep` of the run by its error, at a generator representation `M` the
caller offers and the operation checks. A wrong `M` gives `none`, costing
precision and never soundness, exactly as `backReachForall` does.
It is noncomputable because the exact layer's `reduce` is.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same difference at a representation, `none` where the caller's
generator representation `M` does not check out. -/
noncomputable def LinearSysDT.reachInnerRep (sys : LinearSysDT ℝ n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ)
    (M : Fin (sys.reach (S := 𝒵) o ho R₀ U k).h →
      Fin (sys.reachError o ho R₀ U k).h → ℝ) : Option (Zonotope (Vec ℝ n)) :=
  (sys.reach (S := 𝒵) o ho R₀ U k).minkDiffRep (sys.reachError o ho R₀ U k) M

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
