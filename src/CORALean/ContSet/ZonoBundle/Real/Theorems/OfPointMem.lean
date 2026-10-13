module

public import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem

@[expose] public section

/-!
# A bundle of one point-zonotope contains that point

`construct` is an intersection over `Fin 1`, so the sole conjunct is
`Zonotope.mem_ofPoint` at the family's one member.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mem_ofPoint (v : α) : v ∈ (ZonoBundle.ofPoint v).construct := by
  simp only [ZonoBundle.construct, ZonoBundle.ofPoint, Set.mem_iInter]
  exact fun _ => Zonotope.mem_ofPoint v

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
