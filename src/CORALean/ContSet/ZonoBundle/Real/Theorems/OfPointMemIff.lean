module

public import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
public import CORALean.ContSet.ZonoBundle.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff

@[expose] public section

/-!
# `ZonoBundle.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: the bundle's one zonotope denotes exactly `v`, and the
intersection of that one set is itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mem_ofPoint_iff (v x : α) :
    x ∈ (ZonoBundle.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · intro h
    exact (Zonotope.mem_ofPoint_iff v x).mp (Set.mem_iInter.mp h (0 : Fin 1))
  · rintro rfl
    exact ZonoBundle.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
