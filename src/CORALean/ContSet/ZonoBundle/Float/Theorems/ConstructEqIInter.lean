module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# A float bundle denotes the intersection over its index

`ZonoBundle.construct` is `SetIntersection`'s intersection of the listed members by definition,
at any ambient type; this reads it back over `Fin k` with each member's own inflated set,
through the general `SetIntersection.construct_ofFn`. It is the form a proof about one of CORA's
algorithms, which names members by their index, starts from.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A float bundle denotes the intersection of its members' inflated sets over their index. -/
theorem ZonoBundle.construct_eq_iInter (zB : ZonoBundle α) :
    (zB.construct : Set β) = ⋂ i, (zB.Z i).construct :=
  SetIntersection.construct_ofFn zB.Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
