module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed

@[expose] public section

/-!
# A nonempty zonotope bundle is compact

`k = 0` denotes `univ`, not compact in a nontrivial space, so this needs
`0 < zB.k`: the bundle is then a closed subset of the one compact component it
names, `Set.iInter_subset`, and closed because every component is.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isCompact_construct {zB : ZonoBundle α} (h : 0 < zB.k) :
    IsCompact zB.construct := by
  set i0 : Fin zB.k := ⟨0, h⟩
  refine IsCompact.of_isClosed_subset (zB.Z i0).isCompact_construct ?_ (Set.iInter_subset _ i0)
  exact isClosed_iInter fun i => (zB.Z i).isClosed_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
