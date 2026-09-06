import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed

/-!
# A nonempty zonotope bundle is compact

`k = 0` denotes `univ`, not compact in a nontrivial space, so this needs
`0 < B.k`: the bundle is then a closed subset of the one compact component it
names, `Set.iInter_subset`, and closed because every component is.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isCompact_construct {B : ZonoBundle α} (h : 0 < B.k) :
    IsCompact B.construct := by
  set i0 : Fin B.k := ⟨0, h⟩
  refine IsCompact.of_isClosed_subset (B.Z i0).isCompact_construct ?_ (Set.iInter_subset _ i0)
  exact isClosed_iInter fun i => (B.Z i).isClosed_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
