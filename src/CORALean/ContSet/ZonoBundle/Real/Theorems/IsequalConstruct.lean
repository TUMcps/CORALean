import CORALean.ContSet.ZonoBundle.Real.Operations.Isequal
import CORALean.ContSet.Zonotope.Real.Theorems.IsequalConstruct

/-!
# Zonotope bundles passing `isequal` denote the same set

Sound, not exact, as for `Zonotope.isequal`: the members are compared as representations.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isequal_construct {zB S : ZonoBundle α} (h : zB.isequal S) :
    zB.construct = S.construct := by -- --- PROOF ---
  obtain ⟨e, hZ⟩ := h
  obtain ⟨k₁, Z₁⟩ := zB
  obtain ⟨k₂, Z₂⟩ := S
  simp only at e hZ
  subst e
  unfold ZonoBundle.construct
  exact Set.iInter_congr fun i => Zonotope.isequal_construct (hZ i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
