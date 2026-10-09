import CORALean.ContSet.SpectraShadow.Real.Operations.FullDimShortcut
import CORALean.ContSet.SpectraShadow.Real.Operations.PointExample
import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleConstruct

/-!
# CORA's `isFullDim` shortcut marks a point as empty

`isFullDim.m` answers `false` and caches `emptySet.val = true` whenever `norm(G, 'fro') < 1e-8`.
`representsa_(SpS, 'emptySet')` and `cartProd_` read that cache before computing anything, and the
cache is a handle, so it outlives the call. The point `{0}` of `ℝ¹` (`pointExample`: `1 ⪰ 0`, `G =
0`) is nonempty, and the test fires.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.fullDimShortcut_pointExample :
    SpectraShadow.pointExample.fullDimShortcut ∧ SpectraShadow.pointExample.construct.Nonempty := by
  refine ⟨?_, ?_⟩
  · simp [SpectraShadow.fullDimShortcut, SpectraShadow.gFro, SpectraShadow.pointExample]
  · rw [SpectraShadow.pointExample_construct]
    exact ⟨0, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
