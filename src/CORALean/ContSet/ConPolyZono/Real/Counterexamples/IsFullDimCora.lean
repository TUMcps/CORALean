module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IsFullDimCora
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConPolyZonoExact
public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.IsFullDimCora
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# CORA's `conPolyZono/isFullDim` accepts a curve

The same arc `(a, a²)` as for `polyZonotope/isFullDim`, with no constraints: nonempty, the rank
test true, and no interior point. Read from the source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The rank test holds for the arc `(a, a²)` of `ℝ²`, whose set has empty interior. -/
theorem ConPolyZono.isFullDim_cora_counterexample :
    ∃ cPZ : ConPolyZono (Vec ℝ 2), cPZ.isFullDimCora ∧
      ¬ (interior cPZ.construct).Nonempty := by -- --- PROOF ---
  obtain ⟨pZ, hrank, hint⟩ := PolyZonotope.isFullDim_cora_counterexample
  refine ⟨pZ.conPolyZono, ⟨?_, hrank⟩, ?_⟩
  · rw [← PolyZonotope.conPolyZono_exact]
    exact ⟨_, pZ.point_mem_construct (a := fun _ => 0) fun k => by simp⟩
  · rw [← PolyZonotope.conPolyZono_exact]
    exact hint

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
