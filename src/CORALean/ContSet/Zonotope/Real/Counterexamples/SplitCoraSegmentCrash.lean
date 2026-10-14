module

public import CORALean.ContSet.Zonotope.Real.Counterexamples.SplitCora

@[expose] public section

/-!
# CORA's `split(zonotope([0;0],[1;0]))` crashes

The loop `N = 1, 2` of `@zonotope/split.m` (l. 46-50) reaches `N = 2`, and the bounding box of
the segment has one generator, so `G(:,2)` is out of bounds; the segment can be split. Read from
the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `split` of the segment `zonotope([0;0],[1;0])`: `N = 1` works, `N = 2` errors. -/
theorem Zonotope.split_cora_segment_crash :
    let Z : Zonotope (Vec ℝ 2) := ⟨1, fun _ => 0, fun _ i => if i = 0 then 1 else 0⟩
    (Z.splitCora 1).isSome ∧ Z.splitCora 2 = none := by -- --- PROOF ---
  intro Z
  -- the box has one generator: the zero-width coordinate is dropped
  have hlen : Z.boxCora.h = 1 := by
    simp [Z, Zonotope.boxCora, Zonotope.boxRadiusCora, List.finRange, List.filter]
  simp [Zonotope.splitCora, hlen]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
