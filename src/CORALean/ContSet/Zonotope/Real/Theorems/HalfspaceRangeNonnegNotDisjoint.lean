module

public import CORALean.ContSet.Zonotope.Real.Operations.HalfspaceRange

@[expose] public section

/-!
# `ω̲ ≥ 0` does not rule out an intersection

[1, Sec. 5.2] prints "if `ω̲ ≥ 0`, no intersection occurs". At `n = 1`, the zonotope `{0}`,
`n = 1` and `d = 0`, `ω̲ = 0`, yet `0` lies in `{x | x ≤ 0}`. `halfspaceRange_sound` is the
strict version that holds.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed disjointness test fails for a zonotope meeting the halfspace

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.2] as printed is false: `ω̲ = 0` and the zonotope meets the halfspace. -/
theorem Zonotope.halfspaceRange_nonneg_not_disjoint :
    ∃ (nv : Vec ℝ 1) (d : ℝ) (Z : Zonotope (Vec ℝ 1)),
      0 ≤ (Z.halfspaceRange nv d).inf ∧ ∃ x ∈ Z.construct, nv ⬝ᵥ x ≤ d := by
  refine ⟨fun _ => 1, 0, ⟨0, 0, Fin.elim0⟩, ?_, 0, ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
  · simp [Zonotope.halfspaceRange]
  · simp
  · simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
