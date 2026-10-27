module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint

@[expose] public section

/-!
# `map` carries a factor sub-box to the corresponding subset

[1, Def. 4]'s dependency result, composed: `map_point` says one factor vector names
corresponding points before and after `map`, so a sub-box `B` of the *initial* factor domain
names the corresponding subset of every later set in a chain (`bilin_point` and
`gcnSteps_point` are the same pattern). `map` preserves `p` definitionally, so `B` needs no
transport, unlike a chain through `bilin` or `padFront`.

## Inputs
* `f` – linear map
* `pZ` – polynomial zonotope
* `B` – box of factor values

## Hypotheses
* none

## Conclusion
* subset at the box is the image of the original subset

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `map`'s subset at `B` is `f`'s image of the original subset at `B`. -/
theorem PolyZonotope.map_subsetAt (f : α →ₗ[ℝ] β) (pZ : PolyZonotope α)
    (B : Set (Fin pZ.p → ℝ)) : (pZ.map f).subsetAt B = f '' pZ.subsetAt B := by
  show (pZ.map f).point '' B = f '' (pZ.point '' B)
  rw [← Set.image_comp]
  exact Set.image_congr fun a _ => PolyZonotope.map_point f pZ a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
