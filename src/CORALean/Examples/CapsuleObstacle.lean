import CORALean.ContSet.Capsule.Real.Operations.SupportBound
import CORALean.ContSet.Conversion.Real.Operations.Basic
import CORALean.Specification.Theorems.Separation

/-!
# A capsule earns its keep with `supportBound` alone

`Capsule` is convex and compact but closed under none of `Plus`, `Mtimes` or `LinComb`: CORA uses
it to describe an obstacle, never to carry a set forward. Nothing here computes with the capsule;
the check reads it through `Capsule.supportBound`, the certificate every representation answers a
direction with. A square tilted by 45°, the zonotope with generators `(2, 2)` and `(2, -2)`, stands
in for a reachable set; a short capsule at the corner `(4, 4)` of its bounding box for an obstacle.
The box meets the obstacle, so no per-coordinate test separates the two, only the diagonal
`x₀ + x₁` does (`Specification.holds_unsafeSet_of_separating`). One direction certifies separation
and nothing more.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the zonotope keeps clear of the obstacle
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

-- The reachable set: a square tilted by 45°, `|x₀| + |x₁| ≤ 4`.
def Example.capZono : Zonotope (Vec ℝ 2) := ⟨2, ![0, 0], ![![2, 2], ![2, -2]]⟩

-- The obstacle: a short segment through `(4, 4)`, perpendicular to the diagonal, fattened by `1`.
def Example.capObstacle : Capsule 2 := ⟨![4, 4], ![1, -1], 1⟩

-- The separating direction: the diagonal `x₀ + x₁`.
def Example.capDir : Vec ℝ 2 →ₗ[ℝ] ℝ :=
  (LinearMap.proj (0 : Fin 2) : Vec ℝ 2 →ₗ[ℝ] ℝ) + LinearMap.proj (1 : Fin 2)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set never touches the obstacle, though the obstacle lies inside its bounding
box. `capZono` reaches at most `4` along `capDir`; `capObstacle` reaches back no further than
`-8 + √2 < -4` — neither representation had to run an operation to say so. -/
theorem Example.cap_holds :
    (Specification.unsafeSet Example.capObstacle.construct).Holds
      Example.capZono.construct := by -- --- PROOF ---
  refine Specification.holds_unsafeSet_of_separating
    (Example.capZono.supportBound Example.capDir)
    (Example.capObstacle.supportBound (-Example.capDir)) ?_
  -- `show` gives the sum a fresh `Fintype (Fin 2)`, or `Fin.sum_univ_two` below cannot match it.
  have hu : (Example.capZono.supportBound Example.capDir).val = 4 := by
    show Example.capDir Example.capZono.c
        + ∑ j : Fin 2, |Example.capDir (Example.capZono.G j)| = 4
    simp only [Example.capZono, Example.capDir]
    norm_num [LinearMap.proj_apply, Fin.sum_univ_two]
  have hv : (Example.capObstacle.supportBound (-Example.capDir)).val
      = -8 + Real.sqrt 2 := by
    show (-Example.capDir) Example.capObstacle.c + |(-Example.capDir) Example.capObstacle.g|
        + Example.capObstacle.r
          * Real.sqrt (∑ i : Fin 2, (-Example.capDir) (Pi.single i 1) ^ 2)
        = -8 + Real.sqrt 2
    simp only [Example.capObstacle, Example.capDir]
    norm_num [LinearMap.proj_apply, LinearMap.neg_apply, Pi.single_apply, Fin.sum_univ_two]
  have h2 : Real.sqrt 2 < 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [hu, hv]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
