import CORALean.ContSet.Capsule.Real.Operations.SupportBound
import CORALean.ContSet.Conversion.Real.Zonotope_to_HPolytope
import CORALean.Specification.Theorems.Separation

/-!
# A capsule earns its keep with `supportBound` alone

`Capsule` is convex and compact but closed under none of `Plus`, `Mtimes` or
`LinComb` — CORA uses it to describe an obstacle, never to carry a set
forward. Nothing here computes *with* the capsule: the whole check reads it
through `Capsule.supportBound`, the certificate every representation answers
a direction with regardless of what it can compute.

A unit-generator zonotope stands in for a reachable set, a capsule five units
along the first coordinate for an obstacle, and
`Specification.holds_unsafeSet_of_separating` turns one direction's two
bounds into disjointness — no intersection, no enclosure, nothing the capsule
cannot do.

This is one direction, so it certifies separation and nothing more: a bound
that fails to separate proves no intersection, only that this direction did
not find one.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

-- The reachable set: a unit box at the origin, two unit generators.
def Example.capZono : Zonotope (Vec ℝ 2) := ⟨2, ![0, 0], ![![1, 0], ![0, 1]]⟩

-- The obstacle: a capsule five units out along the first coordinate.
def Example.capObstacle : Capsule 2 := ⟨![5, 0], ![1, 0], 1⟩

-- The separating direction: the first coordinate, read both ways.
def Example.capDir : Vec ℝ 2 →ₗ[ℝ] ℝ := LinearMap.proj (0 : Fin 2)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set never touches the obstacle. `capZono` reaches at most `1`
along `capDir`; `capObstacle` reaches back no further than `-3` — neither
representation had to run an operation to say so. -/
theorem Example.cap_holds :
    (Specification.unsafeSet Example.capObstacle.construct).Holds
      Example.capZono.construct := by -- --- PROOF ---
  refine Specification.holds_unsafeSet_of_separating
    (Example.capZono.supportBound Example.capDir)
    (Example.capObstacle.supportBound (-Example.capDir)) ?_
  -- `show` gives the sum a fresh `Fintype (Fin 2)`, or `Fin.sum_univ_two` below cannot match it.
  have hu : (Example.capZono.supportBound Example.capDir).val = 1 := by
    show Example.capDir Example.capZono.c
        + ∑ j : Fin 2, |Example.capDir (Example.capZono.G j)| = 1
    simp only [Example.capZono, Example.capDir]
    norm_num [LinearMap.proj_apply, Fin.sum_univ_two]
  have hv : (Example.capObstacle.supportBound (-Example.capDir)).val = -3 := by
    show (-Example.capDir) Example.capObstacle.c + |(-Example.capDir) Example.capObstacle.g|
        + Example.capObstacle.r
          * Real.sqrt (∑ i : Fin 2, (-Example.capDir) (Pi.single i 1) ^ 2) = -3
    simp only [Example.capObstacle, Example.capDir]
    norm_num [LinearMap.proj_apply, LinearMap.neg_apply, Pi.single_apply, Fin.sum_univ_two]
  rw [hu, hv]
  norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
