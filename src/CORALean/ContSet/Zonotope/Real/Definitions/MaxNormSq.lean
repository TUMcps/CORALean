module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# The squared maximum zonotope norm

[1, Def. 3]: `⌈Z⌉² = max_{|u| ≤ 1} uᵀ Gᵀ G u`, the largest squared Euclidean distance from the
center to a point of the zonotope. A supremum over the coefficient box, which is attained, the box
being compact (`Zonotope.isGreatest_maxNormSq_sign`).

## Inputs
* `Z` – zonotope

## Output
* largest squared norm over the coefficient box

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⌈Z⌉²`: the largest `‖∑ βⱼ gⱼ‖₂²` over the box `|βⱼ| ≤ 1`. -/
noncomputable def Zonotope.maxNormSq (Z : Zonotope (Vec ℝ n)) : ℝ :=
  sSup {t | ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧ t = ‖∑ j, β j • Z.G j‖₂ ^ 2}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
