import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor

/-!
# Generators pointing upward

Lines 3-6 of [1, Alg. 3] and [1, Alg. 4]: replace a generator `g = (x, y)` with `y < 0`, or `y = 0`
and `x < 0`, by `-g`. This does not change the zonogon, since `[-1, 1]` is symmetric; afterwards
every generator lies in the half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)`, the one the trigonometric order
is taken in.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the zonogon with every generator `g` of `Z` turned upward (lines 4-6). -/
noncomputable def Zonotope.pointUp (Z : Zonotope (Vec ℝ 2)) : Zonotope (Vec ℝ 2) where
  h := Z.h
  c := Z.c
  G := fun i => if Z.G i 1 < 0 ∨ (Z.G i 1 = 0 ∧ Z.G i 0 < 0) then -Z.G i else Z.G i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
