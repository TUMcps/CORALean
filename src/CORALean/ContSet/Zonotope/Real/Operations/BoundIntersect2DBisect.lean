module

public import CORALean.ContSet.Zonotope.Real.Operations.BisectLow
public import CORALean.ContSet.Zonotope.Real.Operations.MirrorY

@[expose] public section

/-!
# [1, Alg. 4]: `BOUND_INTERSECT_2D` by dichotomic search

The zonogon `⟨c; g₁, …, g_r⟩` and the line `L_γ = {(x, y) | x = γ}` with `Z ∩ L_γ` nonempty: the
lower end `m` is found by bisection on the generators from the lowest vertex (`bisectLow`,
lines 1-28), and "the same thing for `M`, starting from the upper vertex of `Z`" (line 29) is the
same search on the zonogon mirrored in the x-axis, whose lowest vertex is the upper vertex of `Z`,
with the sign of `y` restored. Unlike `Alg. 3` the answer is a pair of reals: the search needs the
intersection to be nonempty, where `Alg. 3` returns `[∞; -∞]`.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 4]: the segment `[m; M]` with `{γ} × [m; M] = Z ∩ L_γ`. -/
noncomputable def Zonotope.boundIntersect2DBisect (Z : Zonotope (Vec ℝ 2)) (γ : ℝ) : Interval ℝ :=
  -- 1. lines 1-28: `m`, the lower end, by bisection from the lowest vertex
  let m := Z.bisectLow γ
  -- 29. the same thing for `M`, from the upper vertex: the lower search on the mirror image
  let M := -Z.mirrorY.bisectLow γ
  -- 30. return `[m; M]`
  ⟨m, M⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
