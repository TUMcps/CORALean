module

public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.Global.Tensor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The section of a zonotope by a vertical line is an interval

The intersection of a convex set with `x = γ` is convex in `y`: a weighted average of `(γ, y₁)`
and `(γ, y₂)` is `(γ, a y₁ + b y₂)`. So the output of [1, Alg. 3] and [1, Alg. 4] being an
interval `[m; M]` costs nothing, and the section is determined by its least and greatest `y`.

## Inputs
* `Z` – planar zonotope
* `γ` – abscissa of the vertical line

## Hypotheses
* none

## Conclusion
* the section of `Z` is convex

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.section_convex (Z : Zonotope (Vec ℝ 2)) (γ : ℝ) :
    Convex ℝ {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct} := by -- --- PROOF ---
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  have := Z.convex_construct hy₁ hy₂ ha hb hab
  have e : a • (![γ, y₁] : Vec ℝ 2) + b • (![γ, y₂] : Vec ℝ 2)
      = ![γ, a • y₁ + b • y₂] := by
    ext k; fin_cases k
    · simp [← add_mul, hab]
    · simp
  rw [e] at this
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
