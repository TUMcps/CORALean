module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat

@[expose] public section

/-!
# `Zonotope.interHalfspace`

`eq. (5)`: a zonotope `Z` intersected with the halfspace `H₋ = {x | h x ≤ f}`, in CG-Rep by
the addition of exactly one generator and one equality constraint. `dm` is the paper's own `d_m`,
the orthogonal width of `Z` past `H₋`'s bounding hyperplane; `IntersectHalfspaceExact` is where
`dm ≥ 0` gets used, from the hypothesis that `Z` actually meets the hyperplane.

## Inputs
* `Z` – zonotope
* `h` – halfspace normal functional
* `f` – halfspace offset

## Output
* the zonotope intersected with the halfspace

## References

* [1] [V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica,
      2022.](../../../../../../references/2022/raghuraman-koeln-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 1]: `Z` meeting the halfspace `{x | h x ≤ f}`, eq. (5)'s construction. -/
noncomputable def Zonotope.interHalfspace (Z : Zonotope (Vec ℝ n)) (h : Vec ℝ n →ₗ[ℝ] ℝ) (f : ℝ) :
    ConZonotope (Vec ℝ n) :=
  let dm := f - h Z.c + ∑ i, |h (Z.G i)|
  ConZonotope.ofMat Z.c (Fin.append Z.G (fun _ : Fin 1 => (0 : Vec ℝ n)))
    (fun _ : Fin 1 => Fin.append (fun i => h (Z.G i)) (fun _ : Fin 1 => dm / 2))
    (fun _ : Fin 1 => f - h Z.c - dm / 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
