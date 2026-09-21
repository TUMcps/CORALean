import CORALean.ContSet.ConZonotope.Real.Operations.OfMat

/-!
# `Zonotope.interHalfspace`

`eq. (5)`: a zonotope `Z` intersected with the halfspace `H₋ = {x | h x ≤ f}`, in CG-Rep by
the addition of exactly one generator and one equality constraint. `dm` is the paper's own `d_m`,
the orthogonal width of `Z` past `H₋`'s bounding hyperplane; `IntersectHalfspaceExact` is where
`dm ≥ 0` gets used, from the hypothesis that `Z` actually meets the hyperplane.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   ---
-- Last revision: ---


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
