module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpMatZonoTerm
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# Matrix zonotopes: the Taylor truncation

`expMatZonoTaylor`: [1, Sec. 3.1]'s Taylor truncation as a matrix zonotope, every order evaluated
independently, `i = 0 … η`
matching `MatExp.expTaylor`'s `Finset.range (η + 1)` exactly — `expIntervalTaylor`'s recursion
at a zonotope, so that the correlations between a system matrix's entries survive the powers.

## Inputs
* `M` – matrix zonotope

## Output
* matrix zonotope of the Taylor truncation up to the given order

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor truncation as a matrix zonotope, `i = 0 … η` matching
`MatExp.expTaylor`'s `Finset.range (η + 1)` exactly. -/
noncomputable def MatExp.expMatZonoTaylor (M : Zonotope (Mat ℝ n n)) :
    ℕ → Zonotope (Mat ℝ n n)
  | 0 => MatExp.expMatZonoTerm M 0
  | k + 1 => Zonotope.plus (MatExp.expMatZonoTerm M (k + 1)) (MatExp.expMatZonoTaylor M k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
