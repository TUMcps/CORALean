module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.MatPow
public import CORALean.ContSet.Zonotope.Real.Operations.Map

@[expose] public section

/-!
# The matrix-zonotope order `i` contributes to the input solution, exactly

The matrix-zonotope part of [1, Thm. 1] ([1, Sec. 4.4]): `LinParamSys.inputTerm` with the power kept
as a matrix zonotope rather than over-approximated into an interval matrix, so the
dependency between a member's own powers survives. Only orders `0` and `1`
are kept as a matrix zonotope, but nothing here is special to them — `matPow` is
sound at any order, and the restriction is Sec. 4.4's, not this definition's.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrix-zonotope order `i` contributes to the input solution:
`Aᵢr^{i+1}/(i+1)!` kept as a zonotope over the system's whole matrix zonotope. -/
noncomputable def LinParamSys.inputTermZono {n : ℕ} (sys : LinParamSys 𝕄𝒵 n) (r : ℝ)
    (i : ℕ) : Zonotope (Mat ℝ n n) :=
  Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) (r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)))
    (sys.A.matPow i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
