import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.MatPow
import CORALean.ContSet.Zonotope.Real.Operations.Map

/-!
# The matrix-zonotope order `i` contributes to the input solution, exactly

[1, Prop. 3.6]'s exact part: `LinParamSys.inputTerm` with the power kept as a
matrix zonotope rather than over-approximated into an interval matrix, so the
dependency between a member's own powers survives. Only orders `0` and `1`
appear in the proposition, but nothing here is special to them — `matPow` is
sound at any order, and the restriction is Prop. 3.6's, not this definition's.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
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
