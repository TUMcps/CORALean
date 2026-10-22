module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.MatPow
public import CORALean.ContSet.Zonotope.Float.Operations.MatSmul
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# The matrix-zonotope order `i` of the input solution, in floats

`LinParamSys.aux_inputTermZono` computed in `𝕋` ([1, Thm. 1], [1, Sec. 4.4]): the system's float
matrix zonotope to the power `i`, kept as a matrix zonotope, scaled by `r^{i+1}/(i+1)!`, which
`taylorCoeffBounds` brackets because no float holds it exactly.

## Inputs
* `sys` – system
* `r` – step size
* `i` – order

## Output
* the matrix zonotope that order `i` contributes

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Aᵢ r^{i+1}/(i+1)!` over the system's whole float matrix zonotope, for `r ≥ 0`. -/
def LinParamSys.inputTermZonoFloat (sys : LinParamSys 𝕄𝒵[𝕋] n)
    (r : 𝕋) (i : ℕ) : Zonotope (Mat 𝕋 n n) :=
  let c := MatExp.taylorCoeffBounds r (i + 1)                  -- r^{i+1}/(i+1)! ∈ [c.1, c.2]
  (Zonotope.matSmul c.inf c.sup (sys.A.matPow i)).materialiseMat    -- · Aᵢ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
