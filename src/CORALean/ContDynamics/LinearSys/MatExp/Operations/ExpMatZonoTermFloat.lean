module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContSet.Zonotope.Float.Operations.MatPow
public import CORALean.ContSet.Zonotope.Float.Operations.MatSmul

@[expose] public section

/-!
# `MatExp.expMatZonoTerm`, over a floating-point scalar

`Real.MatExp.expMatZonoTerm` rounded: the matrix zonotope's `i`-th power scaled by
`1/i!`, which no float holds exactly, so by `invFactorialBounds i` as an interval, the
same handle `expIntervalTaylor` uses.

## Inputs
* `M` – float matrix zonotope
* `i` – order

## Output
* float matrix zonotope of the order's Taylor term

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Order `i` of [1, Sec. 3.1]'s series: the `i`-th power, scaled by `[1/i!]`. -/
def MatExp.expMatZonoTerm (M : Zonotope (Mat 𝕋 n n)) (i : ℕ) : Zonotope (Mat 𝕋 n n) :=
  Zonotope.matSmul (MatExp.invFactorialBounds i).inf (MatExp.invFactorialBounds i).sup (M.matPow i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
