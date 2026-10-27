module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinParamSys.Operations.Canonical
public import CORALean.ContDynamics.LinParamSys.Operations.InputTaylorSumTail
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainder
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Operations.MatPow

@[expose] public section

/-!
# The set every input contributes over one step, at a matrix zonotope

[1, Thm. 1]: `LinearSys.inputSolution` adapted to a system matrix that is a matrix zonotope
`A_Z`. Orders `0` and `1` are `aux_inputTermZono`, computed exactly through the matrix zonotope;
from order `2` on, `A_Z` is over-approximated by its enclosing interval matrix `A_Z.interval`,
matching `inputTaylorSumTail` and `intervalInputRemainder` ([1, Sec. 4.4] keeps matrix zonotopes
to second order for the same reason). The four pieces stay four separate products, as CORA's
`priv_inputSolution` takes them, not factored into `(r + A_Zr²/2!)U`.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `U` – input set

## Output
* the set the inputs contribute over one step

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes 𝕄𝒵 S] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The matrix-zonotope order `i` contributes to the input solution:
`Aᵢr^{i+1}/(i+1)!` kept as a zonotope over the system's whole matrix zonotope. -/
noncomputable def LinParamSys.aux_inputTermZono {n : ℕ} (sys : LinParamSys 𝕄𝒵 n) (r : ℝ)
    (i : ℕ) : Zonotope (Mat ℝ n n) :=
  Zonotope.map (LinearMap.lsmul ℝ (Mat ℝ n n) (r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)))
    (sys.A.matPow i)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Everything the input can contribute over one step, at every matrix the
system's matrix zonotope holds: the linear and quadratic orders exact, every
order past them and the remainder over the enclosing interval matrix. -/
noncomputable def LinParamSys.inputSolutionZono (sys : LinParamSys 𝕄𝒵 n) (r : ℝ) (η : ℕ)
    (U : S n) : S n :=
  Mtimes.mtimes (𝕄 := 𝕄𝒵) (sys.aux_inputTermZono r 0) U ⊞
    Mtimes.mtimes (𝕄 := 𝕄𝒵) (sys.aux_inputTermZono r 1) U ⊞
    (LinParamSys.canonical (𝕄 := ℐ) sys.A.interval).inputTaylorSumTail r U η ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.intervalInputRemainder sys.A.interval r η) U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
