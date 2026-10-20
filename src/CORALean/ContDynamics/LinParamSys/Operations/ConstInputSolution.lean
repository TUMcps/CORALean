module

public import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrix
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# What a constant input contributes at every time of one step, at every member

`LinearSys.constInputSolution` with the system matrix ranging over a set,
the split case of [1, Alg. 1] (an input set missing the origin, which [1, Sec. 3.3] leaves out):
the straight line `C(r)` applied to the segment `[0, ũ]`, `inputSolution`'s own enclosure
taking the place of a plain `Mtimes`, widened by the box's own interpolation error
`intervalConstCorrectionMatrix` in place of the point one. That input correction matrix is not in
a paper; CORA's `priv_inputTie` [2]. `expIntegral_mem_constInputSolution` is the guarantee.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `uc` – constant input

## Output
* what the constant input contributes at every time of the step

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
* [2] `contDynamics/@linParamSys/private/priv_inputTie.m`
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the constant `ũ` contributes at any time of `[0, r]`, at every member
of `sys.A`: `C(r) · [0, ũ] ⊕ F̃ ũ`, at Taylor order `η`. -/
noncomputable def LinParamSys.constInputSolution (sys : LinParamSys ℐ n) (r : ℝ) (η : ℕ)
    (uc : Vec ℝ n) : S n :=
  let seg : S n := LinComb.linComb (OfPoint.ofPoint 0) (OfPoint.ofPoint uc)  -- [0, ũ]
  let line := sys.inputSolution r η seg                             -- C(r) applied to [0, ũ]
  let Fc := MatExp.intervalConstCorrectionMatrix sys.A r η          -- F̃ over the box
  let err := Mtimes.mtimes (𝕄 := ℐ) Fc (OfPoint.ofPoint uc)        -- F̃ ũ
  Plus.plus line err                                                -- the line ⊕ F̃ ũ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
