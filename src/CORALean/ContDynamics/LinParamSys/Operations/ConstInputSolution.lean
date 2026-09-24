import CORALean.ContDynamics.LinParamSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrix
import CORALean.ContSet.Interval.Real.Instances

/-!
# What a constant input contributes at every time of one step, at every member

`LinearSys.constInputSolution` with the system matrix ranging over a set,
[1, Alg. 4]'s split case: the straight line `C(r)` applied to the segment
`[0, ũ]`, `inputSolution`'s own enclosure taking the place of a plain `Mtimes`,
widened by the box's own interpolation error `intervalConstCorrectionMatrix`
[1, Prop. 3.4] in place of the point one. `expIntegral_mem_constInputSolution`
is the guarantee.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


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
