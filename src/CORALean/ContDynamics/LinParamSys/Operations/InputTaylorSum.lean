import CORALean.ContDynamics.LinParamSys.Operations.InputTerm

/-!
# The exact orders of the input solution at a set-valued matrix, summed

`LinearSys.inputTaylorSum` with every order an interval matrix rather than a
point one. Recursive rather than a fold over `Finset`, for the reason the point
case gives: `plus` is only an enclosure and never has to be reassociated, and
the guarantee is then one induction.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exact orders of the input solution, `0` through `η`, summed. -/
noncomputable def LinParamSys.inputTaylorSum (sys : LinParamSys ℐ n) (r : ℝ) (U : S n) :
    ℕ → S n
  | 0 => Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r 0) U
  | i + 1 => Plus.plus (sys.inputTaylorSum r U i)
      (Mtimes.mtimes (𝕄 := ℐ) (sys.inputTerm r (i + 1)) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
