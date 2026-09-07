import CORALean.ContDynamics.LinearSys.Operations.InputTerm

/-!
# The exact orders of the input solution, summed

The sum is recursive rather than a fold over `Finset`, since `plus` is only an
enclosure and never has to be reassociated this way; the guarantee is then one
induction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exact orders of the input solution, `0` through `η`, summed. -/
noncomputable def LinearSys.inputTaylorSum (sys : LinearSys 𝕋 n) (r : ℝ) (U : S n) : ℕ → S n
  | 0 => Mtimes.mtimes (sys.inputTerm r 0) U
  | i + 1 => Plus.plus (sys.inputTaylorSum r U i)
      (Mtimes.mtimes (sys.inputTerm r (i + 1)) U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
