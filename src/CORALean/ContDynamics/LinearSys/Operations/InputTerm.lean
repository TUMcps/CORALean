import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# The matrix order a step of the input solution contributes

CORA's `Aⁱr^{i+1}/(i+1)!`: the `i`-th term of the exponential integrated once
over the step. `inputTaylorSum` sums these; `InputSolutionOuter` names the
same order to state what each summand of the input's Taylor series encloses.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrix order `i` contributes to the input solution: `Aⁱ r^{i+1}/(i+1)!`,
the `i`-th term of the exponential integrated once over the step. -/
noncomputable def LinearSys.inputTerm (sys : LinearSys 𝕋 n) (r : ℝ) (i : ℕ) : Mat ℝ n n :=
  (r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • (toRealMat sys.A) ^ i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
