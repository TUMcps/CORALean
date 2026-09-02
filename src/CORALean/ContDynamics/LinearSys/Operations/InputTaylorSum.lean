import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# The exact orders of the input solution

`inputTerm` and `inputTaylorSum` share a file because `inputTerm` is the
summand of this sum and of nothing else: it is CORA's `Aⁱr^{i+1}/(i+1)!`,
named only so that the induction proving the sum's guarantee has something to
name.

The sum is recursive rather than a fold over `Finset`, since `plus` is only an
enclosure and never has to be reassociated this way; the guarantee is then one
induction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

/-- The matrix order `i` contributes to the input solution: `Aⁱ r^{i+1}/(i+1)!`,
the `i`-th term of the exponential integrated once over the step. -/
noncomputable def LinearSys.inputTerm (sys : LinearSys 𝕋 n) (r : ℝ) (i : ℕ) : Mat ℝ n n :=
  (r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • (toRealMat sys.A) ^ i

/-- The exact orders of the input solution, `0` through `η`, summed. -/
noncomputable def LinearSys.inputTaylorSum (sys : LinearSys 𝕋 n) (r : ℝ) (U : S n) : ℕ → S n
  | 0 => Mtimes.mtimes (sys.inputTerm r 0) U
  | i + 1 => Plus.plus (sys.inputTaylorSum r U i)
      (Mtimes.mtimes (sys.inputTerm r (i + 1)) U)

end CORALean.Real
