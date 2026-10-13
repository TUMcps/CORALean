import CORALean.ContDynamics.LinearSys.Operations.DeltaReach
import CORALean.ContDynamics.LinearSys.Operations.InputSolution

/-!
# `postΔ`, named

[1, Sec. 4.1], line 6 of Alg. 1: `R∆(τs) = post∆(R(ts), Ψ(τs), A)`, "a slight
modification of the standard techniques for linear system reachability" that
"returns the set of state differences ... instead of the set of states" — CORA's
own `Rdelta = Rhom + RV`, with `A` carried by `sys`.

Nothing is computed here that `deltaReach` and `inputSolution` do not already:
`Rhom` is `deltaReach`'s homogeneous part, `RV` is `inputSolution` at the
uncertain input set `Ψ`. `NonlinearSys.relinDeltaReach` already runs this exact
composition per step of the re-linearization loop; this file gives the paper's
own name and signature to the composition on its own, decoupled from that loop.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Scalar ContSet

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state difference a step can span under the constant uncertain input
set `Ψ`, from the initial set `R₀`: `deltaReach`'s homogeneous part, plus what
`Ψ` contributes as `inputSolution`. -/
noncomputable def LinearSys.postDelta (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (R₀ Ψ : S n) : S n :=
  sys.deltaReach r η R₀ ⊞ sys.inputSolution r η Ψ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
