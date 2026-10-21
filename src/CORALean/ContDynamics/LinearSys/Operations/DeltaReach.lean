module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContSet.Interval.Real.Instances
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The state differences a step spans

CORA's `aux_deltaReach`: the set of state *differences* `x(t) - x(0)` over a step, not of states.
It is `timeInterval` with the segment anchored at the origin and the far end shifted,
`CH(0, (e^{Ar} - I)X₀) ⊕ F X₀`, the same correction matrix covering the interpolation error. The
origin end is written `0 · ((e^{Ar} - I)X₀)` and not a constructed zero set, which is CORA's own
`zeros(n)*Rhom_tp_delta` "to retain dependencies": at a polynomial zonotope a zero *image* keeps
the factors the segment is written over. The inputs are not in here: CORA's `Rdelta = Rhom + RV`
adds the particular solution, an enclosure a caller supplies and `inputSolution` computes. `exp`
needs a norm on `Mat`, a choice rather than an instance: the `l∞` operator one.

## Inputs
* `sys` – linear system
* `r` – step length
* `η` – Taylor order
* `X₀` – initial set

## Output
* state differences between the step's states and their starting states
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `CH(0, (e^{Ar} - I)X₀) ⊕ F X₀`: every difference between a state of
the step and the state it started from. -/
noncomputable def LinearSys.deltaReach
    (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (X₀ : S n) : S n :=
  LinComb.linComb
      (Mtimes.mtimes (0 : Mat ℝ n n)
        (Mtimes.mtimes (exp (r • toRealMat sys.A) - 1) X₀))
      (Mtimes.mtimes (exp (r • toRealMat sys.A) - 1) X₀) ⊞
    Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrix (toRealMat sys.A) r η) X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
