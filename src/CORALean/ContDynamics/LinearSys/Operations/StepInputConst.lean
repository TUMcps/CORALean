import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# What a constant input contributes over one step

`stepInput`'s vector-valued counterpart: the exponential integral applied to
one vector `c` rather than integrated against a signal `u`. No step index —
a constant input contributes the same amount at every step, which is exactly
the precision `inputSolution`'s set-valued form throws away, by admitting a
different point of the input set at each step rather than the one a zero-order
hold actually holds. `StepInputConstEq` is what makes the two agree when `u`
is that constant.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What a constant input contributes over one step: the exponential integral
applied to that one vector. -/
noncomputable def LinearSys.stepInputConst (sys : LinearSys 𝕋 n) (c : Vec ℝ n) (Δt : ℝ) :
    Vec ℝ n :=
  Real.MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
