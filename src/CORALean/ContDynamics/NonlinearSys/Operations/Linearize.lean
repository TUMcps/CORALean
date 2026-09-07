import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# The linear system a linearization leaves behind

CORA's `nonlinearSys/private/linearize`, minus the derivative: the system is
the matrix and nothing else. Everything the field contributes beyond `A x` —
its value at the expansion point, the input coupling, the abstraction error —
is collected in `linInput` instead, so the two halves of a linearization are
two definitions rather than one returning a pair.

`sys` is not an argument and cannot be: `A` is whatever matrix the certificate
was issued for, and no property of the field is used to read a system off it.

`LinearSys ℝ`, not `LinearSys 𝕋`: the certificate's `A` is real. A float layer
linearizes in float arithmetic and then certifies against the real matrix its
result reads as.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linear system a linearization at any matrix `A` produces. -/
def NonlinearSys.linearize (A : Mat ℝ n n) : LinearSys ℝ n := ⟨A⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
