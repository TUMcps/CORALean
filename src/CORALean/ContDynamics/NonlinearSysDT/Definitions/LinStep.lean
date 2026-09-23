import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

/-!
# One linearization of a discrete step

`AbstractionError` is stated over the map `f` itself, not a system — no flow,
no derivative, nothing continuous — so it applies here unchanged, fed `sys.f`
directly. The certificate it builds is the same one CORA computes for the
continuous case, checked instead against
`f(x,u) = f(xs,us) + A(x - xs) + B(u - us) + L(x,u)`, which is exactly what a
discrete step needs: `x(k+1) = f(x(k), u(k))`, no integral in sight.

`Δt` and `MatExp` play no role, so `LinStep` carries no discretization: the
matrix a certificate is issued for is already what `LinearSysDT.reach` steps
with.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- One linearization of `sys`, with the certificate that makes it conservative
wherever the state stays in `R`. -/
structure NonlinearSysDT.LinStep (sys : NonlinearSysDT n m) (U : S m) where
  A : Mat ℝ n n
  B : Mat ℝ n m
  xs : Vec ℝ n
  us : Vec ℝ m
  R : Set (Vec ℝ n)
  L : S n
  cert : AbstractionError sys.f A B xs us R (construct U) L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
