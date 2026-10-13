module

public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

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

-- Authors:       Claude Sonnet 5
-- Written:       04-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n m : ℕ} {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- One linearization of `sys`, with the certificate that makes it conservative
wherever the state stays in `R`. -/
structure NonlinearSysDT.LinStep (sys : NonlinearSysDT n m) (𝕋 : Type) [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (U : S m) where
  A : Mat 𝕋 n n
  B : Mat 𝕋 n m
  xs : Vec 𝕋 n
  us : Vec 𝕋 m
  /-- A box enclosing the constant `f(x✱,u✱) - A x✱`. -/
  c : Float.Interval (Vec 𝕋 n)
  R : Set (Vec ℝ n)
  L : S n
  cert : AbstractionError sys.f (toRealMat A) (toRealMat B) (toRealVec xs) (toRealVec us) R
    (construct U) L
  c_mem : sys.f (toRealVec xs) (toRealVec us) - toRealMat A *ᵥ toRealVec xs ∈ construct c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
