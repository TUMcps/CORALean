import CORALean.ContDynamics.NonlinearSys.NonlinearSys

/-!
# The abstraction error of a linearization

Althoff's thesis, ch. 3.4. Splitting a nonlinear field at an expansion point,

`f(x,u) = f(x✱,u✱) + A(x - x✱) + B(u - u✱) + L(x,u)`,

leaves a remainder `L`, and this is a set enclosing that remainder over the
whole of `R × U`.

It is a certificate in the sense `SupportBound` is: it says nothing about where
`L` came from — a Lagrange remainder, an interval Hessian, a solver — so
whatever produced it stays outside the trusted base, and a wrong `L` yields no
certificate rather than a wrong reachable set. No derivative of `f` appears
here or anywhere downstream.

Consequently `A` and `B` are *not* required to be the Jacobians at `(x✱, u✱)`.
Any pair of matrices admits a certificate; a bad pair only makes `L` large.
That is why the certificate formulation is stronger than the derivative-based
one rather than merely cheaper: a linearization computed in float arithmetic,
or one deliberately reused across several steps as CORA does, is covered
without a word about how far it is from the true derivative.

`R` and `U` are plain sets, as `SupportBound`'s are, so a certificate is not
tied to any description of where it holds. `L` is a representation, since it
has to enter a computed set, and a parameter rather than a field, since
`linInput` names it in the type of its result.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- `L` encloses what is left of `f` once the affine part at `(xs, us)` is
subtracted, everywhere on `R × U`. -/
structure AbstractionError (sys : NonlinearSys n m) (A : Mat ℝ n n) (B : Mat ℝ n m)
    (xs : Vec ℝ n) (us : Vec ℝ m) (R : Set (Vec ℝ n)) (U : Set (Vec ℝ m))
    (L : S n) : Prop where
  encloses : ∀ x ∈ R, ∀ u ∈ U,
    sys.f x u - (sys.f xs us + A *ᵥ (x - xs) + B *ᵥ (u - us)) ∈ construct L

end CORALean.Real
