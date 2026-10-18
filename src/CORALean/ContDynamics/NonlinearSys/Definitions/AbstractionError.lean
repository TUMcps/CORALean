module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# The abstraction error of a linearization

[1, Eq. 3]. Splitting a nonlinear field at an expansion point,
`f(x,u) = f(x✱,u✱) + A(x - x✱) + B(u - u✱) + L(x,u)`, leaves a remainder `L`, and
this is a set enclosing it over the whole of `R × U`.

It is a certificate in the sense `SupportBound` is: it says nothing about where
`L` came from, so whatever produced it stays outside the trusted base and a wrong
`L` yields no certificate rather than a wrong reachable set. No derivative of `f`
appears here or in anything that spends one — only in `of_hessian`, its supplier.

`A` and `B` are consequently *not* required to be the Jacobians at `(x✱, u✱)`: any
pair admits a certificate, a bad pair only making `L` large. So a linearization
computed in float arithmetic, or reused across several steps as CORA does, is
covered without a word about the true derivative.

`R` and `U` are plain sets, as `SupportBound`'s are. `L` is a representation,
having to enter a computed set, and a parameter rather than a field.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- `L` encloses what is left of `f` once the affine part at `(xs, us)` is
subtracted, everywhere on `R × U`. -/
structure AbstractionError (f : Vec ℝ n → Vec ℝ m → Vec ℝ n) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (xs : Vec ℝ n) (us : Vec ℝ m) (R : Set (Vec ℝ n)) (U : Set (Vec ℝ m))
    (L : S n) : Prop where
  encloses : ∀ x ∈ R, ∀ u ∈ U,
    f x u - (f xs us + A *ᵥ (x - xs) + B *ᵥ (u - us)) ∈ construct L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
