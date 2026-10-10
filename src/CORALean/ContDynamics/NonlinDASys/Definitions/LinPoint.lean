import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# One linearization of a DAE, as `linReach` takes it

What CORA's `priv_linearize` stores in `nlnsysDA.linError` for one start set, and the error
sets of that step: the Jacobian blocks `[A, C, B]` of `f` and `[D, F, E]` of `g` at the
expansion point `z* = (x*, y*, u*)` ([1, Eq. 9]), CORA's `F_inv` (`pinv(F)`), and the error
zonotopes `Verror` (the dynamics', `ℓᵈ - C F⁻¹ ℓᵃ`) and `Verror_y` (the constraint's, `ℓᵃ`).
`f(z*)` and `g(z*)` are not fields: a step takes them from the system.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The data of one DAE linearization step: the Jacobian blocks, `F⁻¹`, the expansion point
and the two error zonotopes. -/
structure NonlinDASys.LinPoint (n p m : ℕ) where
  A : Mat ℝ n n
  B : Mat ℝ n m
  C : Mat ℝ n p
  D : Mat ℝ p n
  E : Mat ℝ p m
  F_inv : Mat ℝ p p
  xs : Vec ℝ n
  ys : Vec ℝ p
  us : Vec ℝ m
  Verror : Zonotope (Vec ℝ n)
  Verror_y : Zonotope (Vec ℝ p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
