import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# What `priv_abstractionError_adaptive` returns

The abstraction errors of one evaluation, in the outputs' order: `Z_error` (the dynamics'
`ℓᵈ - C F⁻¹ ℓᵃ`), `errorInt`, `errorInt_x`, `errorInt_y`, and the parts `Z_error_x` (`ℓᵈ`) and
`Z_error_y` (`ℓᵃ`). `R_y` is the second component of the joint set of the pass that is run
with these errors.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The outputs of `priv_abstractionError_adaptive`. -/
structure NonlinDASys.AbstractionError (n p : ℕ) where
  /-- `Z_error_x`: the dynamics' own error `ℓᵈ`. -/
  Z_error_x : Zonotope (Vec ℝ n)
  /-- `Z_error_y`: the constraint's error `ℓᵃ`. -/
  Z_error_y : Zonotope (Vec ℝ p)
  /-- `Z_error`: `ℓᵈ - C F⁻¹ ℓᵃ`, [1, Eq. 15] with the sign of [1, Cor. 1]. -/
  Z_error : Zonotope (Vec ℝ n)
  /-- `errorInt_x`: the componentwise size of `Z_error_x`. -/
  errorInt_x : Vec ℝ n
  /-- `errorInt_y`: the componentwise size of `Z_error_y`. -/
  errorInt_y : Vec ℝ p
  /-- `errorInt`: the componentwise size of `Z_error`. -/
  errorInt : Vec ℝ n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
