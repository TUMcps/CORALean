import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# The interval Hessians of one abstraction-error evaluation

What CORA's `priv_abstractionError_adaptive` obtains from `nlnsysDA.hessian(totalInt_x,
totalInt_y, totalInt_u)`: the Hessian rows of `f` and `g` over the intervals as a centre and a
radius (`Hᵈ_c ± Hᵈ_Δ`, `Hᵃ_c ± Hᵃ_Δ`, [1, Cor. 1]), and the deviation zonotope
`dz = [dx; dy; du]` they are evaluated against. The Hessians come from the model, so they are
data here, as in `NonlinDASys.linError`.

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

/-- Interval Hessians of `f` (`n` rows) and `g` (`p` rows) in `q` variables, and `dz`. -/
structure NonlinDASys.HessData (n p q : ℕ) where
  /-- `Hᵈ_c`: the centres of the dynamics' Hessians. -/
  Hd_c : Fin n → Mat ℝ q q
  /-- `Hᵈ_Δ`: their radii. -/
  Hd_Δ : Fin n → Mat ℝ q q
  /-- `Hᵃ_c`: the centres of the constraint's Hessians. -/
  Ha_c : Fin p → Mat ℝ q q
  /-- `Hᵃ_Δ`: their radii. -/
  Ha_Δ : Fin p → Mat ℝ q q
  /-- `dz`: the deviation of `(x, y, u)` from the expansion point. -/
  dz : Zonotope (Vec ℝ q)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
