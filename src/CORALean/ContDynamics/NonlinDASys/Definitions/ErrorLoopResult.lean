import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# What the linearization-error loop of [1, Alg. 1] hands on

Lines 4-10 of `[1, Alg. 1]` end with the assumed errors `L̄` of the last pass, the time-interval
set `Rᵈ(τ_k)` that pass computed from them (line 7), the joint set `R(τ_k)` of `(x, y)` (line 8)
and the errors `L` Cor. 1 found over it (line 9). The errors are pairs, the dynamics'
`ℓᵈ - C F⁻¹ ℓᵃ` and the constraint's `ℓᵃ`, as in `NonlinDASys.LinPoint`.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The last pass of [1, Alg. 1]'s lines 4-10. -/
structure NonlinDASys.ErrorLoopResult (n p : ℕ) where
  /-- `L̄`, line 5: the assumed errors. -/
  Lbar : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p)
  /-- `Rᵈ(τ_k)`, line 7. -/
  Rti : Zonotope (Vec ℝ n)
  /-- `R(τ_k)`, line 8: the joint set of the differential and algebraic variables. -/
  Rjoint : Zonotope (Vec ℝ n × Vec ℝ p)
  /-- `L`, line 9: the errors Cor. 1 computes over `R(τ_k)`. -/
  L : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
