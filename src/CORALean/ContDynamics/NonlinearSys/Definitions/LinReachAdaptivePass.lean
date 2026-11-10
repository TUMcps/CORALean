module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# One pass of the adaptive step at a fixed time step size

`LinReachAdaptivePass`: the time-interval and time-point sets of one linearization at `Δt`, the
abstraction error the loop accepted included, and what the tuning reads of it: `A`, the
linearization point, the last `Rmax`, `trueError`, the box radii of `errorSolution_adaptive` of
the error (`abstrerr`), and the zero rows of the error (`Gzero`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- One linearization at a fixed `Δt`: its sets and what the tuning reads of it. -/
structure NonlinearSys.LinReachAdaptivePass (𝕋 : Type) (n : ℕ) where
  /-- `Rti`, the abstraction error included. -/
  Rti : Zonotope (Vec 𝕋 n)
  /-- `Rtp`, the abstraction error included. -/
  Rtp : Zonotope (Vec 𝕋 n)
  /-- `linsys.A`. -/
  A : Mat 𝕋 n n
  /-- `nlnsys.linError.p.x`. -/
  xs : Vec 𝕋 n
  /-- The last `Rmax + p.x` of the abstraction-error loop. -/
  Rmax : Zonotope (Vec 𝕋 n)
  /-- `trueError`. -/
  trueError : Vec 𝕋 n
  /-- `sum(abs(generators(Rerror)),2)`. -/
  abstrerr : Vec 𝕋 n
  /-- `vecnorm(generators(VerrorDyn),1,2) == 0`. -/
  Gzero : Fin n → Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
