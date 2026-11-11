module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# One pass of the adaptive `'poly'` step at a fixed time step size

`LinReachPolyAdaptivePass`: the time-interval and time-point sets of one linearization at `Δt`,
the abstraction error the loop accepted included, and what the tuning reads of it: `A`, the
linearization point, `trueError`, the box radii of the independent generators of `Rerror`
(`abstrerr`), and the zero rows of the dynamic error (`Gzero`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- One linearization at a fixed `Δt`: its sets and what the tuning reads of it. -/
structure NonlinearSys.LinReachPolyAdaptivePass (𝕋 : Type) (n : ℕ) where
  /-- `Rti`, the abstraction error included. -/
  Rti : PolyZonotope (Vec 𝕋 n)
  /-- `Rtp`, the abstraction error included. -/
  Rtp : PolyZonotope (Vec 𝕋 n)
  /-- `linsys.A`. -/
  A : Mat 𝕋 n n
  /-- `nlnsys.linError.p.x`. -/
  xs : Vec 𝕋 n
  /-- `trueError`. -/
  trueError : Vec 𝕋 n
  /-- `sum(abs(Rerror.GI),2)`. -/
  abstrerr : Vec 𝕋 n
  /-- `vecnorm(generators(VerrorDyn),1,2) == 0`. -/
  Gzero : Fin n → Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
