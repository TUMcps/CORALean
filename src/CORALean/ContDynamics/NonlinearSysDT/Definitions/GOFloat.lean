module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.GO
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The GO parameters of a nonlinear discrete-time system as intervals

`NonlinearSysDT.GO` holds the real reference run and real matrices, which a float run cannot
name. `GOFloat` holds, in their place, boxes and interval matrices over `𝕋` that enclose them:
the reference run `x`, `y` and the parameters `A`, `B`, `F`, `C`, `D`, `E` of `computeGO`, with
the same indexing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The general output model parameters of a nonlinear discrete-time system, with the reference
trajectory and the matrices as intervals over `𝕋`. -/
structure NonlinearSysDT.GOFloat (𝕋 : Type) (n m r : ℕ) where
  x : ℕ → Interval (Vec 𝕋 n)
  y : ℕ → Interval (Vec 𝕋 r)
  A : ℕ → Interval (Mat 𝕋 n n)
  B : ℕ → ℕ → Interval (Mat 𝕋 n m)
  F : ℕ → ℕ → Interval (Mat 𝕋 n (n + r))
  C : ℕ → Interval (Mat 𝕋 r n)
  D : ℕ → ℕ → Interval (Mat 𝕋 r m)
  E : ℕ → ℕ → Interval (Mat 𝕋 r (n + r))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
