import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys

/-!
# A closed loop, bundled with its control period

CORA's `neurNetContrSys(sys, nn, dt)` stores the sampling time `dt` with the
system: the controller is evaluated every `dt`, and the set a closed loop reaches
depends on it. `NeurNetContrSys` states `dt` per theorem instead, so `Reach`, whose
`reachExact` reads the system and `params` only, takes it bundled here. The
plant's step `timeStep` stays in `options`, which CORA checks divides `dt`, and so
does `reach`.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- `sys` with its control period `dt`, CORA's `sys.dt`. -/
structure NeurNetContrSys.WithPeriod (𝕋 : Type) [Scalar 𝕋] (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  sys : NeurNetContrSys 𝕋 S n
  dt : ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
