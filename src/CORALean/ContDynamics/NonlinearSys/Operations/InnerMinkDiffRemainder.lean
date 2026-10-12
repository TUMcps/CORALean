import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffOps
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# `innerMinkDiffRemainder`, the Lagrange remainder loop of the inner algorithm

Lines 10-13 of [1, Alg. 1], as in the conservative linearization [1] builds on: enlarge the
remainder guess `L` by `μ`, bound the abstraction error it induces by (13), evaluate the
Lagrange remainder (9) on the box (25) of the time-interval affine solution plus that error,
and repeat until the new remainder `L` lies in the enlarged guess `L̂`; line 14 then spends
`L̂`. The loop's start `L = [0ₙ, 0ₙ]` is line 9, the caller's.

`repeat ... until` states no iteration count, so `fuel` is an argument and the result an
`Option`, `none` once `fuel` passes have not met the condition; the containment test is the
`Bool` the caller supplies, as in `abstrErrLoop`. `L̂` is `Lhat`, the remainder of line 12 `L'`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enlarged remainder `L̂` lines 10-13 of [1, Alg. 1] settle on from the guess `L`, for the
linearization `A` at `xstar` and the time-interval affine solution `Raffτ`; `none` once `fuel`
passes have not settled. -/
def NonlinearSys.innerMinkDiffRemainder (ops : NonlinearSys.InnerMinkDiffOps n 𝓛) (Δt μ : ℝ)
    (A : Mat ℝ n n) (xstar : Vec ℝ n) (Raffτ : Set (Vec ℝ n)) : 𝓛 → ℕ → Option 𝓛
  | _, 0 => none
  | L, k + 1 =>
    let Lhat := ops.smul μ L                           -- 11. L̂ ← μL
    let Rerr := ops.err Δt A Lhat                      -- 11. R̂_err(L̂) ← Eq. (13)
    let Rτ₀ := ops.box (Raffτ + Rerr)                  -- 12. R̂(τ₀) ← Eq. (25)
    let L' := ops.lagr xstar Rτ₀                       -- 12. L ← Eq. (9)
    if ops.sub L' Lhat then some Lhat                  -- 13. until L ⊆ L̂
    else NonlinearSys.innerMinkDiffRemainder ops Δt μ A xstar Raffτ L' k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
