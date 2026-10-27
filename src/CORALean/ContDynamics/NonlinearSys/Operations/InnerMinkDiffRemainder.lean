module

public import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffOps
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# `innerMinkDiffRemainder`, the Lagrange remainder loop of the inner algorithm

Lines 10-13 of [1, Alg. 1]: enlarge the remainder guess `L` by `μ`, bound the abstraction error
it induces by (13), evaluate the Lagrange remainder (9) on the box (25) of the time-interval
affine solution plus that error, and repeat until the new `L` lies in the enlarged guess `L̂`;
line 14 then spends `L̂`. `fuel` bounds the passes, so the result is an `Option`, `none` once
they have not met the condition; the containment test is the `Bool` the caller supplies, as in
`abstrErrLoop`. `L̂` is `Lhat`, the remainder of line 12 `L'`.

## Inputs
* `ops` – set operations
* `Δt` – step size
* `μ` – enlargement factor
* `A` – linearization matrix
* `xstar` – linearization point
* `Raffτ` – time-interval affine solution

## Output
* the enlarged remainder the loop settles on, or none

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


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
    -- 11. L̂ ← μL
    let Lhat := ops.smul μ L
    -- 11. R̂_err(L̂) ← Eq. (13)
    let Rerr := ops.err Δt A Lhat
    -- 12. R̂(τ₀) ← Eq. (25)
    let Rτ₀ := ops.box (Raffτ + Rerr)
    -- 12. L ← Eq. (9)
    let L' := ops.lagr xstar Rτ₀
    -- 13. until L ⊆ L̂
    if ops.sub L' Lhat then some Lhat
    else NonlinearSys.innerMinkDiffRemainder ops Δt μ A xstar Raffτ L' k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
