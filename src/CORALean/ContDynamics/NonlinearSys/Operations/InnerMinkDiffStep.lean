import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffState
import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffRemainder
import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# `innerMinkDiffStep`, one step of the inner Minkowski-difference algorithm

Lines 3-16 of [1, Alg. 1] from the inner set `R̂(t_k)` (`Rtk`), over exact sets: line 4's
linearization point, line 5's `w = f(x*)` and `A = Df(x*)` of (6), line 6's curvature error,
lines 7-8's affine solutions (10)-(12) and (16), lines 9-13's remainder loop
(`innerMinkDiffRemainder`), and lines 14-16: `R̂(t_{k+1}) = R_aff(Δt) ⊖ R̂_err(L̂) + 2c` (`Prop. 1`)
and `R̂(τ_k) = conv(R̂(t_k) ⊖ R̂_err(L̂) ⊖ C, R̂(t_{k+1}) ⊖ C) + 2c` (`Prop. 2`), with line 14's
`c = cen(C) + cen(R̂_err(L̂))`. `none` when the remainder loop runs out of `fuel`.

Three readings of the listing. Line 4 prints `x*(t_k) ← cen(R̂(t_k)) + ½Δt f(x*(t_k))`, `x*`
on both sides; the field is evaluated at `cen(R̂(t_k))`, as CORA's `linReachInner` does.
(10)-(12) and (17) are stated for `x* = 0ₙ`, so `R_hom` maps `R̂(t_k) - x*` and is shifted back
by `x*`, and line 6 boxes `R̂(t_k) - x*`, as `linReachInner` does; `R_aff(Δt)` is then the
affine solution `x* + e^{AΔt}(x(0) - x*) + R_con(Δt)` of (8) in the original coordinates.
`CZ(·)` in line 16 converts a polytope to a constrained zonotope exactly [1, Sec. IV-A], so it
leaves the set unchanged and is not written.

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

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-16 of [1, Alg. 1] from `R̂(t_k)`, for the field `f`, the step `Δt` and the factor `μ`;
`none` once the remainder loop has run `fuel` passes. -/
noncomputable def NonlinearSys.innerMinkDiffStep (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (f : Vec ℝ n → Vec ℝ n) (Δt μ : ℝ) (fuel : ℕ) (Rtk : Set (Vec ℝ n)) :
    Option (NonlinearSys.InnerMinkDiffState n 𝓛) :=
  let xstar := ops.cen Rtk + (Δt / 2) • f (ops.cen Rtk)            -- 4. x*(t_k)
  let w := f xstar                                                  -- 5. w ← Eq. (6)
  let A := ops.jac xstar                                            -- 5. A ← Eq. (6)
  let C := ops.curv Δt A ((fun x => x - xstar) '' ops.box Rtk) w    -- 6. C ← F box ⊕ G w
  let Rhom := (fun x => xstar + exp (Δt • A) *ᵥ (x - xstar)) '' Rtk  -- 7. R_hom ← Eq. (11)
  let Rcon := ∫ θ in (0:ℝ)..Δt, exp ((Δt - θ) • A) *ᵥ w             -- 7. R_con ← Eq. (12)
  let Raff := (fun x => x + Rcon) '' Rhom                           -- 8. R_aff ← Eq. (10)
  let Raffτ := convexHull ℝ (Rtk ∪ Raff) + C                        -- 8. R̂_aff(τ₀) ← Eq. (16)
  let L := ops.zero                                                 -- 9. L ← [0ₙ, 0ₙ]
  (NonlinearSys.innerMinkDiffRemainder ops Δt μ A xstar Raffτ L fuel).map fun Lhat => -- 10-13.
    let Rerr := ops.err Δt A Lhat                                   -- 14. R̂_err(L̂) ← Eq. (13)
    let c := ops.cen C + ops.cen Rerr                               -- 14. c
    let Rtk1 := (fun x => x + (2 : ℝ) • c) '' minkowskiDiff Raff Rerr  -- 15. R̂(t_{k+1})
    let Rtauk := (fun x => x + (2 : ℝ) • c) ''                      -- 16. R̂(τ_k)
      convexHull ℝ (minkowskiDiff (minkowskiDiff Rtk Rerr) C ∪ minkowskiDiff Rtk1 C)
    { xstar, w, A, C, Rcon, Raff, Lhat, Rerr, c, Rtk1, Rtauk }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
