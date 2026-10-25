module

public import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffState
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffRemainder
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# `innerMinkDiffStep`, one step of the inner Minkowski-difference algorithm

Lines 3-16 of [1, Alg. 1] from the inner set `R̂(t_k)` (`Rtk`), over exact sets: linearization
point, `w = f(x*)` and `A = Df(x*)`, curvature error, affine solutions (10)-(12) and (16), the
remainder loop (`innerMinkDiffRemainder`), then `R̂(t_{k+1})` by `Prop. 1` and `R̂(τ_k)` by
`Prop. 2`. `none` when the remainder loop runs out of `fuel`. Line 4 prints `x*` on both sides;
the field is evaluated at `cen(R̂(t_k))`, as CORA's `linReachInner` does. (10)-(12) and (17) are
stated for `x* = 0ₙ`, so `R_hom` maps `R̂(t_k) - x*` and is shifted back by `x*`. `CZ(·)` in
line 16 converts a polytope exactly [1, Sec. IV-A], so it is not written.

## Inputs
* `ops` – set operations
* `f` – autonomous field
* `Δt` – step size
* `μ` – enlargement factor
* `fuel` – bound for remainder loop
* `Rtk` – inner set at step start

## Output
* the next inner set and the time-interval set, or none

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


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
  -- 4. x*(t_k)
  let xstar := ops.cen Rtk + (Δt / 2) • f (ops.cen Rtk)
  -- 5. w ← Eq. (6)
  let w := f xstar
  -- 5. A ← Eq. (6)
  let A := ops.jac xstar
  -- 6. C ← F box ⊕ G w
  let C := ops.curv Δt A ((fun x => x - xstar) '' ops.box Rtk) w
  -- 7. R_hom ← Eq. (11)
  let Rhom := (fun x => xstar + exp (Δt • A) *ᵥ (x - xstar)) '' Rtk
  -- 7. R_con ← Eq. (12)
  let Rcon := ∫ θ in (0:ℝ)..Δt, exp ((Δt - θ) • A) *ᵥ w
  -- 8. R_aff ← Eq. (10)
  let Raff := (fun x => x + Rcon) '' Rhom
  -- 8. R̂_aff(τ₀) ← Eq. (16)
  let Raffτ := convexHull ℝ (Rtk ∪ Raff) + C
  -- 9. L ← [0ₙ, 0ₙ]
  let L := ops.zero
  -- 10.-13. the remainder `L̂`
  (NonlinearSys.innerMinkDiffRemainder ops Δt μ A xstar Raffτ L fuel).map fun Lhat =>
    -- 14. R̂_err(L̂) ← Eq. (13)
    let Rerr := ops.err Δt A Lhat
    -- 14. c
    let c := ops.cen C + ops.cen Rerr
    -- 15. R̂(t_{k+1})
    let Rtk1 := (fun x => x + (2 : ℝ) • c) '' minkowskiDiff Raff Rerr
    -- 16. R̂(τ_k)
    let Rtauk := (fun x => x + (2 : ℝ) • c) ''
      convexHull ℝ (minkowskiDiff (minkowskiDiff Rtk Rerr) C ∪ minkowskiDiff Rtk1 C)
    { xstar, w, A, C, Rcon, Raff, Lhat, Rerr, c, Rtk1, Rtauk }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
