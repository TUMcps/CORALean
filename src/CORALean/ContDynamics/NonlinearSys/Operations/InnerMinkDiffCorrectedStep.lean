module

public import CORALean.ContDynamics.NonlinearSys.Definitions.InnerMinkDiffState
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffRemainder
public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanGenOpNorm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# `innerMinkDiffCorrectedStep`, one step of the inner algorithm with lines 15 and 16 repaired

Lines 3-16 of [1, Alg. 1] as `innerMinkDiffStep` computes them, with two lines repaired. Line 15
shifts `R_aff ⊖ R̂_err` by `2 cen(R̂_err)`, `Prop. 1`'s shift, not by line 14's `2c`, which is
unsound once `cen(C) ≠ 0`. Line 16 erodes the hull by the Euclidean ball `B_µ` of [2],
`µ = √h‖(e^{AΔt} - I)G‖₂`, `G` the `h` generators of `R̂(t_k)`, which `zono` supplies as the
zonotope of `R̂(t_k)`'s center and generators; without it the hull holds points no run reaches
(`innerMinkDiff_timeInterval_counterexample`). `none` when the remainder loop runs out of `fuel`.

## Inputs
* `ops` – set operations
* `zono` – zonotope of a set's center and generators
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
* [2] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-16 of [1, Alg. 1] from `R̂(t_k)`, line 15 shifted by `2 cen(R̂_err)` and line 16's hull
eroded by `B_µ` of [2]; `none` once the remainder loop has run `fuel` passes. -/
noncomputable def NonlinearSys.innerMinkDiffCorrectedStep (ops : NonlinearSys.InnerMinkDiffOps n 𝓛)
    (zono : Set (Vec ℝ n) → Real.Zonotope (Vec ℝ n)) (f : Vec ℝ n → Vec ℝ n) (Δt μ : ℝ)
    (fuel : ℕ) (Rtk : Set (Vec ℝ n)) : Option (NonlinearSys.InnerMinkDiffState n 𝓛) :=
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
    -- 15. R̂(t_{k+1}), shifted by `Prop. 1`'s `2 cen(R̂_err)`
    let Rtk1 := (fun x => x + (2 : ℝ) • ops.cen Rerr) '' minkowskiDiff Raff Rerr
    -- 16. ⟨c, G⟩, the center and `h` generators of R̂(t_k)
    let Z := zono Rtk
    -- 16. µ ← √h ‖(e^{AΔt} - I)G‖₂ of [2]
    let μB := Real.sqrt Z.h * genOpNorm₂ fun j => (exp (Δt • A) - 1) *ᵥ Z.G j
    -- 16. R̂(τ_k), the hull eroded by B_µ
    let Rtauk := (fun x => x + (2 : ℝ) • c) '' minkowskiDiff
      (convexHull ℝ (minkowskiDiff (minkowskiDiff Rtk Rerr) C ∪ minkowskiDiff Rtk1 C))
      {y | ‖y‖₂ ≤ μB}
    { xstar, w, A, C, Rcon, Raff, Lhat, Rerr, c, Rtk1, Rtauk }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
