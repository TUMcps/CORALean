module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# The abstraction error from a slope enclosure

The box `L` an `AbstractionError` certificate asks for, computed in `𝕋` from the
model's slope boxes over `X × U`: with `f(x,u) - f(x✱,u✱) = J_x (x - x✱) + J_u (u - u✱)`
for some `J_x ∈ [J_x]`, `J_u ∈ [J_u]`, what is left once the affine part at
`(x✱, u✱)` is taken off is `(J_x - A)(x - x✱) + (J_u - B)(u - u✱)`, which lies in

`L = ([J_x] - A)(X - x✱) ⊕ ([J_u] - B)(U - u✱)`.

A departure from CORA's `'lin'` (`priv_abstrerr_lin`), which bounds the remainder
by the second-order Lagrange term `½ δᵀ H(ξ) δ` from an interval Hessian [1, Prop.
3.7]: `FloatModel` carries no Hessian enclosure, so this is the first-order
mean-value remainder. It is coarser: over a fixed box it is `O(‖δ‖)` in the
deviation `δ = z - z✱` from the expansion point, the Hessian's `O(‖δ‖²)`; only
the width of `[J] - A`, which shrinks with the box, makes up part of the gap.
`abstrErrLin` stays the real layer's Hessian box; `FloatHessModel.hessRemainder` is its
float run, where the model carries one.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `([J_x] - A)(X - xs) ⊕ ([J_u] - B)(U - us)`, the slope boxes taken over
`X × U`. -/
def NonlinearSys.FloatModel.slopeRemainder (fm : NonlinearSys.FloatModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (X : Interval (Vec 𝕋 n))
    (U : Interval (Vec 𝕋 m)) : Interval (Vec 𝕋 n) :=
  let ΔJx := Interval.matPlus (fm.jacX X U) (Interval.point fun i j => neg (A i j))  -- [J_x] - A
  let ΔJu := Interval.matPlus (fm.jacU X U) (Interval.point fun i j => neg (B i j))  -- [J_u] - B
  let dx := Interval.plus X (Interval.point fun i => neg (xs i))                     -- X - x✱
  let du := Interval.plus U (Interval.point fun i => neg (us i))                     -- U - u✱
  Interval.plus (Interval.mtimesIntervalMat ΔJx dx) (Interval.mtimesIntervalMat ΔJu du)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
