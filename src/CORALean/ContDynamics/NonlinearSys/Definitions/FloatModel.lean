module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# What a float run is told about the field

`NonlinearSys` stores `f` over ℝ, which no float run can evaluate. A `FloatModel` is what it
evaluates instead: interval extensions of `f` and of its two Jacobian blocks over a box `X × U`,
as computable functions at the scalar `𝕋`. `Encloses` ties them to `f`, beside the class rather
than inside it. The Jacobian is asked for as a *slope* enclosure: any two points of the box
differ under `f` by some matrix pair in the boxes applied to their difference, which the mean
value theorem gives for an interval Jacobian over a convex box (`Encloses.of_hasFDerivAt`). The
price is the remainder: `slopeRemainder` is `O(‖δ‖)` in the deviation from the expansion point
where CORA's Hessian bound [1, Prop. 1] is `O(‖δ‖²)`; `FloatHessModel` adds the Hessian.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". 2008 47th IEEE Conference on Decision
      and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- Interval extensions of a field `f` and of its Jacobian blocks `∂f/∂x`,
`∂f/∂u`, each over a box of states `X` and a box of inputs `U`. -/
structure NonlinearSys.FloatModel (𝕋 : Type) (n m : ℕ) where
  f : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 n)
  jacX : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 n n)
  jacU : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 n m)

/-- `fm` encloses `sys` over every box: its value, and the slope between any two
points of the box. A user-supplied hypothesis, checked by no run: trusted unless proved, as
`vdpModel_encloses` (`Examples/RunnableFloat.lean`) does. See the README's trust base. -/
structure NonlinearSys.FloatModel.Encloses (fm : NonlinearSys.FloatModel 𝕋 n m)
    (sys : NonlinearSys n m) : Prop where
  f_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ u ∈ U.construct, sys.f x u ∈ (fm.f X U).construct
  slope_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ x' ∈ X.construct, ∀ u ∈ U.construct, ∀ u' ∈ U.construct,
      ∃ Jx ∈ (fm.jacX X U).construct, ∃ Ju ∈ (fm.jacU X U).construct,
        sys.f x u - sys.f x' u' = Jx *ᵥ (x - x') + Ju *ᵥ (u - u')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
