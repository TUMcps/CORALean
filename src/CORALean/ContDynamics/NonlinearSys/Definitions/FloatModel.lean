import CORALean.ContDynamics.NonlinearSys.NonlinearSys
import CORALean.ContSet.Interval.Float.Instances

/-!
# What a float run is told about the field

`NonlinearSys` stores `f` over ℝ, which no float run can evaluate. A `FloatModel`
is what it evaluates instead: interval extensions of `f` and of its two Jacobian
blocks over a box `X × U`, as computable functions at the scalar `𝕋`. `Encloses`
ties them to `f`, beside the class rather than inside it, so the real class and
every certificate built on it stay unchanged and a float run never holds `f`.

The Jacobian is asked for as a *slope* enclosure: any two points of the box differ
under `f` by some matrix pair in the boxes applied to their difference. That is
all the run spends, it is what the mean value theorem gives for an interval
Jacobian over a convex box (`Encloses.of_hasFDerivAt`), and for a polynomial field
it is plain algebra. The price is the remainder: `slopeRemainder` is first order,
`O(‖δ‖)` in the deviation from the expansion point where CORA's Hessian bound
[1, Prop. 3.7] is `O(‖δ‖²)`; a Hessian enclosure would be a further field.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
points of the box. -/
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
