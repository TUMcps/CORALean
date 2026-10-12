import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Interval.Float.Instances

/-!
# What a float run is told about a differential-algebraic system

`NonlinDASys` stores `f` and `g` over ℝ, which no float run can evaluate. A `FloatModel` is what
it evaluates instead: interval extensions of `f` and `g` and of the four Jacobian blocks CORA's
`jacobian` returns, `A = ∂f/∂x`, `C = ∂f/∂y`, `D = ∂g/∂x`, `F = ∂g/∂y`, over a box `X × Y × U`,
as computable functions at the scalar `𝕋`. `Encloses` ties them to `sys`, beside the structure,
as `NonlinearSys.FloatModel.Encloses` does for an ordinary system.

The blocks are asked for as *slope* enclosures, at a common input: any two states of the box
differ under `f` (under `g`) by some pair `A, C` (`D, F`) in the boxes applied to their
difference. The mean value theorem gives this for interval Jacobians over a convex box, and for a
polynomial system it is algebra.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- Interval extensions of `f`, `g` and of the Jacobian blocks `A, C, D, F`, each over a box of
differential states `X`, of algebraic states `Y` and of inputs `U`. -/
structure NonlinDASys.FloatModel (𝕋 : Type) (n p m : ℕ) where
  f : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 n)
  g : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 p)
  jacA : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 n n)
  jacC : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 n p)
  jacD : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 p n)
  jacF : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 p p)

/-- `fm` encloses `sys` over every box: the values of `f` and `g`, and their slopes between any two
states of the box at a common input. A user-supplied hypothesis, checked by no run. -/
structure NonlinDASys.FloatModel.Encloses (fm : NonlinDASys.FloatModel 𝕋 n p m)
    (sys : NonlinDASys n p m) : Prop where
  f_mem (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ y ∈ Y.construct, ∀ u ∈ U.construct, sys.f x y u ∈ (fm.f X Y U).construct
  g_mem (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ y ∈ Y.construct, ∀ u ∈ U.construct, sys.g x y u ∈ (fm.g X Y U).construct
  slope_f (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ x' ∈ X.construct, ∀ y ∈ Y.construct, ∀ y' ∈ Y.construct,
      ∀ u ∈ U.construct, ∃ A ∈ (fm.jacA X Y U).construct, ∃ C ∈ (fm.jacC X Y U).construct,
        sys.f x y u - sys.f x' y' u = A *ᵥ (x - x') + C *ᵥ (y - y')
  slope_g (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ x' ∈ X.construct, ∀ y ∈ Y.construct, ∀ y' ∈ Y.construct,
      ∀ u ∈ U.construct, ∃ D ∈ (fm.jacD X Y U).construct, ∃ F ∈ (fm.jacF X Y U).construct,
        sys.g x y u - sys.g x' y' u = D *ᵥ (x - x') + F *ᵥ (y - y')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
