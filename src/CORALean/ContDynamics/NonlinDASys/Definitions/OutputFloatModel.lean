module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.Global.Jacobian

@[expose] public section

/-!
# What a float run is told about the output equation

`NonlinDASys` stores the output equation `h` over ℝ, which no float run can evaluate. An
`OutputFloatModel` is what it evaluates instead: interval extensions of `h` and of its three
Jacobian blocks `∂h/∂x`, `∂h/∂y`, `∂h/∂u` over boxes of states, algebraic variables and inputs,
as computable functions at the scalar `𝕋`. `Encloses` ties it to `h`: the value and every
Jacobian at every point of the boxes. The Jacobians are asked for pointwise, as
`NonlinParamSys.FloatModel` does.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- Interval extensions of the output equation and of its Jacobian blocks over boxes of
differential states, algebraic states and inputs. -/
structure NonlinDASys.OutputFloatModel (𝕋 : Type) (n p m q : ℕ) where
  h : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 q)
  jacX : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 q n)
  jacY : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 q p)
  jacU : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 p) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 q m)

/-- `om` encloses `sys.h` over every box: its value, and its Jacobian in each argument at every
point of the boxes. A user-supplied hypothesis, checked by no run. -/
structure NonlinDASys.OutputFloatModel.Encloses (sys : NonlinDASys n p m)
    (om : NonlinDASys.OutputFloatModel 𝕋 n p m sys.q) : Prop where
  h_mem (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ y ∈ Y.construct, ∀ u ∈ U.construct,
      sys.h x y u ∈ (om.h X Y U).construct
  jacX_mem (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ y ∈ Y.construct, ∀ u ∈ U.construct,
      jacobianMat (fun x' => sys.h x' y u) x ∈ (om.jacX X Y U).construct
  jacY_mem (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ y ∈ Y.construct, ∀ u ∈ U.construct,
      jacobianMat (fun y' => sys.h x y' u) y ∈ (om.jacY X Y U).construct
  jacU_mem (X : Interval (Vec 𝕋 n)) (Y : Interval (Vec 𝕋 p)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ X.construct, ∀ y ∈ Y.construct, ∀ u ∈ U.construct,
      jacobianMat (fun u' => sys.h x y u') u ∈ (om.jacU X Y U).construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
