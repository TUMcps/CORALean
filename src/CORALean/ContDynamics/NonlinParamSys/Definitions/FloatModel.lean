module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.Global.Jacobian

@[expose] public section

/-!
# What a float run is told about a parametric field

`NonlinParamSys` stores `f` over ℝ, which no float run can evaluate. A `FloatModel` is what it
evaluates instead: interval extensions of `f` and of its two Jacobian blocks `∂f/∂x`, `∂f/∂u`
over a box of states, a box of inputs and a box of parameters, as computable functions at the
scalar `𝕋`. `Encloses` ties it to `f`, beside the structure rather than inside it.

The Jacobians are asked for pointwise, as `NonlinearSysDT.FloatJacModel` does: at every point of
the three boxes, the Jacobian at that parameter lies in the interval matrix. Unlike CORA's
`linearize`, which builds its zonotopes from `f(x, u, 0)` and the unit vectors and is right only
for a `f` affine in `p` (`NonlinParamSys.linearize_f_counterexample`), an enclosure over the
parameter box asks nothing of `f` but the enclosure itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- Interval extensions of a field `f` and of its Jacobian blocks over states, inputs and
parameters. -/
structure NonlinParamSys.FloatModel (𝕋 : Type) (n m q : ℕ) where
  f : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 q) → Interval (Vec 𝕋 n)
  jacX : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 q) → Interval (Mat 𝕋 n n)
  jacU : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 q) → Interval (Mat 𝕋 n m)

/-- `fm` encloses `sys` over every box: its value, and its Jacobian blocks at every point and
every parameter. A user-supplied hypothesis, checked by no run. -/
structure NonlinParamSys.FloatModel.Encloses (fm : NonlinParamSys.FloatModel 𝕋 n m q)
    (sys : NonlinParamSys n m q) : Prop where
  f_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) (P : Interval (Vec 𝕋 q)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U, ∀ p ∈ construct P,
      sys.f x u p ∈ construct (fm.f X U P)
  jacX_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) (P : Interval (Vec 𝕋 q)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U, ∀ p ∈ construct P,
      jacobianMat (fun x' => sys.f x' u p) x ∈ construct (fm.jacX X U P)
  jacU_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) (P : Interval (Vec 𝕋 q)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U, ∀ p ∈ construct P,
      jacobianMat (fun u' => sys.f x u' p) u ∈ construct (fm.jacU X U P)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
