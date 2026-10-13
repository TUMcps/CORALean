import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
import CORALean.ContSet.Interval.Float.Instances
import CORALean.Global.Jacobian

/-!
# What a float run is told about a map and its Jacobians

`computeGO` linearizes the field `f` and the output equation along the reference run, by real
Jacobians (`jacobianMat`, i.e. `fderiv`), which no float run can evaluate. A `FloatJacModel` of a
map `g : ℝⁿ × ℝᵐ → ℝʳ` is what it evaluates instead: interval extensions of `g` and of its two
Jacobian blocks `∂g/∂x`, `∂g/∂u` over a box of states and a box of inputs, as computable
functions at the scalar `𝕋`. The field is `r = n`, the output equation any `r`. `Encloses` ties it
to `g`, beside the structure rather than inside it.

Unlike `NonlinearSys.FloatModel`, whose Jacobian is a slope enclosure, the Jacobians here are
asked for pointwise: at every point of the boxes, the Jacobian itself lies in the interval
matrix, because `computeGO`'s parameters are products of Jacobians at the reference points.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m r : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- Interval extensions of a map `g` and of its Jacobian blocks `∂g/∂x`, `∂g/∂u`. -/
structure NonlinearSysDT.FloatJacModel (𝕋 : Type) (n m r : ℕ) where
  f : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Vec 𝕋 r)
  jacX : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 r n)
  jacU : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Interval (Mat 𝕋 r m)

/-- `fm` encloses `g` over every box: its value, and its Jacobian blocks at every point. A
user-supplied hypothesis, checked by no run. -/
structure NonlinearSysDT.FloatJacModel.Encloses (fm : NonlinearSysDT.FloatJacModel 𝕋 n m r)
    (g : Vec ℝ n → Vec ℝ m → Vec ℝ r) : Prop where
  f_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U, g x u ∈ construct (fm.f X U)
  jacX_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U,
      jacobianMat (fun x' => g x' u) x ∈ construct (fm.jacX X U)
  jacU_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    ∀ x ∈ construct X, ∀ u ∈ construct U,
      jacobianMat (fun u' => g x u') u ∈ construct (fm.jacU X U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
