import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# What a float run is told about the field's second derivative

A `FloatModel` with one more interval extension: of the Hessian of each component
`fᵢ` in the stacked `z = (x, u)`, over a box `X × U` — CORA's `sys.hessian(totalInt_x,
totalInt_u)`. The `FloatModel` remainder is first order; this is what CORA's `'lin'`
bound (`priv_abstrerr_lin`) and the polynomialization [1] spend instead.

`Encloses` asks the second-order expansion with a Lagrange remainder, read so that
no derivative of `f` appears: at any expansion point `z✱` of the box, the Jacobian
there lies in the model's box at the point, and what is left of `f(z)` is
`½ (z - z✱)ᵀ Hᵢ (z - z✱)` per component for some `Hᵢ` in the Hessian box. Taylor's
theorem on the segment gives it for a `C²` field over a convex box, and for a
polynomial field it is algebra.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A `FloatModel` with interval extensions of the Hessians `∂²fᵢ/∂z²`, `z = (x, u)`,
over a box of states `X` and a box of inputs `U`. -/
structure NonlinearSys.FloatHessModel (𝕋 : Type) (n m : ℕ) extends NonlinearSys.FloatModel 𝕋 n m
    where
  hess : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 m) → Fin n → Interval (Mat 𝕋 (n + m) (n + m))

/-- `fm` encloses `sys` as a `FloatModel` does, and over every box its Jacobian at
a point and its Hessian box expand `f` to second order about that point. -/
structure NonlinearSys.FloatHessModel.Encloses (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (sys : NonlinearSys n m) : Prop extends NonlinearSys.FloatModel.Encloses fm.toFloatModel sys
    where
  taylor_mem (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) :
    toRealVec xs ∈ X.construct → toRealVec us ∈ U.construct →
    ∀ x ∈ X.construct, ∀ u ∈ U.construct,
      ∃ Jx ∈ (fm.jacX (Interval.point xs) (Interval.point us)).construct,
      ∃ Ju ∈ (fm.jacU (Interval.point xs) (Interval.point us)).construct,
      ∃ H : Fin n → Mat ℝ (n + m) (n + m), (∀ i, H i ∈ (fm.hess X U i).construct) ∧
        sys.f x u - sys.f (toRealVec xs) (toRealVec us)
          = Jx *ᵥ (x - toRealVec xs) + Ju *ᵥ (u - toRealVec us)
            + fun i => Fin.append (x - toRealVec xs) (u - toRealVec us)
                ⬝ᵥ (H i *ᵥ Fin.append (x - toRealVec xs) (u - toRealVec us)) / 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
