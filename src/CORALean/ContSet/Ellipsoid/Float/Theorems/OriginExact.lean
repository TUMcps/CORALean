module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Origin
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq

@[expose] public section

/-!
# `Ellipsoid.origin` is exactly the origin

`zero` reads as `0`, so the nominal part is the exact layer's point ellipsoid at the
origin, the zero shape being positive semi-definite, and the error box is the origin box.

## Inputs
* `n` – dimension

## Hypotheses
* none

## Conclusion
* the result is exactly the origin
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.origin_exact (n : ℕ) :
    (Ellipsoid.origin n : Ellipsoid 𝕋 n).construct = {0} := by -- --- PROOF ---
  have hc : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
  have hQ : toRealMat (fun _ _ : Fin n => (zero : 𝕋)) = 0 :=
    funext fun _ => funext fun _ => toReal_zero
  have h : (InflatedContSet.nominal (Ellipsoid.origin n : Ellipsoid 𝕋 n)).ellipsoid
      = Real.Ellipsoid.ofPoint (0 : Vec ℝ n) := by
    show Real.Ellipsoid.ofShape (toRealMat (fun _ _ : Fin n => (zero : 𝕋)))
      (toRealVec (fun _ : Fin n => (zero : 𝕋))) = _
    rw [hQ, hc, Real.Ellipsoid.ofShape_eq .zero]
    rfl
  have hN : InflatedContSet.nominalSet (Ellipsoid.origin n : Ellipsoid 𝕋 n) = {0} := by
    show (InflatedContSet.nominal (Ellipsoid.origin n : Ellipsoid 𝕋 n)).ellipsoid.construct = _
    rw [h]
    exact Set.ext fun x =>
      (Real.Ellipsoid.mem_ofPoint_iff (0 : Vec ℝ n) x).trans Set.mem_singleton_iff.symm
  have hE : (Ellipsoid.origin n : Ellipsoid 𝕋 n).I_error.construct = {0} :=
    Interval.origin_exact n
  show InflatedContSet.nominalSet (Ellipsoid.origin n : Ellipsoid 𝕋 n)
      + (Ellipsoid.origin n : Ellipsoid 𝕋 n).I_error.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
