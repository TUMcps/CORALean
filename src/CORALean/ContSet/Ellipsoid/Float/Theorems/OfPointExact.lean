module

public import CORALean.ContSet.Ellipsoid.Float.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq

@[expose] public section

/-!
# `Ellipsoid.ofPoint` is exactly the point

The nominal part is the exact layer's point ellipsoid at the stored point read as reals, and the
error box is the origin box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.ofPoint_exact (p : Vec 𝕋 n) :
    (Ellipsoid.ofPoint p).construct = {toRealVec p} := by -- --- PROOF ---
  have hQ : toRealMat (fun _ _ : Fin n => (zero : 𝕋)) = 0 :=
    funext fun _ => funext fun _ => toReal_zero
  have h : (InflatedContSet.nominal (Ellipsoid.ofPoint p)).ellipsoid
      = Real.Ellipsoid.ofPoint (toRealVec p) := by
    show Real.Ellipsoid.ofShape (toRealMat (fun _ _ : Fin n => (zero : 𝕋))) (toRealVec p) = _
    rw [hQ, Real.Ellipsoid.ofShape_eq .zero]
    rfl
  have hN : InflatedContSet.nominalSet (Ellipsoid.ofPoint p) = {toRealVec p} := by
    show (InflatedContSet.nominal (Ellipsoid.ofPoint p)).ellipsoid.construct = _
    rw [h]
    exact Set.ext fun x =>
      (Real.Ellipsoid.mem_ofPoint_iff (toRealVec p) x).trans Set.mem_singleton_iff.symm
  have hE : (Ellipsoid.ofPoint p).I_error.construct = {0} := Interval.origin_exact n
  show InflatedContSet.nominalSet (Ellipsoid.ofPoint p) + (Ellipsoid.ofPoint p).I_error.construct =
      _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
