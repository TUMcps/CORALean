import CORALean.ContSet.Ellipsoid.Float.Operations.OfPoint
import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Interval.Float.Theorems.OriginExact

/-!
# `Ellipsoid.ofPoint` is exactly the point

The nominal part is the exact layer's point ellipsoid at the stored point read as reals, and the
error box is the origin box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.ofPoint_exact (p : Vec 𝕋 n) :
    (Ellipsoid.ofPoint p).construct = {toRealVec p} := by -- --- PROOF ---
  have h : InflatedContSet.nominal (Ellipsoid.ofPoint p)
      = Real.Ellipsoid.ofPoint (toRealVec p) := by
    unfold Real.Ellipsoid.ofPoint
    show (⟨0, toRealVec p, toRealMat (fun _ j => j.elim0)⟩ : Real.Ellipsoid n) = ⟨0, _, 0⟩
    congr 1
    funext i j
    exact j.elim0
  have hN : InflatedContSet.nominalSet (Ellipsoid.ofPoint p) = {toRealVec p} := by
    unfold InflatedContSet.nominalSet
    rw [h]
    exact Set.ext fun x =>
      (Real.Ellipsoid.mem_ofPoint_iff (toRealVec p) x).trans Set.mem_singleton_iff.symm
  have hE : (Ellipsoid.ofPoint p).err.construct = {0} := Interval.origin_exact n
  show InflatedContSet.nominalSet (Ellipsoid.ofPoint p) + (Ellipsoid.ofPoint p).err.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
