import CORALean.ContSet.Ellipsoid.Float.Operations.Origin
import CORALean.ContSet.Ellipsoid.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Interval.Float.Theorems.OriginExact

/-!
# `Ellipsoid.origin` is exactly the origin

`zero` reads as `0`, so the nominal part is the exact layer's point ellipsoid at the
origin, and the error box is the origin box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.origin_exact (n : ℕ) :
    (Ellipsoid.origin n : Ellipsoid 𝕋 n).construct = {0} := by -- --- PROOF ---
  have hc : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
  have h : InflatedContSet.nominal (Ellipsoid.origin n : Ellipsoid 𝕋 n)
      = Real.Ellipsoid.ofPoint (0 : Vec ℝ n) := by
    unfold Real.Ellipsoid.ofPoint
    show (⟨0, toRealVec (fun _ : Fin n => (zero : 𝕋)), toRealMat (fun _ j => j.elim0)⟩ :
        Real.Ellipsoid n) = ⟨0, 0, 0⟩
    congr 1
    funext i j
    exact j.elim0
  have hN : InflatedContSet.nominalSet (Ellipsoid.origin n : Ellipsoid 𝕋 n) = {0} := by
    unfold InflatedContSet.nominalSet
    rw [h]
    exact Set.ext fun x =>
      (Real.Ellipsoid.mem_ofPoint_iff (0 : Vec ℝ n) x).trans Set.mem_singleton_iff.symm
  have hE : (Ellipsoid.origin n : Ellipsoid 𝕋 n).err.construct = {0} :=
    Interval.origin_exact n
  show InflatedContSet.nominalSet (Ellipsoid.origin n : Ellipsoid 𝕋 n)
      + (Ellipsoid.origin n : Ellipsoid 𝕋 n).err.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
