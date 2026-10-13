import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.PointBox
import CORALean.ContSet.PolyZonotope.Float.Theorems.MonoBoxOuter
import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# `pointBox` encloses the dependent point

At every factor vector of the box, the nominal set's point lies in `pointBox`: the monomials lie
in `monoBox` (`monoBox_outer`), the generators applied to them in `Interval.mtimes`, and the
centre added in `Interval.plus`.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.pointBox_outer (pZ : PolyZonotope (Vec 𝕋 n)) (X : Interval (Vec 𝕋 pZ.p))
    {a : Vec ℝ pZ.p} (ha : a ∈ X.construct) :
    (PolyZonotope.nominal pZ).point a ∈
      (PolyZonotope.pointBox pZ X).construct := by -- --- PROOF ---
  have hm := PolyZonotope.monoBox_outer pZ.E X ha
  have hM := Interval.mtimes_outer (fun i l => pZ.G l i) (PolyZonotope.monoBox pZ.E X) ⟨_, hm, rfl⟩
  have h := Interval.plus_outer (Interval.point pZ.c) _ ⟨_, Interval.mem_point pZ.c, _, hM, rfl⟩
  -- the point, coordinate by coordinate, is the centre plus the generators' row times the monomials
  have e : (PolyZonotope.nominal pZ).point a = RealImage.realImage pZ.c
      + Matrix.mulVec (toRealMat fun i l => pZ.G l i)
        (fun l => Real.PolyZonotope.monomial pZ.E a l) := by
    funext i
    simp [Real.PolyZonotope.point, Matrix.mulVec, dotProduct, toRealMat, Finset.sum_apply,
      mul_comm]
    rfl
  rw [e, PolyZonotope.pointBox, Interval.materialise_eq]
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
