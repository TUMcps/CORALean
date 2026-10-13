import CORALean.ContSet.VPolytope.Float.Operations.Origin
import CORALean.ContSet.Interval.Float.Theorems.OriginExact
import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint
import CORALean.ContSet.VPolytope.Real.Operations.Point

/-!
# `VPolytope.origin` denotes exactly the origin, over a floating-point scalar

The nominal vertex list is the exact layer's single point `0`, and the error box is the point
`0` as well.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.origin_exact (n : ℕ) :
    (VPolytope.origin n : VPolytope (Vec 𝕋 n)).construct = {0} := by -- --- PROOF ---
  -- the stored zero reads as ℝ's
  have h : InflatedContSet.nominal (VPolytope.origin n : VPolytope (Vec 𝕋 n))
      = Real.VPolytope.point (0 : Vec ℝ n) := by
    rw [VPolytope.nominal_eq]
    show (⟨1, fun _ i => toReal (zero : 𝕋)⟩ : Real.VPolytope (Vec ℝ n)) = ⟨1, fun _ => 0⟩
    congr 1
    funext l i
    exact toReal_zero
  have hN : InflatedContSet.nominalSet (VPolytope.origin n : VPolytope (Vec 𝕋 n)) = {0} := by
    unfold InflatedContSet.nominalSet
    rw [h]
    exact Real.VPolytope.construct_point 0
  have hE : (VPolytope.origin n : VPolytope (Vec 𝕋 n)).E.construct = {0} :=
    Interval.origin_exact n
  show InflatedContSet.nominalSet (VPolytope.origin n : VPolytope (Vec 𝕋 n))
      + (VPolytope.origin n : VPolytope (Vec 𝕋 n)).E.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
