module

public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `Zonotope.point` denotes exactly the point it stores

The nominal part is the exact layer's point zonotope at the stored point read
into ℝ, and the error box is the origin box, so the sum is `{x} + {0}`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_point (c : Vec 𝕋 n) :
    (Zonotope.point c).construct = {toRealVec c} := by -- --- PROOF ---
  have h : InflatedContSet.nominal (Zonotope.point c) = Real.Zonotope.ofPoint (toRealVec c) := by
    unfold Zonotope.point Real.Zonotope.ofPoint
    show (⟨0, toRealVec c, _⟩ : Real.Zonotope (Vec ℝ n)) = ⟨0, toRealVec c, _⟩
    congr 1
    funext j
    exact j.elim0
  have hN : InflatedContSet.nominalSet (Zonotope.point c) = {toRealVec c} := by
    unfold InflatedContSet.nominalSet
    rw [h]
    exact Set.ext fun x =>
      (Real.Zonotope.mem_ofPoint_iff (toRealVec c) x).trans Set.mem_singleton_iff.symm
  have hE : (Zonotope.point c).E.construct = {0} := Interval.origin_exact n
  show InflatedContSet.nominalSet (Zonotope.point c) + (Zonotope.point c).E.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
