module

public import CORALean.ContSet.Polygon.Float.Operations.Minus
public import CORALean.ContSet.Polygon.Float.Theorems.Basic
public import CORALean.ContSet.VPolytope.Float.Theorems.EnclosePointsExact

@[expose] public section

/-!
# `Polygon.minus` encloses the translate

The one-piece polygon holds `-p` read as reals (`enclosePoints_exact`, `neg` exact), so every
`x - p` is a sum `plus_outer` takes into the result. Outer, as the sum is.

## Inputs
* `P` – polygon
* `p` – point of length `2`

## Hypotheses
* none

## Conclusion
* `Polygon.minus` encloses the translate
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.minus_outer (P : Polygon 𝕋) (p : Vec 𝕋 2) : -- --- CONCL ---
    (fun x => x - toRealVec p) '' ContSet.construct P ⊆
      ContSet.construct (Polygon.minus P p) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  -- the point `-p`, read as reals, is in the one-piece polygon
  have hpt : -toRealVec p ∈ ContSet.construct
      (Polygon.ofPieces [VPolytope.enclosePoints fun (_ : Fin 1) i => neg (p i)]) := by
    refine SetUnion.mem_construct.mpr ⟨_, List.mem_singleton_self _, ?_⟩
    show _ ∈ VPolytope.construct _
    rw [VPolytope.enclosePoints_exact]
    refine subset_convexHull ℝ _ ⟨0, ?_⟩
    funext i
    simp [toRealVec, toReal_neg]
  refine Polygon.plus_outer _ _ ⟨x, hx, _, hpt, ?_⟩
  show x + -toRealVec p = x - toRealVec p
  rw [sub_eq_add_neg]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
