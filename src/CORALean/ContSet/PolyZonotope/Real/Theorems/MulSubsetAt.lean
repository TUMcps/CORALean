import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint

/-!
# `mul`'s subset at `B` is the product of the two points, ranged together

`bilin_subsetAt` at the entrywise product, read off `mul_point` rather than
through `bilin` itself, since `mul` and `bilin Entrywise.hadamardLin` agree at
every point but are not the same operation term for term.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mul`'s subset at `B`, read off `mul_point`: the product of the two points,
one shared factor vector driving both. -/
theorem PolyZonotope.mul_subsetAt (pZ₁ pZ₂ : PolyZonotope (Vec ℝ n)) (hp : pZ₁.p = pZ₂.p)
    (B : Set (Fin pZ₁.p → ℝ)) :
    (pZ₁.mul pZ₂ hp).subsetAt B
      = (fun a => pZ₁.point a * pZ₂.point fun k => a (Fin.cast hp.symm k)) '' B := by
  show (pZ₁.mul pZ₂ hp).point '' B = _
  exact Set.image_congr fun a _ => PolyZonotope.mul_point pZ₁ pZ₂ hp a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
