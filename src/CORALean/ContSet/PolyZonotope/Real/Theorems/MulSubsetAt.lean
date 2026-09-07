import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint

/-!
# `mul`'s subset at `B` is the product of the two points, ranged together

`bilin_subsetAt` at the entrywise product, read off `mul_point` rather than
through `bilin` itself, since `mul` and `bilin Entrywise.hadamardLin` agree at
every point but are not the same operation term for term.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mul`'s subset at `B`, read off `mul_point`: the product of the two points,
one shared factor vector driving both. -/
theorem PolyZonotope.mul_subsetAt (S₁ S₂ : PolyZonotope (Vec ℝ n)) (hp : S₁.p = S₂.p)
    (B : Set (Fin S₁.p → ℝ)) :
    (S₁.mul S₂ hp).subsetAt B
      = (fun a => S₁.point a * S₂.point fun k => a (Fin.cast hp.symm k)) '' B := by
  show (S₁.mul S₂ hp).point '' B = _
  exact Set.image_congr fun a _ => PolyZonotope.mul_point S₁ S₂ hp a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
