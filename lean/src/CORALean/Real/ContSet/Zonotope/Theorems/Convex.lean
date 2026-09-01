import CORALean.Real.ContSet.Zonotope.Zonotope

/-!
# A zonotope is convex

The affine image of a cube, so a weighted average of two points is the image of
the same average of their coefficients — which is still a coefficient, `[-1,1]`
being convex.

What an integral valued in the set needs. Unlike `linComb`, which is stated so a
non-convex representation can make it too, this is a property only some
representations have.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem Zonotope.convex_construct (Z : Zonotope n) : Convex ℝ Z.construct := by
  rintro x ⟨β₁, hβ₁, hx⟩ y ⟨β₂, hβ₂, hy⟩ a b ha hb hab
  refine ⟨fun j => a * β₁ j + b * β₂ j, fun j => ?_, fun i => ?_⟩
  · refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    nlinarith [hβ₁ j, hβ₂ j, abs_nonneg (β₁ j), abs_nonneg (β₂ j)]
  · show a * x i + b * y i = _
    rw [hx i, hy i, Finset.sum_congr rfl (fun j _ => by ring : ∀ j ∈ Finset.univ,
        Z.G i j * (a * β₁ j + b * β₂ j)
          = a * (Z.G i j * β₁ j) + b * (Z.G i j * β₂ j)),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination Z.c i * hab

end CORALean.Real
