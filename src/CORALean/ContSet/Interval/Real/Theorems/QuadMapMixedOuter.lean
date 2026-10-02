import CORALean.ContSet.Interval.Real.Operations.QuadMapMixed
import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter

/-!
# `Interval.quadMapMixed` encloses the bilinear map over two boxes

CORA bounds `{x₁ᵀQₖx₂ | x₁ ∈ I₁, x₂ ∈ I₂}` through the boxes' zonotopes, so the statement is an
outer one: a zonotope's coefficients are free, and `Zonotope.bilin` only over-approximates the
products of two of them (`Zonotope.bilin_outer`).
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.quadMapMixed_outer (Q : Fin m → Mat ℝ n n) (I₁ I₂ : Interval (Vec ℝ n)) :
    (fun p : Vec ℝ n × Vec ℝ n => PolyZonotope.quadBilin Q p.1 p.2) ''
        (I₁.construct ×ˢ I₂.construct) ⊆ (I₁.quadMapMixed Q I₂).construct := by
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  refine Zonotope.interval_contains _ (Zonotope.bilin_outer (PolyZonotope.quadBilin Q) _ _ ?_)
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
  exact ⟨x, I₁.zonotope_contains hx, y, I₂.zonotope_contains hy, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
