import CORALean.ContSet.Interval.Real.Operations.QuadMap
import CORALean.ContSet.Interval.Real.Theorems.QuadMapMixedOuter

/-!
# `Interval.quadMap` encloses the quadratic map over the box

CORA bounds `{(xᵀQ₁x, …, xᵀQₘx) | x ∈ I}` through the box's zonotope: the case `I₁ = I₂` of
`Interval.quadMapMixed_outer`, an outer statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.quadMap_outer (Q : Fin m → Mat ℝ n n) (I : Interval (Vec ℝ n)) :
    (fun x : Vec ℝ n => PolyZonotope.quadBilin Q x x) '' I.construct
      ⊆ (I.quadMap Q).construct := by
  rintro _ ⟨x, hx, rfl⟩
  exact I.quadMapMixed_outer Q I ⟨⟨x, x⟩, ⟨hx, hx⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
