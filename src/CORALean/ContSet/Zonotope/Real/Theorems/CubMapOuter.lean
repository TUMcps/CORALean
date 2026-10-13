import CORALean.ContSet.Zonotope.Real.Theorems.CubMapCoeff

/-!
# The cubic map of a zonotope is enclosed by `Zonotope.cubMap`

CORA's `@zonotope/cubMap`: `{ (xᵀ T x) * x | x ∈ Z } ⊆ Z.cubMap T`. Outer only: the monomials
`β_k β_j β_c` of the factors are tied to each other, and a zonotope frees them. The coefficients
are `Zonotope.cubMap_coeff`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `{ (xᵀ T x) * x | x ∈ Z } ⊆ Z.cubMap T`. -/
theorem Zonotope.cubMap_outer (T : Fin m → Fin n → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    PolyZonotope.cubEval T '' Z.construct ⊆ (Z.cubMap T).construct := by
  rintro _ ⟨x, ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨γ, hγ, -, hx⟩ := Zonotope.cubMap_coeff T Z p hp
  exact ⟨γ, hγ, hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
