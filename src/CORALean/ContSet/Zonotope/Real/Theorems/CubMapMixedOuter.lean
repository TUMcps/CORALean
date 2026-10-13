module

public import CORALean.ContSet.Zonotope.Real.Theorems.CubMapMixedCoeff

@[expose] public section

/-!
# The mixed cubic map of zonotopes is enclosed by `Zonotope.cubMapMixed`

CORA's `@zonotope/cubMap` for three zonotopes:
`{ (x₁ᵀ T x₂) * x₃ | x₁ ∈ Z₁, x₂ ∈ Z₂, x₃ ∈ Z₃ } ⊆ Z₁.cubMapMixed T Z₂ Z₃`. Outer only: the three
families of factors are independent, but the generators `β₃ⱼ β₂ᵦ β₁ₐ` are products of them, tied to
each other. The coefficients are `Zonotope.cubMapMixed_coeff`.
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

/-- `{ (x₁ᵀ T x₂) * x₃ | xᵢ ∈ Zᵢ } ⊆ cubMapMixed`. -/
theorem Zonotope.cubMapMixed_outer (T : Fin m → Fin n → Mat ℝ n n)
    (Z₁ Z₂ Z₃ : Zonotope (Vec ℝ n)) :
    (fun x : Vec ℝ n × Vec ℝ n × Vec ℝ n => PolyZonotope.cubEvalMixed T x.1 x.2.1 x.2.2)
        '' (Z₁.construct ×ˢ Z₂.construct ×ˢ Z₃.construct)
      ⊆ (Z₁.cubMapMixed T Z₂ Z₃).construct := by
  rintro _ ⟨⟨x₁, x₂, x₃⟩, ⟨⟨p₁, hp₁, rfl⟩, ⟨p₂, hp₂, rfl⟩, ⟨p₃, hp₃, rfl⟩⟩, rfl⟩
  obtain ⟨γ, hγ, -, -, -, hx⟩ := Zonotope.cubMapMixed_coeff T Z₁ Z₂ Z₃ p₁ p₂ p₃ hp₁ hp₂ hp₃
  exact ⟨γ, hγ, hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
