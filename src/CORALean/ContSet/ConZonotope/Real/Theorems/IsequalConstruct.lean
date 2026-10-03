import CORALean.ContSet.ConZonotope.Real.Operations.Isequal

/-!
# Constrained zonotopes passing `isequal` denote the same set

Sound, not exact: `isequal` compares the representation, and different data can denote one set.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isequal_construct {Z S : ConZonotope α} (h : Z.isequal S) :
    Z.construct = S.construct := by -- --- PROOF ---
  obtain ⟨e, hc, hG, hP⟩ := h
  obtain ⟨h₁, c₁, G₁, P₁⟩ := Z
  obtain ⟨h₂, c₂, G₂, P₂⟩ := S
  simp only at e hc hG hP
  subst e hc
  have : G₁ = G₂ := funext fun j => hG j
  subst this
  cases eq_of_heq hP
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
