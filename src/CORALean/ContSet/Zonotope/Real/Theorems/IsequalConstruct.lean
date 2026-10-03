import CORALean.ContSet.Zonotope.Real.Operations.Isequal

/-!
# Zonotopes passing `isequal` denote the same set

Sound, not exact: `isequal` compares the representation, and different generator lists can
generate the same zonotope.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isequal_construct {Z S : Zonotope α} (h : Z.isequal S) :
    Z.construct = S.construct := by -- --- PROOF ---
  obtain ⟨e, hc, hG⟩ := h
  obtain ⟨h₁, c₁, G₁⟩ := Z
  obtain ⟨h₂, c₂, G₂⟩ := S
  simp only at e hc hG
  subst e hc
  have : G₁ = G₂ := funext fun j => hG j
  subst this
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
