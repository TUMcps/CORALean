module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Isequal

@[expose] public section

/-!
# Polynomial zonotopes passing `isequal` denote the same set

Sound, not exact: `isequal` compares the representation, and different data can denote one set.

## Inputs
* `Z` – first polynomial zonotope
* `S` – second polynomial zonotope

## Hypotheses
* `h` – the equality test holds

## Conclusion
* the two sets are equal
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.isequal_construct {Z S : PolyZonotope α} (h : Z.isequal S) :
    Z.construct = S.construct := by -- --- PROOF ---
  obtain ⟨ep, eh, eq, hc, hG, hE, hGI⟩ := h
  obtain ⟨p₁, h₁, q₁, c₁, G₁, E₁, GI₁⟩ := Z
  obtain ⟨p₂, h₂, q₂, c₂, G₂, E₂, GI₂⟩ := S
  simp only at ep eh eq hc hG hE hGI
  subst ep eh eq hc
  have h1 : G₁ = G₂ := funext fun j => hG j
  have h2 : E₁ = E₂ := funext fun k => funext fun i => hE k i
  have h3 : GI₁ = GI₂ := funext fun j => hGI j
  subst h1 h2 h3
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
