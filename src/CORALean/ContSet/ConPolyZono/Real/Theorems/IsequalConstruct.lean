module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Isequal

@[expose] public section

/-!
# Constrained polynomial zonotopes passing `isequal` denote the same set

Sound, not exact: `isequal` compares the representation, and different data can denote one set.

## Inputs
* `Z` – first set
* `S` – second set

## Hypotheses
* `h` – the two sets pass the equality test

## Conclusion
* the two sets are equal
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isequal_construct {Z S : ConPolyZono α} (h : Z.isequal S) :
    Z.construct = S.construct := by -- --- PROOF ---
  obtain ⟨ep, eh, eq, em, es, hc, hG, hE, hGI, hA, hb, hR⟩ := h
  obtain ⟨p₁, h₁, qI₁, c₁, G₁, E₁, GI₁, ⟨m₁, q₁, A₁, R₁, b₁, op₁, dom₁⟩, hop₁, hdom₁⟩ := Z
  obtain ⟨p₂, h₂, qI₂, c₂, G₂, E₂, GI₂, ⟨m₂, q₂, A₂, R₂, b₂, op₂, dom₂⟩, hop₂, hdom₂⟩ := S
  simp only at ep eh eq em es hc hG hE hGI hA hb hR
  subst ep eh eq em es hc
  have h1 : G₁ = G₂ := funext fun j => hG j
  have h2 : E₁ = E₂ := funext fun k => funext fun i => hE k i
  have h3 : GI₁ = GI₂ := funext fun j => hGI j
  have h4 : R₁ = R₂ := funext fun k => funext fun i => hR k i
  -- every row of both is an equation, so the operators agree too
  have h5 : op₁ = op₂ := funext fun i => (hop₁ i).trans (hop₂ i).symm
  -- and both boxes are the unit box
  have h6 : dom₁ = dom₂ := hdom₁.trans hdom₂.symm
  subst h1 h2 h3 h4 h5 h6
  cases eq_of_heq hA
  cases eq_of_heq hb
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
