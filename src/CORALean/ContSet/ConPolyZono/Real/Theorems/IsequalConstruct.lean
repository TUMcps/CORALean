module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Isequal

@[expose] public section

/-!
# Constrained polynomial zonotopes passing `isequal` denote the same set

Sound, not exact: `isequal` compares the representation, and different data can denote one set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isequal_construct {Z S : ConPolyZono α} (h : Z.isequal S) :
    Z.construct = S.construct := by -- --- PROOF ---
  obtain ⟨ep, eh, eq, em, es, hc, hG, hE, hGI, hA, hb, hEC⟩ := h
  obtain ⟨p₁, h₁, q₁, m₁, s₁, c₁, G₁, E₁, GI₁, A₁, b₁, EC₁⟩ := Z
  obtain ⟨p₂, h₂, q₂, m₂, s₂, c₂, G₂, E₂, GI₂, A₂, b₂, EC₂⟩ := S
  simp only at ep eh eq em es hc hG hE hGI hA hb hEC
  subst ep eh eq em es hc
  have h1 : G₁ = G₂ := funext fun j => hG j
  have h2 : E₁ = E₂ := funext fun k => funext fun i => hE k i
  have h3 : GI₁ = GI₂ := funext fun j => hGI j
  have h4 : EC₁ = EC₂ := funext fun k => funext fun i => hEC k i
  subst h1 h2 h3 h4
  cases eq_of_heq hA
  cases eq_of_heq hb
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
