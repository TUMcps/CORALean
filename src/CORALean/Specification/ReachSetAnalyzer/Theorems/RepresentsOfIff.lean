module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.RepresentsOfIff
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Represents

@[expose] public section

/-!
# What an analyzer says depends on the predicates only up to equivalence

If an analyzer represents `PT` and `PF` and these are equivalent to `PT'` and `PF'`, it
represents those.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.represents_of_iff (obj : ReachSetAnalyzer S n) (d : ℝ)
    {PT PF PT' PF' : String → ℝ → Prop} (h : obj.Represents d PT PF)
    (hT : ∀ k t, PT k t ↔ PT' k t) (hF : ∀ k t, PF k t ↔ PF' k t) :
    obj.Represents d PT' PF' :=
  ⟨h.1, fun p hp => by
    obtain ⟨b, hb, hr⟩ := h.2 p hp
    exact ⟨b, hb, FiniteKleeneSignalBuilder.represents_of_iff b d hr (hT p.1) (hF p.1)⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
