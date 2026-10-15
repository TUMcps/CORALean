module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Represents
public import CORALean.Specification.ReachSetAnalyzer.ReachSetAnalyzer

@[expose] public section

/-!
# What an analyzer says

An analyzer says, for a duration `d`, that proposition `k` can be true at the times `t` of `[0,d]`
with `PT k t` and can be false at those with `PF k t`: its keys are distinct and each one's builder
says so (`FiniteKleeneSignalBuilder.Represents`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The builders of the analyzer mark `PT k` as possibly true and `PF k` as possibly false. -/
def ReachSetAnalyzer.Represents (obj : ReachSetAnalyzer S n) (d : ℝ) (PT PF : String → ℝ → Prop) :
    Prop :=
  (obj.aps.map Prod.fst).Nodup ∧ ∀ p ∈ obj.aps, ∃ b, obj.sigBuilder.lookup p.1 = some b ∧
    b.Represents d (PT p.1) (PF p.1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
