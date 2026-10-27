module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.Formula

@[expose] public section

/-!
# Subformulas

`a` is `φ` or a subformula of it: the operands of `φ`, their operands, and so on.

## Inputs
* `a` – formula

## Output
* `a` occurs in `φ`
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {A : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def OnlineReachSetAnalyzer.Formula.IsSub (a : OnlineReachSetAnalyzer.Formula ℝ A) :
    OnlineReachSetAnalyzer.Formula ℝ A → Prop
  | .not b => a = .not b ∨ a.IsSub b
  | .and b c => a = .and b c ∨ a.IsSub b ∨ a.IsSub c
  | .or b c => a = .or b c ∨ a.IsSub b ∨ a.IsSub c
  | .until I b c => a = .until I b c ∨ a.IsSub b ∨ a.IsSub c
  | φ => a = φ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
