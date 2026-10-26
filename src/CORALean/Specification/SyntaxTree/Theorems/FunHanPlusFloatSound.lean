module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanPlusFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_plus_` over floats is sound

`SyntaxTree.funHanPlusFloat` keeps every solution of `s₁ + s₂ ∈ int`: each operand is the sum minus
the other operand, which the rounded difference encloses.

## Inputs
* `prev₁` – first previous interval
* `prev₂` – second previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float backpropagation of the sum keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_plus_` over floats is sound for the sum. -/
theorem SyntaxTree.funHanPlusFloat_sound (prev₁ prev₂ v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsBinarySoundFloat SyntaxTree.Binary.plus.fn prev₁ prev₂ v
      SyntaxTree.funHanPlusFloat := by -- --- PROOF ---
  intro int _ s₁ s₂ h₁ h₂ hi
  have hi' : int.contains (s₁ + s₂) := hi
  have a := SyntaxTree.contains_minusFloat hi' h₂
  have b := SyntaxTree.contains_minusFloat hi' h₁
  rw [add_sub_cancel_right] at a
  rw [add_sub_cancel_left] at b
  have m₁ := SyntaxTree.meet_containsFloat h₁ a
  have m₂ := SyntaxTree.meet_containsFloat h₂ b
  exact ⟨m₁.1, m₂.1, m₁.2, m₂.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
