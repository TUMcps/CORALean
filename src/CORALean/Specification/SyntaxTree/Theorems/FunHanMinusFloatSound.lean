module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanMinusFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_minus_` over floats is sound

`SyntaxTree.funHanMinusFloat` keeps every solution of `s₁ - s₂ ∈ int`: `s₁` is the difference's sum
with `s₂`, and `s₂` the difference of `s₁` and the difference, each of which the rounded sum and
difference enclose.

## Inputs
* `prev₁` – first previous interval
* `prev₂` – second previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float backpropagation of the difference keeps every solution
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

/-- `aux_minus_` over floats is sound for the difference. -/
theorem SyntaxTree.funHanMinusFloat_sound
    (prev₁ prev₂ v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsBinarySoundFloat SyntaxTree.Binary.minus.fn prev₁ prev₂ v
      SyntaxTree.funHanMinusFloat := by -- --- PROOF ---
  intro int _ s₁ s₂ h₁ h₂ hi
  have hi' : int.contains (s₁ - s₂) := hi
  have a := SyntaxTree.contains_plusFloat hi' h₂
  have b := SyntaxTree.contains_minusFloat h₁ hi'
  rw [sub_add_cancel] at a
  rw [sub_sub_cancel] at b
  have m₁ := SyntaxTree.meet_containsFloat h₁ a
  have m₂ := SyntaxTree.meet_containsFloat h₂ b
  exact ⟨m₁.1, m₂.1, m₁.2, m₂.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
