module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic

@[expose] public section

/-!
# `aux_uminus_` over floats is sound

`SyntaxTree.funHanUminusFloat` keeps every solution of `-s ∈ int`: `s` is the negative of `-s`,
which the exact negation of `int` holds, and the meet with the previous interval keeps it.

## Inputs
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float inverse of the negation keeps every solution
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

/-- `aux_uminus_` over floats is sound for the negation. -/
theorem SyntaxTree.funHanUminusFloat_sound (prev v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.uminus.fn prev v
      SyntaxTree.funHanUminusFloat := by -- --- PROOF ---
  intro int _ s hs hi
  have hi' : int.contains (-s) := hi
  have h := SyntaxTree.contains_uminusFloat hi'
  rw [neg_neg] at h
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [Float.SyntaxTree.Dom.contains, Float.Interval.intersection, toReal_maximum,
      toReal_minimum]
    exact ⟨max_le h.1 hs.1, le_min h.2 hs.2⟩
  · simp only [Float.SyntaxTree.Dom.IsWithin, Float.Interval.intersection, toReal_maximum,
      toReal_minimum]
    exact ⟨le_max_right _ _, min_le_right _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
