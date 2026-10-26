module

public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.SoundTimesFloat

@[expose] public section

/-!
# `prod` of sound float trees is sound

The node `prod` of a vector of float trees folds `times` over it, so it is sound when every tree is,
by induction on the list.

## Inputs
* `rest` – remaining trees

## Hypotheses
* `h` – the first tree is sound
* `hr` – every remaining tree is sound

## Conclusion
* the `prod` tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
    {n : ℕ} {B : Float.Interval (Vec 𝕋 n)} {t : Float.SyntaxTree 𝕋 n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `prod` of sound float trees is sound. -/
theorem SyntaxTree.sound_prodFloat {rest : List (Float.SyntaxTree 𝕋 n)}
    (h : SyntaxTree.IsSoundFloat B t)
    (hr : ∀ r ∈ rest, SyntaxTree.IsSoundFloat B r) : -- --- CONCL ---
    SyntaxTree.IsSoundFloat B (SyntaxTree.prodFloat t rest) := by -- --- PROOF ---
  induction rest generalizing t with
  | nil => exact h
  | cons r rs ih =>
    exact ih (SyntaxTree.sound_timesFloat h (hr r List.mem_cons_self))
      (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
