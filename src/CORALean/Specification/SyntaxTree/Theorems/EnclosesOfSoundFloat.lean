module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat

@[expose] public section

/-!
# A sound float tree encloses its function

`IsSoundFloat` holds the enclosure of the root, whichever the root.

## Inputs
* none

## Hypotheses
* `h` – the tree is sound over the box

## Conclusion
* the tree encloses its function over the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    {n : ℕ} {B : Float.Interval (Vec 𝕋 n)} {t : Float.SyntaxTree 𝕋 n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sound float tree encloses its function over the box. -/
theorem SyntaxTree.encloses_of_soundFloat (h : SyntaxTree.IsSoundFloat B t) : -- --- CONCL ---
    t.Encloses B := by -- --- PROOF ---
  cases t with
  | var i v => exact fun x hx => h x hx
  | unary op v f t => exact h.2.1
  | binary op v f t₁ t₂ => exact h.2.2.1
  | numLeft op v f c t => exact h.2.1
  | numRight op v f t c => exact h.2.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
