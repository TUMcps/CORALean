module

public import CORALean.Specification.SyntaxTree.Operations.PiFloat

@[expose] public section

/-!
# `piFloat` contains `π`

The lower bound `2 acosDown(0)` is at most `2 arccos 0 = π`, and the upper bound `2 acosUp(0)` is at
least it.

## Inputs
* `p` – precision of acos
* `k` – Newton steps for sqrt

## Hypotheses
* none

## Conclusion
* the bounds of `piFloat` enclose `π`
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

/-- The bounds of `piFloat` enclose `π`. -/
theorem SyntaxTree.piFloat_contains (p k : ℕ) : -- --- CONCL ---
    toReal (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf ≤ Real.pi ∧ Real.pi ≤ toReal
      (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup := by -- --- PROOF ---
  have h0 : toReal (zero : 𝕋) = 0 := toReal_zero
  have hd := acosDown_le p k (zero : 𝕋)
  have hu := le_acosUp p k (zero : 𝕋)
  rw [h0, Real.arccos_zero] at hd hu
  have h1 := addDown_le_add (acosDown p k (zero : 𝕋)) (acosDown p k zero)
  have h2 := add_le_addUp (acosUp p k (zero : 𝕋)) (acosUp p k zero)
  exact ⟨by simp only [SyntaxTree.piFloat]; linarith, by simp only [SyntaxTree.piFloat]; linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
