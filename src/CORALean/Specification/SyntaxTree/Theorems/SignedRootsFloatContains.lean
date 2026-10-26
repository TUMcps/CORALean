module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.SignedRootsFloat

@[expose] public section

/-!
# `signedRootsFloat` holds the signed roots

A point of the previous interval whose absolute value lies between the two roots lies in
`SyntaxTree.signedRootsFloat`: its absolute value between the minimum and the maximum, so it is that
value if the interval is nonnegative, its negative if it is nonpositive, and in `[-m, m]` whichever
the sign.

## Inputs
* `prev` – previous interval
* `preInf` – lower root
* `preSup` – upper root
* `s` – point

## Hypotheses
* `hs` – the previous interval holds the point
* `h₁` – the lower root is at most the point's absolute value
* `h₂` – the point's absolute value is at most the upper root

## Conclusion
* the signed roots hold the point
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

/-- A point of `prev` with `|s|` between the roots lies in the signed roots. -/
theorem SyntaxTree.signedRootsFloat_contains {prev : Float.SyntaxTree.Dom 𝕋} {preInf preSup : 𝕋}
    {s : ℝ} (hs : prev.contains s) (h₁ : toReal preInf ≤ |s|)
    (h₂ : |s| ≤ toReal preSup) : -- --- CONCL ---
    (SyntaxTree.signedRootsFloat prev preInf preSup).contains s := by -- --- PROOF ---
  have a : toReal (minimum preInf preSup) ≤ |s| := by
    rw [toReal_minimum]; exact min_le_of_left_le h₁
  have b : |s| ≤ toReal (maximum preInf preSup) := by
    rw [toReal_maximum]; exact le_max_of_le_right h₂
  unfold SyntaxTree.signedRootsFloat
  split_ifs with h0 h1
  · have hn : 0 ≤ s := by
      have := toReal_le_of_le h0
      rw [toReal_zero] at this
      exact this.trans hs.1
    rw [abs_of_nonneg hn] at a b
    exact ⟨a, b⟩
  · have hn : s ≤ 0 := by
      have := toReal_le_of_le h1
      rw [toReal_zero] at this
      exact hs.2.trans this
    rw [abs_of_nonpos hn] at a b
    exact ⟨by simp only [toReal_neg]; linarith, by simp only [toReal_neg]; linarith⟩
  · exact ⟨by simp only [toReal_neg]; linarith [neg_abs_le s], by linarith [le_abs_self s]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
