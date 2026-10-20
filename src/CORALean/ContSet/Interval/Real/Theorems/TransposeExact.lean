module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.transpose` is exactly the transposed set

The transposes of the matrices in the box fill the transposed box, with no hypothesis, since
transposition only permutes the entries and so the bounds on them.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the transposed box is exactly the set of transposes
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.transpose_exact (I : Interval (Mat ℝ m n)) : -- --- CONCL ---
    I.transpose.construct = Matrix.transpose '' I.construct := by -- --- PROOF ---
  ext B
  constructor
  · intro hB
    refine ⟨B.transpose, fun p => ?_, Matrix.transpose_transpose B⟩
    exact hB (p.2, p.1)
  · rintro ⟨A, hA, rfl⟩ p
    exact hA (p.2, p.1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
