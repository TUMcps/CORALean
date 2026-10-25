module

public import CORALean.ContSet.Taylm.Real.Definitions.IsScaled

@[expose] public section

/-!
# `Taylm.uminus` keeps the scaling

Negation changes no magnitude: the coefficients' and the remainder ends' (swapped) are the same.
A step of [1, Thm. 1] for subtraction, which is a sum with a negation.

## Inputs
* `T` – Taylor model
* `h` – domain radius
* `C` – scaling constant

## Hypotheses
* `hT` – the model is scaled by the constant

## Conclusion
* the negated model is scaled by the same constant

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.uminus_scaled {T : Taylm n} {h C : ℝ} (hT : T.IsScaled h C) : -- --- CONCL ---
    T.uminus.IsScaled h C := by -- --- PROOF ---
  obtain ⟨w, i, s⟩ := hT
  refine ⟨?_, by simpa [Taylm.uminus] using s, by simpa [Taylm.uminus] using i⟩
  have : Taylm.weight T.uminus.terms h = Taylm.weight T.terms h := by
    simp [Taylm.uminus, Taylm.weight, Function.comp_def]
  rw [this]
  exact w

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
