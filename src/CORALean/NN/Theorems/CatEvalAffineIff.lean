module

public import CORALean.NN.Definitions.Cat

@[expose] public section

/-!
# What an affine CAT function maps a point to

`W x + b`, and nothing else: [1, Fig. 3]'s first form is a function. The inversion of
`Cat.Evaluates` at `.affine`, which every computation of a CAT function's value starts from.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `x` – input point
* `y` – output point

## Hypotheses
* none

## Conclusion
* the affine function maps the point to the output iff it is the affine image

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2: Safety
      and Robustness Certification of Neural Networks with Abstract Interpretation". 2018 IEEE
      Symposium on Security and Privacy (SP), 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.eval_affine_iff (W : Mat 𝕋 n m) (b : Vec 𝕋 n) (x : Vec ℝ m)
    (y : Vec ℝ n) : -- --- CONCL ---
    (Cat.affine W b).Evaluates x y ↔ y = toRealMat W *ᵥ x + toRealVec b := by -- --- PROOF ---
  constructor
  · rintro (_ | _ | _)
    rfl
  · rintro rfl
    exact Cat.Evaluates.affine W b x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
