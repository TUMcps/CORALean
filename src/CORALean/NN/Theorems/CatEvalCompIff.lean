module

public import CORALean.NN.Definitions.Cat

@[expose] public section

/-!
# What a composed CAT function maps a point to

`f₂ ∘ f₁` maps `x` to `y` exactly when some intermediate `z` is a value of `f₁` at `x` and `y`
one of `f₂` at `z`: the inversion of `Cat.Eval` at `.comp`, [1, Fig. 3]'s third form.

## Inputs
* `f₂` – second function
* `f₁` – first function
* `x` – input point
* `y` – output point

## Hypotheses
* none

## Conclusion
* the composition maps the point to the output iff some intermediate point links them

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m l n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.eval_comp_iff (f₂ : Cat 𝕋 l n) (f₁ : Cat 𝕋 m l) (x : Vec ℝ m)
    (y : Vec ℝ n) : -- --- CONCL ---
    (Cat.comp f₂ f₁).Eval x y ↔ ∃ z, f₁.Eval x z ∧ f₂.Eval z y := by -- --- PROOF ---
  constructor
  · rintro (_ | _ | ⟨_, _, z, h₁, h₂⟩)
    exact ⟨z, h₁, h₂⟩
  · rintro ⟨z, h₁, h₂⟩
    exact Cat.Eval.comp f₂ f₁ z h₁ h₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
