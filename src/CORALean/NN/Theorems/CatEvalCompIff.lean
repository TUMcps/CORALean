module

public import CORALean.NN.Definitions.Cat

@[expose] public section

/-!
# What a composed CAT function maps a point to

`f₂ ∘ f₁` maps `x` to `y` exactly when some intermediate `z` is a value of `f₁` at `x` and `y`
one of `f₂` at `z`: the inversion of `Cat.Evaluates` at `.comp`, [1, Fig. 3]'s third form.

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

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m l n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.eval_comp_iff (f₂ : Cat 𝕋 l n) (f₁ : Cat 𝕋 m l) (x : Vec ℝ m)
    (y : Vec ℝ n) : -- --- CONCL ---
    (Cat.comp f₂ f₁).Evaluates x y ↔ ∃ z, f₁.Evaluates x z ∧ f₂.Evaluates z y := by -- --- PROOF ---
  constructor
  · rintro (_ | _ | ⟨_, _, z, h₁, h₂⟩)
    exact ⟨z, h₁, h₂⟩
  · rintro ⟨z, h₁, h₂⟩
    exact Cat.Evaluates.comp f₂ f₁ z h₁ h₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
