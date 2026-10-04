import CORALean.NN.Definitions.Cat

/-!
# What a composed CAT function maps a point to

`f₂ ∘ f₁` maps `x` to `y` exactly when some intermediate `z` is a value of `f₁` at `x` and `y`
one of `f₂` at `z`: the inversion of `Cat.Eval` at `.comp`, [1, Fig. 3]'s third form.

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m l n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Cat.eval_comp_iff (f₂ : Cat 𝕋 l n) (f₁ : Cat 𝕋 m l) (x : Vec ℝ m) (y : Vec ℝ n) :
    (Cat.comp f₂ f₁).Eval x y ↔ ∃ z, f₁.Eval x z ∧ f₂.Eval z y := by -- --- PROOF ---
  constructor
  · rintro (_ | _ | ⟨_, _, z, h₁, h₂⟩)
    exact ⟨z, h₁, h₂⟩
  · rintro ⟨z, h₁, h₂⟩
    exact Cat.Eval.comp f₂ f₁ z h₁ h₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
