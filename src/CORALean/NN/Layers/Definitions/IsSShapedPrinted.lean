module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

/-!
# The S-shaped functions of DeepZ's footnote, as printed

[1, Thm. 3.2]'s footnote: a smooth `f : ℝ → ℝ` is S-shaped if `f' ≥ 0` and there is an `x'`
with `f''(x) ≤ 0 ⇔ x ≤ x'`. That makes `f` concave left of `x'` and convex right of it, the
reverse of the sigmoid, which is convex left of `0`; `x ↦ x³` is S-shaped by this definition.
Stated with `deriv`, the functions being smooth.

## Inputs
* `f` – activation function

## Output
* the function has the S-shape the printed footnote asks for

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". Advances in Neural Information Processing Systems, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Thm. 3.2]'s footnote, as printed. -/
def IsSShapedPrinted (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ deriv f x) ∧
    ∃ x' : ℝ, ∀ x, deriv (deriv f) x ≤ 0 ↔ x ≤ x'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
