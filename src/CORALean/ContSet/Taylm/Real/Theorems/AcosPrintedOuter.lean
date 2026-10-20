module

public import CORALean.ContSet.Taylm.Real.Operations.AcosPrinted
public import CORALean.ContSet.Taylm.Real.Theorems.AsinOuter
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MinusOuter
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/-!
# `Taylm.acosPrinted` encloses `arccos ∘ f`

[1, Def. 3 (arccos)]: `arccos f = π/2 - arcsin f` is a Taylor model of `arccos ∘ f`, under
`asin`'s own domain condition. The constant is exact, `asin_outer` encloses `arcsin ∘ f`,
`minus_outer` the difference, and Mathlib's `Real.arccos_eq_pi_div_two_sub_arcsin` is the
identity.

## Inputs
* `T` – Taylor model
* `f` – enclosed function

## Hypotheses
* `h` – the model encloses the function
* `hdom` – the model's magnitude is below one

## Conclusion
* the printed model encloses arccos of the function

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.acosPrinted_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hdom : T.mag < 1) :
    T.acosPrinted.Encloses fun t => Real.arccos (f t) := by
  have h' := Taylm.minus_outer (Taylm.const_outer (n := n) (Real.pi / 2) T.maxOrder)
    (Taylm.asin_outer h hdom)
  simp only [Taylm.acosPrinted, Real.arccos_eq_pi_div_two_sub_arcsin]
  exact h'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
