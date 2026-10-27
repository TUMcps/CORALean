module

public import CORALean.ContSet.Taylm.Real.Operations.Rdivide
public import CORALean.ContSet.Taylm.Real.Theorems.InvOuter
public import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter

@[expose] public section

/-!
# `Taylm.rdivide` encloses the quotient

Under the inverse's condition on the denominator, `inv_outer` and `times_outer` compose: the
result encloses `f / g`.

[1, Eq. 9]: `T₁/T₂ = T₁·(1/T₂)` encloses `f/g`.

## Inputs
* `T₁` – numerator model
* `T₂` – denominator model
* `f` – numerator function
* `g` – denominator function

## Hypotheses
* `h₁` – the numerator encloses its function
* `h₂` – the denominator encloses its function
* `hside` – the denominator's range stays on one side of zero

## Conclusion
* the quotient model encloses the quotient of the functions

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.rdivide_outer {T₁ T₂ : Taylm n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g)
    (hside : 0 < min T₂.constCoef T₂.bounds.inf ∨ max T₂.constCoef T₂.bounds.sup < 0) :
    (T₁.rdivide T₂).Encloses fun t => f t / g t := by
  simpa [Taylm.rdivide, div_eq_mul_inv] using Taylm.times_outer h₁ (Taylm.inv_outer h₂ hside)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
