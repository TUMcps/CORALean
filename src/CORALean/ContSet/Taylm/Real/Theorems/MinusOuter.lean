module

public import CORALean.ContSet.Taylm.Real.Operations.Minus
public import CORALean.ContSet.Taylm.Real.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Real.Theorems.UminusOuter

@[expose] public section

/-!
# `Taylm.minus` encloses the difference

[1, Eq. 7]: the difference encloses `f - g`.

## Inputs
* `T₁` – first model
* `T₂` – second model
* `f` – first function
* `g` – second function

## Hypotheses
* `h₁` – the first model encloses its function
* `h₂` – the second model encloses its function

## Conclusion
* the difference model encloses the difference of the functions

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.minus_outer {T₁ T₂ : Taylm n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.minus T₂).Encloses fun t => f t - g t := by
  show (T₁.plus T₂.uminus).Encloses _
  simpa only [sub_eq_add_neg] using Taylm.plus_outer h₁ (Taylm.uminus_outer h₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
