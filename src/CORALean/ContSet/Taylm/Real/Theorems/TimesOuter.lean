module

public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.ContSet.Taylm.Real.Operations.Times
public import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfFilter
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfMulTerms
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# `Taylm.times` encloses the product

`fg - kept = dropped + p₁(g - p₂) + p₂(f - p₁) + (f - p₁)(g - p₂)`, each summand in the
interval `times` adds for it.

The product of [1, Def. 2] is a Taylor model of `f·g`.

## Inputs
* `T₁` – first model
* `T₂` – second model
* `f` – first function
* `g` – second function

## Hypotheses
* `h₁` – the first model encloses its function
* `h₂` – the second model encloses its function

## Conclusion
* the product model encloses the product of the functions

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.times_outer {T₁ T₂ : Taylm n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : -- --- CONCL ---
    (T₁.times T₂).Encloses fun t => f t * g t := by -- --- PROOF ---
  intro t ht
  -- the product list split into what is kept and what is bounded
  have hsplit := Taylm.polyOf_filter (Taylm.mulTerms T₁.terms T₂.terms)
    (fun a => Nat.ble (Taylm.degree a.2) (max T₁.maxOrder T₂.maxOrder)) t
  have hL := Taylm.polyOf_mulTerms T₁.terms T₂.terms t
  have hD := Taylm.polyBounds_mem ((Taylm.mulTerms T₁.terms T₂.terms).filter
    fun a => !Nat.ble (Taylm.degree a.2) (max T₁.maxOrder T₂.maxOrder)) ht
  have hP₁ := Taylm.polyBounds_mem T₁.terms ht
  have hP₂ := Taylm.polyBounds_mem T₂.terms ht
  have hr₁ := h₁ t ht
  have hr₂ := h₂ t ht
  -- the three cross terms, each between its corner products
  have m₁ := Interval.mul_between_corners hP₁.1 hP₁.2 hr₂.1 hr₂.2
  have m₂ := Interval.mul_between_corners hP₂.1 hP₂.2 hr₁.1 hr₁.2
  have m₃ := Interval.mul_between_corners hr₁.1 hr₁.2 hr₂.1 hr₂.2
  simp only [Taylm.poly] at hr₁ hr₂ m₁ m₂ m₃ ⊢
  have key : f t * g t - Taylm.polyOf (T₁.times T₂).terms t
      = Taylm.polyOf ((Taylm.mulTerms T₁.terms T₂.terms).filter
          fun a => !Nat.ble (Taylm.degree a.2) (max T₁.maxOrder T₂.maxOrder)) t
        + Taylm.polyOf T₁.terms t * (g t - Taylm.polyOf T₂.terms t)
        + Taylm.polyOf T₂.terms t * (f t - Taylm.polyOf T₁.terms t)
        + (f t - Taylm.polyOf T₁.terms t) * (g t - Taylm.polyOf T₂.terms t) := by
    simp only [Taylm.times]
    linear_combination hsplit - hL
  rw [key]
  simp only [Taylm.times]
  constructor <;> linarith [m₁.1, m₁.2, m₂.1, m₂.2, m₃.1, m₃.2, hD.1, hD.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
