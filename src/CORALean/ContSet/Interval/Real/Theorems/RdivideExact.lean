module

public import CORALean.ContSet.Interval.Real.Operations.Rdivide
public import CORALean.ContSet.Interval.Real.Theorems.RecipExact
public import CORALean.ContSet.Interval.Real.Theorems.TimesExact

@[expose] public section

/-!
# `Interval.rdivide` is exactly the set of entrywise quotients

`rdivide` is `times` at the reciprocal box, `times_exact` makes that the entrywise product with
a reciprocal, and `recip_exact` makes the reciprocals those of the denominator's points. The
numerator may contain `0`; the denominator avoids it in every coordinate, as CORA's `±Inf` and
`NaN` branches, which `ℝ` cannot hold, are the cases where it does not.

[1, Eq. 3] on boxes away from `0`, `[x]/[y] = [x]·(1/[y])`.

## Inputs
* `I` – first interval box
* `J` – second interval box

## Hypotheses
* `hI` – `I` nonempty
* `hJ` – `J` nonempty
* `h0` – no coordinate of `J` contains zero

## Conclusion
* the quotient box is exactly the set of entrywise quotients

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.rdivide_exact {I J : Interval (Vec ℝ n)} (hI : I.IsNonempty)
    (hJ : J.IsNonempty) (h0 : ∀ i, 0 < J.inf i ∨ J.sup i < 0) : -- --- CONCL ---
    (I.rdivide J).construct =
      Set.image2 (fun x y i => x i / y i) I.construct J.construct := by -- --- PROOF ---
  -- the reciprocal box is nonempty because the denominator's signs are fixed
  have hr : J.recip.IsNonempty := fun i => by
    rcases h0 i with h | h
    · exact inv_anti₀ h (hJ i)
    · exact (inv_le_inv_of_neg h (lt_of_le_of_lt (hJ i) h)).mpr (hJ i)
  unfold Interval.rdivide
  rw [Interval.times_exact hI hr, Interval.recip_exact J hJ h0, Set.image2_image_right]
  simp only [div_eq_mul_inv]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
