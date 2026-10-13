module

public import CORALean.ContSet.Taylm.Real.Operations.Smul
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfSmul
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `Taylm.smul` encloses the scaled function

The remainder scales as an interval: `a (f - p)` lies between the corner products.

With `plus_outer` and `minus_outer`, the linear combinations of [1, Eq. 6] and [1, Eq. 7].

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.smul_outer (a : ℝ) {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    (T.smul a).Encloses fun t => a * f t := by -- --- PROOF ---
  intro t ht
  have h' := h t ht
  have hm := Interval.mul_between_corners (le_refl a) (le_refl a) h'.1 h'.2
  simp only [Taylm.smul, Taylm.poly, Taylm.polyOf_smul] at *
  rw [← mul_sub]
  exact hm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
