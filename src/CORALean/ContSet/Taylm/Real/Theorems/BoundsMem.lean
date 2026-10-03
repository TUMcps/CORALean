import CORALean.ContSet.Taylm.Real.Operations.Bounds
import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem

/-!
# An enclosed function stays in `bounds` on the box

[1, Eq. 5]'s `B` over-approximates the range: the enclosed function stays in it on the box.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bounds_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {t : Vec ℝ n}
    (ht : t ∈ Taylm.box n) : T.bounds.1 ≤ f t ∧ f t ≤ T.bounds.2 := by
  have h₁ := h t ht
  have h₂ := Taylm.polyBounds_mem T.terms ht
  simp only [Taylm.bounds, Taylm.poly] at *
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
