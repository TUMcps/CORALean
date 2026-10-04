import CORALean.ContSet.Interval.Real.Operations.OfCenterRadius

/-!
# `Interval.ofCenterRadius` denotes the matrices within the half-width

`x` is in `[c - r, c + r]` iff each entry is within the matching entry of `r` of the one of `c`.
This is the meaning of CORA's `intervalMatrix(C, Δ)`.

[1, Sec. 2]: `[x] = mid([x]) ⊕ rad([x]) ⊗ [-1, 1]`, membership read off the centre and radius.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mem_ofCenterRadius (c r x : α) :
    x ∈ (Interval.ofCenterRadius c r).construct ↔ ∀ i, |entry x i - entry c i| ≤ entry r i := by
  refine forall_congr' fun i => ?_
  simp only [Interval.ofCenterRadius, entry_sub, entry_add, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
