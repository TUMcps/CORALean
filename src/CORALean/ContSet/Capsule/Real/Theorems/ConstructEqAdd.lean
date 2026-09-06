import CORALean.ContSet.Capsule.Real.Capsule

/-!
# A non-degenerate capsule as a sum of sets

At `0 ≤ C.r`, `Real.sqrt_le_left` turns the defining bound into `∑ … ≤ C.r ^ 2`,
splitting a point of `C.construct` into the segment point `c + t g` and the
remainder, a point of the Euclidean ball of squared radius `C.r ^ 2`. Shared by
`Convex.lean` and `IsCompact.lean`, both of which transfer their property from
the two summands with `Convex.add`/`IsCompact.add`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.construct_eq_add {C : Capsule n} (hr : 0 ≤ C.r) :
    C.construct = (fun t : ℝ => C.c + t • C.g) '' Set.Icc (-1 : ℝ) 1 +
      {y : Vec ℝ n | ∑ i, y i ^ 2 ≤ C.r ^ 2} := by -- --- PROOF ---
  ext x
  simp only [Capsule.construct, Set.mem_setOf_eq, Set.mem_add, Set.mem_image]
  constructor
  · rintro ⟨t, ht, hle⟩
    rw [Real.sqrt_le_left hr] at hle
    refine ⟨C.c + t • C.g, ⟨t, ht, rfl⟩, x - (C.c + t • C.g), ?_, by abel⟩
    simpa [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hle
  · rintro ⟨_, ⟨t, ht, rfl⟩, y, hy, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [Real.sqrt_le_left hr]
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hy

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
