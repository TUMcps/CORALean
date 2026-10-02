import CORALean.ContSet.Capsule.Real.Operations.Radius
import CORALean.Global.EuclideanNorm

/-!
# Every point of a capsule is within `radius` of the centre

The segment contributes at most `‖g‖₂` (`t ∈ [-1, 1]`), the ball at most `r`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of the capsule is within `radius` of the centre. -/
theorem Capsule.norm₂_sub_centre_le {C : Capsule n} {x : Vec ℝ n} (hx : x ∈ C.construct) :
    ‖x - C.c‖₂ ≤ C.radius := by -- --- PROOF ---
  obtain ⟨t, ht, hle⟩ := hx
  have hy : ‖x - (C.c + t • C.g)‖₂ ≤ C.r := hle
  have hsplit : x - C.c = t • C.g + (x - (C.c + t • C.g)) := by abel
  have hg : ‖t • C.g‖₂ ≤ ‖C.g‖₂ := by
    rw [norm₂_smul]
    exact mul_le_of_le_one_left (norm₂_nonneg _) (abs_le.mpr ht)
  rw [hsplit]
  exact (norm₂_add_le _ _).trans (add_le_add hg hy)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
