module

public import CORALean.ContSet.Capsule.Real.Operations.Radius
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# Every point of a capsule is within `radius` of the center

The segment contributes at most `‖g‖₂` (`t ∈ [-1, 1]`), the ball at most `r`.

## Inputs
* `C` – capsule
* `x` – point

## Hypotheses
* `hx` – `x ∈ C`

## Conclusion
* the distance of `x` to the center is at most the radius
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point of the capsule is within `radius` of the center. -/
theorem Capsule.norm₂_sub_center_le {C : Capsule n} {x : Vec ℝ n}
    (hx : x ∈ C.construct) : -- --- CONCL ---
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
