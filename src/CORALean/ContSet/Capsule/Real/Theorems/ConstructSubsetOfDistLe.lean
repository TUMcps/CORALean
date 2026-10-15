module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# A capsule inside another, by the distances between their parts

If the centers are `δc` apart, the generators `δg` apart and `C.r + δc + δg ≤ C'.r`, every point
`x = c + t g + b` of `C` is `c' + t g' + (b + (c - c') + t (g - g'))` and the last term has length
at most `r + δc + δg` (`|t| ≤ 1`). This is how a float capsule, whose center and generator are
rounded, covers an exact one.
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

theorem Capsule.construct_subset_of_dist_le {C C' : Capsule n}
    (h : ‖C.c - C'.c‖₂ + ‖C.g - C'.g‖₂ + C.r ≤ C'.r) :
    C.construct ⊆ C'.construct := by -- --- PROOF ---
  rintro x ⟨t, ht, hx⟩
  refine ⟨t, ht, ?_⟩
  have hb : ‖x - (C.c + t • C.g)‖₂ ≤ C.r := hx
  have hg : ‖t • (C.g - C'.g)‖₂ ≤ ‖C.g - C'.g‖₂ := by
    rw [norm₂_smul]
    exact mul_le_of_le_one_left (norm₂_nonneg _) (abs_le.mpr ht)
  have hsplit : x - (C'.c + t • C'.g) =
      (x - (C.c + t • C.g)) + (C.c - C'.c) + t • (C.g - C'.g) := by
    rw [smul_sub]; abel
  change ‖x - (C'.c + t • C'.g)‖₂ ≤ C'.r
  rw [hsplit]
  calc _ ≤ ‖(x - (C.c + t • C.g)) + (C.c - C'.c)‖₂ + ‖t • (C.g - C'.g)‖₂ := norm₂_add_le _ _
    _ ≤ (‖x - (C.c + t • C.g)‖₂ + ‖C.c - C'.c‖₂) + ‖C.g - C'.g‖₂ :=
        add_le_add (norm₂_add_le _ _) hg
    _ ≤ C'.r := by linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
