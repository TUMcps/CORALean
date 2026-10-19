module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Volume

@[expose] public section

/-!
# `volume` without independent generators

With no independent generators and as many factors as dimensions, `volume` is the integral
of the Jacobian determinant of the set itself (no `dependent` step).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.volume_of_q_zero {n : ℕ} (pZ : PolyZonotope (Vec ℝ n)) (hq : pZ.q = 0)
    (h : pZ.p = n) : pZ.volume = some (pZ.aux_jacobianDetIntegral h) := by
  unfold PolyZonotope.volume
  simp only [hq, if_true]
  rw [if_neg (by omega), dif_pos h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
