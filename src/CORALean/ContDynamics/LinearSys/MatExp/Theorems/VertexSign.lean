module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# The sign of `t + c t²` against the parabola's vertex

`t + c t² = t² (c - (-1/t))`, so it takes the sign of `c` measured against the vertex `-1/t` of
[1, Lemma 3.1]'s `γ` — and vanishes at `t = 0`, where `-1/t` reads as `0`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.vertex_sign {t c : ℝ} : t + c * t ^ 2 = t ^ 2 * (c - -1 / t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · ring
  · field_simp
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
