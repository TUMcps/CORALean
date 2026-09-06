import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Weighting a coefficient keeps it a coefficient

Scaling by a weight in `[0,1]` cannot leave the unit ball, which is the shape a
convex combination of two zonotopes takes. Stated in both arithmetic layers'
terms — it is arithmetic on `ℝ` and nothing else — though no proof in the tree
reaches for it as it stands.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.abs_mul_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : |b| ≤ 1) :
    |a * b| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg ha0]
  nlinarith [abs_nonneg b]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
