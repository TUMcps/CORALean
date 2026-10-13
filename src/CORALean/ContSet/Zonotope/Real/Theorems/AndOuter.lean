import CORALean.ContSet.Zonotope.Real.Operations.And

/-!
# The `'conZonotope'` intersection of zonotopes encloses the intersection

Through the exact constrained-zonotope intersection (`ConZonotope.intersection_exact`) and the
conversions: an outer statement only, the enclosing zonotope forgets the constraints.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.and_outer (Z S : Zonotope (Vec ℝ n)) :
    Z.construct ∩ S.construct ⊆ (Z.and_ S).construct := by -- --- PROOF ---
  intro x hx
  have h1 : x ∈ Z.conZonotope.construct ∩ S.conZonotope.construct := by
    rw [Z.conZonotope_exact, S.conZonotope_exact] at hx; exact hx
  rw [ConZonotope.intersection_exact] at h1
  exact (ConZonotope.zonotope_contains _) h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
