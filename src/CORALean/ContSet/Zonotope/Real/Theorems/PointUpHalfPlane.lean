import CORALean.ContSet.Zonotope.Real.Operations.PointUp

/-!
# Every generator of `pointUp` is in the upper half-plane

`y > 0 ∨ (y = 0 ∧ x ≥ 0)`, the half-plane in which the trigonometric order of [1, Alg. 3] and
[1, Alg. 4] is taken: a generator with `y < 0`, or `y = 0` and `x < 0`, is negated, and the
others are already there.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.pointUp_half_plane (Z : Zonotope (Vec ℝ 2)) (j : Fin Z.h) :
    0 ≤ Z.pointUp.G j 1 ∧ (0 < Z.pointUp.G j 1 ∨ 0 ≤ Z.pointUp.G j 0) := by -- --- PROOF ---
  by_cases h : Z.G j 1 < 0 ∨ (Z.G j 1 = 0 ∧ Z.G j 0 < 0)
  · simp only [Zonotope.pointUp, h, if_true, Pi.neg_apply]
    rcases h with h | ⟨h0, h1⟩
    · exact ⟨by linarith, Or.inl (by linarith)⟩
    · exact ⟨by linarith, Or.inr (by linarith)⟩
  · simp only [Zonotope.pointUp, h, if_false]
    push Not at h
    refine ⟨h.1, ?_⟩
    rcases h.1.eq_or_lt with h0 | h0
    · exact Or.inr (h.2 h0.symm)
    · exact Or.inl h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
