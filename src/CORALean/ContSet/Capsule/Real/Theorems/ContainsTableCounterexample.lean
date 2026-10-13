module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.Global.EuclideanNorm
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# [1, Table 2]'s capsule test misses the boundary

[1, Table 2] tests `x` against the capsule `⟨c, g⟩ ⊕ {‖·‖₂ ≤ r}` by
`(‖(δ^T g_n) g_n - δ‖₂ < r ∧ |δ^T g_n| < ‖g‖₂) ∨ ‖δ - g‖₂ ≤ r ∨ ‖δ + g‖₂ ≤ r` — and presents
it among the exact containment checks. The strict `< r` rejects every point at distance
exactly `r` from the open axis: `c = 0`, `g = (1, 0)`, `r = 1`, `x = (0, 1)` is in the
capsule (the axis point `0` is at distance `1`), yet the axis test fails (`1 < 1`) and
both end spheres are `√2` away. With `≤ r` the test is exact (`ContainsTableIff`).
CORA's `aux_containsPoint` compares `dist < r | withinTol(dist, r)`, so it is not affected.

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Table 2]'s capsule test, as printed, rejects a point of the capsule. -/
theorem Capsule.contains_table_counterexample :
    ∃ (C : Capsule 2) (x : Vec ℝ 2), x ∈ C.construct ∧
      ¬ ((‖((x - C.c) ⬝ᵥ (‖C.g‖₂⁻¹ • C.g)) • (‖C.g‖₂⁻¹ • C.g) - (x - C.c)‖₂ < C.r ∧
          |(x - C.c) ⬝ᵥ (‖C.g‖₂⁻¹ • C.g)| < ‖C.g‖₂) ∨
        ‖(x - C.c) - C.g‖₂ ≤ C.r ∨ ‖(x - C.c) + C.g‖₂ ≤ C.r) := by -- --- PROOF ---
  have hg : ‖(![1, 0] : Vec ℝ 2)‖₂ = 1 := by simp [norm₂, Fin.sum_univ_two]
  refine ⟨⟨![0, 0], ![1, 0], 1⟩, ![0, 1], ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
  · simp [Fin.sum_univ_two]
  · simp only [hg, inv_one, one_smul]
    -- the axis test reads `1 < 1`, each end sphere `√2 ≤ 1`
    simp [norm₂, Fin.sum_univ_two, dotProduct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
