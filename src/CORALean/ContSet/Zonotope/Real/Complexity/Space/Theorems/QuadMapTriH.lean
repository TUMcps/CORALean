module

public import CORALean.ContSet.Zonotope.Real.Operations.QuadMapTri
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `Zonotope.quadMapTri_h`

[1, Lemma 1 (generators)]: the enclosing zonotope of the quadratic map has `σ = C(p + 2, 2) - 1`
generators, `p` linear ones, `p` squares and `C(p, 2)` pairs. `p + p + C(p, 2) = C(p + 2, 2) - 1` is
Pascal's rule twice, `C(p + 2, 2) = C(p + 1, 2) + p + 1 = C(p, 2) + p + p + 1`.

## Inputs
* `n` – dimension
* `m` – output dimension
* `Q` – family of quadratic matrices
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* result has `C(p + 2, 2) - 1` generators

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1 (generators)]: `σ = C(p + 2, 2) - 1`. -/
theorem Zonotope.quadMapTri_h {n m : ℕ} (Q : Fin m → Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) :
    (Z.quadMapTri Q).h = (Z.h + 2).choose 2 - 1 := by -- --- PROOF ---
  show Z.h + Z.h + Z.h.choose 2 = (Z.h + 2).choose 2 - 1
  -- Pascal's rule twice
  have h2 : (Z.h + 2).choose 2 = (Z.h + 1).choose 2 + (Z.h + 1) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have h1 : (Z.h + 1).choose 2 = Z.h.choose 2 + Z.h := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  rw [h2, h1]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
