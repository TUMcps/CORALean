module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortTailP
public import CORALean.ContSet.PolyZonotope.Real.Operations.Shift

@[expose] public section

/-!
# [1, Alg. 2]'s recursion, paired with its factor-count proof

The constant term is line 15's `a_0 +`, a shift of the center, and everything
above it is the tail. Split off from `evalPolySort` the way `evalPolyP` is, so
that the factor count travels with the set rather than being reproved.

## Inputs
* `pZ` – polynomial zonotope

## Output
* evaluator mapping coefficients to a set with the same factor count

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] with the proof that it never leaves `pZ`'s factor count. -/
noncomputable def PolyZonotope.evalPolySortP (pZ : PolyZonotope (Vec ℝ n)) :
    List (Vec ℝ n) → {R : PolyZonotope (Vec ℝ n) // R.p = pZ.p}
  -- 15. the empty polynomial: `0`
  | [] => ⟨⟨pZ.p, 0, 0, 0, Fin.elim0, fun _ => Fin.elim0, Fin.elim0⟩, rfl⟩
  | a0 :: rest =>
      -- 15. `sortPlus(a₁ PZ¹, …, a_o PZ^o)`, lines 1-14 of the tail, from degree `1`
      let S := PolyZonotope.evalPolySortTailP pZ rest 0
      -- 15. `gPZ ← a₀ + …`: the constant term shifts the center
      ⟨S.1.shift a0, S.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
