import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortTailP
import CORALean.ContSet.PolyZonotope.Real.Operations.Shift

/-!
# [1, Alg. 2]'s recursion, paired with its factor-count proof

The constant term is line 15's `a_0 +`, a shift of the centre, and everything
above it is the tail. Split off from `evalPolySort` the way `evalPolyP` is, so
that the factor count travels with the set rather than being reproved.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] with the proof that it never leaves `pZ`'s factor count. -/
noncomputable def PolyZonotope.evalPolySortP (pZ : PolyZonotope (Vec ℝ n)) :
    List (Vec ℝ n) → {R : PolyZonotope (Vec ℝ n) // R.p = pZ.p}
  | [] => ⟨⟨pZ.p, 0, 0, 0, Fin.elim0, fun _ => Fin.elim0, Fin.elim0⟩, rfl⟩
  | a0 :: rest =>
      let S := PolyZonotope.evalPolySortTailP pZ rest 0
      ⟨S.1.shift a0, S.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
