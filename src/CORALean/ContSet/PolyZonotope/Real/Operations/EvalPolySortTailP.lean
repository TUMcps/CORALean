module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.ContSet.PolyZonotope.Real.Operations.PowSort
public import CORALean.ContSet.PolyZonotope.Real.Operations.SortPlus
public import CORALean.Global.Hadamard

@[expose] public section

/-!
# [1, Alg. 2]'s sum over the powers

Lines 12-15 without the constant term: `a_k·PZ^(k+1) + a_{k+1}·PZ^(k+2) + …`,
each coefficient applied by `map` at the Hadamard multiplier (line 13, which is
[1, Prop. 2.8]) and the terms added with `sortPlus` (line 15).

[1] merges all `o` terms at once; here they are added in pairs, which is what
`sortPlus` is written for and denotes the same set. The recursion carries the
degree `k` down the list and the factor-count proof up, so no step needs one of
its own.

## Inputs
* `pZ` – polynomial zonotope

## Output
* evaluator of the sum over the powers, with its factor count

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The tail of [1, Alg. 2]'s sum, from degree `k + 1` upward. -/
noncomputable def PolyZonotope.evalPolySortTailP (pZ : PolyZonotope (Vec ℝ n)) :
    List (Vec ℝ n) → ℕ → {R : PolyZonotope (Vec ℝ n) // R.p = pZ.p}
  -- 15. no terms left: `0`
  | [], _ => ⟨⟨pZ.p, 0, 0, 0, Fin.elim0, fun _ => Fin.elim0, Fin.elim0⟩, rfl⟩
  | a :: rest, k =>
      -- 13. `PZⁱ ← aᵢ · PZⁱ`, the sorted power (lines 1-10, `powSort`) scaled by its coefficient
      let T := (pZ.powSort k).1.map (Entrywise.hadamardLin a)
      -- 15. the terms of higher degree, summed
      let S := PolyZonotope.evalPolySortTailP pZ rest (k + 1)
      -- 15. `sortPlus(…)`: add the term to the rest
      ⟨T.sortPlus S.1 ((pZ.powSort k).2.trans S.2.symm), (pZ.powSort k).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
