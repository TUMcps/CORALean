module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortTailP
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyReal
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PowSortPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPlusPoint

@[expose] public section

/-!
# [1, Alg. 2]'s sum over the powers is the polynomial from that degree up

The induction behind `evalPolySort_exact`, stated with the degree `k` the
recursion carries: the tail is `x^(k+1)` times Horner's rule on what is left of
the coefficient list, which is what makes the step fall out of
`evalPolyReal`'s own recursion.

`sortPlus_point` splits the term off, `map_point` applies the coefficient and
`powSort_point` names the power; the rest is `ring` at one coordinate.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.evalPolySortTail_point (pZ : PolyZonotope (Vec ℝ n))
    (coeffs : List (Vec ℝ n)) (k : ℕ) (a : Fin pZ.p → ℝ) : -- --- STMT ---
    (pZ.evalPolySortTailP coeffs k).1.point
        (fun l => a (Fin.cast (pZ.evalPolySortTailP coeffs k).2 l))
      = fun i => pZ.point a i ^ (k + 1)
          * PolyZonotope.evalPolyReal (coeffs.map fun v => v i)
              (pZ.point a i) := by -- --- PROOF ---
  induction coeffs generalizing k with
  | nil =>
    -- an empty tail is the zero set, and Horner's rule on `[]` is `0`
    funext i
    simp [PolyZonotope.evalPolySortTailP, PolyZonotope.point, PolyZonotope.evalPolyReal]
  | cons a0 rest ih =>
    calc (pZ.evalPolySortTailP (a0 :: rest) k).1.point
          (fun l => a (Fin.cast (pZ.evalPolySortTailP (a0 :: rest) k).2 l))
        = ((pZ.powSort k).1.map (Entrywise.hadamardLin a0)).point
              (fun l => a (Fin.cast (pZ.powSort k).2 l))
            + (pZ.evalPolySortTailP rest (k + 1)).1.point
              (fun l => a (Fin.cast (pZ.evalPolySortTailP rest (k + 1)).2 l)) :=
          PolyZonotope.sortPlus_point _ _ _ _
      -- the coefficient comes out of the term, the power out of `powSort`
      _ = Entrywise.hadamardLin a0 ((pZ.powSort k).1.point
              (fun l => a (Fin.cast (pZ.powSort k).2 l)))
            + (pZ.evalPolySortTailP rest (k + 1)).1.point
              (fun l => a (Fin.cast (pZ.evalPolySortTailP rest (k + 1)).2 l)) :=
          congrArg (fun x => x + _) (PolyZonotope.map_point _ _ _)
      _ = Entrywise.hadamardLin a0 (fun i => pZ.point a i ^ (k + 1))
            + (fun i => pZ.point a i ^ (k + 1 + 1)
                * PolyZonotope.evalPolyReal (rest.map fun v => v i) (pZ.point a i)) := by
          rw [PolyZonotope.powSort_point pZ k a, ih (k + 1)]
      _ = fun i => pZ.point a i ^ (k + 1)
            * PolyZonotope.evalPolyReal ((a0 :: rest).map fun v => v i) (pZ.point a i) := by
          funext i
          show a0 i * pZ.point a i ^ (k + 1)
              + pZ.point a i ^ (k + 1 + 1)
                * PolyZonotope.evalPolyReal (rest.map fun v => v i) (pZ.point a i)
            = pZ.point a i ^ (k + 1)
              * PolyZonotope.evalPolyReal ((a0 :: rest).map fun v => v i) (pZ.point a i)
          rw [List.map_cons, PolyZonotope.evalPolyReal]
          ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
