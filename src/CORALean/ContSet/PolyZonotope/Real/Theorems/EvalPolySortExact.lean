module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySort
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortFactorCount
public import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolySortTailPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ShiftPoint

@[expose] public section

/-!
# [1, Alg. 2] is exactly the polynomial, evaluated coordinatewise

The soundness half of [1, Prop. 3.5], in the form `evalPoly_exact` states it:
about `point` and not `construct`, so no product of sets appears, and against
`evalPolyReal` — the same reference evaluator Horner's rule is measured by,
which is what says the two routes reach the same value.

What is *not* claimed: [1, Prop. 3.5] also gives the result `O(h^o)`
generators and a running cost, and neither is proved here or asserted under
`Complexity/`. Of its regularity only `merge_col_injective` holds,
for the reason `Merge.lean` gives.

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

theorem PolyZonotope.evalPolySort_exact (pZ : PolyZonotope (Vec ℝ n))
    (coeffs : List (Vec ℝ n)) (a : Fin pZ.p → ℝ) :
    (pZ.evalPolySort coeffs).point (fun l => a (Fin.cast (pZ.evalPolySort_p coeffs) l))
      = fun i => PolyZonotope.evalPolyReal (coeffs.map fun v => v i)
          (pZ.point a i) := by -- --- PROOF ---
  match coeffs with
  | [] =>
    -- no coefficients at all: the zero set, and `evalPolyReal []` is `0`
    funext i
    simp [PolyZonotope.evalPolySort, PolyZonotope.evalPolySortP, PolyZonotope.point,
      PolyZonotope.evalPolyReal]
  | a0 :: rest =>
    calc (pZ.evalPolySort (a0 :: rest)).point
          (fun l => a (Fin.cast (pZ.evalPolySort_p (a0 :: rest)) l))
        = (pZ.evalPolySortTailP rest 0).1.point
              (fun l => a (Fin.cast (pZ.evalPolySortTailP rest 0).2 l)) + a0 :=
          PolyZonotope.shift_point _ _ _
      -- the tail is the polynomial from degree one up; `a0` is the constant term
      _ = (fun i => pZ.point a i ^ (0 + 1)
            * PolyZonotope.evalPolyReal (rest.map fun v => v i) (pZ.point a i)) + a0 :=
          congrArg (fun x => x + a0) (PolyZonotope.evalPolySortTail_point pZ rest 0 a)
      _ = fun i => PolyZonotope.evalPolyReal ((a0 :: rest).map fun v => v i)
            (pZ.point a i) := by
          funext i
          show pZ.point a i ^ (0 + 1)
              * PolyZonotope.evalPolyReal (rest.map fun v => v i) (pZ.point a i) + a0 i
            = PolyZonotope.evalPolyReal ((a0 :: rest).map fun v => v i) (pZ.point a i)
          rw [List.map_cons, PolyZonotope.evalPolyReal]
          ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
