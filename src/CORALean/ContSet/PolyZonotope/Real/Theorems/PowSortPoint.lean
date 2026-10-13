module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PowSort
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MergePoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPoint

@[expose] public section

/-!
# The powers [1, Alg. 2] builds are the powers

`powSort pZ k`'s point is `pZ`'s point raised to `k + 1`, coordinatewise. The
induction is `mul_point` once per step, with `sort` and `merge` contributing
nothing — which is the whole content of [1, Alg. 2] lines 3-10.

Written as a `calc` rather than a chain of rewrites: the factor vector is read
through `Fin.cast` at each level, and rewriting under that binder asks the
elaborator to identify two index types it will not identify in tactic position.

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

theorem PolyZonotope.powSort_point (pZ : PolyZonotope (Vec ℝ n)) (k : ℕ) (a : Fin pZ.p → ℝ) :
    (pZ.powSort k).1.point (fun l => a (Fin.cast (pZ.powSort k).2 l))
      = fun i => pZ.point a i ^ (k + 1) := by -- --- PROOF ---
  induction k with
  | zero =>
    -- the first power is `sort`, and its own `p`-proof is `rfl`
    show pZ.sort.point a = _
    rw [PolyZonotope.sort_point]
    funext i
    rw [pow_one]
  | succ m ih =>
    calc (pZ.powSort (m + 1)).1.point (fun l => a (Fin.cast (pZ.powSort (m + 1)).2 l))
        = ((pZ.powSort m).1.mul pZ (pZ.powSort m).2).point
            (fun l => a (Fin.cast (pZ.powSort m).2 l)) :=
          (PolyZonotope.merge_point _ _).trans (PolyZonotope.sort_point _ _)
      -- the right factor's own vector is the left's cast back, so it is `a`
      _ = (pZ.powSort m).1.point (fun l => a (Fin.cast (pZ.powSort m).2 l)) * pZ.point a :=
          PolyZonotope.mul_point _ _ _ _
      _ = (fun i => pZ.point a i ^ (m + 1)) * pZ.point a :=
          congrArg (fun f => f * pZ.point a) ih
      _ = fun i => pZ.point a i ^ (m + 1 + 1) := by
          funext i
          show pZ.point a i ^ (m + 1) * pZ.point a i = pZ.point a i ^ (m + 1 + 1)
          ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
