module

public import CORALean.Global.Chunks
public import CORALean.HybridDynamics.Operations.GuardIntersectLevelSet

@[expose] public section

/-!
# `Location.guardTransitionLevelSet`, the transition through a nonlinear guard

[1, Sec. 3.2], the procedure its Fig. 1 draws, one `let` per step, for one guard `{g = 0}` and its
reset `r`. Step 1's reach sets are the input; Step 1 keeps those that potentially meet the guard.
Step 2 boxes and contracts each (`Location.guardIntersectLevelSet`), Step 3 unites runs of at
most `μ` (`chunks`), Step 4 encloses the guard in each (`intersect`, e.g. [1, Prop. 1, 2]), Step 5
applies the reset (`reset`, e.g. [1, Eq. 14]) and Step 6 unifies the parallel sets (`unify`).
Every operator is an argument; `Theorems.GuardTransitionLevelSetOuter` states what each must
guarantee. Real layer only: Step 1 compares real bounds.

## Inputs
* `R` – reach set type
* `T` – enclosure type
* `bound` – bound of the guard function
* `box` – box enclosure
* `contract` – box contractor
* `μ` – chunk size
* `intersect` – guard intersection of a box
* `reset` – reset map
* `unify` – union of parallel sets
* `Rs` – reach sets

## Output
* unified sets after the reset

## References

* [1] [N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.](../../../../references/2020/kochdumper-hscc-nonlinear-guards.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.2]: Steps 1-6 on the reachable sets `Rs`, for the guard of `bound`, `contract`
and `intersect` and the reset of `reset`. -/
noncomputable def Location.guardTransitionLevelSet {R T : Type} (bound : R → Real.Interval ℝ)
    (box : R → Real.Interval (Vec ℝ n))
    (contract : Real.Interval (Vec ℝ n) → Real.Interval (Vec ℝ n)) (μ : ℕ)
    (intersect : Real.Interval (Vec ℝ n) → T) (reset : T → T) (unify : List T → T)
    (Rs : List R) : T :=
  let hit := Rs.filter fun Rj => (bound Rj).inf ≤ 0 ∧ 0 ≤ (bound Rj).sup  -- 1: l ≤ 0 ∧ u ≥ 0
  let I := hit.map box                                                  -- 2: boxes I
  let DI := (chunks μ I).map fun c =>                                   -- 2-3: contracted,
    Location.guardIntersectLevelSet contract c.1 c.2                    --   ≤ μ united
  let F := DI.map intersect                                             -- 4: I ∩ G ⊆ F
  let RF := F.map reset                                                 -- 5: r(F)
  unify RF                                                              -- 6: unify

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
