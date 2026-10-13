module

public import CORALean.Global.Chunks
public import CORALean.HybridDynamics.Operations.GuardIntersectLevelSet

@[expose] public section

/-!
# `Location.guardTransitionLevelSet`, the transition through a nonlinear guard

[1, Sec. 3.2], the procedure its Fig. 1 draws, one `let` per step, for one guard `{g = 0}` and its
reset `r`. Step 1's reachable sets `R(τⱼ)` are the input, computed by a continuous algorithm
until they leave the invariant; Step 1 keeps those that potentially meet the guard,
`[l, u] = bound(g, R(τⱼ))` with `l ≤ 0 ∧ u ≥ 0` ([1, Sec. 4.1]). Step 2 encloses each by a box
and contracts it (`Location.guardIntersectLevelSet`), Step 3 unites consecutive runs of at most
`μ` of them (`chunks`), Step 4 encloses the guard in each united box (`intersect`, e.g.
[1, Prop. 1] or [1, Prop. 2]), Step 5 applies the reset (`reset`, e.g. [1, Eq. 14]) and Step 6
unifies the parallel sets (`unify`, e.g. the convex hull). Every operator is an argument, as the
procedure leaves each to a later section; `Theorems.GuardTransitionLevelSetOuter` states what each
must guarantee.

Real layer only: Step 1 compares real bounds, which no float scalar is supplied for here.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.2]: Steps 1-6 on the reachable sets `Rs`, for the guard of `bound`, `contract`
and `intersect` and the reset of `reset`. -/
noncomputable def Location.guardTransitionLevelSet {R T : Type} (bound : R → ℝ × ℝ)
    (box : R → Real.Interval (Vec ℝ n))
    (contract : Real.Interval (Vec ℝ n) → Real.Interval (Vec ℝ n)) (μ : ℕ)
    (intersect : Real.Interval (Vec ℝ n) → T) (reset : T → T) (unify : List T → T)
    (Rs : List R) : T :=
  let hit := Rs.filter fun Rj => (bound Rj).1 ≤ 0 ∧ 0 ≤ (bound Rj).2  -- 1: l ≤ 0 ∧ u ≥ 0
  let I := hit.map box                                                  -- 2: boxes I
  let DI := (chunks μ I).map fun c =>                                   -- 2-3: contracted,
    Location.guardIntersectLevelSet contract c.1 c.2                    --   ≤ μ united
  let F := DI.map intersect                                             -- 4: I ∩ G ⊆ F
  let RF := F.map reset                                                 -- 5: r(F)
  unify RF                                                              -- 6: unify

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
