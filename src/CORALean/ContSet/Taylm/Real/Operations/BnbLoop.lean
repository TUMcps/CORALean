module

public import CORALean.ContSet.Taylm.Real.Operations.BnbStep
public import CORALean.ContSet.Taylm.Real.Operations.ListMin
public import CORALean.ContSet.Taylm.Real.Operations.ListMax

@[expose] public section

/-!
# The branch and bound loop

Lines 6-32 of [1, Alg. 1]'s `repeat … until`: a step, the union of all boxes' intervals (line 30),
and the stopping test of line 31, that neither end moved by more than `2ε·rad([r∪])`. The source's
loop has no bound on its iterations; here `fuel` bounds them, and the union is returned when it
runs out.

## Inputs
* `bnd` – bounding function on a box
* `ε` – tolerance

## Output
* enclosure of the range from the search loop

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.bnbLoop (bnd : (Fin n → Interval ℝ) → Interval ℝ) (ε : ℝ) :
    ℕ → List (Fin n → Interval ℝ) → Interval ℝ
  | 0, l => ⟨Taylm.listMin (fun B => (bnd B).inf) l, Taylm.listMax (fun B => (bnd B).sup) l⟩
  | fuel + 1, l =>
    -- 7: the previous union
    let prev : Interval ℝ := ⟨Taylm.listMin (fun B => (bnd B).inf) l,
        Taylm.listMax (fun B => (bnd B).sup) l⟩
    let l₁ := Taylm.bnbStep bnd l
    -- 30: the new union
    let cur : Interval ℝ := ⟨Taylm.listMin (fun B => (bnd B).inf) l₁,
        Taylm.listMax (fun B => (bnd B).sup) l₁⟩
    -- 31: stop once neither end moved by more than `2ε·rad`
    if |prev.sup - cur.sup| ≤ 2 * ε * ((cur.sup - cur.inf) / 2) ∧
        |cur.inf - prev.inf| ≤ 2 * ε * ((cur.sup - cur.inf) / 2) then cur
    else Taylm.bnbLoop bnd ε fuel l₁

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
