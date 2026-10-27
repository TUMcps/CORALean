module

public import CORALean.ContSet.Taylm.Real.Operations.BranchAndBound
public import CORALean.ContSet.Taylm.Real.Theorems.BnbLoopMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyBoxBoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.ReexpBoxBoundsMem

@[expose] public section

/-!
# Branch and bound encloses the polynomial's range

[1, Alg. 1] returns an interval holding `P` on all of `[x]`, in either setting, for any `ε` and
however soon it stops: each sub-box bound is sound (eq. (12), or the re-expansion), and the
loop's boxes always cover `[x]`.

## Inputs
* `P` – terms of the polynomial
* `X` – domain box
* `ε` – tolerance
* `adv` – advanced bounding flag
* `fuel` – step budget
* `t` – point

## Hypotheses
* `ht` – point lies in the domain box

## Conclusion
* the enclosure contains the polynomial's value at the point

## References

* [1] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.branchAndBound_mem (P : List (ℝ × (Fin n → ℕ))) (X : Fin n → Interval ℝ) (ε : ℝ)
    (adv : Bool) (fuel : ℕ) {t : Vec ℝ n} (ht : Taylm.IsInBox X t) : -- --- CONCL ---
    (Taylm.branchAndBound P X ε adv fuel).inf ≤ Taylm.polyOf P t ∧
      Taylm.polyOf P t ≤ (Taylm.branchAndBound P X ε adv fuel).sup := by -- --- PROOF ---
  refine Taylm.bnbLoop_mem (fun B t hB => ?_) ε ht fuel [X] fun t' h' => ⟨X, by simp, h'⟩
  -- each setting's bound of a sub-box
  cases adv
  · exact Taylm.polyBoxBounds_mem P hB
  · exact Taylm.reexpBoxBounds_mem P hB

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
