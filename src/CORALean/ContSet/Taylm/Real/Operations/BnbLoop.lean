import CORALean.ContSet.Taylm.Real.Operations.BnbStep
import CORALean.ContSet.Taylm.Real.Operations.ListMin
import CORALean.ContSet.Taylm.Real.Operations.ListMax

/-!
# The branch and bound loop

Lines 6-32 of [1, Alg. 1]'s `repeat … until`: a step, the union of all boxes' intervals (line 30),
and the stopping test of line 31, that neither end moved by more than `2ε·rad([r∪])`. The source's
loop has no bound on its iterations; here `fuel` bounds them, and the union is returned when it
runs out.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.bnbLoop (bnd : (Fin n → ℝ × ℝ) → ℝ × ℝ) (ε : ℝ) :
    ℕ → List (Fin n → ℝ × ℝ) → ℝ × ℝ
  | 0, l => (Taylm.listMin (fun B => (bnd B).1) l, Taylm.listMax (fun B => (bnd B).2) l)
  | fuel + 1, l =>
    -- 7: the previous union
    let prev := (Taylm.listMin (fun B => (bnd B).1) l, Taylm.listMax (fun B => (bnd B).2) l)
    let l₁ := Taylm.bnbStep bnd l
    -- 30: the new union
    let cur := (Taylm.listMin (fun B => (bnd B).1) l₁, Taylm.listMax (fun B => (bnd B).2) l₁)
    -- 31: stop once neither end moved by more than `2ε·rad`
    if |prev.2 - cur.2| ≤ 2 * ε * ((cur.2 - cur.1) / 2) ∧
        |cur.1 - prev.1| ≤ 2 * ε * ((cur.2 - cur.1) / 2) then cur
    else Taylm.bnbLoop bnd ε fuel l₁

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
