import CORALean.ContSet.Taylm.Real.Operations.Ldb
import CORALean.ContSet.Taylm.Real.Theorems.LdbLoopLe

/-!
# `Taylm.ldb` is a lower bound

[1, Sec. 2]'s LDB is sound: whatever `ε` and however many repetitions, its result is below the
enclosed function on the normalized box.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.ldb_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : ℝ) (fuel : ℕ)
    {t : Vec ℝ n} (ht : t ∈ Taylm.box n) : T.ldb ε fuel ≤ f t :=
  Taylm.ldbLoop_le h ε fuel _ (fun _ => ⟨le_refl _, le_refl _⟩) t fun k => abs_le.1 (ht k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
