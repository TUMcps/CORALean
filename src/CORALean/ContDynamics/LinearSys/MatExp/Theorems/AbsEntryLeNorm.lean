import CORALean.ContSet.Interval.Real.Interval
/-!
# An entry never exceeds the `l∞` operator norm

Sound because under the `l∞` operator norm an entry never exceeds its row sum,
and a row sum never exceeds the norm — the two `Finset` bounds chained here.
Every entrywise enclosure in this directory reaches its bound through this.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- Under the `l∞` operator norm an entry never exceeds the whole norm. -/
theorem abs_entry_le_norm {m k : ℕ} (M : Mat ℝ m k) (i : Fin m) (j : Fin k) :
    |M i j| ≤ ‖M‖ := by -- --- PROOF ---
  have h : ‖M i j‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact le_trans (Finset.single_le_sum (f := fun j => ‖M i j‖₊)
      (fun _ _ => zero_le) (Finset.mem_univ j))
      (Finset.le_sup (f := fun i => ∑ j, ‖M i j‖₊) (Finset.mem_univ i))
  rw [← Real.norm_eq_abs]
  exact_mod_cast h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
