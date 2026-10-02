import CORALean.ContSet.Taylm.Real.Operations.Sum
import CORALean.ContSet.Taylm.Real.Theorems.PlusOuter

/-!
# `Taylm.sum` encloses the sum
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sum_outer : ∀ {m : ℕ} {T : Fin m → Taylm n} {f : Fin m → Vec ℝ n → ℝ},
    (∀ i, (T i).Encloses (f i)) → (Taylm.sum T).Encloses fun t => ∑ i, f i t := by -- --- PROOF ---
  intro m
  induction m with
  | zero => intro T f _ t _; simp [Taylm.sum, Taylm.poly]
  | succ m ih =>
    intro T f h
    have := Taylm.plus_outer (h 0) (ih (T := fun i => T i.succ) (f := fun i => f i.succ)
      fun i => h i.succ)
    simpa only [Taylm.sum, Fin.sum_univ_succ] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
