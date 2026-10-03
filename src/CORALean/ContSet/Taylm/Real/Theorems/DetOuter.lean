import CORALean.ContSet.Taylm.Real.Operations.Det
import CORALean.ContSet.Taylm.Real.Theorems.SumOuter
import CORALean.ContSet.Taylm.Real.Theorems.SmulOuter
import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# `Taylm.det` encloses the determinant

Induction on the size, expanding the determinant along its first row
(`Matrix.det_succ_row_zero`) exactly as `Taylm.det` does: each summand is the sign times the entry
(`smul_outer`) times the minor's determinant (`times_outer`, the induction hypothesis), and the sum
is `sum_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.det_outer : ∀ {d : ℕ} {A : Fin (d + 1) → Fin (d + 1) → Taylm n}
    {f : Fin (d + 1) → Fin (d + 1) → Vec ℝ n → ℝ}, (∀ i j, (A i j).Encloses (f i j)) →
    (Taylm.det A).Encloses fun t => (Matrix.of fun i j => f i j t).det := by -- --- PROOF ---
  intro d
  induction d with
  | zero => intro A f h; simpa [Taylm.det, Matrix.det_unique] using h 0 0
  | succ d ih =>
    intro A f h
    have hs := Taylm.sum_outer (T := fun j => ((A 0 j).smul ((-1) ^ (j : ℕ))).times
        (Taylm.det fun i k => A i.succ (j.succAbove k)))
      (f := fun j t => (-1) ^ (j : ℕ) * f 0 j t * (Matrix.of fun i k =>
        f i.succ (j.succAbove k) t).det)
      fun j => Taylm.times_outer (Taylm.smul_outer _ (h 0 j))
        (ih (A := fun i k => A i.succ (j.succAbove k)) (f := fun i k => f i.succ (j.succAbove k))
          fun i k => h _ _)
    refine fun t ht => ?_
    have := hs t ht
    simp only [Taylm.det] at *
    rw [Matrix.det_succ_row_zero]
    simpa [Matrix.submatrix] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
