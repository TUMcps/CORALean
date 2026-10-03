import CORALean.ContSet.Taylm.Float.Operations.Det
import CORALean.ContSet.Taylm.Float.Theorems.SumOuter
import CORALean.ContSet.Taylm.Float.Theorems.SmulOuter
import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# `Taylm.det` encloses the determinant

As in the exact layer: induction on the size, the first-row expansion
(`Matrix.det_succ_row_zero`), `smul_outer` with the sign read back as `(-1)^j`, `times_outer`
and `sum_outer`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_toReal_sign (j : ℕ) :
    toReal (if j % 2 = 0 then (one : 𝕋) else neg one) = (-1) ^ j := by
  by_cases h : j % 2 = 0
  · rw [if_pos h, toReal_one, (Nat.even_iff.mpr h).neg_one_pow]
  · rw [if_neg h, toReal_neg, toReal_one,
      (Nat.odd_iff.mpr (by omega : j % 2 = 1)).neg_one_pow]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.det_outer : ∀ {d : ℕ} {A : Fin (d + 1) → Fin (d + 1) → Taylm 𝕋 n}
    {f : Fin (d + 1) → Fin (d + 1) → Vec ℝ n → ℝ}, (∀ i j, (A i j).Encloses (f i j)) →
    (Taylm.det A).Encloses fun t => (Matrix.of fun i j => f i j t).det := by -- --- PROOF ---
  intro d
  induction d with
  | zero => intro A f h; simpa [Taylm.det, Matrix.det_unique] using h 0 0
  | succ d ih =>
    intro A f h
    have hs := Taylm.sum_outer (T := fun j =>
        let s : 𝕋 := if (j : ℕ) % 2 = 0 then one else neg one
        ((A 0 j).smul s s).times (Taylm.det fun i k => A i.succ (j.succAbove k)))
      (f := fun j t => (-1) ^ (j : ℕ) * f 0 j t * (Matrix.of fun i k =>
        f i.succ (j.succAbove k) t).det)
      fun j => Taylm.times_outer
        (Taylm.smul_outer (by rw [aux_toReal_sign (𝕋 := 𝕋)]; exact ⟨le_rfl, le_rfl⟩) (h 0 j))
        (ih (A := fun i k => A i.succ (j.succAbove k)) (f := fun i k => f i.succ (j.succAbove k))
          fun i k => h _ _)
    refine fun t ht => ?_
    have := hs t ht
    simp only [Taylm.det] at *
    rw [Matrix.det_succ_row_zero]
    simpa [Matrix.submatrix] using this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
