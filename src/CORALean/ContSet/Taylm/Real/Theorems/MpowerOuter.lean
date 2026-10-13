import Mathlib.Data.Matrix.Mul
import CORALean.ContSet.Taylm.Real.Operations.Mpower
import CORALean.ContSet.Taylm.Real.Theorems.MmulOuter
import CORALean.ContSet.Taylm.Real.Theorems.ConstOuter

/-!
# `Taylm.mpower` encloses the matrix power

Entry `(i, j)` of the power encloses the `(i, j)` entry of the power of the matrix of the enclosed
functions, pointwise: `M ^ 0 = 1`, `M ^ (e + 1) = M ^ e * M`, the order of `mpower`'s loop.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.mpower_outer {k : ℕ} {A : Fin k → Fin k → Taylm n} {F : Fin k → Fin k → Vec ℝ n → ℝ}
    (hA : ∀ i j, (A i j).Encloses (F i j)) (e : ℕ) (i j : Fin k) :
    (Taylm.mpower A e i j).Encloses fun t =>
      (Matrix.of (fun i j => F i j t) ^ e) i j := by -- --- PROOF ---
  -- the positive exponents, by the loop's own recursion: `P ↦ P * A`
  have key : ∀ e : ℕ, ∀ i j, ((fun P => Taylm.mmul P A)^[e] A i j).Encloses
      fun t => (Matrix.of (fun i j => F i j t) ^ (e + 1)) i j := by
    intro e
    induction e with
    | zero => intro i j; simpa using hA i j
    | succ e ih =>
      intro i j
      -- one more factor: `M ^ (e + 2) = M ^ (e + 1) * M`
      rw [Function.iterate_succ_apply']
      have hf : (fun t : Vec ℝ n => (Matrix.of (fun i j => F i j t) ^ (e + 1 + 1)) i j) =
          fun t => ((Matrix.of fun i k => (Matrix.of (fun i j => F i j t) ^ (e + 1)) i k) *
            Matrix.of (fun k j => F k j t)) i j := by
        funext t
        rw [pow_succ _ (e + 1)]
        rfl
      rw [hf]
      exact Taylm.mmul_outer ih hA i j
  -- exponent `0` is the identity matrix as constants, the others are `key`
  cases e with
  | zero =>
    simpa [Taylm.mpower, Matrix.one_apply, apply_ite] using
      Taylm.const_outer (n := n) (if i = j then 1 else 0) 0
  | succ e => exact key e i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
