module

public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.Taylm.Float.Operations.Mpower
public import CORALean.ContSet.Taylm.Float.Theorems.MmulOuter
public import CORALean.ContSet.Taylm.Float.Theorems.ConstOuter

@[expose] public section

/-!
# `Taylm.mpower` encloses the matrix power, float

Entry `(i, j)` of the power encloses the `(i, j)` entry of the power of the matrix of the enclosed
functions, pointwise: `M ^ 0 = 1`, `M ^ (e + 1) = M ^ e * M`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.mpower_outer {k : ℕ} {A : Fin k → Fin k → Taylm 𝕋 n}
    {F : Fin k → Fin k → Vec ℝ n → ℝ} (hA : ∀ i j, (A i j).Encloses (F i j)) (e : ℕ)
    (i j : Fin k) :
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
    have h := Taylm.const_outer (𝕋 := 𝕋) (n := n) (if i = j then FloatOps.one else FloatOps.zero) 0
    have hf : (fun t : Vec ℝ n => (Matrix.of (fun i j => F i j t) ^ 0) i j) =
        fun _ => toReal (if i = j then (FloatOps.one : 𝕋) else FloatOps.zero) := by
      funext t
      by_cases hij : i = j <;> simp [hij, toReal_one, toReal_zero]
    rw [hf]
    exact h
  | succ e => exact key e i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
