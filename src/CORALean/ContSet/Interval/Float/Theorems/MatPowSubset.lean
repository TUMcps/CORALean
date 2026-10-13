import CORALean.ContSet.Interval.Float.Theorems.MatMulSubset
import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter

/-!
# A real box power inside a float one, the base box inside

`matMul_subset` along `matPow`'s recursion: a non-empty real box inside a float
one has every real power box inside the float power. Each real power is
non-empty, holding a member's power, which is what `matMul_subset` asks of its
second factor; the base case is the identity, which the float power holds as any
member's zeroth power.

What lets a point of a real power box that is no member's power — a product of
different members, averaged — be read in the float box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matPow_subset {X : Real.Interval (Mat ℝ n n)} {X' : Interval (Mat 𝕋 n n)}
    {M₀ : Mat ℝ n n} (hM₀ : M₀ ∈ X.construct) (hX : X.construct ⊆ X'.construct) (k : ℕ) :
    (Real.Interval.matPow X k).construct ⊆ (Interval.matPow X' k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    intro P hP
    -- the real zeroth power is the identity alone
    have h1 : P = 1 := by
      funext i j
      exact le_antisymm (Real.Interval.mem_mat_iff.mp hP i j).2
        (Real.Interval.mem_mat_iff.mp hP i j).1
    rw [h1, ← pow_zero M₀]
    exact Interval.matPow_outer X' (hX hM₀) 0
  | succ k ih =>
    show _ ⊆ (Interval.matMul X' (Interval.matPow X' k)).materialiseMat.construct
    rw [Interval.materialiseMat_eq]
    exact Interval.matMul_subset hM₀ (Real.Interval.matPow_outer X hM₀ k) hX ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
