module

public import CORALean.ContSet.Interval.Float.Operations.DescProd
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.Global.DescProd

@[expose] public section

/-!
# `Interval.descProd` encloses the product of any matrices in the boxes

Induction on the number of factors, against `matMul_outer`; the empty product is `mem_point` at
the stored identity block, read back as `(1 : Mat ℝ n n)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.descProd_outer (A : ℕ → Interval (Mat 𝕋 n n)) {M : ℕ → Mat ℝ n n}
    (hM : ∀ k, M k ∈ (A k).construct) (hi d : ℕ) :
    CORALean.descProd M hi d ∈ (Interval.descProd A hi d).construct := by -- --- PROOF ---
  induction d generalizing hi with
  | zero =>
    -- the empty product is the identity, `matPow`'s zeroth power
    have h := Interval.matPow_outer (A hi) (hM hi) 0
    rw [pow_zero] at h
    exact h
  | succ d ih =>
    -- one more factor on the left
    show M hi * CORALean.descProd M (hi - 1) d ∈
      (Interval.matMul (A hi) (Interval.descProd A (hi - 1) d)).materialiseMat.construct
    rw [Interval.materialiseMat_eq]
    exact Interval.matMul_outer _ _ (hM hi) (ih (hi - 1))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
